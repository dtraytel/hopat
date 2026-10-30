section \<open>Soundness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Sound
  imports Bicompose_Norm
begin

text \<open>
  A theorem with flex-flex pairs \<open>tps\<close> and proposition \<open>P\<close> is valid if every ground instance
  of \<open>P\<close> holds whose instance of \<open>tps\<close> is solved. The theorems produced by \<open>bicompose_aux\<close> from
  a valid proof state and a valid rule are valid.
\<close>

subsection \<open>Prefixes\<close>

fun nall :: "litem list \<Rightarrow> nat" where
  "nall [] = 0"
| "nall (LImp c H # p) = nall p"
| "nall (LAll c a T # p) = Suc (nall p)"

fun pvars :: "litem list \<Rightarrow> indexname set" where
  "pvars [] = {}"
| "pvars (LImp c H # p) = vars c \<union> vars H \<union> pvars p"
| "pvars (LAll c a T # p) = vars c \<union> pvars p"

lemma vars_lift_pre: "vars (lift_pre p X) = pvars p \<union> vars X"
  by (induction p X rule: lift_pre.induct) auto

lemma vars_abs_pre: "vars (abs_pre p X) = vars X"
  by (induction p X rule: abs_pre.induct) auto

lemma sm_abs_pre: "sm \<rho> \<sigma> (abs_pre p X) = Abs_m (nall p) (sm \<rho> \<sigma> X)"
  by (induction p X rule: abs_pre.induct) auto

context pure_sem
begin

text \<open>
  If the closures of \<open>X\<close> and \<open>Y\<close> over the parameters of a prefix are equal, then \<open>Y\<close> under the
  prefix holds if \<open>X\<close> does.
\<close>

lemma holds_lift_pre_transfer_substs:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "\<forall>i\<in>set p. litem_ok i"
    "cok (lift_pre p X)" "cok (lift_pre p Y)" "\<forall>w\<in>set ws. closed w"
    "no_loose_bound (tr (lift_pre p X)) (length ws)" "no_loose_bound (tr (lift_pre p Y)) (length ws)"
    "\<And>vs. \<forall>v\<in>set vs. closed v \<Longrightarrow> length vs = nall p \<Longrightarrow>
      substs 0 (vs @ ws) (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 (vs @ ws) (sm \<rho> \<sigma> Y)"
    "holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p X)))"
  shows "holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Y)))"
  using assms(3-)
proof (induction p arbitrary: ws)
  case Nil
  have cl: "closed (substs 0 ws (sm \<rho> \<sigma> Z))" if "no_loose_bound (tr Z) (length ws)" for Z
    using no_loose_bound_substs[OF Nil.prems(4), of _ 0] that assms(2) by (simp add: no_loose_bound_sm)
  have "substs 0 ([] @ ws) (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 ([] @ ws) (sm \<rho> \<sigma> Y)"
    by (rule Nil.prems(7)) simp_all
  then have "substs 0 ws (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 ws (sm \<rho> \<sigma> Y)" by simp
  with Nil.prems(5,6,8) show ?case using holds_equiv[OF cl cl] by simp
next
  case (Cons i p)
  have cl: "closed (substs 0 ws (sm \<rho> \<sigma> Z))" if "no_loose_bound (tr Z) (length ws)" for Z
    using no_loose_bound_substs[OF Cons.prems(4), of _ 0] that assms(2) by (simp add: no_loose_bound_sm)
  show ?case
  proof (cases i)
    case (LImp c H)
    from Cons.prems(1) LImp obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    from cok_imp[of _ U H] Cons.prems(2,3) LImp c have ok: "U = imp_type" "cok H"
      "cok (lift_pre p X)" "cok (lift_pre p Y)" by auto
    then have c: "c = implies" using c by (simp add: implies_imp_type)
    have sm: "substs 0 ws (sm \<rho> \<sigma> (lift_pre (i # p) Z)) =
        dIMP (substs 0 ws (sm \<rho> \<sigma> H)) (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Z)))" for Z
      using assms(1) by (simp add: LImp c)
    have nb: "no_loose_bound (tr H) (length ws)" "no_loose_bound (tr (lift_pre p X)) (length ws)"
      "no_loose_bound (tr (lift_pre p Y)) (length ws)"
      using Cons.prems(5,6) by (simp_all add: LImp c)
    have "holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p X))) \<Longrightarrow> holds (substs 0 ws (sm \<rho> \<sigma> (lift_pre p Y)))"
      by (rule Cons.IH) (use Cons.prems ok nb in \<open>simp_all add: LImp\<close>)
    with Cons.prems(8) show ?thesis
      unfolding sm by (simp add: holds_imp cl nb)
  next
    case (LAll c a T)
    from Cons.prems(1) LAll obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    from Cons.prems(2,3) LAll c have ok: "U = all_type T" "cok (lift_pre p X)" "cok (lift_pre p Y)"
      by auto
    then have c: "c = all_const T" using c by (simp add: all_const_all_type)
    have sm: "substs 0 ws (sm \<rho> \<sigma> (lift_pre (i # p) Z)) =
        dALL (tsubst \<rho> T) (substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p Z)))" for Z
      using assms(1) by (simp add: LAll c)
    have nb: "no_loose_bound (tr (lift_pre p X)) (Suc (length ws))"
      "no_loose_bound (tr (lift_pre p Y)) (Suc (length ws))"
      using Cons.prems(5,6) by (simp_all add: LAll c)
    have nb1: "no_loose_bound (substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p Z))) 1"
      if "no_loose_bound (tr (lift_pre p Z)) (Suc (length ws))" for Z
      using no_loose_bound_substs[OF Cons.prems(4), of _ "Suc 0"] that assms(2) by (simp add: no_loose_bound_sm)
    have eq: "(substs (Suc 0) ws t)[u/0] = substs 0 (u # ws) t" if "inhab (tsubst \<rho> T) u" for u t
      using substs_Suc_subst[OF inhab_closed[OF that] Cons.prems(4)] by simp
    have IH: "holds (substs 0 (u # ws) (sm \<rho> \<sigma> (lift_pre p X))) \<Longrightarrow>
        holds (substs 0 (u # ws) (sm \<rho> \<sigma> (lift_pre p Y)))" if u: "inhab (tsubst \<rho> T) u" for u
    proof (rule Cons.IH)
      show "substs 0 (vs @ u # ws) (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 (vs @ u # ws) (sm \<rho> \<sigma> Y)"
        if "\<forall>v\<in>set vs. closed v" "length vs = nall p" for vs
      proof -
        have "substs 0 ((vs @ [u]) @ ws) (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 ((vs @ [u]) @ ws) (sm \<rho> \<sigma> Y)"
          by (rule Cons.prems(7)) (use that inhab_closed[OF u] in \<open>simp_all add: LAll\<close>)
        then show ?thesis by simp
      qed
    qed (use Cons.prems ok nb inhab_closed[OF u] in \<open>simp_all add: LAll\<close>)
    have "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds ((substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p X)))[u/0])"
      using Cons.prems(8) unfolding sm by (simp add: holds_all[OF nb1[OF nb(1)]])
    then have "\<forall>u. inhab (tsubst \<rho> T) u \<longrightarrow> holds ((substs (Suc 0) ws (sm \<rho> \<sigma> (lift_pre p Y)))[u/0])"
      using IH eq by simp
    then show ?thesis unfolding sm by (simp add: holds_all[OF nb1[OF nb(2)]])
  qed
qed

lemma holds_lift_pre_transfer:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "\<forall>i\<in>set p. litem_ok i"
    "cok (lift_pre p X)" "cok (lift_pre p Y)"
    "no_loose_bound (tr (lift_pre p X)) 0" "no_loose_bound (tr (lift_pre p Y)) 0"
    "sm \<rho> \<sigma> (abs_pre p X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (abs_pre p Y)"
    "holds (sm \<rho> \<sigma> (lift_pre p X))"
  shows "holds (sm \<rho> \<sigma> (lift_pre p Y))"
proof -
  let ?n = "nall p"
  have e: "Abs_m ?n (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?n (sm \<rho> \<sigma> Y)"
    using assms(8) by (simp add: sm_abs_pre)
  have "substs 0 vs (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 vs (sm \<rho> \<sigma> Y)"
    if "\<forall>v\<in>set vs. closed v" "length vs = ?n" for vs
  proof -
    have cu: "\<forall>u\<in>set (rev vs). closed u" "length (rev vs) = ?n" using that by simp_all
    have "substs 0 vs (sm \<rho> \<sigma> X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?n (sm \<rho> \<sigma> X) \<degree>\<degree> rev vs"
      using Abs_m_apps_substs[OF cu, of "sm \<rho> \<sigma> X"] by (simp add: equiv_sym beta_into_equiv)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?n (sm \<rho> \<sigma> Y) \<degree>\<degree> rev vs"
      by (rule equiv_list_app[OF e]) (simp add: list_all2_refl)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> substs 0 vs (sm \<rho> \<sigma> Y)"
      using Abs_m_apps_substs[OF cu, of "sm \<rho> \<sigma> Y"] by (simp add: beta_into_equiv)
    finally show ?thesis .
  qed
  then show ?thesis
    using holds_lift_pre_transfer_substs[OF assms(1-5), of "[]"] assms(6,7,9) by simp
qed

end


subsection \<open>Renaming lifted premises\<close>

lemma sm_lift_pre_ren:
  assumes "\<forall>x\<in>pvars p. snd x \<le> m" "\<forall>x\<in>vars X. m < snd x"
  shows "sm \<rho> \<sigma> (lift_pre p (ren_term r X)) = sm \<rho> (\<sigma> \<circ>\<^sub>s rsub m (fst r)) (lift_pre p X)"
  using assms by (induction p X rule: lift_pre.induct) (auto simp: sm_ren_term sm_rsub_id)


subsection \<open>The hypotheses along the spine\<close>

function spine_hyps :: "pterm \<Rightarrow> pterm list" where
  "spine_hyps t =
    (case dest_imp t of
      Some (H, B) \<Rightarrow> H # spine_hyps B
    | None \<Rightarrow> (case dest_all t of Some (_, _, b) \<Rightarrow> spine_hyps b | None \<Rightarrow> []))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare spine_hyps.simps[simp del]

fun phyps :: "litem list \<Rightarrow> pterm list" where
  "phyps [] = []"
| "phyps (LImp c H # p) = H # phyps p"
| "phyps (LAll c a T # p) = phyps p"

lemma vars_phyps: "H \<in> set (phyps p) \<Longrightarrow> vars H \<subseteq> pvars p"
  by (induction p rule: phyps.induct) auto

lemma spine_hyps_lift_pre: "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> spine_hyps (lift_pre p X) = phyps p @ spine_hyps X"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) (subst spine_hyps.simps; auto)+
qed simp

lemma count_prems_lift_pre_le:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic Y \<Longrightarrow> count_prems (lift_pre p Y) \<le> ilength (phyps p)"
proof (induction p)
  case Nil
  then show ?case by (subst count_prems.simps) (simp add: atomic_def)
next
  case (Cons i p)
  then show ?case by (cases i) (subst count_prems.simps; auto)+
qed

lemma count_prems_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic Y \<Longrightarrow> count_prems (strip_all_body (lift_pre p Y)) \<le> ilength (phyps p)"
proof (induction p)
  case Nil
  then show ?case by (subst strip_all_body.simps, subst count_prems.simps) (simp add: atomic_def)
next
  case (Cons i p)
  then show ?case
    by (cases i) (subst strip_all_body.simps; use count_prems_lift_pre_le[of "i # p" Y] in auto)+
qed

lemma skip_unb_take:
  "0 \<le> n \<Longrightarrow> \<forall>H\<in>set (take (nat_of_integer n) (spine_hyps t)). unb env H \<Longrightarrow> skip_unb env n t"
proof (induction env n t rule: skip_unb.induct)
  case (1 env n t)
  show ?case
  proof (cases "n = 0")
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      then have "dest_imp t = None" by (auto simp: dest_all_Some)
      with aTb have "spine_hyps t = spine_hyps b" by (subst spine_hyps.simps) simp
      with "1.IH"(2)[OF aTb refl refl] "1.prems" aTb show ?thesis by (subst skip_unb.simps) simp
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case (Some AB)
        then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
        then have "spine_hyps t = A # spine_hyps B" by (subst spine_hyps.simps) simp
        moreover have "nat_of_integer n = Suc (nat_of_integer (n - 1))" "0 \<le> n - 1"
          using "1.prems"(1) False by (simp_all add: integer_reps)
        ultimately show ?thesis
          using "1.IH"(1)[OF None AB refl] "1.prems"(2) None AB by (subst skip_unb.simps) simp
      next
        case None': None
        with None show ?thesis by (subst skip_unb.simps) simp
      qed
    qed
  qed (subst skip_unb.simps; simp)
qed

text \<open>Elim-resolution with a lifted rule uses lifted assumptions.\<close>

lemma strip_assums_imp_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Y" "0 \<le> k" "k \<le> count_prems (lift_pre p Y)"
    "strip_assums_imp k Hs (lift_pre p X) = (Hs', B)"
  shows "set Hs' \<subseteq> set Hs \<union> set (phyps p)"
  using assms
proof (induction p arbitrary: k Hs)
  case Nil
  then have "k = 0" by (subst (asm) count_prems.simps) (simp add: atomic_def)
  with Nil.prems show ?case by (subst (asm) strip_assums_imp.simps) simp
next
  case (Cons i p)
  show ?case
  proof (cases "k = 0")
    case True
    with Cons.prems show ?thesis by (subst (asm) strip_assums_imp.simps) simp
  next
    case False
    show ?thesis
    proof (cases i)
      case (LImp c H)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
      have k: "0 \<le> k - 1" using Cons.prems(3) False by (simp add: integer_reps)
      from Cons.prems(4) LImp c have kc: "k - 1 \<le> count_prems (lift_pre p Y)"
        by (subst (asm) count_prems.simps) simp
      from Cons.prems(5) False LImp c
      have s: "strip_assums_imp (k - 1) (H # Hs) (lift_pre p X) = (Hs', B)"
        by (subst (asm) strip_assums_imp.simps) simp
      from Cons.prems(1) have "set Hs' \<subseteq> set (H # Hs) \<union> set (phyps p)"
        by (intro Cons.IH[OF _ Cons.prems(2) k kc s]) simp
      with LImp show ?thesis by auto
    next
      case (LAll c a T)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
      from Cons.prems(4) LAll c have "k \<le> 0" by (subst (asm) count_prems.simps) simp
      with Cons.prems(3) False show ?thesis by simp
    qed
  qed
qed

lemma assum_problems_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Y" "k \<le> count_prems (strip_all_body (lift_pre p Y))"
    "assum_problems k (lift_pre p X) = (params, asms, concl)" "0 \<le> k"
  shows "set asms \<subseteq> set (phyps p)"
proof -
  obtain ps A' where a: "strip_assums_all [] (lift_pre p X) = (ps, A')"
    by (cases "strip_assums_all [] (lift_pre p X)")
  obtain Hs B where b: "strip_assums_imp k [] A' = (Hs, B)" by (cases "strip_assums_imp k [] A'")
  from assms(4) a b have asms: "asms = rev Hs" by (simp add: assum_problems_def)
  have "set Hs \<subseteq> set (phyps p)" if "strip_assums_all qs (lift_pre p X) = (ps, A')" for qs
    using assms(1-3) that
  proof (induction p arbitrary: qs)
    case Nil
    then have "k = 0"
      using assms(5) by (subst (asm) strip_all_body.simps, subst (asm) count_prems.simps) (simp add: atomic_def)
    with b show ?case by (subst (asm) strip_assums_imp.simps) simp
  next
    case (Cons i p)
    show ?case
    proof (cases i)
      case (LImp c H)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
      from Cons.prems(4) LImp c have "A' = lift_pre (i # p) X"
        by (subst (asm) strip_assums_all.simps) simp
      with b have s: "strip_assums_imp k [] (lift_pre (i # p) X) = (Hs, B)" by simp
      from Cons.prems(3) LImp c have kc: "k \<le> count_prems (lift_pre (i # p) Y)"
        by (subst (asm) strip_all_body.simps) simp
      show ?thesis using strip_assums_imp_lift_pre[OF Cons.prems(1,2) assms(5) kc s] by simp
    next
      case (LAll c a T)
      with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
      from Cons.prems(4) LAll c have "strip_assums_all ((a, T) # qs) (lift_pre p X) = (ps, A')"
        by (subst (asm) strip_assums_all.simps) simp
      moreover from Cons.prems(3) LAll c have "k \<le> count_prems (strip_all_body (lift_pre p Y))"
        by (subst (asm) strip_all_body.simps) simp
      ultimately show ?thesis using Cons.IH Cons.prems(1,2) LAll by simp
    qed
  qed
  with a asms show ?thesis by simp
qed


subsection \<open>The new premises\<close>

text \<open>Well-formed propositions.\<close>

definition wfp :: "(name \<Rightarrow> nat) \<Rightarrow> pterm \<Rightarrow> bool" where
  "wfp ar t \<longleftrightarrow> cok t \<and> proper t \<and> twft ar t \<and> no_loose_bound (tr t) 0"

text \<open>
  The premises of a rule lifted over the subgoal \<open>Bi\<close> of a proof state with maximal index \<open>m\<close>:
  the variables of the rule have been incremented above \<open>m\<close>.
\<close>

definition lifted_rule :: "integer \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "lifted_rule m Bi As B \<longleftrightarrow> (\<exists>p Bi0 As0 B0. lsplit Bi = (p, Bi0) \<and> As = map (lift_pre p) As0 \<and>
    B = lift_pre p B0 \<and> (\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x))"

lemma list_all2_imp_all: "list_all2 (\<lambda>a b. P a \<longrightarrow> Q b) xs ys \<Longrightarrow> \<forall>x\<in>set xs. P x \<Longrightarrow> \<forall>y\<in>set ys. Q y"
  by (induction rule: list_all2_induct) auto

lemma wfp_impliesD: "wfp ar (implies $ A $ B) \<Longrightarrow> wfp ar A \<and> wfp ar B"
  by (simp add: wfp_def)

lemma wfp_list_impliesD: "wfp ar (list_implies As B) \<Longrightarrow> (\<forall>A\<in>set As. wfp ar A) \<and> wfp ar B"
  by (induction As) (auto dest: wfp_impliesD)

lemma ibelow_simps:
  "ibelow m (s $ t) \<longleftrightarrow> ibelow m s \<and> ibelow m t"
  "ibelow m (Abs a T t) \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. snd v \<le> m) \<and> ibelow m t"
  by (auto simp: ibelow_def)

lemma ibelow_implies: "ibelow m implies"
  by (simp add: ibelow_def implies_imp_type imp_type_def propT_def)

lemma ibelow_list_implies[simp]: "ibelow m (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. ibelow m A) \<and> ibelow m B"
  by (induction As) (simp_all add: ibelow_simps ibelow_implies)

lemma lifted_rule_Cons:
  assumes "lifted_rule m Bi (A # As) B"
  shows "lifted_rule m Bi As B"
proof -
  from assms obtain p Bi0 As0 B0 where "lsplit Bi = (p, Bi0)" "A # As = map (lift_pre p) As0"
    "B = lift_pre p B0" "\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x"
    unfolding lifted_rule_def by (elim exE conjE) simp
  then show ?thesis
    unfolding lifted_rule_def by (intro exI[of _ p] exI[of _ Bi0] exI[of _ "tl As0"] exI[of _ B0]) (cases As0; auto)
qed

lemma ptpok_swf: "ptpok ar A W env e0 (t, u) \<Longrightarrow> swf_tm ar [] t \<and> swf_tm ar [] u"
  by (auto simp: ptpok_def swf_tm_def proper_rlist_abs twft_rlist_abs no_loose_bound_tr_rlist_abs)

lemma ibelow_spine_hyps: "ibelow m t \<Longrightarrow> H \<in> set (spine_hyps t) \<Longrightarrow> ibelow m H"
proof (induction t rule: spine_hyps.induct)
  case (1 t)
  show ?case
  proof (cases "dest_imp t")
    case (Some HB)
    then obtain H' B where HB: "dest_imp t = Some (H', B)" by (cases HB) auto
    with "1.prems" "1.IH"(2)[OF HB refl] show ?thesis
      by (subst (asm) spine_hyps.simps) (auto simp: dest_imp_Some ibelow_simps)
  next
    case None
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      with "1.prems" "1.IH"(1)[OF None aTb refl refl] None show ?thesis
        by (subst (asm) spine_hyps.simps) (auto simp: dest_all_Some ibelow_simps)
    next
      case None': None
      with "1.prems" None show ?thesis by (subst (asm) spine_hyps.simps) simp
    qed
  qed
qed

lemma strip_assums_imp_length:
  "strip_assums_imp k Hs B = (Hs', B') \<Longrightarrow> 0 \<le> k \<Longrightarrow> ilength Hs' \<le> ilength Hs + k"
proof (induction k Hs B rule: strip_assums_imp.induct)
  case (1 k Hs B)
  show ?case
  proof (cases "k = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_assums_imp.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp B")
      case (Some HB)
      then obtain H B1 where HB: "dest_imp B = Some (H, B1)" by (cases HB) auto
      with "1.prems"(1) False have "strip_assums_imp (k - 1) (H # Hs) B1 = (Hs', B')"
        by (subst (asm) strip_assums_imp.simps) simp
      moreover have "0 \<le> k - 1" using "1.prems"(2) False by (simp add: integer_reps)
      ultimately show ?thesis using "1.IH"[OF False HB refl] by simp
    next
      case None
      with "1.prems"(1) False have "Hs' = Hs" by (subst (asm) strip_assums_imp.simps) simp
      with "1.prems"(2) show ?thesis by simp
    qed
  qed
qed

lemma assum_problems_length: "assum_problems k A = (params, asms, concl) \<Longrightarrow> 0 \<le> k \<Longrightarrow> ilength asms \<le> k"
  by (auto simp: assum_problems_def ilength_eq dest!: strip_assums_imp_length split: prod.splits)

lemma count_prems_nonneg: "0 \<le> count_prems t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  then show ?case by (subst count_prems.simps) (auto split: option.splits dest: dest_size)
qed

text \<open>
  The new premises before flattening (\<^const>\<open>na_oldAs\<close>) are the original ones or, if the rule
  is lifted, their renamings. The schematic variables renamed by \<open>tab\<close> occur neither on the left
  of the disagreement pairs nor in the flex-flex pairs.
\<close>

lemma newAs_ren:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
  obtains tab r2 where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
proof -
  have h: "\<not> okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseT e) y" for e and y :: newas
    by (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)
  from assms have flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    and old: "na_oldAs na = As0 \<or> (\<exists>r. bc_lifted ctx \<and>
      rename_bvars dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0 = Some r \<and>
      na_oldAs na = map (strip_apply (ren_term r) (bc_Bi ctx)) As0)"
    unfolding newAs_def
    by (auto simp: okT_handleT h ok_mapM list.rel_eq split: if_splits option.splits)
  from old show thesis
  proof (elim disjE exE conjE)
    assume "na_oldAs na = As0"
    with that[of "[]", OF _ _ flat] show thesis by (simp add: ren_name_def)
  next
    fix r assume "bc_lifted ctx" and r: "rename_bvars dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0 = Some r"
      and "na_oldAs na = map (strip_apply (ren_term r) (bc_Bi ctx)) As0"
    then show thesis using rename_bvars_unknowns[OF r] flat by (intro that[of "fst r" "snd r"]) auto
  qed
qed

text \<open>Renaming the premise of a lifted rule preserves well-formedness.\<close>

lemma twft_ren_term[simp]: "twft ar (ren_term r t) \<longleftrightarrow> twft ar t"
  by (induction r t rule: ren_term.induct) auto

lemma wfp_lift_pre_ren_term: "wfp ar (lift_pre p (ren_term r X)) \<longleftrightarrow> wfp ar (lift_pre p X)"
proof -
  have "cok (lift_pre p (ren_term r X)) \<longleftrightarrow> cok (lift_pre p X)"
  proof (induction p X rule: lift_pre.induct)
    case (3 c a T p t)
    then show ?case by (cases c) simp_all
  qed simp_all
  moreover have "proper (lift_pre p (ren_term r X)) \<longleftrightarrow> proper (lift_pre p X)"
    "twft ar (lift_pre p (ren_term r X)) \<longleftrightarrow> twft ar (lift_pre p X)"
    by (induction p X rule: lift_pre.induct) simp_all
  moreover have "no_loose_bound (tr (lift_pre p (ren_term r X))) k \<longleftrightarrow> no_loose_bound (tr (lift_pre p X)) k"
    for k by (induction p X arbitrary: k rule: lift_pre.induct) (simp_all add: tr_ren_term_nlb)
  ultimately show ?thesis by (simp add: wfp_def)
qed

lemma lifted_rule_lift_pre:
  assumes "lifted_rule m Bi As0 B"
  obtains p Bi0 As0' where "Bi = lift_pre p Bi0" "\<forall>i\<in>set p. litem_ok i" "atomic Bi0"
    "As0 = map (lift_pre p) As0'" "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. m < snd x"
  using assms lsplit_ok unfolding lifted_rule_def by blast

context pure_sem
begin

lemma newAs_holds:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" and wf: "\<forall>A\<in>set As0. wfp ar A"
    and vl: "\<And>xs. length (vl xs) = length xs"
  obtains tab where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    "\<not> bc_lifted ctx \<Longrightarrow> tab = []"
    "\<And>\<rho> \<sigma>. rigid_subst \<sigma> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow>
      list_all2 (\<lambda>A' A. holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub (bc_smax ctx) tab) A)) (na_As na) As0"
proof -
  let ?m = "bc_smax ctx"
  obtain tab r2 where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    and old: "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    by (rule newAs_ren[OF na]) (rule that)
  text \<open>The renamed premises are well-formed and have the instances of the original ones.\<close>
  have oldAs: "list_all2 (\<lambda>A1 A. wfp ar A1 \<and> (\<forall>\<rho> \<sigma>. sm \<rho> \<sigma> A1 = sm \<rho> (\<sigma> \<circ>\<^sub>s rsub ?m tab) A))
    (na_oldAs na) As0"
    using old
  proof (elim disjE conjE)
    assume "na_oldAs na = As0" "tab = []"
    then show ?thesis
      using wf by (auto simp: ren_name_def sm_rsub_id intro!: list.rel_refl_strong)
  next
    assume lf: "bc_lifted ctx"
      and o: "na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    from lr[OF lf] obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
      and As0: "As0 = map (lift_pre p) As0'" and above: "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. ?m < snd x"
      by (rule lifted_rule_lift_pre)
    have pv: "\<forall>x\<in>pvars p. snd x \<le> ?m" using ib Bi by (auto simp: ibelow_def vars_lift_pre)
    have "na_oldAs na = map (\<lambda>X. lift_pre p (ren_term (tab, r2) X)) As0'"
      using o As0 Bi strip_apply_lift_pre[OF ok at] by simp
    then show ?thesis
      using As0 wf pv above
      by (auto simp: list_all2_map1 list_all2_map2 wfp_lift_pre_ren_term sm_lift_pre_ren
          intro!: list.rel_refl_strong)
  qed
  show thesis
  proof (rule that[OF ren])
    show "\<not> bc_lifted ctx \<Longrightarrow> tab = []" using old by blast
    fix \<rho> \<sigma> assume rg: "rigid_subst \<sigma>" and cl: "closed_on UNIV \<sigma>"
    have step: "holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub ?m tab) A)"
      if f: "if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A'"
        and o: "wfp ar A1 \<and> (\<forall>\<rho> \<sigma>. sm \<rho> \<sigma> A1 = sm \<rho> (\<sigma> \<circ>\<^sub>s rsub ?m tab) A)" for A' A1 A
    proof
      assume h: "holds (sm \<rho> \<sigma> A')"
      have "holds (sm \<rho> \<sigma> A1)"
      proof (cases "bc_flatten ctx")
        case True
        with f have "ok (flatten_params vl n A1) A'" by simp
        from flatten_params_holds[OF this _ rg cl _ _ _ h] o vl show ?thesis by (simp add: wfp_def)
      next
        case False
        with f h show ?thesis by simp
      qed
      with o show "holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub ?m tab) A)" by simp
    qed
    have flat': "list_all2 (\<lambda>A' A1. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_As na) (na_oldAs na)"
      using flat by (simp add: list_all2_conv_all_nth)
    show "list_all2 (\<lambda>A' A. holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub ?m tab) A)) (na_As na) As0"
      by (rule list_all2_trans[OF step flat' oldAs])
  qed
qed

end

text \<open>Flattening (\<^const>\<open>flatten_params\<close>) preserves well-formedness.\<close>

lemma twft_list_forall: "twft ar (list_forall vs X) \<longleftrightarrow> (\<forall>(a, T)\<in>set vs. wft ar (all_type T)) \<and> twft ar X"
  by (induction vs X rule: list_forall.induct) (auto simp: all_const_all_type all_type_def)

lemma twft_strip_params: "cok A \<Longrightarrow> twft ar A \<Longrightarrow> (a, T) \<in> set (strip_params A) \<Longrightarrow> wft ar (all_type T)"
proof (induction A rule: strip_params.induct)
  case (1 A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    with "1.prems" "1.IH"(2)[OF HB refl] show ?thesis by (auto dest: cok_dest_imp simp: strip_params_imp)
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a' T' b where aTb: "dest_all A = Some (a', T', b)" by (cases aTb) auto
      with "1.prems" "1.IH"(1)[OF None aTb refl refl] None show ?thesis
        by (auto dest: cok_dest_all simp: strip_params_all all_const_all_type)
    next
      case None': None
      with "1.prems" None show ?thesis by (simp add: strip_params_other)
    qed
  qed
qed

lemma remove_params_twft:
  assumes "ok (remove_params j n A) A'" "cok A" "twft ar A"
  shows "twft ar A'"
  using assms
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
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
      from cok_dest_imp[OF "1.prems"(2) HB] "1.prems"(3)
      have A: "cok B" "twft ar implies" "twft ar H" "twft ar B" by auto
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this A(1,4)] show ?thesis .
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        from "1.IH"(3)[OF False HB refl n1 B' A(1,4)] A(2,3) A' show ?thesis
          by (simp add: twft_incr_boundvars)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        from cok_dest_all[OF "1.prems"(2) aTb] "1.prems"(3) have b: "cok b" "twft ar b" by auto
        from rp False None aTb have "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl this b] show ?thesis .
      next
        case None': None
        with rp False None "1.prems" show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits)
      qed
    qed
  qed
qed

lemma flatten_params_wfp:
  assumes "ok (flatten_params vl n A) A'" "length (vl (map fst (strip_params A))) = length (strip_params A)"
    "wfp ar A"
  shows "wfp ar A'"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have lv: "length ?vars = length ?ps" using assms(2) by simp
  from assms(1) obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''"
    and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def)
  have j: "ilength (strip_params A) = ilength ?vars" using lv by (simp add: ilength_eq)
  from assms(3) have wA: "cok A" "proper A" "twft ar A" "no_loose_bound (tr A) 0"
    by (simp_all add: wfp_def)
  have "proper A'' \<and> cok A'' \<and> no_loose_bound (tr A'') (length ?ps)"
    using remove_params_wf[OF r j wA(2,1,4)] lv by (simp add: ilength_eq)
  moreover have "twft ar A''" by (rule remove_params_twft[OF r wA(1,3)])
  moreover have "wft ar (all_type T)" if "(a, T) \<in> set ?vars" for a T
  proof -
    from set_zip_rightD[OF that] obtain a' where "(a', T) \<in> set ?ps" by auto
    then show ?thesis by (rule twft_strip_params[OF wA(1,3)])
  qed
  ultimately show ?thesis
    using lv by (auto simp: A' wfp_def twft_list_forall no_loose_bound_list_forall)
qed

lemma newAs_wfp:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
    "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    "\<forall>A\<in>set As0. wfp ar A" "\<And>xs. length (vl xs) = length xs"
  shows "\<forall>A\<in>set (na_As na). wfp ar A"
proof -
  obtain tab r2 where
    old: "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    by (rule newAs_ren[OF assms(1)]) (rule that)
  have "list_all2 (\<lambda>A1 A'. wfp ar A1 \<longrightarrow> wfp ar A') (na_oldAs na) (na_As na)"
    using flat by (rule list_all2_mono) (auto simp: assms(4) dest: flatten_params_wfp split: if_splits)
  moreover have "\<forall>A1\<in>set (na_oldAs na). wfp ar A1"
    using old
  proof (elim disjE conjE)
    assume "bc_lifted ctx"
      and o: "na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    from assms(2)[OF this(1)] obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      and "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. bc_smax ctx < snd x"
      by (rule lifted_rule_lift_pre)
    from o assms(3) show ?thesis by (simp add: As0 Bi strip_apply_lift_pre[OF ok at] wfp_lift_pre_ren_term)
  qed (use assms(3) in simp)
  ultimately show ?thesis by (rule list_all2_imp_all)
qed

lemma spine_hyps_list_forall: "spine_hyps (list_forall vs X) = spine_hyps X"
proof (induction vs X rule: list_forall.induct)
  case (2 a T vs t)
  then show ?case by (subst spine_hyps.simps) (simp add: all_const_def)
qed simp

lemma spine_hyps_atomic: "atomic t \<Longrightarrow> spine_hyps t = []"
  by (subst spine_hyps.simps) (simp add: atomic_def)

text \<open>
  Removing the parameters keeps the hypotheses along the spine up to renumbering bound variables,
  except for the deleted one.
\<close>

lemma remove_params_spine_hyps:
  assumes "ok (remove_params j n A) A'" "H \<in> set (take k (spine_hyps A'))"
  shows "\<exists>H0\<in>set (take (k + (if 0 < n then 1 else 0)) (spine_hyps A)). vars H = vars H0 \<and> tys H = tys H0"
  using assms
proof (induction j n A arbitrary: A' k rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  have same: ?case if "A' = A"
    using "1.prems"(2) set_take_subset_set_take[of k "k + (if 0 < n then 1 else 0)" "spine_hyps A"] that
    by (intro bexI[of _ H]) auto
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (intro same) (subst (asm) remove_params.simps; simp)
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H0 B where HB: "dest_imp A = Some (H0, B)" by (cases HB) auto
      then have sA: "spine_hyps A = H0 # spine_hyps B" by (subst spine_hyps.simps) simp
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this "1.prems"(2)] True sA show ?thesis by auto
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H0 $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        have sA': "spine_hyps A' = incr_boundvars j H0 # spine_hyps B'"
          by (subst spine_hyps.simps) (simp add: A' implies_def)
        show ?thesis
        proof (cases k)
          case 0
          with "1.prems"(2) show ?thesis by simp
        next
          case (Suc k')
          with "1.prems"(2) sA' have "H = incr_boundvars j H0 \<or> H \<in> set (take k' (spine_hyps B'))" by auto
          then show ?thesis
          proof
            assume "H = incr_boundvars j H0"
            then show ?thesis using sA Suc by auto
          next
            assume "H \<in> set (take k' (spine_hyps B'))"
            from "1.IH"(3)[OF False HB refl n1 B' this] obtain H1 where
              H1: "H1 \<in> set (take (k' + (if 0 < n - 1 then 1 else 0)) (spine_hyps B))"
              "vars H = vars H1 \<and> tys H = tys H1"
              by blast
            have "set (take (k' + (if 0 < n - 1 then 1 else 0)) (spine_hyps B)) \<subseteq>
                set (take (k + (if 0 < n then 1 else 0)) (spine_hyps A))"
              using set_take_subset_set_take[of "k' + (if 0 < n - 1 then 1 else 0)"
                  "k' + (if 0 < n then 1 else 0)" "spine_hyps B"] Suc sA
              by auto
            with H1 show ?thesis by blast
          qed
        qed
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        with None have "spine_hyps A = spine_hyps b" by (subst spine_hyps.simps) simp
        moreover from rp False None aTb have "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        ultimately show ?thesis using "1.IH"(1)[OF False None aTb refl refl _ "1.prems"(2)] by simp
      next
        case None': None
        with rp False None show ?thesis
          by (intro same) (subst (asm) remove_params.simps; auto split: if_splits)
      qed
    qed
  qed
qed

lemma newAs_skip:
  assumes "okT (newAs vl ctx As0 n dps tps1) na" "bc_lifted ctx"
    "lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" "\<forall>A\<in>set As0. wfp ar A" "\<And>xs. length (vl xs) = length xs"
    "0 \<le> k" "k + (if 0 < n \<and> bc_flatten ctx then 1 else 0) \<le> count_prems (strip_all_body (bc_Bi ctx))"
    "n \<le> count_prems (strip_all_body (bc_Bi ctx))"
  shows "\<forall>A\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer k) (spine_hyps A)).
    \<exists>H0\<in>set (spine_hyps (bc_Bi ctx)). vars H = vars H0 \<and> tys H = tys H0"
proof -
  let ?K = "nat_of_integer k" and ?d = "if 0 < n \<and> bc_flatten ctx then 1 else 0 :: nat"
  obtain tab r2 where
    old: "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    by (rule newAs_ren[OF assms(1)]) (rule that)
  from assms(3) obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
    and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
    and "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. bc_smax ctx < snd x"
    by (rule lifted_rule_lift_pre)
  have sBi: "spine_hyps (bc_Bi ctx) = phyps p"
    by (simp add: Bi spine_hyps_lift_pre[OF ok] spine_hyps_atomic[OF at])
  have "k + (if 0 < n \<and> bc_flatten ctx then 1 else 0) \<le> ilength (phyps p)"
    using order_trans[OF assms(7)[unfolded Bi] count_prems_lift_pre[OF ok at]] .
  then have len: "?K + ?d \<le> length (phyps p)"
    using assms(6)
    by (auto simp: ilength_eq integer_reps integer_of_nat.rep_eq nat_le_iff Suc_le_eq
        nat_less_iff split: if_splits)
  text \<open>The first \<open>k\<close> hypotheses of a new premise are lifted ones.\<close>
  have step: "\<exists>H0\<in>set (phyps p). vars H = vars H0 \<and> tys H = tys H0"
    if f: "if bc_flatten ctx then ok (flatten_params vl n A1) A else A1 = A"
      and A1: "A1 = lift_pre p Z" and H: "H \<in> set (take ?K (spine_hyps A))" for A1 A Z H
  proof -
    have "\<exists>H1\<in>set (take (?K + ?d) (spine_hyps A1)). vars H = vars H1 \<and> tys H = tys H1"
    proof (cases "bc_flatten ctx")
      case True
      with f obtain A'' vs where r: "ok (remove_params (ilength vs) n A1) A''"
        and A: "A = list_forall vs A''"
        by (auto simp: flatten_params_def Let_def)
      from H have "H \<in> set (take ?K (spine_hyps A''))" by (simp add: A spine_hyps_list_forall)
      from remove_params_spine_hyps[OF r this] True show ?thesis by simp
    next
      case False
      with f H show ?thesis by auto
    qed
    moreover have "take (?K + ?d) (spine_hyps A1) = take (?K + ?d) (phyps p)"
      using len by (simp add: A1 spine_hyps_lift_pre[OF ok])
    ultimately show ?thesis using set_take_subset by fastforce
  qed
  have "list_all2 (\<lambda>A1 A. (\<exists>Z. A1 = lift_pre p Z) \<longrightarrow> (\<forall>H\<in>set (take ?K (spine_hyps A)).
      \<exists>H0\<in>set (phyps p). vars H = vars H0 \<and> tys H = tys H0)) (na_oldAs na) (na_As na)"
    using flat by (rule list_all2_mono) (blast intro: step)
  moreover have "\<forall>A1\<in>set (na_oldAs na). \<exists>Z. A1 = lift_pre p Z"
    using old by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
  ultimately show ?thesis unfolding sBi by (rule list_all2_imp_all)
qed


subsection \<open>The new theorem\<close>

text \<open>The cases of \<^const>\<open>addth\<close>.\<close>

lemma addth_cases:
  assumes "okT (addth ctx A na (env, tps)) r"
  obtains (empty) "env_is_empty env" "r = BRes env tps (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)) A na"
  | (norm) ntps Hs C' where "\<not> env_is_empty env" "r = BRes env ntps (list_implies Hs C') A na"
      "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
      "above env (bc_smax ctx) \<and> bc_lifted ctx \<and> C' = bc_C ctx \<and>
        (\<exists>As'. Hs = bc_Bs ctx @ As' \<and> list_all2 (\<lambda>X X'. okT (norm_term_skip env (bc_nlift ctx) X) X') (na_As na) As') \<or>
       above env (bc_smax ctx) \<and> \<not> bc_lifted ctx \<and> C' = bc_C ctx \<and>
        (\<exists>As'. Hs = bc_Bs ctx @ As' \<and> list_all2 (\<lambda>X X'. ok (norm_term env X) X') (na_As na) As') \<or>
       \<not> above env (bc_smax ctx) \<and> list_all2 (\<lambda>X X'. ok (norm_term env X) X') (bc_Bs ctx @ na_As na) Hs \<and>
        ok (norm_term env (bc_C ctx)) C'"
proof (cases "env_is_empty env")
  case True
  with assms show thesis by (intro empty) (auto simp: addth_def)
next
  case False
  from assms False obtain ntps where nt: "ok (mapM (norm_tpair env) tps) ntps"
    and rest: "okT (do {
          (ntpairs, Hs, C') \<leftarrow>
            if above env (bc_smax ctx) then
              if bc_lifted ctx then do {
                As' \<leftarrow> mapT (norm_term_skip env (bc_nlift ctx)) (na_As na);
                returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
              else do {
                As' \<leftarrow> liftMT (mapM (norm_term env) (na_As na));
                returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
            else if bc_match ctx then raiseT COMPOSE
            else do {
              Hs \<leftarrow> liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na));
              C' \<leftarrow> liftMT (norm_term env (bc_C ctx));
              returnT (ntps, Hs, C')};
          returnT (BRes env ntpairs (list_implies Hs C') A na)}) r"
    by (auto simp: addth_def)
  have l: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
    using nt unfolding ok_mapM
    by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
  show thesis
  proof (cases "above env (bc_smax ctx)")
    case True
    show thesis
    proof (cases "bc_lifted ctx")
      case lf: True
      with True rest obtain As' where "list_all2 (\<lambda>X X'. okT (norm_term_skip env (bc_nlift ctx) X) X') (na_As na) As'"
        "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: okT_mapT)
      with False l True lf show thesis by (intro norm) auto
    next
      case lf: False
      with True rest obtain As' where "list_all2 (\<lambda>X X'. ok (norm_term env X) X') (na_As na) As'"
        "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: ok_mapM)
      with False l True lf show thesis by (intro norm) auto
    qed
  next
    case na: False
    with rest obtain Hs C' where "list_all2 (\<lambda>X X'. ok (norm_term env X) X') (bc_Bs ctx @ na_As na) Hs"
      "ok (norm_term env (bc_C ctx)) C'" "r = BRes env ntps (list_implies Hs C') A na"
      by (auto simp: ok_mapM split: if_splits)
    with False l na show thesis by (intro norm) auto
  qed
qed

lemma list_all2_ex1: "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y\<in>set ys. P x y"
  by (induction rule: list_all2_induct) auto

lemma list_all2_ex2: "list_all2 P xs ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. P x y"
  by (induction rule: list_all2_induct) auto

lemma closed_foldr_dIMP: "closed (foldr dIMP As B) \<longleftrightarrow> (\<forall>A\<in>set As. closed A) \<and> closed B"
  by (induction As) auto

locale bicompose_sem = wf_algebra alg ar + pure_sem holds inhab
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and holds :: "dB \<Rightarrow> bool" and inhab :: "ptyp \<Rightarrow> dB \<Rightarrow> bool"
begin

definition valid :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid tps P \<longleftrightarrow> (\<forall>\<rho> \<sigma>. gtinst \<rho> \<longrightarrow> closed_on UNIV \<sigma> \<longrightarrow> rigid_subst \<sigma> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<longrightarrow> holds (sm \<rho> \<sigma> P))"

lemma validD:
  "valid tps P \<Longrightarrow> gtinst \<rho> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<Longrightarrow> holds (sm \<rho> \<sigma> P)"
  unfolding valid_def by blast

lemma validI:
  "(\<And>\<rho> \<sigma>. gtinst \<rho> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<Longrightarrow> holds (sm \<rho> \<sigma> P)) \<Longrightarrow> valid tps P"
  unfolding valid_def by blast

text \<open>
  The new theorem of \<^const>\<open>addth\<close>: its flex-flex pairs and its proposition are the
  normalizations of those of the unifier and of \<open>\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C\<close>.
\<close>

lemma holds_foldr_dIMP_equiv:
  assumes "list_all2 (\<lambda>X Y. Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> X \<and> closed Y \<and> closed X) Xs Ys" "C' \<equiv>\<^sub>\<beta>\<^sub>\<eta> C" "closed C'" "closed C"
    "holds (foldr dIMP Xs C)"
  shows "holds (foldr dIMP Ys C')"
  using assms(1,5)
proof (induction rule: list_all2_induct)
  case Nil
  with assms(2-4) show ?case using holds_equiv[OF assms(4,3) equiv_sym[OF assms(2)]] by simp
next
  case (Cons X Xs Y Ys)
  have c: "closed (foldr dIMP Xs C)" "closed (foldr dIMP Ys C')"
    using Cons.hyps(2) assms(3,4) by (auto simp: closed_foldr_dIMP dest: list_all2_ex1 list_all2_ex2)
  from Cons.prems Cons.hyps(1) c have "holds X \<longrightarrow> holds (foldr dIMP Xs C)" by (simp add: holds_imp)
  moreover have "holds Y \<Longrightarrow> holds X" using holds_equiv Cons.hyps(1) by blast
  ultimately have "holds Y \<longrightarrow> holds (foldr dIMP Ys C')" using Cons.IH by blast
  with Cons.hyps(1) c show ?case by (simp add: holds_imp)
qed

text \<open>The instances of the components of the new theorem.\<close>

abbreviation (input) inst_rel :: "tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' X Y \<equiv> sm \<rho> \<sigma> Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X \<and> closed (sm \<rho> \<sigma> Y) \<and> closed (sm \<rho>' \<sigma>' X)"

lemma inst_rel_unb:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "wfp ar X" "unb env X"
  shows "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' X X"
  using iext_unb[OF assms(1,2,5)] assms(3,4) by (simp add: wfp_def no_loose_bound_sm)

lemma inst_rel_norm:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "swf_env ar env" "wfp ar X"
    "ok (norm_term env X) Y"
  shows "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' X Y"
proof -
  have sw: "swf_tm ar [] X" using assms(5) by (simp add: wfp_def swf_tm_def)
  have cl': "closed_on UNIV \<sigma>'" using assms(1) by (simp add: iext_def)
  from norm_term_swf_tm[OF assms(6,4) sw] have "swf_tm ar [] Y" by simp
  with iext_norm_term[OF assms(1,2,4) sw assms(6)] assms(3,5) cl' show ?thesis
    by (simp add: swf_tm_def wfp_def no_loose_bound_sm)
qed

lemma inst_rel_skip:
  assumes "iext env \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "swf_env ar env" "wfp ar X"
    "skip_unb env n X" "okT (norm_term_skip env n X) Y"
  shows "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' X Y"
proof -
  have sw: "swf_tm ar [] X" "cok X" using assms(5) by (simp_all add: wfp_def swf_tm_def)
  have cl': "closed_on UNIV \<sigma>'" using assms(1) by (simp add: iext_def)
  from norm_term_skip_swf[OF assms(7,4) sw] have "swf_tm ar [] Y" .
  with iext_norm_term_skip[OF assms(1,2,4) assms(7) sw assms(6)] assms(3,5) cl' show ?thesis
    by (simp add: swf_tm_def wfp_def no_loose_bound_sm)
qed

lemma addth_tpairs:
  assumes "okT (addth ctx A na (env', tps)) r" "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>"
    "swf_env ar env'" "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u"
    "\<forall>(t, u)\<in>set (br_tpairs r). sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
  shows "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
  using assms(1)
proof (cases rule: addth_cases)
  case empty
  have "sm \<rho>' \<sigma>' t = sm \<rho> \<sigma> t" for t by (rule iext_unb[OF assms(2,3) unb_empty[OF empty(1)]])
  with assms(6) empty(2) show ?thesis by auto
next
  case (norm ntps Hs C')
  show ?thesis
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    from list_all2_ex1[OF norm(3) tu] obtain tu' where tu': "tu' \<in> set ntps"
      and n: "ok (norm_term env' t) (fst tu')" "ok (norm_term env' u) (snd tu')"
      by auto
    obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
    note tu' = tu'[unfolded tu''] and n = n[unfolded tu'' fst_conv snd_conv]
    from assms(5) tu have sw: "swf_tm ar [] t" "swf_tm ar [] u" by auto
    have "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> t'" by (rule equiv_sym[OF iext_norm_term[OF assms(2,3,4) sw(1) n(1)]])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u'" using assms(6) tu' norm(2) by auto
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" by (rule iext_norm_term[OF assms(2,3,4) sw(2) n(2)])
    finally show "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" .
  qed
qed

lemma addth_holds:
  assumes "okT (addth ctx A na (env', tps)) r" "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>"
    "swf_env ar env'" "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wfp ar X \<and> ibelow (bc_smax ctx) X"
    "\<forall>X\<in>set (na_As na). wfp ar X"
    "bc_lifted ctx \<Longrightarrow> 0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
    "holds (sm \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
  shows "holds (sm \<rho> \<sigma> (br_prop r))"
proof -
  let ?Bs = "bc_Bs ctx" and ?As = "na_As na" and ?C = "bc_C ctx"
  have rg': "rigid_subst \<sigma>'" using assms(2) by (simp add: iext_def)
  have tr: "holds (sm \<rho> \<sigma> (list_implies Hs C'))"
    if "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') (?Bs @ ?As) Hs" "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' ?C C'" for Hs C'
  proof -
    have "list_all2 (\<lambda>X Y. Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> X \<and> closed Y \<and> closed X) (map (sm \<rho>' \<sigma>') (?Bs @ ?As)) (map (sm \<rho> \<sigma>) Hs)"
      using that(1) by (simp only: list_all2_map1 list_all2_map2)
    from holds_foldr_dIMP_equiv[OF this, of "sm \<rho> \<sigma> C'" "sm \<rho>' \<sigma>' ?C"] that(2) assms(9) show ?thesis
      by (simp add: sm_list_implies[OF assms(3)] sm_list_implies[OF rg'] del: map_append foldr_append)
  qed
  have rel_unb: "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') Xs Xs" if "\<forall>X\<in>set Xs. wfp ar X \<and> unb env' X" for Xs
    using that by (intro list.rel_refl_strong) (simp add: inst_rel_unb[OF assms(2-4)])
  have rel_norm: "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') Xs Ys"
    if "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y) Xs Ys" "\<forall>X\<in>set Xs. wfp ar X" for Xs Ys
  proof -
    have "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y \<and> X \<in> set Xs) Xs Ys"
      using that(1) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
    then show ?thesis by (rule list_all2_mono) (use that(2) inst_rel_norm[OF assms(2-5)] in blast)
  qed
  have wS: "\<forall>X\<in>set ?Bs. wfp ar X" "wfp ar ?C" using assms(6) by auto
  have unbS: "\<forall>X\<in>set ?Bs. unb env' X" "unb env' ?C" if "above env' (bc_smax ctx)"
    using assms(6) above_unb[OF that] by auto
  show ?thesis
    using assms(1)
  proof (cases rule: addth_cases)
    case empty
    have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') (?Bs @ ?As) (?Bs @ ?As)"
      using wS assms(7) unb_empty[OF empty(1)] by (intro rel_unb) auto
    moreover have "inst_rel \<rho> \<sigma> \<rho>' \<sigma>' ?C ?C" by (rule inst_rel_unb[OF assms(2-4) wS(2) unb_empty[OF empty(1)]])
    ultimately show ?thesis using tr empty(2) by simp
  next
    case (norm ntps Hs C')
    from norm(4) consider
      (lifted) As' where "above env' (bc_smax ctx)" "bc_lifted ctx" "C' = ?C" "Hs = ?Bs @ As'"
        "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X') ?As As'"
    | (above) As' where "above env' (bc_smax ctx)" "C' = ?C" "Hs = ?Bs @ As'"
        "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') ?As As'"
    | (all) "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (?Bs @ ?As) Hs" "ok (norm_term env' ?C) C'"
      by blast
    then have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') (?Bs @ ?As) Hs \<and> inst_rel \<rho> \<sigma> \<rho>' \<sigma>' ?C C'"
    proof cases
      case lifted
      from assms(8)[OF lifted(2)] have n: "0 \<le> bc_nlift ctx"
        and h: "\<forall>X\<in>set ?As. \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H"
        by auto
      have sk: "skip_unb env' (bc_nlift ctx) X" if "X \<in> set ?As" for X
        by (rule skip_unb_take[OF n]) (use h that above_unb[OF lifted(1)] in blast)
      have "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X' \<and> X \<in> set ?As) ?As As'"
        using lifted(5) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
      then have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') ?As As'"
        by (rule list_all2_mono) (use assms(7) sk inst_rel_skip[OF assms(2-5)] in blast)
      moreover have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') ?Bs ?Bs" using wS unbS[OF lifted(1)] by (intro rel_unb) auto
      ultimately show ?thesis
        using lifted inst_rel_unb[OF assms(2-4) wS(2) unbS(2)[OF lifted(1)]] by (simp add: list_all2_appendI)
    next
      case above
      have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') ?As As'" by (rule rel_norm[OF above(4) assms(7)])
      moreover have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') ?Bs ?Bs" using wS unbS[OF above(1)] by (intro rel_unb) auto
      ultimately show ?thesis
        using above inst_rel_unb[OF assms(2-4) wS(2) unbS(2)[OF above(1)]] by (simp add: list_all2_appendI)
    next
      case all
      have "list_all2 (inst_rel \<rho> \<sigma> \<rho>' \<sigma>') (?Bs @ ?As) Hs" by (rule rel_norm[OF all(1)]) (use wS assms(7) in auto)
      with inst_rel_norm[OF assms(2-5) wS(2) all(2)] show ?thesis by simp
    qed
    with tr norm(2) show ?thesis by simp
  qed
qed


subsection \<open>Composition\<close>

text \<open>
  The results of a call of \<open>bicompose_aux\<close> for a valid proof state \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> with
  flex-flex pairs \<open>stpairs\<close> and maximal index \<open>smax\<close>, and a valid rule \<open>\<lbrakk>As\<rbrakk> \<Longrightarrow> B\<close> with
  flex-flex pairs \<open>rtpairs\<close>, lifted over \<open>Bi\<close> if \<open>lifted\<close>, are valid.
\<close>

theorem rchar_valid:
  assumes sp: "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and r: "rchar sp r"
    and state: "valid stpairs (list_implies (Bs @ [Bi]) C)" "wfp ar (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "valid rtpairs (list_implies (rev rAs) B)" "wfp ar (list_implies (rev rAs) B)"
      "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "valid (br_tpairs r) (br_prop r)"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "bs_eres sp = eres_flg" "bs_ctx sp = ctx" "bs_vl sp = vl" "bs_rAs sp = rAs" "bs_env sp = env"
    "bs_A sp = A"
    by (simp_all add: sp')
  from r obtain A1o na tus env' tps where its: "itsok sp A1o na tus"
    and pu: "punifier env (dps_of tus) env' tps" and pr: "prres alg ar A env' tps"
    and ad: "okT (addth ctx A1o na (env', tps)) r"
    by (auto simp: rchar_def sp')
  from pr obtain W e0 where pi: "pinv alg ar A W env' []" and tpok: "\<forall>ab\<in>set tps. ptpok ar A W env' e0 ab"
    by (auto simp: prres_def)
  have pe: "penv_inv alg ar W env'" by (rule pinvD(1)[OF pi])
  have swf: "swf_env ar env'" by (rule penv_inv_swf_env[OF pe])
  have tps_wf: "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u"
    using tpok ptpok_swf by fast
  have wS: "\<forall>X\<in>set Bs. wfp ar X" "wfp ar Bi" "wfp ar C" using wfp_list_impliesD[OF state(2)] by simp_all
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using state(3) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wfp ar X" "wfp ar B" using wfp_list_impliesD[OF rule(2)] by simp_all
  text \<open>The problem and the new premises: the premises \<open>Pre\<close> of the rule that are proved
    (none, or the first by an assumption), the other premises \<open>As0\<close>, and the further
    disagreement pairs \<open>dps\<close> given to \<^const>\<open>newAs\<close>.\<close>
  obtain Pre As0 n dps tps1 where
    rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps"
    and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl asm. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
      (rlist_abs params concl, rlist_abs params asm) \<in> set dps \<and>
      (rlist_abs params asm, rlist_abs params concl) \<in> set tus"
  proof -
    from its consider (res) tps1 where "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
        "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      | (eres) n asm tps1 where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
        "okT (newAs vl ctx (er_As (eres_of sp)) n
          [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      using its unfolding itsok_def sp_sel ctx_sel by blast
    then show thesis
    proof cases
      case res
      have "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
      with res show thesis
        by (intro that[of "[]" "rev rAs" 0 "[BBi]" tps1]) (simp_all add: nlift_def)
    next
      case eres
      have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
      obtain A1 As where rA: "rev rAs = A1 # As"
        using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
      obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
        by (cases "assum_problems (nlift + 1) A1")
      have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
        using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
      have asm: "asm \<in> set asms" using eres(2-4) er(2) by (simp add: integer_reps)
      have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
      have "ilength asms \<le> nlift + 1"
        by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
      moreover have "n \<le> ilength asms" using eres(2,3) er(2)
        by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
      ultimately have nle: "n \<le> nlift + 1" by simp
      show thesis
      proof (rule that[of "[A1]" As n "[BBi, (rlist_abs params concl, rlist_abs params asm)]" tps1])
        show "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
          using eres(6) er by simp
        show "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
          using eres(5) er by (auto simp: eres_prob_def sp' ctx_sel)
        show "\<exists>params' asms' concl' asm'. eres_flg \<and> [A1] = [A1'] \<and>
            assum_problems (nlift + 1) A1' = (params', asms', concl') \<and> asm' \<in> set asms' \<and>
            (rlist_abs params' concl', rlist_abs params' asm') \<in> set [BBi, (rlist_abs params concl, rlist_abs params asm)] \<and>
            (rlist_abs params' asm', rlist_abs params' concl') \<in> set tus"
          if "A1' \<in> set [A1]" for A1'
          using that eres(1,5) ap asm er by (auto simp: eres_prob_def)
      qed (use rA eres(2) nle cnt in auto)
    qed
  qed
  have wP: "\<forall>X\<in>set Pre. wfp ar X" "\<forall>X\<in>set As0. wfp ar X" using wR(1) rAs by auto
  have lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (Pre @ As0) B" using rule(3) rAs by simp
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    using lr0 by (induction Pre) (auto dest: lifted_rule_Cons)
  obtain tab where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (rtpairs @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    and nlt: "\<not> lifted \<Longrightarrow> tab = []"
    and nah: "\<And>\<rho> \<sigma>. rigid_subst \<sigma> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow>
      list_all2 (\<lambda>A' A. holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub smax tab) A)) (na_As na) As0"
    using newAs_holds[OF na, of B ar] lr iS(2) wP(2) vl by (auto simp: ctx_sel)
  have wN: "\<forall>X\<in>set (na_As na). wfp ar X"
    using newAs_wfp[OF na _ wP(2) vl, of B] lr by (simp add: ctx_sel)
  text \<open>The variables that are not renamed.\<close>
  have keep: "sm \<rho> (\<sigma> \<circ>\<^sub>s rsub smax tab) t = sm \<rho> \<sigma> t"
    if "\<And>x. x \<in> vars t \<Longrightarrow> snd x \<le> smax \<or> ren_name tab (fst x) = fst x" for \<rho> \<sigma> t
    using that by (intro sm_rsub_id) blast
  show ?thesis
  proof (rule validI)
    fix \<rho> \<sigma> assume g: "gtinst \<rho>" and cl: "closed_on UNIV \<sigma>" and rg: "rigid_subst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (br_tpairs r) \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
    obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" by (rule iext_exists[OF pe g cl rg])
    from ie have gs: "gsol alg ar (tyenv env') \<rho>'" and cl': "closed_on UNIV \<sigma>'"
      and rg': "rigid_subst \<sigma>'" and ps: "psat (\<sigma>' \<circ> cren \<rho>') env'"
      by (simp_all add: iext_def)
    have g': "gtinst \<rho>'" by (rule gtinst_gsol[OF gs])
    let ?\<sigma>r = "\<sigma>' \<circ>\<^sub>s rsub smax tab"
    have clr: "closed_on UNIV ?\<sigma>r" by (rule closed_comp_rsub[OF cl'])
    have rgr: "rigid_subst ?\<sigma>r" by (rule rigid_subst_comp_rsub[OF rg'])
    have tsol: "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
      by (rule addth_tpairs[OF ad ie rg swf tps_wf]) (use sol in auto)
    have dsol: "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
    proof -
      have "\<forall>(t, u)\<in>set tps. mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma>' \<circ> cren \<rho>') (tr u)"
        using tsol by (simp add: sm_def mk_subst_inst)
      with pu ps have "dsolved_all (\<sigma>' \<circ> cren \<rho>') (dps_of tus)" by (auto simp: punifier_def)
      with that have "dsolved (\<sigma>' \<circ> cren \<rho>') ([], t, u)" by fastforce
      then show ?thesis by (simp add: dsolved_Nil unifies_def sm_def mk_subst_inst)
    qed
    text \<open>The instances of the proof state and of the rule.\<close>
    have hS: "holds (sm \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule validD[OF state(1) g' cl' rg']) (use dsol tus in auto)
    have hR: "holds (sm \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
    proof (rule validD[OF rule(1) g' clr rgr])
      fix t u assume tu: "(t, u) \<in> set rtpairs"
      have nr: "ren_name tab (fst x) = fst x" if "x \<in> vars t \<union> vars u" for x
      proof (rule ccontr)
        assume "ren_name tab (fst x) \<noteq> fst x"
        from ren[OF this] have "\<forall>(t, u)\<in>set rtpairs. fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u"
          by simp
        with tu have "fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u" by blast
        with that show False by blast
      qed
      have "sm \<rho>' ?\<sigma>r t = sm \<rho>' \<sigma>' t" "sm \<rho>' ?\<sigma>r u = sm \<rho>' \<sigma>' u"
        by (rule keep; simp add: nr)+
      with dsol[of t u] tus tu show "sm \<rho>' ?\<sigma>r t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' ?\<sigma>r u" by auto
    qed
    text \<open>The conclusion of the rule implies the subgoal.\<close>
    have BBi_sol: "sm \<rho>' \<sigma>' (fst BBi) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' (snd BBi)"
      using dsol[of "fst BBi" "snd BBi"] tus by simp
    have pv: "\<forall>x\<in>pvars p. snd x \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
      using iS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
    have hBi: "holds (sm \<rho>' \<sigma>' Bi)" if hB: "holds (sm \<rho>' ?\<sigma>r B)"
    proof (cases lifted)
      case True
      from lr0[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      have nr: "ren_name tab (fst x) = fst x" if "x \<in> vars B0" for x
      proof (rule ccontr)
        assume "ren_name tab (fst x) \<noteq> fst x"
        from ren[OF this] dps have "case BBi of (t, u) \<Rightarrow> fst x \<notin> fst ` vars t" by blast
        with that BBi show False by (simp add: vars_abs_pre)
      qed
      have "sm \<rho>' ?\<sigma>r B = sm \<rho>' \<sigma>' B"
        by (rule keep) (use pv[OF ls] nr in \<open>auto simp: B vars_lift_pre\<close>)
      with hB have "holds (sm \<rho>' \<sigma>' (lift_pre p B0))" by (simp add: B)
      from holds_lift_pre_transfer[OF rg' cl' ok _ _ _ _ _ this] wR(2) wS(2) BBi_sol BBi B Bi
      show ?thesis by (simp add: wfp_def)
    next
      case False
      then have "sm \<rho>' ?\<sigma>r B = sm \<rho>' \<sigma>' B" by (intro keep) (simp add: nlt ren_name_def)
      moreover have "BBi = (B, Bi)" using False by (simp add: BBi_def)
      ultimately show ?thesis using hB BBi_sol wR(2) wS(2)
        by (intro holds_equiv[of "sm \<rho>' \<sigma>' B" "sm \<rho>' \<sigma>' Bi"]) (auto simp: wfp_def no_loose_bound_sm[OF cl'])
    qed
    text \<open>The premise proved by an assumption.\<close>
    have hPre: "holds (sm \<rho>' ?\<sigma>r A1)" if A1: "A1 \<in> set Pre" for A1
    proof -
      from pre[OF A1] obtain params asms concl asm where er: "eres_flg" "Pre = [A1]"
        and ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and asm: "asm \<in> set asms"
        and cd: "(rlist_abs params concl, rlist_abs params asm) \<in> set dps"
        and ac: "(rlist_abs params asm, rlist_abs params concl) \<in> set tus"
        by blast
      have wA1: "wfp ar A1" using wP(1) A1 by blast
      have e: "sm \<rho>' \<sigma>' (rlist_abs params asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' (rlist_abs params concl)" by (rule dsol[OF ac])
      have c: "sm \<rho>' ?\<sigma>r (rlist_abs params concl) = sm \<rho>' \<sigma>' (rlist_abs params concl)"
      proof (rule keep)
        fix x assume x: "x \<in> vars (rlist_abs params concl)"
        show "snd x \<le> smax \<or> ren_name tab (fst x) = fst x"
        proof (rule disjI2, rule ccontr)
          assume "ren_name tab (fst x) \<noteq> fst x"
          from ren[OF this] cd have "fst x \<notin> fst ` vars (rlist_abs params concl)" by auto
          with x show False by blast
        qed
      qed
      have a: "sm \<rho>' ?\<sigma>r (rlist_abs params asm) = sm \<rho>' \<sigma>' (rlist_abs params asm)"
      proof (cases lifted)
        case True
        from lr0[OF True] obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
          and As: "Pre @ As0 = map (lift_pre p) As0'" by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        from As er(2) obtain X1 where A1': "A1 = lift_pre p X1" by (cases As0') auto
        have "nlift + 1 = count_prems (strip_all_body Bi)" using er(1) by (simp add: nlift_def)
        then have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ ap[unfolded A1']] Bi n(4) by simp
        with asm have "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        with pv[OF ls] show ?thesis by (intro keep) (auto simp: vars_rlist_abs)
      next
        case False
        then show ?thesis by (intro keep) (simp add: nlt ren_name_def)
      qed
      show ?thesis
        by (rule eres_holds[OF ap asm _ rgr clr]) (use e a c wA1 in \<open>simp_all add: wfp_def\<close>)
    qed
    text \<open>The instance of the composed theorem.\<close>
    have clX: "closed (sm \<rho>' \<sigma>' X)" if "wfp ar X" for X
      using that cl' by (simp add: wfp_def no_loose_bound_sm)
    have clXr: "closed (sm \<rho>' ?\<sigma>r X)" if "wfp ar X" for X
      using that clr by (simp add: wfp_def no_loose_bound_sm)
    have hS': "holds (sm \<rho>' \<sigma>' C)"
      if "\<forall>X\<in>set Bs. holds (sm \<rho>' \<sigma>' X)" "holds (sm \<rho>' \<sigma>' Bi)"
    proof -
      have "\<forall>A\<in>set (map (sm \<rho>' \<sigma>') (Bs @ [Bi])). closed A" using wS clX by auto
      from holds_foldr_dIMP[OF this clX[OF wS(3)]] hS that show ?thesis
        by (simp add: sm_list_implies[OF rg'] del: map_append foldr_append)
    qed
    have hR': "holds (sm \<rho>' ?\<sigma>r B)" if "\<forall>X\<in>set (Pre @ As0). holds (sm \<rho>' ?\<sigma>r X)"
    proof -
      have "\<forall>A\<in>set (map (sm \<rho>' ?\<sigma>r) (Pre @ As0)). closed A" using wP clXr by auto
      from holds_foldr_dIMP[OF this clXr[OF wR(2)]] hR that rAs show ?thesis
        by (simp add: sm_list_implies[OF rgr] del: map_append foldr_append)
    qed
    have hN: "holds (sm \<rho>' \<sigma>' (list_implies (Bs @ na_As na) C))"
    proof -
      have "holds (sm \<rho>' \<sigma>' C)" if H: "\<forall>X\<in>set (Bs @ na_As na). holds (sm \<rho>' \<sigma>' X)"
      proof -
        have "\<forall>X\<in>set As0. holds (sm \<rho>' ?\<sigma>r X)"
          using list_all2_imp_all[OF nah[OF rg' cl', of \<rho>']] H by simp
        with hPre have "holds (sm \<rho>' ?\<sigma>r B)" by (intro hR') auto
        then have "holds (sm \<rho>' \<sigma>' Bi)" by (rule hBi)
        with H show ?thesis by (intro hS') auto
      qed
      moreover have "\<forall>A\<in>set (map (sm \<rho>' \<sigma>') (Bs @ na_As na)). closed A" using wS wN clX by auto
      ultimately show ?thesis using holds_foldr_dIMP[OF _ clX[OF wS(3)]]
        by (simp add: sm_list_implies[OF rg'] del: map_append foldr_append)
    qed
    text \<open>The new theorem.\<close>
    show "holds (sm \<rho> \<sigma> (br_prop r))"
    proof (rule addth_holds[OF ad ie rg cl swf])
      show "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wfp ar X \<and> ibelow (bc_smax ctx) X"
        using wS iS by (simp add: ctx_sel)
      show "\<forall>X\<in>set (na_As na). wfp ar X" by (rule wN)
      show "holds (sm \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
        using hN by (simp add: ctx_sel)
      assume "bc_lifted ctx"
      then have lf: lifted by (simp add: ctx_sel)
      have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> tys H = tys H0"
        using newAs_skip[OF na _ _ wP(2) vl n(4)] lf lr n(2,3) by (simp add: ctx_sel)
      then show "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
          \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
        using ibelow_spine_hyps[OF iS(2)] n(4) by (fastforce simp: ctx_sel ibelow_def)
    qed
  qed
qed

end

end
