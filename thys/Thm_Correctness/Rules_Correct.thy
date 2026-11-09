section \<open>Soundness of the primitive and derived rules\<close>

theory Rules_Correct
  imports Thm_Type "Pure_Thm.Pure_Subst_Rules"
begin

text \<open>
  The rules of \<^theory>\<open>Pure_Thm.Pure_Rules\<close> and \<^theory>\<open>Pure_Thm.Pure_Subst_Rules\<close> map valid
  theorems to valid theorems (\<^const>\<open>pure_model.valid\<close>). The hypotheses and sort hypotheses
  of the new theorems are those that the ML wrapper computes, as sets: the union for rules with
  two premises, without the discharged hypothesis for \<open>implies_intr\<close>.
\<close>


subsection \<open>Flex-flex pairs of two theorems\<close>

lemma eq_tpair_refl [simp]: "eq_tpair x x"
  by (simp add: eq_tpair_def)

lemma set_foldr_insert_tpair:
  "set (foldr insert_tpair us ts) \<subseteq> set us \<union> set ts \<and>
    set ts \<subseteq> set (foldr insert_tpair us ts) \<and>
    (\<forall>x\<in>set us. \<exists>y\<in>set (foldr insert_tpair us ts). eq_tpair x y)"
proof (induction us)
  case (Cons u us)
  let ?r = "foldr insert_tpair us ts"
  show ?case
  proof (cases "\<exists>y\<in>set ?r. eq_tpair u y")
    case True
    with Cons show ?thesis by (auto simp: insert_tpair_def)
  next
    case False
    with Cons show ?thesis by (auto simp: insert_tpair_def)
  qed
qed simp

lemma union_tpairs_set:
  "set (union_tpairs ts us) \<subseteq> set ts \<union> set us"
  "\<forall>x\<in>set ts \<union> set us. \<exists>y\<in>set (union_tpairs ts us). eq_tpair x y"
proof -
  show "set (union_tpairs ts us) \<subseteq> set ts \<union> set us"
    using set_foldr_insert_tpair[of us ts] by (auto simp: union_tpairs_def)
  show "\<forall>x\<in>set ts \<union> set us. \<exists>y\<in>set (union_tpairs ts us). eq_tpair x y"
  proof
    fix x assume x: "x \<in> set ts \<union> set us"
    note f = set_foldr_insert_tpair[of us ts]
    show "\<exists>y\<in>set (union_tpairs ts us). eq_tpair x y"
    proof (cases "ts = []")
      case True
      with x show ?thesis by (intro bexI[of _ x]) (simp_all add: union_tpairs_def)
    next
      case False
      show ?thesis
      proof (cases "x \<in> set ts")
        case True
        with f False show ?thesis by (intro bexI[of _ x]) (auto simp: union_tpairs_def)
      next
        case nt: False
        with x have "x \<in> set us" by simp
        with f False show ?thesis by (simp add: union_tpairs_def)
      qed
    qed
  qed
qed

context pure_model
begin

lemma sol_union_tpairs:
  assumes "\<And>t u. (t, u) \<in> set (union_tpairs ts us) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and "(t, u) \<in> set ts \<union> set us"
  shows "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  from union_tpairs_set(2) assms(2) obtain y where y: "y \<in> set (union_tpairs ts us)" "eq_tpair (t, u) y"
    by blast
  obtain t' u' where yy: "y = (t', u')" by (cases y)
  with y have tu': "(t', u') \<in> set (union_tpairs ts us)" and a: "aconv_term t t'" "aconv_term u u'"
    by (simp_all add: eq_tpair_def)
  have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
    using a by (blast intro: aconv_term_conv aconv_term_ap)+
  with assms(1)[OF tu'] show ?thesis by (meson conv_sym conv_trans)
qed


subsection \<open>Implication elimination\<close>

lemma dest_imp_wtp:
  assumes "dest_imp P = Some (A, B)" "wtp P"
  shows "P = implies $ A $ B" "wtp A" "wtp B"
proof -
  from assms(1) obtain U where P: "P = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: dest_imp_Some)
  from wtpD(2)[OF assms(2), of "\<lambda>_. propT"] P have "U = imp_type"
    by (auto simp: const_typ_ok_def imp_type_def propT_def)
  then show P': "P = implies $ A $ B" using P by (simp add: implies_imp_type)
  from wtpD[OF assms(2)] P' have "closed (implies $ A $ B)" "\<And>e. e \<turnstile> implies $ A $ B : propT"
    by simp_all
  then show "wtp A" "wtp B" by (auto simp: wtp_def typing_implies closed_def)
qed

theorem implies_elim_valid:
  assumes ok: "okT (implies_elim thAB thA) th"
    and v1: "valid Sh1 hs1 (th_tpairs thAB) (th_prop thAB)"
    and v2: "valid Sh2 hs2 (th_tpairs thA) (th_prop thA)"
    and w1: "wtp (th_prop thAB)" and w2: "wtp (th_prop thA)"
  shows "valid (Sh1 \<union> Sh2) (hs2 @ hs1) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain A B where d: "dest_imp (th_prop thAB) = Some (A, B)" and a: "aconv_term A (th_prop thA)"
    and th: "th = mk_rep (max (th_maxidx thA) (th_maxidx thAB)) (union_tpairs (th_tpairs thA) (th_tpairs thAB)) B"
    by (auto simp: implies_elim_def returnW_def raiseW_def split: option.splits if_splits)
  note dw = dest_imp_wtp[OF d w1]
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh1 \<union> Sh2 \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs2 @ hs1) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    have sol': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if "(t, u) \<in> set (th_tpairs thA) \<union> set (th_tpairs thAB)" for t u
      by (rule sol_union_tpairs[OF _ that]) (use sol th in \<open>simp add: mk_rep_def\<close>)
    have h1: "holds (ap \<rho> \<sigma> (th_prop thAB))"
      by (rule validD[OF v1]) (use sh \<rho> \<rho>i \<sigma> sol' hh g in auto)
    have h2: "holds (ap \<rho> \<sigma> (th_prop thA))"
      by (rule validD[OF v2]) (use sh \<rho> \<rho>i \<sigma> sol' hh g in auto)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have hA: "holds (ap \<rho> \<sigma> A)"
      by (rule holds_conv[OF gt[OF w2] gt[OF dw(2)] _ h2])
        (use a in \<open>blast intro: conv_sym aconv_term_conv aconv_term_ap\<close>)
    from h1 have "holds (implies $ ap \<rho> \<sigma> A $ ap \<rho> \<sigma> B)" by (simp add: dw(1))
    with hA holds_imp[OF gt[OF dw(2)] gt[OF dw(3)]] have "holds (ap \<rho> \<sigma> B)" by blast
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))" by (simp add: th mk_rep_def)
  qed
qed

subsection \<open>Implication introduction, assumption, trivial implication\<close>

text \<open>
  \<open>Thm.implies_intr A\<close> removes the hypotheses that are \<open>\<alpha>\<close>-equivalent to \<open>A\<close>
  (\<open>Ord_List.remove Term_Ord.fast_term_ord\<close>, as a set).
\<close>

theorem implies_intr_valid:
  assumes ok: "okT (implies_intr (CTerm A U m) th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wA: "wtp A" and w: "wtp (th_prop th0)" and hw: "\<forall>h\<in>set hs. wtp h"
  shows "valid Sh (filter (\<lambda>h. \<not> aconv_term A h) hs) (th_tpairs th) (th_prop th)"
proof -
  from ok have U: "U = propT" and th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (mk_implies A (th_prop th0))"
    by (auto simp: implies_intr_def returnW_def raiseW_def split: if_splits)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (filter (\<lambda>h. \<not> aconv_term A h) hs) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (ap \<rho> \<sigma> A) \<longrightarrow> holds (ap \<rho> \<sigma> (th_prop th0))"
    proof
      assume hA: "holds (ap \<rho> \<sigma> A)"
      show "holds (ap \<rho> \<sigma> (th_prop th0))"
      proof (rule validD[OF v sh g \<rho> \<rho>i \<sigma>])
        fix t u assume "(t, u) \<in> set (th_tpairs th0)"
        then show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using sol th by (simp add: mk_rep_def)
      next
        fix h assume h: "h \<in> set hs"
        show "holds (ap \<rho> \<sigma> h)"
        proof (cases "aconv_term A h")
          case True
          then have "ap \<rho> \<sigma> A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> h" by (blast intro: aconv_term_conv aconv_term_ap)
          moreover have "wtp h" using h hw by blast
          ultimately show ?thesis using holds_conv[OF gt[OF wA] gt[OF \<open>wtp h\<close>] _ hA] by blast
        next
          case False
          with h hh show ?thesis by simp
        qed
      qed
    qed
    with holds_imp[OF gt[OF wA] gt[OF w]] have "holds (implies $ ap \<rho> \<sigma> A $ ap \<rho> \<sigma> (th_prop th0))" by blast
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))" by (simp add: th mk_rep_def mk_implies_def)
  qed
qed

theorem assume_valid:
  assumes "okT (assume_rule ct) th"
  shows "valid Sh [th_prop th] (th_tpairs th) (th_prop th)"
  by (rule validI) simp

theorem trivial_valid:
  assumes ok: "okT (trivial (CTerm A U m)) th" and wA: "wtp A"
  shows "valid Sh [] (th_tpairs th) (th_prop th)"
proof -
  from ok have th: "th = mk_rep m [] (mk_implies A A)"
    by (auto simp: trivial_def returnW_def raiseW_def split: if_splits)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF wA cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (implies $ ap \<rho> \<sigma> A $ ap \<rho> \<sigma> A)" using holds_imp[OF gt gt] by blast
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))" by (simp add: th mk_rep_def mk_implies_def)
  qed
qed

text \<open>\<open>Thm.weaken\<close> adds a hypothesis; the logical part is unchanged.\<close>

theorem weaken_valid:
  assumes ok: "okT (weaken ct th0) th" and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
  shows "valid Sh (A # hs) (th_tpairs th) (th_prop th)"
proof -
  from ok have "th = th0" by (auto simp: weaken_def returnW_def raiseW_def Let_def split: if_splits)
  with v show ?thesis unfolding valid_def by auto
qed

theorem renamed_prop_valid:
  assumes ok: "okT (renamed_prop P th0) th" and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and w: "wtp (th_prop th0)" and hw: "\<forall>h\<in>set hs. wtp h"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  from ok have a: "aconv_term (th_prop th0) P" and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) P"
    by (auto simp: renamed_prop_def returnW_def raiseW_def split: if_splits)
  have wP: "wtp P" using w a loose_bvar1_aconv[OF a]
    by (auto simp: wtp_def typing_aconv closed_iff_loose_bvar1)
  have "valid Sh hs (th_tpairs th0) P"
  proof (rule valid_conv[OF v aconv_term_conv[OF a] wtpD(1)[OF w] wtpD(2)[OF w] wtpD(1)[OF wP] wtpD(2)[OF wP]])
    show "list_all2 (\<lambda>h h'. h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h' \<and> closed h \<and> (\<exists>e. e \<turnstile> h : propT) \<and> closed h' \<and> (\<exists>e. e \<turnstile> h' : propT)) hs hs"
      using hw by (auto simp: list_all2_conv_all_nth wtp_def)
    show "list_all2 (\<lambda>(t, u) (t', u'). t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u') (th_tpairs th0) (th_tpairs th0)"
      by (auto simp: list_all2_conv_all_nth)
  qed
  then show ?thesis by (simp add: th mk_rep_def)
qed

theorem adjust_maxidx_thm_valid:
  assumes "valid Sh hs (th_tpairs th0) (th_prop th0)"
  shows "valid Sh hs (th_tpairs (adjust_maxidx_thm i th0)) (th_prop (adjust_maxidx_thm i th0))"
  using assms by (simp add: adjust_maxidx_thm_def mk_rep_def)

end

end
