section \<open>Soundness of the primitive and derived rules\<close>

theory Rules_Correct
  imports Biresolution_Proofs Bicompose_Results "Pure_Thm.Pure_Subst_Rules"
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

context pure_sig
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

end

subsection \<open>Implication elimination\<close>

context pure_sig
begin

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

end

context pure_model
begin

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

subsection \<open>Forall elimination\<close>

context pure_sig
begin

lemma dest_all_app_wtp:
  assumes "dest_all_app P = Some (T, A)" "wtp P"
  shows "P = all_const T $ A" "closed A" "\<And>e. e \<turnstile> A : T \<rightarrow>\<^sub>T propT"
proof -
  from assms(1) obtain V W where P: "P = Const STR ''Pure.all'' (Type STR ''fun'' [Type STR ''fun'' [T, V], W]) $ A"
    by (cases P rule: dest_all_app.cases) (auto split: if_splits)
  from wtpD(2)[OF assms(2), of "\<lambda>_. propT"] P have "V = propT" "W = propT"
    by (auto simp: const_typ_ok_def propT_def)
  then show P': "P = all_const T $ A" using P by (simp add: all_const_def propT_def)
  from wtpD[OF assms(2)] P' show "closed A" "\<And>e. e \<turnstile> A : T \<rightarrow>\<^sub>T propT"
    by (auto simp: closed_def all_const_def)
qed

lemma betapply_conv: "wt (A $ t) \<Longrightarrow> A $ t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> betapply A t"
proof (cases A)
  case (Abs a T b)
  moreover assume "wt (A $ t)"
  ultimately show ?thesis by (auto intro: conv_beta simp: subst_bound_subst)
qed simp_all

end

context pure_model
begin

lemma sem_all_app':
  assumes "sem \<eta> \<xi> bv f \<in>\<^sub>u ufun (tsem \<eta> U) ubool" "sem \<eta> \<xi> bv (all_const U $ f) = utrue" "v \<in>\<^sub>u tsem \<eta> U"
  shows "uapp (sem \<eta> \<xi> bv f) v = utrue"
  using assms by (simp add: all_const_def csem_def all_val_def uapp_ulam all_type_def)

theorem forall_elim_valid:
  assumes ok: "okT (forall_elim (CTerm t T m) th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and w: "wtp (th_prop th0)" and ct: "closed t" "\<And>e. e \<turnstile> t : T"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  from ok obtain A where d: "dest_all_app (th_prop th0) = Some (T, A)"
    and th: "th = mk_rep (max m (th_maxidx th0)) (th_tpairs th0) (betapply A t)"
    by (auto simp: forall_elim_def returnW_def raiseW_def split: option.splits if_splits)
  note dw = dest_all_app_wtp[OF d w]
  have wAt: "wtp (A $ t)" using dw(2,3) ct by (intro wtpI) (auto simp: closed_def)
  have wt: "wt (A $ t)" unfolding wt_def using wtpD(2)[OF wAt, of "\<lambda>_. propT"] by blast
  have wB: "wtp (betapply A t)"
  proof (cases A)
    case (Abs a U b)
    then have red: "A $ t \<rightarrow>\<^sub>\<beta> betapply A t" by (simp add: subst_bound_subst)
    show ?thesis
    proof (rule wtpI)
      show "closed (betapply A t)"
        using wtpD(1)[OF wAt] free_beta[OF red] by (auto simp: closed_iff_loose_bvar1)
      show "(\<lambda>_. propT) \<turnstile> betapply A t : propT" by (rule subject_reduction_beta[OF wtpD(2)[OF wAt] red])
    qed
  qed (use wAt in simp_all)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    have h: "holds (ap \<rho> \<sigma> (th_prop th0))"
      by (rule validD[OF v sh g \<rho> \<rho>i \<sigma>]) (use sol hh th in \<open>simp_all add: mk_rep_def\<close>)
    have gA: "gterm (ap \<rho> \<sigma> A) (tsubst \<rho> T \<rightarrow>\<^sub>T propT)"
      using gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma> dw(2) dw(3)] by (simp add: tsubst_propT)
    have gt: "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> T)" by (rule gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma> ct])
    have "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> A) \<in>\<^sub>u ufun (tsem \<eta> (tsubst \<rho> T)) ubool"
      using sem_typing[OF good gtermD(2)[OF gA], of "\<lambda>_. propT"] by (simp add: bvals_def ubool_mem)
    moreover have "sem \<eta> \<xi> bv0 (all_const (tsubst \<rho> T) $ ap \<rho> \<sigma> A) = utrue"
      using h dw(1) by (simp add: holds_at_def)
    moreover have "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> t) \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
      using sem_typing[OF good gtermD(2)[OF gt], of "\<lambda>_. propT"] by (simp add: bvals_def ubool_mem)
    ultimately have "holds (ap \<rho> \<sigma> (A $ t))" by (simp add: holds_at_def sem_all_app')
    moreover have "ap \<rho> \<sigma> (A $ t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (betapply A t)"
      by (rule conv_ap[OF betapply_conv[OF wt] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
    ultimately have "holds (ap \<rho> \<sigma> (betapply A t))"
      using holds_conv[OF gterm_ap_wtp[OF wAt cinstD(2)[OF \<rho>] \<sigma>] gterm_ap_wtp[OF wB cinstD(2)[OF \<rho>] \<sigma>]] by blast
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))" by (simp add: th mk_rep_def)
  qed
qed

subsection \<open>Permutation of premises\<close>

lemma valid_list_implies_perm:
  assumes v: "valid Sh hs tps (list_implies As B)" and w: "wtp (list_implies As B)"
    and s: "set As' = set As" and l: "length As' = length As"
  shows "valid Sh hs tps (list_implies As' B)" "wtp (list_implies As' B)"
proof -
  have ty: "(\<lambda>_. propT) \<turnstile> list_implies As B : propT" by (rule wtpD(2)[OF w])
  have imp: "As' \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type"
    using typing_list_implies_imp[OF ty] l by (metis length_0_conv)
  show w': "wtp (list_implies As' B)"
  proof (rule wtpI)
    show "closed (list_implies As' B)"
      using wtpD(1)[OF w] s by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies As' B : propT"
      using typing_list_impliesD[OF ty] imp s by (intro typing_list_impliesI) auto
  qed
  show "valid Sh hs tps (list_implies As' B)"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (ap \<rho> \<sigma> (list_implies As B))" by (rule validD[OF v sh g \<rho> \<rho>i \<sigma> sol hh])
    with holds_list_implies[of "map (ap \<rho> \<sigma>) As" "ap \<rho> \<sigma> B"] gt[OF w]
    have "(\<forall>A\<in>set As. holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> B)" by (simp add: ap_list_implies)
    with holds_list_implies[of "map (ap \<rho> \<sigma>) As'" "ap \<rho> \<sigma> B"] gt[OF w'] s
    show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (list_implies As' B))" by (simp add: ap_list_implies)
  qed
qed

end

context pure_sig
begin

lemma set_rotate_take_drop: "set (drop m xs @ take m xs) = set xs"
  by (metis Un_commute append_take_drop_id set_append)

end

context pure_model
begin

lemma permute_data_shape:
  assumes "okT (permute_data j k rl) (th, prems', m)"
  defines "ps \<equiv> strip_imp_prems (th_prop rl)"
  shows "th = mk_rep (th_maxidx rl) (th_tpairs rl) (th_prop rl) \<or>
    (th = mk_rep (th_maxidx rl) (th_tpairs rl) (list_implies prems' (strip_imp_concl (th_prop rl))) \<and>
     (\<exists>J M. prems' = take J ps @ drop M (drop J ps) @ take M (drop J ps)))"
  using assms unfolding permute_data_def Let_def
  by (auto simp: returnW_def raiseW_def split: if_splits)

theorem permute_prems_valid:
  assumes ok: "okT (permute_prems j k th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)" and w: "wtp (th_prop th0)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)" "wtp (th_prop th)"
proof -
  let ?ps = "strip_imp_prems (th_prop th0)" and ?concl = "strip_imp_concl (th_prop th0)"
  have P: "th_prop th0 = list_implies ?ps ?concl"
    by (rule list_implies_strip_imp[OF wtpD(2)[OF w, of "\<lambda>_. propT"]])
  from ok obtain prems' m where "okT (permute_data j k th0) (th, prems', m)"
    by (auto simp: permute_prems_def returnW_def)
  from permute_data_shape[OF this]
  have "valid Sh hs (th_tpairs th) (th_prop th) \<and> wtp (th_prop th)"
  proof (elim disjE conjE exE)
    fix J M assume th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) (list_implies prems' ?concl)"
      and p: "prems' = take J ?ps @ drop M (drop J ?ps) @ take M (drop J ?ps)"
    have "set prems' = set ?ps"
      unfolding p by (metis append_take_drop_id set_append set_rotate_take_drop)
    moreover have "length prems' = length ?ps" unfolding p by simp
    ultimately show ?thesis
      using valid_list_implies_perm[of Sh hs "th_tpairs th0" ?ps ?concl prems'] v w P
      by (simp add: th mk_rep_def)
  qed (use v w in \<open>simp add: mk_rep_def\<close>)
  then show "valid Sh hs (th_tpairs th) (th_prop th)" "wtp (th_prop th)" by simp_all
qed

end

subsection \<open>Rotation of the premises of a subgoal\<close>

context pure_sig
begin

declare strip_all_vars.simps[simp del]

lemma list_forall_strip_all:
  "e \<turnstile> t : propT \<Longrightarrow> list_forall (strip_all_vars t) (strip_all_body t) = t"
proof (induction t arbitrary: e rule: strip_all_vars.induct)
  case (1 t)
  show ?case
  proof (cases "dest_all t")
    case None
    then show ?thesis by (simp add: strip_all_vars.simps strip_all_body.simps)
  next
    case (Some x)
    then obtain a T b where d: "dest_all t = Some (a, T, b)" by (cases x) auto
    note ty = typing_dest_all[OF "1.prems" d]
    have "list_forall (strip_all_vars b) (strip_all_body b) = b" by (rule "1.IH"[OF d HOL.refl HOL.refl ty(5)])
    with d ty(1) show ?thesis
      by (subst strip_all_vars.simps, subst strip_all_body.simps) simp
  qed
qed

lemma loose_bvar_list_forall_cong:
  "(\<And>k. loose_bvar X k \<longleftrightarrow> loose_bvar Y k) \<Longrightarrow>
    loose_bvar (list_forall ps X) k \<longleftrightarrow> loose_bvar (list_forall ps Y) k"
  by (induction ps arbitrary: k) (auto simp: all_const_def)

lemma list_forall_implies_perm:
  assumes ty: "e \<turnstile> list_forall ps (list_implies As B) : propT" and s: "set As' = set As"
  shows "e \<turnstile> list_forall ps (list_implies As' B) : propT"
    "loose_bvar (list_forall ps (list_implies As' B)) k \<longleftrightarrow> loose_bvar (list_forall ps (list_implies As B)) k"
proof -
  from ty have c: "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tX: "pushes e (map snd ps) \<turnstile> list_implies As B : propT"
    by (simp_all add: typing_list_forall)
  have "As' \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type"
    using typing_list_implies_imp[OF tX] s by (metis set_empty)
  with typing_list_impliesD[OF tX] s have "pushes e (map snd ps) \<turnstile> list_implies As' B : propT"
    by (intro typing_list_impliesI) auto
  with c show "e \<turnstile> list_forall ps (list_implies As' B) : propT" by (simp add: typing_list_forall)
  show "loose_bvar (list_forall ps (list_implies As' B)) k \<longleftrightarrow> loose_bvar (list_forall ps (list_implies As B)) k"
    by (rule loose_bvar_list_forall_cong) (simp add: loose_bvar_list_implies s)
qed

end

context pure_valuation
begin

lemma hb_list_forall_perm:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and bv: "bvals \<eta> (ienv \<rho> e) bv"
    and ty: "e \<turnstile> list_forall ps (list_implies As B) : propT" and s: "set As' = set As"
  shows "hb bv (ap \<rho> \<sigma> (list_forall ps (list_implies As' B))) \<longleftrightarrow>
    hb bv (ap \<rho> \<sigma> (list_forall ps (list_implies As B)))"
proof -
  have ty': "e \<turnstile> list_forall ps (list_implies As' B) : propT" by (rule list_forall_implies_perm(1)[OF ty s])
  have hl: "hb bv (ap \<rho> \<sigma> (list_forall ps (list_implies Xs B))) \<longleftrightarrow>
      (\<forall>us. pvals \<rho> ps us \<longrightarrow> ((\<forall>A\<in>set Xs. hb (vpushes bv us) (ap \<rho> \<sigma> A)) \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> B)))"
    if tX: "e \<turnstile> list_forall ps (list_implies Xs B) : propT" for Xs
  proof -
    from tX have c: "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
      and tX': "pushes e (map snd ps) \<turnstile> list_implies Xs B : propT"
      by (simp_all add: typing_list_forall)
    note tD = typing_list_impliesD[OF tX']
    have "hb (vpushes bv us) (ap \<rho> \<sigma> (list_implies Xs B)) \<longleftrightarrow>
        ((\<forall>A\<in>set Xs. hb (vpushes bv us) (ap \<rho> \<sigma> A)) \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> B))"
      if us: "pvals \<rho> ps us" for us
    proof -
      note bv' = bvals_vpushes_p[OF us bv]
      show ?thesis
        using sem_list_implies[of "map (ap \<rho> \<sigma>) Xs" "vpushes bv us" "ap \<rho> \<sigma> B"]
          sem_ap_bool[OF \<rho> \<sigma> _ bv'] tD
        by (simp add: ap_list_implies)
    qed
    then show ?thesis using holds_list_forall[OF \<rho> \<sigma> bv tX' c] by simp
  qed
  show ?thesis using hl[OF ty] hl[OF ty'] s by simp
qed

end

context pure_model
begin

lemma rotate_data_shape:
  assumes "okT (rotate_data k i state) (th, Bs, Bi', params, asms, m)"
  obtains tpairs Bi C where "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    "th = mk_rep (th_maxidx state) tpairs (list_implies (Bs @ [Bi']) C)"
    "Bi' = Bi \<or> Bi' = list_forall (strip_all_vars Bi)
      (list_implies (drop (nat_of_integer m) (strip_imp_prems (strip_all_body Bi)) @
        take (nat_of_integer m) (strip_imp_prems (strip_all_body Bi)))
        (strip_imp_concl (strip_all_body Bi)))"
  using assms unfolding rotate_data_def Let_def
  by (auto simp: returnW_def raiseW_def split: if_splits)

theorem rotate_rule_valid:
  assumes ok: "okT (rotate_rule k i th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)" and w: "wtp (th_prop th0)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)" "wtp (th_prop th)"
proof -
  from ok obtain Bs Bi' params asms m where "okT (rotate_data k i th0) (th, Bs, Bi', params, asms, m)"
    by (auto simp: rotate_rule_def returnW_def)
  then obtain tpairs Bi C where d: "okT (dest_state th0 i) (tpairs, Bs, Bi, C)"
    and th: "th = mk_rep (th_maxidx th0) tpairs (list_implies (Bs @ [Bi']) C)"
    and Bi'0: "Bi' = Bi \<or> Bi' = list_forall (strip_all_vars Bi)
      (list_implies (drop (nat_of_integer m) (strip_imp_prems (strip_all_body Bi)) @
        take (nat_of_integer m) (strip_imp_prems (strip_all_body Bi)))
        (strip_imp_concl (strip_all_body Bi)))"
    by (rule rotate_data_shape)
  note ds = okT_dest_state[OF d]
  have P: "th_prop th0 = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  define ps where "ps = strip_all_vars Bi"
  define As where "As = strip_imp_prems (strip_all_body Bi)"
  define c where "c = strip_imp_concl (strip_all_body Bi)"
  define As' where "As' = drop (nat_of_integer m) As @ take (nat_of_integer m) As"
  have Bi': "Bi' = Bi \<or> Bi' = list_forall ps (list_implies As' c)"
    using Bi'0 by (simp only: ps_def As_def c_def As'_def)
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF w] P by simp
  note tD = typing_list_impliesD[OF tP]
  have tBi: "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  have Bi: "Bi = list_forall ps (list_implies As c)"
  proof -
    have "pushes (\<lambda>_. propT) (map snd ps) \<turnstile> strip_all_body Bi : propT"
      using tBi list_forall_strip_all[OF tBi] unfolding ps_def by (metis typing_list_forall)
    from list_implies_strip_imp[OF this] list_forall_strip_all[OF tBi] show ?thesis
      by (simp add: ps_def As_def c_def)
  qed
  have s: "set As' = set As" unfolding As'_def by (rule set_rotate_take_drop)
  have tBi0: "(\<lambda>_. propT) \<turnstile> list_forall ps (list_implies As c) : propT" using tBi Bi by simp
  note pm = list_forall_implies_perm[OF tBi0 s]
  have tBi': "(\<lambda>_. propT) \<turnstile> Bi' : propT" using Bi' pm(1) tBi by blast
  have lb: "loose_bvar Bi' k \<longleftrightarrow> loose_bvar Bi k" for k
    using Bi' pm(2)[of k] Bi by metis
  have w': "wtp (list_implies (Bs @ [Bi']) C)"
  proof (rule wtpI)
    show "closed (list_implies (Bs @ [Bi']) C)"
      using wtpD(1)[OF w] P lb by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi']) C : propT"
      using tD tBi' typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  have "valid Sh hs tpairs (list_implies (Bs @ [Bi']) C)"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tpairs \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
      using validD[OF v sh g \<rho> \<rho>i \<sigma>] sol hh ds(1) P by simp
    then have h0: "(\<forall>A\<in>set (Bs @ [Bi]). holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) (Bs @ [Bi])" "ap \<rho> \<sigma> C"] gt[OF w] P
      by (simp add: ap_list_implies)
    have "holds (ap \<rho> \<sigma> Bi') \<longleftrightarrow> holds (ap \<rho> \<sigma> Bi)"
      using Bi' hb_list_forall_perm[OF cinstD(2)[OF \<rho>] \<sigma> bvals0 tBi0 s] Bi
      unfolding holds_hb by metis
    with h0 have "(\<forall>A\<in>set (Bs @ [Bi']). holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)" by simp
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (list_implies (Bs @ [Bi']) C))"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) (Bs @ [Bi'])" "ap \<rho> \<sigma> C"] gt[OF w']
      by (simp add: ap_list_implies)
  qed
  then show "valid Sh hs (th_tpairs th) (th_prop th)" "wtp (th_prop th)"
    using w' ds(1) by (simp_all add: th mk_rep_def)
qed

subsection \<open>Increment of indices\<close>

lemma ap_incr_indexes0:
  assumes "closed t" "gsubst \<sigma>"
  shows "ap \<rho> \<sigma> (incr_indexes [] inc t) = ap (tinc inc \<rho>) (lsubst inc \<rho> [] \<sigma> []) t"
proof -
  have "bfree 0 [] (ap \<rho> \<sigma> (incr_idx [] inc 0 t)) = ap (tinc inc \<rho>) (lsubst inc \<rho> [] \<sigma> []) t"
    by (rule bfree_ap_incr_idx[OF gsubstD(2)[OF assms(2)]]) (use assms(1) in \<open>simp_all add: closed_def\<close>)
  then show ?thesis by (simp add: incr_indexes_idx)
qed

lemma wtp_incr_indexes0: "wtp P \<Longrightarrow> wtp (incr_indexes [] inc P)"
  using typing_incr_idx0[OF wtpD(2) wtpD(1), of P "[]" "\<lambda>_. propT" inc] closed_incr_idx0[OF wtpD(1), of P "[]" inc]
  by (intro wtpI) (simp_all add: incr_indexes_idx closed_def incr_tvar_tren tsubst_propT)

theorem incr_indexes_thm_valid:
  assumes ok: "okT (incr_indexes_thm i th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and cP: "closed (th_prop th0)" and ct: "\<forall>(t, u)\<in>set (th_tpairs th0). closed t \<and> closed u"
    and hg: "\<forall>h\<in>set hs. vars h = {} \<and> ttvars h = {}"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof (cases "i = 0")
  case True
  with ok have "th = th0" by (auto simp: incr_indexes_thm_def returnW_def raiseW_def)
  with v show ?thesis by simp
next
  case False
  with ok have th: "th = mk_rep (th_maxidx th0 + i)
      (map (\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)) (th_tpairs th0))
      (incr_indexes [] i (th_prop th0))"
    by (auto simp: incr_indexes_thm_def returnW_def raiseW_def split: if_splits)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    let ?\<rho> = "tinc i \<rho>" and ?\<sigma> = "lsubst i \<rho> [] \<sigma> []"
    have \<sigma>': "gsubst ?\<sigma>"
      by (rule gsubst_lsubst[OF \<sigma> cinstD(2)[OF \<rho>]]) auto
    note a = ap_incr_indexes0[OF _ \<sigma>, of _ \<rho> i]
    have "holds_at \<eta> \<xi> (ap ?\<rho> ?\<sigma> (th_prop th0))"
    proof (rule validD[OF v sh g cinst_tinc[OF \<rho>] inh_inst_tinc[OF \<rho>i] \<sigma>'])
      fix t u assume tu: "(t, u) \<in> set (th_tpairs th0)"
      then have "(incr_indexes [] i t, incr_indexes [] i u) \<in> set (th_tpairs th)"
        by (force simp: th mk_rep_def)
      with sol a tu ct show "ap ?\<rho> ?\<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho> ?\<sigma> u" by fastforce
    next
      fix h assume "h \<in> set hs"
      with hh hg show "holds_at \<eta> \<xi> (ap ?\<rho> ?\<sigma> h)" by (simp add: ap_ground)
    qed
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))" by (simp add: th mk_rep_def a[OF cP])
  qed
qed

end

end
