section \<open>Soundness of the equality rules\<close>

theory Equality_Correct
  imports Instantiate_Correct
begin

text \<open>
  The equality rules are sound if the signature declares \<open>Pure.eq\<close> with its polymorphic type
  (\<^const>\<open>pure_model.eq_ok\<close>), so that the semantics interprets it as the identity of values.
\<close>

abbreviation eq_const :: "ptyp \<Rightarrow> pterm" where
  "eq_const T \<equiv> Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT)"

lemma dest_eq_any_SomeD: "dest_eq_any P = Some (t, u) \<Longrightarrow> \<exists>V. P = Const STR ''Pure.eq'' V $ t $ u"
  by (cases P rule: dest_eq_any.cases) (auto split: if_splits)

lemma dest_eq_any_dest_eq: "dest_eq P = Some (T, t, u) \<Longrightarrow> dest_eq_any P = Some (t, u)"
  by (cases P rule: dest_eq.cases) (auto split: if_splits)

lemma dest_eq_any_dest_eq_fun: "dest_eq_fun P = Some (T, t, u) \<Longrightarrow> dest_eq_any P = Some (t, u)"
  by (cases P rule: dest_eq_fun.cases) (auto split: if_splits)

context pure_model
begin

lemma sem_eq:
  assumes "eq_ok" "sem \<eta> \<xi> bv s \<in>\<^sub>u tsem \<eta> A" "sem \<eta> \<xi> bv t \<in>\<^sub>u tsem \<eta> A"
  shows "sem \<eta> \<xi> bv (eq_const A $ s $ t) = ubval (sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t)"
proof -
  have "ulam (tsem \<eta> A) (\<lambda>y. ubval (sem \<eta> \<xi> bv s = y)) \<in>\<^sub>u ufun (tsem \<eta> A) ubool"
    by (rule ulam_mem) simp
  with assms show ?thesis by (simp add: csem_eq eq_val_def uapp_ulam propT_def)
qed

lemma dest_eq_any_wtp:
  assumes "eq_ok" "dest_eq_any P = Some (t, u)" "wtp P"
  shows "\<exists>T. P = eq_const T $ t $ u \<and> closed t \<and> closed u \<and> (\<forall>e. e \<turnstile> t : T) \<and> (\<forall>e. e \<turnstile> u : T)"
proof -
  from dest_eq_any_SomeD[OF assms(2)] obtain V where P: "P = Const STR ''Pure.eq'' V $ t $ u" by blast
  from wtpD(2)[OF assms(3), of "\<lambda>_. propT"] P obtain A B where
    c: "const_typ_ok ctab (STR ''Pure.eq'') V" "V = A \<rightarrow>\<^sub>T B \<rightarrow>\<^sub>T propT"
    and tt: "(\<lambda>_. propT) \<turnstile> t : A" "(\<lambda>_. propT) \<turnstile> u : B"
    by auto
  obtain T where V: "V = T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT" by (rule eq_ok_typ[OF assms(1) c(1)])
  with c(2) have AB: "A = T" "B = T" by (auto simp: propT_def)
  have cl: "closed t" "closed u" using wtpD(1)[OF assms(3)] P by (simp_all add: closed_def)
  have "e \<turnstile> t : T" "e \<turnstile> u : T" for e
    using wtpD(2)[OF assms(3), of e] P V by auto
  then show ?thesis using P V cl by blast
qed

end

context pure_valuation
begin

lemma holds_eq:
  assumes "eq_ok" "cert_inst \<rho>" "gsubst \<sigma>" "closed s" "closed t" "\<And>e. e \<turnstile> s : T" "\<And>e. e \<turnstile> t : T"
  shows "holds (ap \<rho> \<sigma> (eq_const T $ s $ t)) \<longleftrightarrow> sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> s) = sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> t)"
proof -
  have g: "gterm (ap \<rho> \<sigma> s) (tsubst \<rho> T)" "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> T)"
    using gterm_ap[OF assms(2,3)] assms(4-7) by blast+
  have "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> s) \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> t) \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
    using sem_typing[OF good gtermD(2)[OF g(1)], of "\<lambda>_. propT"] sem_typing[OF good gtermD(2)[OF g(2)], of "\<lambda>_. propT"]
    by (simp_all add: bvals_def ubool_mem)
  with sem_eq[OF assms(1)] show ?thesis by (simp add: holds_at_def propT_def)
qed

end


context pure_model
begin

lemma mk_equals_ok:
  assumes "ok (mk_equals (t, u)) P" "closed t" "\<And>e. e \<turnstile> t : T"
  shows "P = eq_const T $ t $ u"
  using assms fastype_of_closed[OF assms(3) assms(2)] by (simp add: mk_equals_def)

text \<open>A theorem whose proposition holds in every instance that satisfies the hypotheses:\<close>

lemma valid_eqI:
  assumes "eq_ok" "closed s" "closed t" "\<And>e. e \<turnstile> s : T" "\<And>e. e \<turnstile> t : T"
    and "\<And>\<eta> \<xi> \<rho> \<sigma>. (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow> cinst \<rho> \<Longrightarrow> inh_inst \<rho> \<Longrightarrow>
      gsubst \<sigma> \<Longrightarrow> (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) \<Longrightarrow>
      (\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)) \<Longrightarrow>
      sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> s) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t)"
  shows "valid Sh hs tps (eq_const T $ s $ t)"
proof (rule validI)
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
    by unfold_locales (rule g)
  show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (eq_const T $ s $ t))"
    using holds_eq[OF assms(1) cinstD(2)[OF \<rho>] \<sigma> assms(2-5)] assms(6)[OF sh g \<rho> \<rho>i \<sigma> sol hh] by simp
qed

text \<open>The equation of a valid theorem holds in its instances:\<close>

lemma valid_eqD:
  assumes v: "valid Sh hs tps P" and "eq_ok" "dest_eq_any P = Some (s, t)" "wtp P"
    and "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" "good \<eta> \<xi>" "cinst \<rho>" "inh_inst \<rho>" "gsubst \<sigma>"
    "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  shows "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> s) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t)"
proof -
  interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
    by unfold_locales (rule assms(6))
  obtain T where P: "P = eq_const T $ s $ t" and c: "closed s" "closed t" and ty: "\<And>e. e \<turnstile> s : T" "\<And>e. e \<turnstile> t : T"
    using dest_eq_any_wtp[OF assms(2-4)] by blast
  have "holds (ap \<rho> \<sigma> P)" by (rule validD[OF v assms(5-11)])
  with holds_eq[OF assms(2) cinstD(2)[OF assms(7)] assms(9) c ty] P show ?thesis by simp
qed


subsection \<open>Reflexivity, symmetry, transitivity\<close>

theorem reflexive_valid:
  assumes ok: "okT (reflexive (CTerm t T m)) th" and eq: "eq_ok" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "valid Sh [] (th_tpairs th) (th_prop th)"
proof -
  from ok obtain P where P: "ok (mk_equals (t, t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: reflexive_def)
  have "valid Sh [] [] (eq_const T $ t $ t)" by (rule valid_eqI[OF eq c c ty ty]) simp
  then show ?thesis using mk_equals_ok[OF P c ty] by (simp add: th mk_rep_def)
qed

theorem symmetric_valid:
  assumes ok: "okT (symmetric th0) th" and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and eq: "eq_ok" and w: "wtp (th_prop th0)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  from ok obtain e t u where P: "th_prop th0 = e $ t $ u" and d: "dest_eq_fun (th_prop th0) \<noteq> None"
    and th: "th = mk_rep (th_maxidx th0) (th_tpairs th0) (e $ u $ t)"
    by (auto simp: symmetric_def returnW_def raiseW_def split: pterm.splits option.splits)
  then obtain T' where "dest_eq_fun (th_prop th0) = Some (T', t, u)"
    by (cases "th_prop th0" rule: dest_eq_fun.cases) (auto split: if_splits)
  then have d': "dest_eq_any (th_prop th0) = Some (t, u)" by (rule dest_eq_any_dest_eq_fun)
  obtain T where P': "th_prop th0 = eq_const T $ t $ u" and c: "closed t" "closed u"
    and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
    using dest_eq_any_wtp[OF eq d' w] by blast
  have "valid Sh hs (th_tpairs th0) (eq_const T $ u $ t)"
    by (rule valid_eqI[OF eq c(2,1) ty(2,1)]) (use valid_eqD[OF v eq d' w] in metis)
  then show ?thesis using P P' by (simp add: th mk_rep_def)
qed

theorem transitive_valid:
  assumes ok: "okT (transitive th1 th2) th"
    and v1: "valid Sh1 hs1 (th_tpairs th1) (th_prop th1)" and v2: "valid Sh2 hs2 (th_tpairs th2) (th_prop th2)"
    and eq: "eq_ok" and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
  shows "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain e x y T t1 u u' t2 where P1: "th_prop th1 = e $ x $ y" and d1: "dest_eq (th_prop th1) = Some (T, t1, u)"
    and d2: "dest_eq_any (th_prop th2) = Some (u', t2)" and a: "aconv_term u u'"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) (e $ t1 $ t2)"
    by (auto simp: transitive_def returnW_def raiseW_def split: pterm.splits option.splits prod.splits if_splits)
  have d1': "dest_eq_any (th_prop th1) = Some (t1, u)" by (rule dest_eq_any_dest_eq[OF d1])
  obtain A where P1': "th_prop th1 = eq_const A $ t1 $ u" and c1: "closed t1" "closed u"
    and ty1: "\<And>e. e \<turnstile> t1 : A" "\<And>e. e \<turnstile> u : A"
    using dest_eq_any_wtp[OF eq d1' w1] by blast
  obtain B where P2': "th_prop th2 = eq_const B $ u' $ t2" and c2: "closed u'" "closed t2"
    and ty2: "\<And>e. e \<turnstile> u' : B" "\<And>e. e \<turnstile> t2 : B"
    using dest_eq_any_wtp[OF eq d2 w2] by blast
  have AB: "A = B" using typing_aconv[OF a ty1(2)] ty2(1) typing_unique by metis
  have "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (union_tpairs (th_tpairs th1) (th_tpairs th2)) (eq_const A $ t1 $ t2)"
  proof (rule valid_eqI[OF eq c1(1) c2(2) ty1(1)])
    show "e \<turnstile> t2 : A" for e using ty2(2) AB by simp
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh1 \<union> Sh2 \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (union_tpairs (th_tpairs th1) (th_tpairs th2)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs1 @ hs2) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    have s1: "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t1) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> u)"
      by (rule valid_eqD[OF v1 eq d1' w1 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    have s2: "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> u') = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t2)"
      by (rule valid_eqD[OF v2 eq d2 w2 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    have "ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by (blast intro: aconv_term_conv aconv_term_ap a)
    moreover have "gterm (ap \<rho> \<sigma> u) (tsubst \<rho> A)" "gterm (ap \<rho> \<sigma> u') (tsubst \<rho> A)"
      using gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma>] c1 c2 ty1 ty2 AB by blast+
    ultimately have "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> u) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> u')"
      by (intro sem_conv[OF g, of "\<lambda>_. propT" _ "tsubst \<rho> A"]) (simp_all add: gterm_def bvals_def ubool_mem)
    with s1 s2 show "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t1) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t2)" by simp
  qed
  moreover from d1 P1 have "e = Const STR ''Pure.eq'' (A \<rightarrow>\<^sub>T A \<rightarrow>\<^sub>T propT)" using P1' by simp
  ultimately show ?thesis by (simp add: th mk_rep_def)
qed



subsection \<open>Equality of propositions\<close>

theorem equal_elim_valid:
  assumes ok: "okT (equal_elim th1 th2) th"
    and v1: "valid Sh1 hs1 (th_tpairs th1) (th_prop th1)" and v2: "valid Sh2 hs2 (th_tpairs th2) (th_prop th2)"
    and eq: "eq_ok" and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
  shows "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain A B where d: "dest_eq_any (th_prop th1) = Some (A, B)" and a: "aconv_term (th_prop th2) A"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) B"
    by (auto simp: equal_elim_def returnW_def raiseW_def split: option.splits if_splits)
  obtain T where P: "th_prop th1 = eq_const T $ A $ B" and c: "closed A" "closed B"
    and ty: "\<And>e. e \<turnstile> A : T" "\<And>e. e \<turnstile> B : T"
    using dest_eq_any_wtp[OF eq d w1] by blast
  have T: "T = propT" using typing_aconv[OF a wtpD(2)[OF w2]] ty(1) typing_unique by metis
  have "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (union_tpairs (th_tpairs th1) (th_tpairs th2)) B"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh1 \<union> Sh2 \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (union_tpairs (th_tpairs th1) (th_tpairs th2)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs1 @ hs2) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    have s: "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> A) = sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> B)"
      by (rule valid_eqD[OF v1 eq d w1 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    have h2: "holds (ap \<rho> \<sigma> (th_prop th2))"
      by (rule validD[OF v2 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    have wA: "wtp A" using c ty T by (auto intro: wtpI)
    have "holds (ap \<rho> \<sigma> A)"
      using holds_conv[OF gterm_ap_wtp[OF w2 cinstD(2)[OF \<rho>] \<sigma>] gterm_ap_wtp[OF wA cinstD(2)[OF \<rho>] \<sigma>] _ h2]
        a by (blast intro: aconv_term_conv aconv_term_ap)
    with s show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> B)" by (simp add: holds_at_def)
  qed
  then show ?thesis by (simp add: th mk_rep_def)
qed

theorem equal_intr_valid:
  assumes ok: "okT (equal_intr th1 th2) th"
    and v1: "valid Sh1 hs1 (th_tpairs th1) (th_prop th1)" and v2: "valid Sh2 hs2 (th_tpairs th2) (th_prop th2)"
    and eq: "eq_ok" and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
  shows "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain A B B' A' P where d1: "dest_imp (th_prop th1) = Some (A, B)" and d2: "dest_imp (th_prop th2) = Some (B', A')"
    and a: "aconv_term A A'" "aconv_term B B'" and mk: "ok (mk_equals (A, B)) P"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P"
    by (auto simp: equal_intr_def returnW_def raiseW_def split: option.splits if_splits prod.splits)
  note dw1 = dest_imp_wtp[OF d1 w1] and dw2 = dest_imp_wtp[OF d2 w2]
  have P: "P = eq_const propT $ A $ B" by (rule mk_equals_ok[OF mk wtpD(1)[OF dw1(2)] wtpD(2)[OF dw1(2)]])
  have "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (union_tpairs (th_tpairs th1) (th_tpairs th2)) (eq_const propT $ A $ B)"
  proof (rule valid_eqI[OF eq wtpD(1)[OF dw1(2)] wtpD(1)[OF dw1(3)] wtpD(2)[OF dw1(2)] wtpD(2)[OF dw1(3)]])
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh1 \<union> Sh2 \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (union_tpairs (th_tpairs th1) (th_tpairs th2)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs1 @ hs2) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have h1: "holds (ap \<rho> \<sigma> (implies $ A $ B))"
      using validD[OF v1 _ g \<rho> \<rho>i \<sigma>] sh sol_union_tpairs[OF sol] hh dw1(1) by auto
    have h2: "holds (ap \<rho> \<sigma> (implies $ B' $ A'))"
      using validD[OF v2 _ g \<rho> \<rho>i \<sigma>] sh sol_union_tpairs[OF sol] hh dw2(1) by auto
    have i1: "holds (ap \<rho> \<sigma> A) \<longrightarrow> holds (ap \<rho> \<sigma> B)"
      using h1 holds_imp[OF gt[OF dw1(2)] gt[OF dw1(3)]] by simp
    have cA: "ap \<rho> \<sigma> A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> A'" and cB: "ap \<rho> \<sigma> B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> B'"
      using a by (blast intro: aconv_term_conv aconv_term_ap)+
    have "holds (ap \<rho> \<sigma> B') \<longrightarrow> holds (ap \<rho> \<sigma> A')"
      using h2 holds_imp[OF gt[OF dw2(2)] gt[OF dw2(3)]] by simp
    then have i2: "holds (ap \<rho> \<sigma> B) \<longrightarrow> holds (ap \<rho> \<sigma> A)"
      using holds_conv[OF gt[OF dw1(3)] gt[OF dw2(2)] cB] holds_conv[OF gt[OF dw2(3)] gt[OF dw1(2)] conv_sym[OF cA]]
      by blast
    have "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> A) \<in>\<^sub>u ubool" "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> B) \<in>\<^sub>u ubool"
      using gterm_bool[OF gt[OF dw1(2)]] gterm_bool[OF gt[OF dw1(3)]] by simp_all
    with i1 i2 show "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> A) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> B)"
      by (auto simp: holds_at_def ubool_mem)
  qed
  then show ?thesis by (simp add: th P mk_rep_def)
qed


subsection \<open>Combination\<close>

lemma combination_data_ok:
  assumes "okT (combination_data th1 th2) (fT, U, f, g, t, u)"
  obtains T1 where "dest_eq_fun (th_prop th1) = Some (fT, f, g)" "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
    "fT = T1 \<rightarrow>\<^sub>T U"
  using assms
  by (auto simp: combination_data_def returnW_def raiseW_def split: option.splits ptyp.splits list.splits if_splits)

theorem combination_valid:
  assumes ok: "okT (combination th1 th2) th"
    and v1: "valid Sh1 hs1 (th_tpairs th1) (th_prop th1)" and v2: "valid Sh2 hs2 (th_tpairs th2) (th_prop th2)"
    and eq: "eq_ok" and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
  shows "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (th_tpairs th) (th_prop th)"
proof -
  from ok obtain fT U f g t u P where cd: "okT (combination_data th1 th2) (fT, U, f, g, t, u)"
    and mk: "ok (mk_equals (f $ t, g $ u)) P"
    and th: "th = mk_rep (max (th_maxidx th1) (th_maxidx th2)) (union_tpairs (th_tpairs th1) (th_tpairs th2)) P"
    by (auto simp: combination_def)
  obtain T1 where d1: "dest_eq_fun (th_prop th1) = Some (fT, f, g)" and d2: "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
    and fT: "fT = T1 \<rightarrow>\<^sub>T U"
    by (rule combination_data_ok[OF cd])
  note d1' = dest_eq_any_dest_eq_fun[OF d1] and d2' = dest_eq_any_dest_eq_fun[OF d2]
  obtain A where P1: "th_prop th1 = eq_const A $ f $ g" and c1: "closed f" "closed g"
    and ty1: "\<And>e. e \<turnstile> f : A" "\<And>e. e \<turnstile> g : A"
    using dest_eq_any_wtp[OF eq d1' w1] by blast
  obtain B where P2: "th_prop th2 = eq_const B $ t $ u" and c2: "closed t" "closed u"
    and ty2: "\<And>e. e \<turnstile> t : B" "\<And>e. e \<turnstile> u : B"
    using dest_eq_any_wtp[OF eq d2' w2] by blast
  from d1 P1 have A: "A = fT" by (simp add: propT_def)
  from d2 P2 have B: "B = T1" by (simp add: propT_def)
  have tft: "e \<turnstile> f $ t : U" "e \<turnstile> g $ u : U" for e using ty1 ty2 A B fT by auto
  have cft: "closed (f $ t)" "closed (g $ u)" using c1 c2 by (simp_all add: closed_def)
  have P: "P = eq_const U $ (f $ t) $ (g $ u)" by (rule mk_equals_ok[OF mk cft(1) tft(1)])
  have "valid (Sh1 \<union> Sh2) (hs1 @ hs2) (union_tpairs (th_tpairs th1) (th_tpairs th2)) (eq_const U $ (f $ t) $ (g $ u))"
  proof (rule valid_eqI[OF eq cft tft])
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh1 \<union> Sh2 \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (union_tpairs (th_tpairs th1) (th_tpairs th2)) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs1 @ hs2) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    have s1: "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> f) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> g)"
      by (rule valid_eqD[OF v1 eq d1' w1 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    have s2: "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> u)"
      by (rule valid_eqD[OF v2 eq d2' w2 _ g \<rho> \<rho>i \<sigma>]) (use sh sol_union_tpairs[OF sol] hh in auto)
    from s1 s2 show "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> (f $ t)) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> (g $ u))"
      by (simp add: ap_def)
  qed
  then show ?thesis by (simp add: th P mk_rep_def)
qed


subsection \<open>Conversions\<close>

lemma vt_is_empty_vt_empty [simp]: "vt_is_empty vt_empty"
  by transfer simp

lemma beta_norm_reds: "ok (beta_norm t) t' \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
proof -
  assume n: "ok (beta_norm t) t'"
  have e: "env_is_empty (empty_env (-1))" by (simp add: env_is_empty_def empty_env_def)
  have "acyc (empty_env (-1))" "closed_env (empty_env (-1))" "tacyc (tyenv (empty_env (-1)))"
    by (simp_all add: acyc_def dep_def closed_env_def empty_env_def tacyc_empty acyclic_def)
  from norm_term_env_apply(1)[OF n[unfolded beta_norm_def] this] show ?thesis by (simp add: env_apply_empty[OF e])
qed

lemma eta_reds_closed: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> closed s \<Longrightarrow> closed t"
  by (induction rule: rtranclp_induct) (auto simp: closed_iff_loose_bvar1 dest: free_eta)

lemma eta_reds_typing: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_eta)

lemma eta_reds_sup: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

text \<open>A conversion of closed well-typed terms is a valid equation:\<close>

lemma valid_conv_eq:
  assumes eq: "eq_ok" and c: "closed t" "closed t'" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T"
    and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'"
  shows "valid Sh [] [] (eq_const T $ t $ t')"
proof (rule valid_eqI[OF eq c ty])
  fix \<eta> \<xi> \<rho> \<sigma> assume g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have "gterm (ap \<rho> \<sigma> t) (tsubst \<rho> T)" "gterm (ap \<rho> \<sigma> t') (tsubst \<rho> T)"
    using gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma>] c ty by blast+
  moreover have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" by (rule conv_ap[OF cv cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
  ultimately show "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> t')"
    by (intro sem_conv[OF g, of "\<lambda>_. propT" _ "tsubst \<rho> T"]) (simp_all add: gterm_def bvals_def ubool_mem)
qed

lemma valid_reds_eq:
  assumes eq: "eq_ok" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T" and r: "(sup beta eta)\<^sup>*\<^sup>* t t'"
    and c': "closed t'" and ty': "\<And>e. e \<turnstile> t' : T"
  shows "valid Sh [] [] (eq_const T $ t $ t')"
proof (rule valid_conv_eq[OF eq c c' ty ty'])
  show "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" by (rule beta_eta_conv[OF r]) (use ty in \<open>auto simp: wt_def\<close>)
qed

theorem beta_conversion_valid:
  assumes ok: "okT (beta_conversion full (CTerm t T m)) th" and eq: "eq_ok"
    and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "valid Sh [] (th_tpairs th) (th_prop th)"
proof -
  from ok obtain t' P where r: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and mk: "ok (mk_equals (t, t')) P" and th: "th = mk_rep m [] P"
    by (auto simp: beta_conversion_def returnW_def raiseW_def subst_bound_subst
      dest: beta_norm_reds split: if_splits pterm.splits)
  have c': "closed t'" by (rule beta_reds_closed[OF r c])
  have ty': "e \<turnstile> t' : T" for e by (rule subject_reduction_beta'[OF r ty])
  have "valid Sh [] [] (eq_const T $ t $ t')" by (rule valid_reds_eq[OF eq c ty beta_reds_sup[OF r] c' ty'])
  then show ?thesis using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed

theorem eta_conversion_valid:
  assumes ok: "okT (eta_conversion (CTerm t T m)) th" and eq: "eq_ok"
    and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "valid Sh [] (th_tpairs th) (th_prop th)"
proof -
  from ok obtain P where mk: "ok (mk_equals (t, eta_contract t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: eta_conversion_def)
  note r = eta_contract_reds[of t]
  have c': "closed (eta_contract t)" by (rule eta_reds_closed[OF r c])
  have ty': "e \<turnstile> eta_contract t : T" for e by (rule eta_reds_typing[OF r ty])
  have "valid Sh [] [] (eq_const T $ t $ eta_contract t)" by (rule valid_reds_eq[OF eq c ty eta_reds_sup[OF r] c' ty'])
  then show ?thesis using mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
qed


subsection \<open>Abstraction\<close>

lemma loose_bvar_mono: "\<not> loose_bvar t k \<Longrightarrow> k \<le> k' \<Longrightarrow> \<not> loose_bvar t k'"
  by (induction t arbitrary: k k') auto

lemma abstract_rule_data_ok:
  assumes "okT (abstract_rule_data b hyps (CTerm x T m) th0) (U, f, g)" "\<And>e. e \<turnstile> x : T"
  obtains t u a z where "dest_eq_fun (th_prop th0) = Some (U, t, u)"
    "f = Abs b T (abstract_over x t)" "g = Abs b T (abstract_over x u)"
    "(x = Free a T \<and> \<not> occs_hyps x hyps (th_tpairs th0)) \<or> (x = Var z T \<and> \<not> occs_hyps x [] (th_tpairs th0))"
proof (cases x)
  case (Free a V)
  with assms(2)[of "\<lambda>_. propT"] have V: "V = T" by auto
  from assms(1) Free V show ?thesis
    by (auto simp: abstract_rule_data_def returnW_def raiseW_def Let_def
      split: option.splits prod.splits if_splits intro: that)
next
  case (Var zi V)
  with assms(2)[of "\<lambda>_. propT"] have V: "V = T" by auto
  from assms(1) Var V show ?thesis
    by (cases zi) (auto simp: abstract_rule_data_def returnW_def raiseW_def Let_def
      split: option.splits prod.splits if_splits intro: that)
qed (use assms(1) in \<open>auto simp: abstract_rule_data_def raiseW_def Let_def split: option.splits prod.splits\<close>)

theorem abstract_rule_valid:
  assumes ok: "okT (abstract_rule b hs (CTerm x T m) th0) th"
    and vth: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and eq: "eq_ok"
    and tx: "\<And>e. e \<turnstile> x : T"
    and uF: "\<And>t a U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<Longrightarrow> x = Free a T \<Longrightarrow> (a, U) \<in> pfrees t \<Longrightarrow> U = T"
    and uV: "\<And>t z U. t \<in> thm_terms hs (th_tpairs th0) (th_prop th0) \<Longrightarrow> x = Var z T \<Longrightarrow> (z, U) \<in> vars t \<Longrightarrow> U = T"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  from ok obtain U f g P where ad: "okT (abstract_rule_data b hs (CTerm x T m) th0) (U, f, g)"
    and mk: "ok (mk_equals (f, g)) P" and th: "th = mk_rep (maxidx_typ T (th_maxidx th0)) ?tps P"
    by (auto simp: abstract_rule_def)
  obtain t u a z where d: "dest_eq_fun ?P = Some (U, t, u)"
    and f: "f = Abs b T (abstract_over x t)" and g: "g = Abs b T (abstract_over x u)"
    and xc: "(x = Free a T \<and> \<not> occs_hyps x hs ?tps) \<or> (x = Var z T \<and> \<not> occs_hyps x [] ?tps)"
    by (rule abstract_rule_data_ok[OF ad tx])
  have hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {}" and wP: "wtp ?P" using wt by (simp_all add: wt_thm_def)
  have x: "x = Free a T \<or> x = Var z T" using xc by blast
  have nh: "\<forall>h\<in>set hs. \<not> occs x h" and nt: "\<forall>(t, u)\<in>set ?tps. \<not> occs x t \<and> \<not> occs x u"
    using xc hv by (fastforce simp: occs_hyps_def occs_Var)+
  note d' = dest_eq_any_dest_eq_fun[OF d]
  obtain A where P0: "?P = eq_const A $ t $ u" and c: "closed t" "closed u"
    and ty: "\<And>e. e \<turnstile> t : A" "\<And>e. e \<turnstile> u : A"
    using dest_eq_any_wtp[OF eq d' wP] by blast
  have tQ: "e\<langle>0:T\<rangle> \<turnstile> abstract_over x s : A" if "closed s" "\<And>e. e \<turnstile> s : A" for s e
    unfolding abstract_over_def
    by (rule typing_abstract_over_aux[OF x that(2)]) (use that(1) in \<open>simp_all add: closed_def\<close>)
  have cT: "cert_typ alg ar T" using tx[of "\<lambda>_. propT"] x by auto
  have tf: "e \<turnstile> f : T \<rightarrow>\<^sub>T A" "e \<turnstile> g : T \<rightarrow>\<^sub>T A" for e
    using tQ[OF c(1) ty(1)] tQ[OF c(2) ty(2)] cT by (auto simp: f g)
  have cf: "closed f" "closed g"
    using loose_bvar_abstract_over_aux[OF loose_bvar_mono[of t 0 1], of 0 x]
      loose_bvar_abstract_over_aux[OF loose_bvar_mono[of u 0 1], of 0 x] c
    by (simp_all add: f g closed_def abstract_over_def)
  have P: "P = eq_const (T \<rightarrow>\<^sub>T A) $ f $ g" by (rule mk_equals_ok[OF mk cf(1) tf(1)])
  have "valid Sh hs ?tps (eq_const (T \<rightarrow>\<^sub>T A) $ f $ g)"
  proof (rule valid_eqI[OF eq cf tf])
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and gd: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set ?tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    let ?\<eta> = "apv_t \<eta> \<rho>" and ?\<xi> = "apv_v \<eta> \<xi> \<rho> \<sigma>"
    have body: "sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x s)) = sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) s"
      if "closed s" "\<And>e. e \<turnstile> s : A" for s v
    proof -
      have "sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x s)) = sem ?\<eta> ?\<xi> (push v (\<lambda>_. utrue)) (abstract_over x s)"
        by (rule sem_ap[OF gsubstD(1)[OF \<sigma>] tQ[OF that]])
      also have "\<dots> = sem ?\<eta> (vupd x v ?\<xi>) (push v (\<lambda>_. utrue)) s"
        using sem_abstract_over_aux[OF x, of 0 ?\<eta> ?\<xi> "push v (\<lambda>_. utrue)" s] by (simp add: abstract_over_def push_def)
      also have "\<dots> = sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) s" by (rule sem_closed[OF that(1)])
      finally show ?thesis .
    qed
    have eqv: "sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) t = sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) u
        \<and> sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) t \<in>\<^sub>u tsem \<eta> (tsubst \<rho> A)"
      if v: "v \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for v
    proof -
      have g': "good ?\<eta> (vupd x v ?\<xi>)"
        by (rule good_vupd[OF good_ap[OF gd \<rho> \<rho>i gsubstD(1)[OF \<sigma>]] x]) (use v in \<open>simp add: tsem_tsubst apv_t_def\<close>)
      have m: "sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) s \<in>\<^sub>u tsem ?\<eta> A" if "\<And>e. e \<turnstile> s : A" for s
        using sem_typing[OF g' that, of "\<lambda>_. propT"] by (simp add: bvals_def apv_t_def tinstv_def ubool_mem tsubst_propT)
      have "sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) ?P = utrue"
        by (rule forall_sem[OF vth wt x nh nt _ _ sh gd \<rho> \<rho>i \<sigma> sol hh v]) (use uF uV in blast)+
      with sem_eq[OF eq m[OF ty(1)] m[OF ty(2)]] P0 have "sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) t = sem ?\<eta> (vupd x v ?\<xi>) (\<lambda>_. utrue) u"
        by simp
      with m[OF ty(1)] show ?thesis by (simp add: apv_t_def tsem_tsubst)
    qed
    have "ulam (tsem \<eta> (tsubst \<rho> T)) (\<lambda>v. sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x t))) =
        ulam (tsem \<eta> (tsubst \<rho> T)) (\<lambda>v. sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x u)))"
    proof (rule ulam_cong[where B = "tsem \<eta> (tsubst \<rho> A)"])
      fix v assume v: "v \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
      show "sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x t)) \<in>\<^sub>u tsem \<eta> (tsubst \<rho> A)"
        using body[OF c(1) ty(1)] eqv[OF v] by metis
      show "sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x t)) =
          sem \<eta> \<xi> (push v (\<lambda>_. utrue)) (ap \<rho> \<sigma> (abstract_over x u))"
        using body[OF c(1) ty(1)] body[OF c(2) ty(2)] eqv[OF v] by simp
    qed
    then show "sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> f) = sem \<eta> \<xi> (\<lambda>_. utrue) (ap \<rho> \<sigma> g)"
      by (simp add: f g ap_def)
  qed
  then show ?thesis by (simp add: th P mk_rep_def)
qed

end

end
