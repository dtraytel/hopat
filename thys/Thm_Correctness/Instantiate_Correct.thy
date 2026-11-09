section \<open>Soundness of instantiation\<close>

theory Instantiate_Correct
  imports Generalize_Correct
begin

subsection \<open>The instantiation tables as substitutions\<close>

definition tab_inst :: "instT_m \<Rightarrow> tinst" where
  "tab_inst tab v S = (case map_of tab (v, S) of Some (T, _) \<Rightarrow> T | None \<Rightarrow> TVar v S)"

definition tab_subst :: "inst_m \<Rightarrow> vsubst" where
  "tab_subst tt x T = (case lookup_var tt (x, T) of Some (t, _) \<Rightarrow> t | None \<Rightarrow> Var x T)"

lemma instT_m_fst:
  "fst (instT_m tab T m) = tsubst (tab_inst tab) T"
  "fst (instTs_m tab Ts m) = map (tsubst (tab_inst tab)) Ts"
  by (induction tab T m and tab Ts m rule: instT_m_instTs_m.induct)
    (auto simp: tab_inst_def split: prod.splits option.splits)

lemma instT_m_eq: "instT_m tab T m = (T', m') \<Longrightarrow> T' = tsubst (tab_inst tab) T"
  using instT_m_fst(1)[of tab T m] by simp

lemma inst_m_fst: "fst (inst_m tT tt t m) = vsubst (tab_subst tt) (inst (tab_inst tT) t)"
  by (induction tT tt t m rule: inst_m.induct)
    (auto simp: tab_subst_def dest: instT_m_eq split: prod.splits option.splits)

lemma list_comb_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<Longrightarrow> list_all2 beta_reds us us' \<Longrightarrow> list_comb s us \<rightarrow>\<^sub>\<beta>\<^sup>* list_comb s' us'"
proof (induction us arbitrary: s s' us')
  case (Cons u us)
  then obtain u' us'' where "us' = u' # us''" "u \<rightarrow>\<^sub>\<beta>\<^sup>* u'" "list_all2 beta_reds us us''"
    by (cases us') auto
  with Cons.IH[of "s $ u" "s' $ u'" us''] Cons.prems show ?case by (auto simp: list_comb_def)
qed (simp add: list_comb_def)

lemma betapplys_beta_reds: "list_comb t us \<rightarrow>\<^sub>\<beta>\<^sup>* betapplys t us"
proof (induction us arbitrary: t)
  case (Cons u us)
  have "t $ u \<rightarrow>\<^sub>\<beta>\<^sup>* betapply t u"
    by (cases t) (auto simp: subst_bound_subst)
  then have "list_comb (t $ u) us \<rightarrow>\<^sub>\<beta>\<^sup>* list_comb (betapply t u) us"
    by (rule list_comb_beta_reds) (simp add: list_all2_refl)
  with Cons.IH[of "betapply t u"] show ?case by (simp add: list_comb_def)
qed (simp add: list_comb_def)

text \<open>The instantiation with \<open>\<beta>\<close>-reduction of the instances applied to arguments:\<close>

lemma inst_beta_m_reds:
  "vsubst (tab_subst tt) (inst (tab_inst tT) t) \<rightarrow>\<^sub>\<beta>\<^sup>* fst (inst_beta_m tT tt t m)"
  "list_all2 beta_reds args0 args \<Longrightarrow>
    list_comb (vsubst (tab_subst tt) (inst (tab_inst tT) t)) args0 \<rightarrow>\<^sub>\<beta>\<^sup>* fst (inst_beta_spine tT tt t args m)"
proof (induction tT tt t m and tT tt t args m arbitrary: and args0 rule: inst_beta_m_inst_beta_spine.induct)
  case (5 tT tt x T b m)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  from "5.IH"[OF e[symmetric]] e instT_m_fst(1)[of tT T m] show ?case
    by (auto simp: rtrancl_beta_Abs split: prod.splits)
next
  case (6 tT tt t u m)
  obtain u' m1 where e: "inst_beta_m tT tt u m = (u', m1)" by (cases "inst_beta_m tT tt u m")
  have "list_comb (vsubst (tab_subst tt) (inst (tab_inst tT) t)) [vsubst (tab_subst tt) (inst (tab_inst tT) u)]
      \<rightarrow>\<^sub>\<beta>\<^sup>* fst (inst_beta_spine tT tt t [u'] m1)"
    by (rule "6.IH"(2)[OF e[symmetric]]) (use "6.IH"(1) e in simp)
  with e show ?case by (simp add: list_comb_def)
next
  case (7 tT tt t u args m)
  obtain u' m1 where e: "inst_beta_m tT tt u m = (u', m1)" by (cases "inst_beta_m tT tt u m")
  have "list_comb (vsubst (tab_subst tt) (inst (tab_inst tT) t)) (vsubst (tab_subst tt) (inst (tab_inst tT) u) # args0)
      \<rightarrow>\<^sub>\<beta>\<^sup>* fst (inst_beta_spine tT tt t (u' # args) m1)"
    by (rule "7.IH"(2)[OF e[symmetric]]) (use "7.IH"(1) e "7.prems" in simp)
  with e show ?case by (simp add: list_comb_def)
next
  case (8 tT tt x i T args m)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have T': "T' = tsubst (tab_inst tT) T" using instT_m_fst(1)[of tT T m] e by simp
  show ?case
  proof (cases "lookup_var tt ((x, i), T')")
    case None
    with "8.prems" e T' show ?thesis
      by (auto simp: tab_subst_def intro: list_comb_beta_reds)
  next
    case (Some r)
    obtain t' j where r: "r = (t', j)" by (cases r)
    have "list_comb t' args0 \<rightarrow>\<^sub>\<beta>\<^sup>* list_comb t' args" by (rule list_comb_beta_reds) (use "8.prems" in auto)
    moreover have "list_comb t' args \<rightarrow>\<^sub>\<beta>\<^sup>* (if is_Abs t' then betapplys t' args else list_comb t' args)"
      using betapplys_beta_reds by auto
    ultimately show ?thesis using Some r e T'
      by (auto simp: tab_subst_def)
  qed
next
  case (12 tT tt x T b args m)
  obtain T' m1 where e: "instT_m tT T m = (T', m1)" by (cases "instT_m tT T m")
  have T': "T' = tsubst (tab_inst tT) T" using instT_m_fst(1)[of tT T m] e by simp
  obtain b' m2 where e2: "inst_beta_m tT tt b m1 = (b', m2)" by (cases "inst_beta_m tT tt b m1")
  have "Abs x T' (vsubst (tab_subst tt) (inst (tab_inst tT) b)) \<rightarrow>\<^sub>\<beta>\<^sup>* Abs x T' b'"
    using "12.IH"[OF e[symmetric]] e2 by (auto intro: rtrancl_beta_Abs)
  with "12.prems" e e2 T' show ?case
    by (auto intro: list_comb_beta_reds)
next
  case (3 tT tt xi T m)
  from "3.IH"[of "[]"] show ?case by (simp add: list_comb_def)
qed (auto dest: instT_m_eq intro!: list_comb_beta_reds split: prod.splits)


lemma lookup_var_SomeD: "lookup_var xs v = Some r \<Longrightarrow> (v, r) \<in> set xs"
  by (induction xs v rule: lookup_var.induct) (auto split: if_splits)

lemma fold_tpairs:
  assumes "\<And>t i. R t (fst (f t i))"
  shows "\<exists>ps. fst (fold (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
      (acc @ [(t', u')], i2)) tps (acc0, m)) = acc0 @ ps \<and> list_all2 (\<lambda>(t, u) (t', u'). R t t' \<and> R u u') tps ps"
proof (induction tps arbitrary: acc0 m)
  case (Cons p tps)
  obtain t u where p: "p = (t, u)" by (cases p)
  obtain t' i1 where e1: "f t m = (t', i1)" by (cases "f t m")
  obtain u' i2 where e2: "f u i1 = (u', i2)" by (cases "f u i1")
  from Cons.IH[of "acc0 @ [(t', u')]" i2] obtain ps where
    "fst (fold (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
      (acc @ [(t', u')], i2)) tps (acc0 @ [(t', u')], i2)) = acc0 @ [(t', u')] @ ps"
    "list_all2 (\<lambda>(t, u) (t', u'). R t t' \<and> R u u') tps ps" by auto
  moreover have "R t t'" "R u u'" using assms[of t m] assms[of u i1] e1 e2 by simp_all
  ultimately show ?case using p e1 e2 by (intro exI[of _ "(t', u') # ps"]) simp
qed simp

context pure_sig
begin

lemma beta_reds_closed: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> closed s \<Longrightarrow> closed t"
  by (induction rule: rtranclp_induct) (auto simp: closed_iff_loose_bvar1 dest: free_beta)

lemma beta_reds_sup: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* s t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

end

context pure_model
begin

lemma vars_inst: "vars (inst \<rho> t) = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vars t"
  by (induction t) auto

lemma has_sort_check_instT:
  "okT (check_instT alg tab) () \<Longrightarrow> ((v, S), (U, j)) \<in> set tab \<Longrightarrow> wft ar U \<Longrightarrow> has_sort alg U S"
proof (induction tab)
  case (Cons e xs)
  obtain a i S' U' j' where e: "e = (((a, i), S'), (U', j'))" by (metis prod.collapse)
  from Cons.prems(1) e obtain b where b: "ok (of_sort alg U' S') b"
    and r: "okT (if b then check_instT alg xs else raiseW (NOT_OF_SORT U' S')) ()"
    by auto
  from r have b': "b" "okT (check_instT alg xs) ()" by (auto simp: raiseW_def split: if_splits)
  show ?case
  proof (cases "((v, S), (U, j)) = (((a, i), S'), (U', j'))")
    case True
    then have eq: "U = U'" "S = S'" by auto
    with Cons.prems(3) have "of_sort alg U' S' = return (has_sort alg U' S')" by (simp add: of_sort_sem)
    with b b'(1) eq show ?thesis by simp
  next
    case False
    with Cons.prems(2) e have "((v, S), (U, j)) \<in> set xs" by auto
    from Cons.IH[OF b'(2) this Cons.prems(3)] show ?thesis .
  qed
qed simp

lemma check_inst_eq: "okT (check_inst insts) () \<Longrightarrow> ((v, T), (u, U, j)) \<in> set insts \<Longrightarrow> T = U"
  by (induction insts rule: check_inst.induct) (auto simp: raiseW_def split: if_splits)



lemma vars_cert: "e \<turnstile> t : T \<Longrightarrow> (x, U) \<in> vars t \<Longrightarrow> cert_typ alg ar U"
  by (induction rule: typing.induct) auto

lemma thm_vars_inst:
  "thm_vars (map (inst \<rho>) hs) (map (\<lambda>(t, u). (inst \<rho> t, inst \<rho> u)) tps) (inst \<rho> P) =
    (\<lambda>(x, T). (x, tsubst \<rho> T)) ` thm_vars hs tps P"
  by (auto simp: thm_vars_def vars_inst image_Un image_UN split: prod.splits) force+

theorem instantiate_valid:
  assumes ok: "okT (instantiate alg bt instT insts th0) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and cT: "\<forall>((v, S), (U, j))\<in>set instT. cert_typ alg ar U \<and> tsorts U \<subseteq> Sh'" and Sh: "Sh \<subseteq> Sh'"
    and ct: "\<forall>((v, T), (u, U, j))\<in>set insts. closed u \<and> (\<forall>e. e \<turnstile> u : U)"
    and uniq: "\<And>x T U. (x, T) \<in> thm_vars hs (th_tpairs th0) (th_prop th0) \<Longrightarrow>
      (x, U) \<in> thm_vars hs (th_tpairs th0) (th_prop th0) \<Longrightarrow> tsubst (tab_inst instT) T = tsubst (tab_inst instT) U"
  shows "valid Sh' hs (th_tpairs th) (th_prop th)"
proof (cases "instT = [] \<and> insts = []")
  case True
  with ok have "th = th0" by (simp add: instantiate_def returnW_def)
  with v Sh show ?thesis by (simp add: valid_mono)
next
  case False
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  define tt where "tt = map (\<lambda>(v, (u, U, j)). (v, (u, j))) insts"
  define f where "f = (if bt then inst_beta_m instT tt else inst_m instT tt)"
  define F where "F = (\<lambda>(t, u) (acc, i). case f t i of (t', i1) \<Rightarrow> case f u i1 of (u', i2) \<Rightarrow>
    (acc @ [(t' :: pterm, u')], i2))"
  have ci: "okT (check_instT alg instT) ()" and cs: "okT (check_inst insts) ()"
    and thP: "th_prop th = fst (f ?P (-1))" and thT: "th_tpairs th = fst (fold F ?tps ([], snd (f ?P (-1))))"
    using ok False unfolding instantiate_def f_def F_def tt_def
    by (auto simp: returnW_def raiseW_def Let_def mk_rep_def split: prod.splits)
  define \<rho>0 where "\<rho>0 = tab_inst instT"
  define \<sigma>0 where "\<sigma>0 = tab_subst tt"
  let ?S = "\<lambda>t. vsubst \<sigma>0 (inst \<rho>0 t)"
  have wP: "wtp ?P" and hw: "\<And>h. h \<in> set hs \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    and tw: "\<And>t u. (t, u) \<in> set ?tps \<Longrightarrow> closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using wt by (fastforce simp: wt_thm_def)+
  have c\<rho>: "cinst \<rho>0" unfolding cinst_def
  proof
    show "wsinst alg \<rho>0" unfolding wsinst_def
    proof (intro allI)
      fix v S show "has_sort alg (\<rho>0 v S) S"
      proof (cases "map_of instT (v, S)")
        case (Some r)
        obtain U j where r: "r = (U, j)" by (cases r)
        with Some have "((v, S), (U, j)) \<in> set instT" by (auto dest: map_of_SomeD)
        moreover from this cT have "wft ar U" by (auto simp: cert_typ_def)
        ultimately show ?thesis using has_sort_check_instT[OF ci] Some r by (simp add: \<rho>0_def tab_inst_def)
      next
        case None
        then have "\<rho>0 v S = TVar v S" by (simp add: \<rho>0_def tab_inst_def)
        then show ?thesis by (simp only: has_sort_TVar_refl)
      qed
    qed
    show "cert_inst \<rho>0" unfolding cert_inst_def
    proof (intro allI impI)
      fix v S assume "sort_ok alg S"
      then show "cert_typ alg ar (\<rho>0 v S)" using cT
        by (auto simp: \<rho>0_def tab_inst_def cert_typ_def split: option.splits dest!: map_of_SomeD)
    qed
  qed
  have sb: "sbound \<rho>0 Sh'" using cT
    by (auto simp: sbound_def \<rho>0_def tab_inst_def split: option.splits dest!: map_of_SomeD)
  have \<sigma>0: "wt_subst \<sigma>0" unfolding wt_subst_def closed_subst_def
  proof (intro conjI allI impI)
    fix x T
    show "closed (\<sigma>0 x T)" using ct
      by (auto simp: \<sigma>0_def tab_subst_def tt_def closed_def split: option.splits dest!: lookup_var_SomeD)
    assume "cert_typ alg ar T"
    then show "\<exists>e. e \<turnstile> \<sigma>0 x T : T"
    proof (cases "lookup_var tt (x, T)")
      case (Some r)
      obtain u j where r: "r = (u, j)" by (cases r)
      with Some obtain U where "((x, T), (u, U, j)) \<in> set insts"
        by (auto simp: tt_def dest!: lookup_var_SomeD)
      with ct check_inst_eq[OF cs this] Some r show ?thesis by (auto simp: \<sigma>0_def tab_subst_def)
    qed (auto simp: \<sigma>0_def tab_subst_def)
  qed
  have v1: "valid Sh' (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps) (inst \<rho>0 ?P)"
    by (rule valid_tinst[OF v c\<rho> Sh sb])
  have cV: "cert_typ alg ar T" if "(x, T) \<in> thm_vars hs ?tps ?P" for x T
  proof -
    have "\<exists>t U. e \<turnstile> t : U \<and> (x, T) \<in> vars t" for e
      using that wtpD(2)[OF wP] hw tw unfolding thm_vars_def by fastforce
    then show ?thesis by (auto dest: vars_cert)
  qed
  have v2: "valid Sh' (map (vsubst \<sigma>0) (map (inst \<rho>0) hs))
      (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps))
      (vsubst \<sigma>0 (inst \<rho>0 ?P))"
  proof (rule valid_vsubst[OF v1 \<sigma>0])
    fix x T U
    assume "(x, T) \<in> thm_vars (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps) (inst \<rho>0 ?P)"
      "(x, U) \<in> thm_vars (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps) (inst \<rho>0 ?P)"
    then show "T = U" using uniq unfolding thm_vars_inst \<rho>0_def by auto
  next
    fix x T
    assume "(x, T) \<in> thm_vars (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) ?tps) (inst \<rho>0 ?P)"
    then show "cert_typ alg ar T"
      using cV cert_typ_tsubst[OF _ cinstD(2)[OF c\<rho>]] unfolding thm_vars_inst by auto
  qed
  have hs_eq: "map (vsubst \<sigma>0) (map (inst \<rho>0) hs) = hs"
    using hw ap_ground[of _ \<rho>0 \<sigma>0] by (auto simp: ap_def intro: map_idI)
  have v3: "valid Sh' hs (map (\<lambda>(t, u). (?S t, ?S u)) ?tps) (?S ?P)"
    using v2 unfolding hs_eq by (simp add: comp_def case_prod_unfold)
  show ?thesis
  proof (cases bt)
    case False
    then have fS: "fst (f t i) = ?S t" for t i by (simp add: f_def inst_m_fst \<rho>0_def \<sigma>0_def)
    obtain ps where ps: "fst (fold F ?tps ([], snd (f ?P (-1)))) = [] @ ps"
      and r: "list_all2 (\<lambda>(t, u) (t', u'). t' = ?S t \<and> u' = ?S u) ?tps ps"
      using fold_tpairs[of "\<lambda>t t'. t' = ?S t" f ?tps "[]" "snd (f ?P (-1))"] fS unfolding F_def by auto
    from r have "ps = map (\<lambda>(t, u). (?S t, ?S u)) ?tps"
      by (induction rule: list_all2_induct) auto
    with v3 ps show ?thesis by (simp add: thP thT fS)
  next
    case True
    then have fS: "?S t \<rightarrow>\<^sub>\<beta>\<^sup>* fst (f t i)" for t i
      using inst_beta_m_reds(1) by (simp add: f_def \<rho>0_def \<sigma>0_def)
    obtain ps where ps: "fst (fold F ?tps ([], snd (f ?P (-1)))) = [] @ ps"
      and r: "list_all2 (\<lambda>(t, u) (t', u'). ?S t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> ?S u \<rightarrow>\<^sub>\<beta>\<^sup>* u') ?tps ps"
      using fold_tpairs[of "\<lambda>t t'. ?S t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" f ?tps "[]" "snd (f ?P (-1))"] fS unfolding F_def by auto
    have gS: "gterm (?S t) (tsubst \<rho>0 T)" if "closed t" "\<And>e. e \<turnstile> t : T" for t T
      using gterm_ap[OF cinstD(2)[OF c\<rho>] _ that] \<sigma>0 by (simp add: ap_def gsubst_def)
    have cv: "?S t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" if "?S t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "closed t" "\<And>e. e \<turnstile> t : T" for t t' T
      using beta_eta_conv[OF beta_reds_sup[OF that(1)]] gS[OF that(2,3)] by (auto simp: gterm_def wt_def)
    let ?P' = "fst (f ?P (-1))"
    have gP: "gterm (?S ?P) propT" using gS[OF wtpD(1)[OF wP] wtpD(2)[OF wP]] by (simp add: tsubst_propT)
    have "valid Sh' hs ps ?P'"
    proof (rule valid_conv[OF v3])
      show "?S ?P \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?P'" by (rule cv[OF fS wtpD(1)[OF wP] wtpD(2)[OF wP]])
      show "closed (?S ?P)" "(\<lambda>_. propT) \<turnstile> ?S ?P : propT" using gP by (simp_all add: gterm_def)
      show "closed ?P'" by (rule beta_reds_closed[OF fS]) (use gP in \<open>simp add: gterm_def\<close>)
      show "(\<lambda>_. propT) \<turnstile> ?P' : propT" by (rule subject_reduction_beta'[OF fS]) (use gP in \<open>simp add: gterm_def\<close>)
      show "list_all2 (\<lambda>h h'. h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h' \<and> closed h \<and> (\<exists>e. e \<turnstile> h : propT) \<and> closed h' \<and> (\<exists>e. e \<turnstile> h' : propT)) hs hs"
        using hw by (auto simp: list_all2_conv_all_nth wtp_def)
      have l: "length ps = length ?tps" using r by (simp add: list_all2_lengthD)
      have "?S (fst (?tps ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> fst (ps ! i) \<and> ?S (snd (?tps ! i)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd (ps ! i)"
        if i: "i < length ?tps" for i
      proof -
        obtain t u where p: "?tps ! i = (t, u)" by (cases "?tps ! i")
        obtain t' u' where q: "ps ! i = (t', u')" by (cases "ps ! i")
        from list_all2_nthD[OF r i] p q have red: "?S t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "?S u \<rightarrow>\<^sub>\<beta>\<^sup>* u'" by simp_all
        from tw[of t u] nth_mem[OF i] p obtain T where "closed t" "closed u" "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T"
          by auto
        with red cv p q show ?thesis by auto
      qed
      then show "list_all2 (\<lambda>(t, u) (t', u'). t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u') (map (\<lambda>(t, u). (?S t, ?S u)) ?tps) ps"
        using l by (auto simp: list_all2_conv_all_nth case_prod_unfold)
    qed
    with ps show ?thesis by (simp add: thP thT)
  qed
qed

end

end
