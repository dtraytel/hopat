section \<open>Soundness of proof by an equivalent assumption\<close>

theory Assumption_Correct
  imports Rules_Correct "Pure_Thm.Pure_Assumption"
begin

lemma find_index_from_SomeD: "find_index_from P xs k = Some n \<Longrightarrow> \<exists>x\<in>set xs. P x"
  by (induction P xs k rule: find_index_from.induct) (auto split: if_splits)

context pure_valuation
begin

text \<open>A subgoal one of whose assumptions is equivalent to its conclusion holds:\<close>

lemma hb_list_forall_taut:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and bv: "bvals \<eta> (ienv \<rho> e) bv"
    and ty: "e \<turnstile> list_forall ps (list_implies As B) : propT" and A: "A \<in> set As" and c: "aeconv A B"
  shows "hb bv (ap \<rho> \<sigma> (list_forall ps (list_implies As B)))"
proof -
  from ty have cs: "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tX: "pushes e (map snd ps) \<turnstile> list_implies As B : propT"
    by (simp_all add: typing_list_forall)
  note tD = typing_list_impliesD[OF tX]
  let ?e = "pushes e (map snd ps)"
  have tA: "?e \<turnstile> A : propT" using tD A by blast
  have cv: "A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B" by (rule aeconv_conv[OF c]) (use tA tD in \<open>auto simp: wt_def\<close>)
  have "hb (vpushes bv us) (ap \<rho> \<sigma> (list_implies As B))" if us: "pvals \<rho> ps us" for us
  proof -
    note bv' = bvals_vpushes_p[OF us bv]
    note ta = typing_ap_inst[OF _ \<rho> gsubstD(1)[OF \<sigma>]]
    have "sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> A) = sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> B)"
      by (rule sem_conv[OF good ta[OF tA] ta[OF tD[THEN conjunct2]] conv_ap[OF cv \<rho> gsubstD(1)[OF \<sigma>]]])
        (rule bv')
    then show ?thesis
      using sem_list_implies[of "map (ap \<rho> \<sigma>) As" "vpushes bv us" "ap \<rho> \<sigma> B"] sem_ap_bool[OF \<rho> \<sigma> _ bv'] tD A
      by (auto simp: ap_list_implies)
  qed
  then show ?thesis using holds_list_forall[OF \<rho> \<sigma> bv tX cs] by simp
qed

end

lemma eq_assumption_ok:
  assumes "okT (eq_assumption i state) (n, th)"
  shows "\<exists>tpairs Bs Bi C params asms concl. okT (dest_state state i) (tpairs, Bs, Bi, C) \<and>
    assum_problems (-1) Bi = (params, asms, concl) \<and> (\<exists>a\<in>set asms. aeconv a concl) \<and>
    th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
proof -
  obtain tpairs Bs Bi C where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and
    r: "okT (case assum_problems (-1) Bi of (_, asms, concl) \<Rightarrow>
      (case find_index_from (\<lambda>asm. aeconv asm concl) asms 0 of
        None \<Rightarrow> raiseW (THM (STR ''eq_assumption'') 0 State)
      | Some n \<Rightarrow> returnW (n + 1,
          \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>))) (n, th)"
    using assms by (auto simp: eq_assumption_def)
  obtain params asms concl where a: "assum_problems (-1) Bi = (params, asms, concl)"
    by (cases "assum_problems (-1) Bi") auto
  with r obtain k where "find_index_from (\<lambda>asm. aeconv asm concl) asms 0 = Some k"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    by (auto simp: returnW_def raiseW_def split: option.splits)
  with d a show ?thesis by (blast dest: find_index_from_SomeD)
qed

context pure_model
begin

theorem eq_assumption_valid:
  assumes ok: "okT (eq_assumption i state) (n, th)"
    and v: "valid Sh hs (th_tpairs state) (th_prop state)" and w: "wtp (th_prop state)"
  shows "valid Sh hs (th_tpairs th) (th_prop th)"
proof -
  from ok obtain tpairs Bs Bi C params asms concl where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)" and f: "\<exists>a\<in>set asms. aeconv a concl"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs, th_prop = list_implies Bs C\<rparr>"
    using eq_assumption_ok[OF ok] by blast
  note ds = okT_dest_state[OF d]
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF w] P by simp
  note tD = typing_list_impliesD[OF tP]
  have tBi: "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  note st = assum_problems_struct[OF ap tBi]
  have tBi': "(\<lambda>_. propT) \<turnstile> list_forall (rev params) (list_implies asms concl) : propT"
    using tBi st(1) by simp
  have wBs: "wtp (list_implies Bs C)"
  proof (rule wtpI)
    show "closed (list_implies Bs C)" using wtpD(1)[OF w] P by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies Bs C : propT"
      using tD typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  have "valid Sh hs tpairs (list_implies Bs C)"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tpairs \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    note gt = gterm_ap_wtp[OF _ cinstD(2)[OF \<rho>] \<sigma>]
    have "holds (ap \<rho> \<sigma> (list_implies (Bs @ [Bi]) C))"
      using validD[OF v sh g \<rho> \<rho>i \<sigma>] sol hh ds(1) P by simp
    then have h0: "(\<forall>A\<in>set (Bs @ [Bi]). holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) (Bs @ [Bi])" "ap \<rho> \<sigma> C"] gt[OF w] P
      by (simp add: ap_list_implies)
    obtain a where a: "a \<in> set asms" "aeconv a concl" using f by blast
    have "holds (ap \<rho> \<sigma> Bi)"
      using hb_list_forall_taut[OF cinstD(2)[OF \<rho>] \<sigma> bvals0 tBi' a] st(1) by (simp add: holds_hb)
    with h0 have "(\<forall>A\<in>set Bs. holds (ap \<rho> \<sigma> A)) \<longrightarrow> holds (ap \<rho> \<sigma> C)" by simp
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (list_implies Bs C))"
      using holds_list_implies[of "map (ap \<rho> \<sigma>) Bs" "ap \<rho> \<sigma> C"] gt[OF wBs]
      by (simp add: ap_list_implies)
  qed
  then show ?thesis using ds(1) by (simp add: th)
qed


subsection \<open>Instantiation by a unifier of the flex-flex pairs\<close>

text \<open>
  The new theorem of \<open>flexflex_rule\<close> for a unifier \<open>env\<close> (which satisfies the invariants of the
  results of unification) is valid, with the sorts of the type instantiation of \<open>env\<close> as
  additional sort hypotheses.
\<close>

end

context pure_sig
begin

lemma fnewth_ok:
  assumes "ok (fnewth th0 env) th" "\<not> (env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th0). aconv_term t u))"
  obtains ntps P where "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
      (th_tpairs th0) ntps"
    "ok (norm_term env (th_prop th0)) P"
    "th_tpairs th = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop th = P"
proof -
  from assms obtain ntps P where nt: "ok (mapM (norm_tpair env) (th_tpairs th0)) ntps"
    and P: "ok (norm_term env (th_prop th0)) P"
    and th: "th_tpairs th = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop th = P"
    using assms(1) unfolding fnewth_def if_not_P[OF assms(2)] by (auto simp: Let_def)
  have l: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
      (th_tpairs th0) ntps"
    using nt unfolding ok_mapM by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
  show thesis by (rule that[OF l P th])
qed

end

context pure_model
begin

lemma iext_norm_eq_at':
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and g: "good \<eta> \<xi>" and \<sigma>: "gsubst \<sigma>"
    and n: "ok (norm_term env t) t'" and c: "closed t" and ty: "e \<turnstile> inst \<rho>' t : T"
  shows "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho> \<sigma> t')"
proof -
  note i = iextD[OF ie]
  have tyi: "(\<lambda>_. propT) \<turnstile> inst \<rho>' t : T"
    using typing_closed[OF ty] c by (simp add: closed_def)
  note nn = iext_norm_term[OF ie n tyi]
  have c': "closed t'" using nsoundD(2)[OF norm_term_sound[OF n i(5,4)], of 0] c by (simp add: closed_def)
  have g1: "gterm (ap \<rho>' \<sigma>' t) T" by (rule gterm_apI[OF i(2) c tyi])
  have g2: "gterm (ap \<rho> \<sigma> t') T" by (rule gterm_apI[OF \<sigma> c' nn(2)])
  show ?thesis by (rule eq_at_conv[OF g g1 g2 conv_sym[OF nn(1)]])
qed

lemma iext_norm_eq_at:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and g: "good \<eta> \<xi>" and \<sigma>: "gsubst \<sigma>"
    and n: "ok (norm_term env t) t'" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
  shows "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho> \<sigma> t')"
proof -
  have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF iextD(1)[OF ie]])
  show ?thesis by (rule iext_norm_eq_at'[OF ie g \<sigma> n c typing_inst[OF ty cert_inst_inst_ok[OF ci']]])
qed

theorem fnewth_valid:
  assumes ok: "ok (fnewth th0 env) th"
    and v: "valid Sh hs (th_tpairs th0) (th_prop th0)" and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)"
    and ei: "einv A K env" and wi: "winv env X"
  shows "valid (Sh \<union> tyenv_sorts (tyenv env)) hs (th_tpairs th) (th_prop th)"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th0). aconv_term t u)")
  case True
  with ok have "th = th0" by (simp add: fnewth_def)
  with v show ?thesis by (auto intro: valid_mono)
next
  case False
  obtain ntps P where nt: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
      (th_tpairs th0) ntps"
    and nP: "ok (norm_term env (th_prop th0)) P"
    and th: "th_tpairs th = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop th = P"
    by (rule fnewth_ok[OF ok False])
  have wP: "wtp (th_prop th0)" and hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
    and tw: "\<And>t u. (t, u) \<in> set (th_tpairs th0) \<Longrightarrow> closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using wt by (fastforce simp: wt_thm_def)+
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<union> tyenv_sorts (tyenv env) \<Longrightarrow> sinh S"
      and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (th_tpairs th) \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    obtain \<rho>' \<sigma>' \<rho>0 where ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and c0: "cinst \<rho>0"
      and sb: "sbound \<rho>0 (tyenv_sorts (tyenv env))" and eq: "\<And>v S. \<rho>' v S = tsubst \<rho> (\<rho>0 v S)"
      by (rule iext_exists_sb[OF ei wi \<rho> \<sigma>]) blast
    note i = iextD[OF ie]
    have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
    have \<rho>i': "inh_inst \<rho>'"
    proof -
      have "inh_inst (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))"
        by (rule inh_inst_comp[OF \<rho>i c0 inh_inst_sbound[OF sb]]) (use sh in blast)
      moreover have "\<rho>' = (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))" using eq by blast
      ultimately show ?thesis by simp
    qed
    have tyi: "(\<lambda>_. propT) \<turnstile> inst \<rho>' s : tsubst \<rho>' T" if "\<And>e. e \<turnstile> s : T" "closed s" for s T
      using typing_closed[OF typing_inst[OF that(1) cert_inst_inst_ok[OF ci']]] that(2) by (simp add: closed_def)
    have "holds (ap \<rho>' \<sigma>' (th_prop th0))"
    proof (rule validD[OF v _ g i(1) \<rho>i' i(2)])
      show "sinh S" if "S \<in> Sh" for S using sh that by blast
    next
      fix t u assume tu: "(t, u) \<in> set (th_tpairs th0)"
      from list_all2_ex1[OF nt tu] obtain tu' where tu': "tu' \<in> set ntps"
        and n: "ok (norm_term env t) (fst tu')" "ok (norm_term env u) (snd tu')" by auto
      obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
      from tw[OF tu] obtain T where c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
      have e1: "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho> \<sigma> t')"
        by (rule iext_norm_eq_at[OF ie g \<sigma> n(1)[unfolded tu'' fst_conv] c(1) ty(1)])
      have e3: "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' u) (ap \<rho> \<sigma> u')"
        by (rule iext_norm_eq_at[OF ie g \<sigma> n(2)[unfolded tu'' snd_conv] c(2) ty(2)])
      have e2: "eq_at \<eta> \<xi> (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')"
      proof (cases "aconv_term t' u'")
        case True
        then have "aconv_term (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')" by (rule aconv_term_ap)
        then show ?thesis by (simp add: eq_at_def sem_aconv)
      next
        case False
        with tu' tu'' th(1) show ?thesis by (intro sol) auto
      qed
      from e1 e2 e3 show "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)" by (meson eq_at_sym eq_at_trans)
    next
      fix h assume h: "h \<in> set hs"
      have "unb env h" using hv[OF h] by (simp add: unb_def)
      with iext_unb[OF ie] hh[OF h] show "holds (ap \<rho>' \<sigma>' h)" by simp
    qed
    moreover have tP: "(\<lambda>_. propT) \<turnstile> inst \<rho>' (th_prop th0) : propT"
      using tyi[of "th_prop th0" propT] wtpD[OF wP] by (simp add: tsubst_propT)
    note n = iext_norm_term[OF ie nP tP]
    have "closed P"
      using nsoundD(2)[OF norm_term_sound[OF nP i(5,4)], of 0] wtpD(1)[OF wP] by (simp add: closed_def)
    then have "gterm (ap \<rho> \<sigma> P) propT" using gterm_apI[OF \<sigma> _ n(2)] by blast
    moreover have "gterm (ap \<rho>' \<sigma>' (th_prop th0)) propT" by (rule gterm_ap_wtp[OF wP ci' i(2)])
    ultimately show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (th_prop th))"
      using holds_conv conv_sym[OF n(1)] th(2) by blast
  qed
qed


subsection \<open>Proof by assumption\<close>

text \<open>
  A result of \<open>assumption i state\<close> for a unifier \<open>env\<close> of an assumption \<open>asm\<close> of subgoal \<open>i\<close> with
  its conclusion is valid, if every solution of the unifier and its flex-flex pairs solves the
  problem (as \<open>ures_solves\<close> shows for the unifiers of \<open>Unify.unifiers\<close>).
\<close>

theorem assumption_result_valid:
  assumes d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)" and asm: "asm \<in> set asms"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) n (env, tps)) r"
    and v: "valid Sh hs (th_tpairs state) (th_prop state)" and wt: "wt_thm m hs (th_tpairs state) (th_prop state)"
    and ei: "einv A K env" and wi: "winv env X"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
    and solves: "\<And>\<rho>' \<sigma>' \<eta> \<xi>. solution \<rho>' \<sigma>' env \<Longrightarrow> cert_inst \<rho>' \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow>
      (\<forall>(t, u)\<in>set tps. eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)) \<Longrightarrow>
      \<forall>(t, u)\<in>set ((rlist_abs params asm, rlist_abs params concl) # tpairs). eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
  shows "valid (Sh \<union> tyenv_sorts (tyenv env)) hs (th_tpairs (ar_thm r)) (th_prop (ar_thm r))"
proof -
  let ?ctx = "ACtx (th_maxidx state) tpairs Bs Bi C params concl"
  note ds = okT_dest_state[OF d]
  have wS: "wtp (th_prop state)" and hv: "\<And>h. h \<in> set hs \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
    using wt by (fastforce simp: wt_thm_def)+
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF wS, of "\<lambda>_. propT"]] by simp
  have tP: "(\<lambda>_. propT) \<turnstile> list_implies (Bs @ [Bi]) C : propT" using wtpD(2)[OF wS] P by simp
  note tD = typing_list_impliesD[OF tP]
  have cBi: "closed Bi" using wtpD(1)[OF wS] P by (simp add: closed_def loose_bvar_list_implies)
  have wBs: "wtp (list_implies Bs C)"
  proof (rule wtpI)
    show "closed (list_implies Bs C)" using wtpD(1)[OF wS] P by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies Bs C : propT"
      using tD typing_list_implies_imp[OF tP] by (intro typing_list_impliesI) auto
  qed
  \<comment> \<open>the new theorem: its flex-flex pairs and proposition are related to those of the unifier\<close>
  obtain ntps P' where r: "ar_thm r = \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P'\<rparr>"
    and rel: "env_is_empty env \<and> ntps = tps \<and> P' = list_implies Bs C \<or>
      list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps \<and>
      ok (norm_term env (list_implies Bs C)) P'"
  proof (cases "env_is_empty env")
    case True
    with nt show thesis by (intro that[of tps "list_implies Bs C"]) (auto simp: newth_def returnW_def)
  next
    case False
    with nt obtain ntps P' where n: "ok (mapM (norm_tpair env) tps) ntps" "ok (norm_term env (list_implies Bs C)) P'"
      and r: "ar_thm r = \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P'\<rparr>"
      by (auto simp: newth_def)
    have "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
      using n(1) unfolding ok_mapM by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
    with r n(2) show thesis by (intro that[of ntps P']) auto
  qed
  show ?thesis unfolding r
  proof (rule validI, unfold thm_rep.simps)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<union> tyenv_sorts (tyenv env) \<Longrightarrow> sinh S"
      and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set ntps \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    obtain \<rho>' \<sigma>' \<rho>0 where ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and c0: "cinst \<rho>0"
      and sb: "sbound \<rho>0 (tyenv_sorts (tyenv env))" and eq: "\<And>v S. \<rho>' v S = tsubst \<rho> (\<rho>0 v S)"
      by (rule iext_exists_sb[OF ei wi \<rho> \<sigma>]) blast
    note i = iextD[OF ie]
    have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
    have \<rho>i': "inh_inst \<rho>'"
    proof -
      have "inh_inst (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))"
        by (rule inh_inst_comp[OF \<rho>i c0 inh_inst_sbound[OF sb]]) (use sh in blast)
      moreover have "\<rho>' = (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))" using eq by blast
      ultimately show ?thesis by simp
    qed
    have tyi: "(\<lambda>_. propT) \<turnstile> inst \<rho>' s : tsubst \<rho>' T" if "\<And>e. e \<turnstile> s : T" "closed s" for s T
      using typing_closed[OF typing_inst[OF that(1) cert_inst_inst_ok[OF ci']]] that(2) by (simp add: closed_def)
    \<comment> \<open>the flex-flex pairs of the unifier are solved at the extension\<close>
    have stps: "\<forall>(t, u)\<in>set tps. eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set tps"
      from tw tu i(5) ci' obtain e0 T where c: "closed t" "closed u"
        and ty: "e0 \<turnstile> inst \<rho>' t : T" "e0 \<turnstile> inst \<rho>' u : T" by blast
      from rel show "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      proof (elim disjE conjE)
        assume e: "env_is_empty env" "ntps = tps"
        have "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" for s by (rule iext_unb[OF ie unb_empty[OF e(1)]])
        with sol[of t u] tu e(2) show ?thesis by simp
      next
        assume l: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
        from list_all2_ex1[OF l tu] obtain tu' where tu': "tu' \<in> set ntps"
          and n: "ok (norm_term env t) (fst tu')" "ok (norm_term env u) (snd tu')" by auto
        obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
        have e1: "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho> \<sigma> t')"
          by (rule iext_norm_eq_at'[OF ie g \<sigma> n(1)[unfolded tu'' fst_conv] c(1) ty(1)])
        have e3: "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' u) (ap \<rho> \<sigma> u')"
          by (rule iext_norm_eq_at'[OF ie g \<sigma> n(2)[unfolded tu'' snd_conv] c(2) ty(2)])
        have e2: "eq_at \<eta> \<xi> (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')" using sol tu' tu'' by blast
        from e1 e2 e3 show ?thesis by (meson eq_at_sym eq_at_trans)
      qed
    qed
    note sv = solves[OF i(3) ci' g stps]
    have hS: "holds (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
    proof (rule validD[OF v _ g i(1) \<rho>i' i(2), unfolded P])
      show "sinh S" if "S \<in> Sh" for S using sh that by blast
      show "eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)" if "(t, u) \<in> set (th_tpairs state)" for t u
        using sv that ds(1) by auto
      show "holds (ap \<rho>' \<sigma>' h)" if h: "h \<in> set hs" for h
      proof -
        have "unb env h" using hv[OF h] by (simp add: unb_def)
        with iext_unb[OF ie] hh[OF h] show ?thesis by simp
      qed
    qed
    have hBi: "holds (ap \<rho>' \<sigma>' Bi)"
      by (rule eres_holds[OF ap asm _ ci' i(2) _ cBi]) (use sv tD in \<open>auto simp: eq_at_def\<close>)
    note gt = gterm_ap_wtp[OF _ ci' i(2)]
    have "(\<forall>A\<in>set (Bs @ [Bi]). holds (ap \<rho>' \<sigma>' A)) \<longrightarrow> holds (ap \<rho>' \<sigma>' C)"
      using hS holds_list_implies[of "map (ap \<rho>' \<sigma>') (Bs @ [Bi])" "ap \<rho>' \<sigma>' C"] gt[OF wS] P
      by (simp add: ap_list_implies)
    with hBi have "(\<forall>A\<in>set Bs. holds (ap \<rho>' \<sigma>' A)) \<longrightarrow> holds (ap \<rho>' \<sigma>' C)" by simp
    then have h': "holds (ap \<rho>' \<sigma>' (list_implies Bs C))"
      using holds_list_implies[of "map (ap \<rho>' \<sigma>') Bs" "ap \<rho>' \<sigma>' C"] gt[OF wBs]
      by (simp add: ap_list_implies)
    from rel show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> P')"
    proof (elim disjE conjE)
      assume e: "env_is_empty env" "P' = list_implies Bs C"
      with h' iext_unb[OF ie unb_empty[OF e(1)]] show ?thesis by simp
    next
      assume nP: "ok (norm_term env (list_implies Bs C)) P'"
      have tP': "(\<lambda>_. propT) \<turnstile> inst \<rho>' (list_implies Bs C) : propT"
        using tyi[of "list_implies Bs C" propT] wtpD[OF wBs] by (simp add: tsubst_propT)
      note n = iext_norm_term[OF ie nP tP']
      have "closed P'"
        using nsoundD(2)[OF norm_term_sound[OF nP i(5,4)], of 0] wtpD(1)[OF wBs] by (simp add: closed_def)
      then have "gterm (ap \<rho> \<sigma> P') propT" using gterm_apI[OF \<sigma> _ n(2)] by blast
      with h' gt[OF wBs] show ?thesis using holds_conv conv_sym[OF n(1)] by blast
    qed
  qed
qed

end

end
