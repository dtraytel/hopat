section \<open>Finiteness of the Search\<close>

theory Unify_Pull_Fin
  imports Unify_Mc_Fin Unify_Ffeta Unify_Pull_Sound
begin

text \<open>
  The search of \<^const>\<open>hounifiers\<close> terminates without an exception, after finitely many
  unifiers: the depth of the search is bounded by \<^const>\<open>cfg_search_bound\<close>, each node simplifies
  its problem (\<^const>\<open>SIMPL\<close>, theorem @{thm [source] pure_sig_gen.SIMPL_term}) and enumerates finitely
  many new problems by \<^const>\<open>MATCH\<close> (theorem @{thm [source] pure_sig_gen.MATCH_fin}). A leaf
  without flex-rigid pairs returns a unifier after the treatment of its flex-flex pairs by
  \<^const>\<open>add_ffpair\<close>, which raises no exception on the flex-flex pairs of \<^const>\<open>SIMPL\<close>
  (theorem @{thm [source] pure_sig_gen.SIMPL_add_ffpair_ok}).

  The same induction gives the soundness of the search: the invariant gives the hypothesis of
  \<^const>\<open>MATCH\<close> (theorem \<open>sinv_MATCH_ok\<close> below), whose new problems are then steps
  from the problem of the node (theorem @{thm [source] pure_sig_gen.MATCH_sound}).
\<close>

context pure_sig_gen
begin

text \<open>The unifiers: the results of \<^const>\<open>add_ffpair\<close> on the flex-flex pairs of a simplified problem,
  with the type variables \<open>A0\<close> of the original problem \<open>env0\<close> among the known ones, and only type
  variables that are known in the original problem or new (\<^const>\<open>tnew\<close>).\<close>

definition rres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> elem \<Rightarrow> bool" where
  "rres A0 env0 x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> (\<exists>A K X env ffs. finite X \<and> finite K \<and> A0 \<subseteq> A \<and>
    tnew A0 env0 A env \<and>
    sinv A K X env ffs \<and> (\<forall>dp\<in>set ffs. ff_shape env dp) \<and> okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps) \<and>
    finv A K env env' \<and> (\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    (\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u)))"

text \<open>
  The hypothesis of \<^const>\<open>MATCH\<close> holds for flex-rigid pairs in the invariant: the types of the
  two sides are equal modulo the type environment.
\<close>

lemma sinv_MATCH_ok:
  assumes sh: "frs_shape (rb, t, u)" and si: "sinv A K X env ((rb, t, u) # dps)"
  shows "MATCH_ok env (rb, t, u)"
proof -
  have ei: "einv A K env" and p: "upok A env rb X t u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei]
  from fastype_pair_term[OF ei p] obtain T1 U1 where
    ty: "fastype env rb t = return T1" "fastype env rb u = return U1"
      "tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A" "tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) T1 = tnorm (tyenv env) U1"
    by blast
  have "tspine (tyenv env) T1 U1"
    by (rule tspine_tnorm[OF e(6,7) tinv_tcons[OF e(2) ty(3)] tinv_tcons[OF e(2) ty(4)] ty(5)])
  with ty(1,2) show ?thesis by (intro frs_shape_MATCH_ok[OF sh]) (simp_all add: return_def)
qed

lemma fin_ev_conj: "fin cfg s P \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> Q x) \<Longrightarrow> fin cfg s (\<lambda>x. P x \<and> Q x)"
  unfolding fin_def using evals_ev_set by blast

lemma fin_Cons:
  assumes "resW (pull cfg s) (Ok (Some (x, s')))" "Q x" "fin cfg s' Q"
  shows "fin cfg s Q"
proof -
  from assms(3) obtain xs where xs: "evals cfg s' xs" "\<forall>y\<in>set xs. Q y" by (auto simp: fin_def)
  from assms(1) obtain evs where "pull cfg s = Some (evs, Ok (Some (x, s')))" by (auto simp: resW_def)
  from evals.Cons[OF this xs(1)] xs(2) assms(2) show ?thesis
    unfolding fin_def by (intro exI[of _ "x # xs"]) simp
qed

lemma resW_handleW_bindW_ok: "okW m x \<Longrightarrow> resW (handleW (bindW m f) h) r \<longleftrightarrow> resW (handleW (f x) h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_bindW_ok)

lemma resW_handleW_whenW: "resW (handleW (bindW (whenW b (emit e)) (\<lambda>_. m)) h) r \<longleftrightarrow> resW (handleW m h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_whenW_emit)

lemma resW_handleW_emit: "resW (handleW (bindW (emit e) (\<lambda>_. m)) h) r \<longleftrightarrow> resW (handleW m h) r"
  by (rule resW_cong_handleW) (simp_all add: resW_emit)

lemma resW_handleW_bindW_err:
  assumes "m = Some (evs, Err e)"
  shows "resW (handleW (bindW m f) h) r \<longleftrightarrow> resW (h e) r"
proof -
  have "bindW m f = Some (evs, Err e)" using assms by (simp add: bindW_def)
  then show ?thesis by (rule resW_handleW_err)
qed

lemma lfin_ev_conj:
  assumes "lfin cfg s P" "\<And>x. ev cfg s x \<Longrightarrow> Q x"
  shows "lfin cfg s (\<lambda>x. P x \<and> Q x)"
proof (cases "loose = {}")
  case True
  show ?thesis unfolding lfin_strict[OF True]
    by (rule fin_ev_conj[OF assms(1)[unfolded lfin_strict[OF True]] assms(2)])
next
  case False
  show ?thesis by (rule lfin_looseI[OF False]) (use lfin_D[OF assms(1)] assms(2) in blast)
qed

lemma lfin_mono_nf:
  assumes "lfin cfg s P" "\<And>x. nfree (eenv x) \<Longrightarrow> P x \<Longrightarrow> Q x"
  shows "lfin cfg s Q"
proof (cases "loose = {}")
  case True
  show ?thesis by (rule lfin_mono[OF assms(1)]) (rule assms(2)[OF nfree_strict[OF True]])
next
  case False
  show ?thesis by (rule lfin_looseI[OF False]) (use lfin_D[OF assms(1)] assms(2) in blast)
qed

text \<open>
  A node of the search: the simplified problem either has no flex-rigid pair, and the treatment of
  its flex-flex pairs gives a unifier, or the assignments of \<^const>\<open>MATCH\<close> to its first flex-rigid
  pair continue the search. Without loose names this is the evaluation of the node by
  \<^const>\<open>pull\<close>; with loose names it is a statement on the elements whose environment binds no
  loose name, and such an element comes from a simplified problem whose environment binds none.
\<close>

lemma lfin_AddUnify:
  assumes fR: "lfin cfg R Q"
    and S: "lcuok fst (SIMPL (cfg_alg cfg) env dps) P"
    and N: "\<And>env' ffs. okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, []) \<Longrightarrow> P (env', ffs, []) \<Longrightarrow> nfree env' \<Longrightarrow>
      lxokE (\<lambda>_. False) fst (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) (\<lambda>r. Q (El_R (fst r) (snd r)))"
    and C: "\<And>env' ffs dp frs'. okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs') \<Longrightarrow>
      P (env', ffs, dp # frs') \<Longrightarrow> nfree env' \<Longrightarrow> \<not> td > cfg_search_bound cfg \<Longrightarrow>
      lxokS (\<lambda>e. e = CANTUNIFY) (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. lfin cfg (S_ItRight (td + 1) ms R) Q)"
  shows "lfin cfg (S_AddUnify td env dps R) Q"
proof (cases "loose = {}")
  case True
  note LS = lxokE_strict[OF True] and LF = lfin_strict[OF True] and nfs = nfree_strict[OF True]
  have fR': "fin cfg R Q" using fR by (simp add: LF)
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have eq: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow>
      resW (handleW (bindW (SIMPL (cfg_alg cfg) env dps) (au_cont cfg td R)) ?h) r" for r
    by (rule resW_pull_AddUnify)
  from S[unfolded LS] consider (cu) evs where "SIMPL (cfg_alg cfg) env dps = Some (evs, Err CANTUNIFY)"
    | (ok) st where "okW (SIMPL (cfg_alg cfg) env dps) st" "P st"
    by blast
  then have "fin cfg (S_AddUnify td env dps R) Q"
  proof cases
    case cu
    have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
      unfolding eq resW_handleW_bindW_err[OF cu] by simp
    from fin_res[OF this fR'] show ?thesis .
  next
    case (ok st)
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    have eq1: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?h) r" for r
      unfolding eq resW_handleW_bindW_ok[OF ok(1)] ..
    show ?thesis
    proof (cases frs)
      case Nil
      from N[OF ok(1)[unfolded st Nil] ok(2)[unfolded st Nil] nfs, unfolded LS]
      obtain r0 where r0: "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r0"
        and Qr: "Q (El_R (fst r0) (snd r0))" by blast
      have ok2: "okW (au_cont cfg td R st) (Some (El_R (fst r0) (snd r0), R))"
        unfolding st Nil au_cont_def using r0 by auto
      have r1: "resW (pull cfg (S_AddUnify td env dps R)) (Ok (Some (El_R (fst r0) (snd r0), R)))"
        unfolding eq1 resW_handleW_ok[OF ok2] by simp
      from fin_Cons[OF r1 Qr fR'] show ?thesis .
    next
      case (Cons dp frs')
      show ?thesis
      proof (cases "td > cfg_search_bound cfg")
        case True
        have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
          unfolding eq1 st Cons au_cont_def using True
          by (simp add: resW_handleW_emit resW_handleW_fin[OF _ fR'])
        from fin_res[OF this fR'] show ?thesis .
      next
        case False
        let ?m = "bindW (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. pull cfg (S_ItRight (td + 1) ms R))"
        have eq2: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW ?m ?h) r" for r
          unfolding eq1 st Cons au_cont_def using False by (simp add: resW_handleW_whenW)
        from C[OF ok(1)[unfolded st Cons] ok(2)[unfolded st Cons] nfs False, unfolded LS LF]
        consider (cu) evs where "MATCH cfg env' dp (frs' @ ffs) = Some (evs, Err CANTUNIFY)"
          | (ok) ms where "okW (MATCH cfg env' dp (frs' @ ffs)) ms" "fin cfg (S_ItRight (td + 1) ms R) Q"
          by blast
        then show ?thesis
        proof cases
          case cu
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
            unfolding eq2 resW_handleW_bindW_err[OF cu] by simp
          from fin_res[OF this fR'] show ?thesis .
        next
          case (ok ms)
          note fI = ok(2)
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            unfolding eq2 by (rule resW_handleW_fin[OF _ fI]) (simp add: resW_bindW_ok[OF ok(1)])
          from fin_res[OF this fI] show ?thesis .
        qed
      qed
    qed
  qed
  then show ?thesis by (simp add: LF)
next
  case False
  show ?thesis
  proof (rule lfin_looseI[OF False])
    fix x assume ev: "ev cfg (S_AddUnify td env dps R) x" and nf: "nfree (eenv x)"
    from ev consider (tl) "ev cfg R x"
      | (res) env' ffs r where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, [])"
          "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r" "x = El_R (fst r) (snd r)"
      | (mt) env' ffs dp frs ms where "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
          "\<not> td > cfg_search_bound cfg" "okW (MATCH cfg env' dp (frs @ ffs)) ms"
          "ev cfg (S_ItRight (td + 1) ms R) x"
      by (rule ev_AddUnifyE) blast+
    then show "Q x"
    proof cases
      case tl
      from lfin_D[OF fR tl nf] show ?thesis .
    next
      case res
      obtain e1 tps where r: "r = (e1, tps)" by (cases r)
      have nf1: "nfree e1" using nf res(3) r by simp
      have "extends env' e1" using dstepD(1)[OF foldrW_add_ffpair_sound[OF res(2)[unfolded r]]] .
      then have nf': "nfree env'" using nf1 by (rule nfree_extends)
      have P: "P (env', ffs, [])" using lxokE_D[OF S res(1)] nf' by simp
      from lxokE_D[OF N[OF res(1) P nf'] res(2)] nf1 r show ?thesis unfolding res(3) by simp
    next
      case mt
      from mt(4) consider (tl) "ev cfg R x"
        | (hd) env2 dps2 where "ev cfg ms (El_E env2 dps2)" "\<And>R'. ev cfg (S_AddUnify (td + 1) env2 dps2 R') x"
        by (auto elim!: ev_ItRightE)
      then show ?thesis
      proof cases
        case tl
        from lfin_D[OF fR tl nf] show ?thesis .
      next
        case hd
        have "sext env2 (S_AddUnify (td + 1) env2 dps2 S_Empty)" by (auto intro: sext.intros extends_refl)
        from ev_nfree[OF hd(2)[of S_Empty] this nf] have nf2: "nfree env2" .
        have "extends env' env2" using ev_sext[OF hd(1) MATCH_sext[OF mt(3)]] by simp
        then have nf': "nfree env'" using nf2 by (rule nfree_extends)
        have P: "P (env', ffs, dp # frs)" using lxokE_D[OF S mt(1)] nf' by simp
        from lxokE_D[OF C[OF mt(1) P nf' mt(2)] mt(3)]
        have "lfin cfg (S_ItRight (td + 1) ms R) Q" by simp
        from lfin_D[OF this mt(4) nf] show ?thesis .
      qed
    qed
  qed
qed

text \<open>
  A node of the search at depth \<open>td\<close>, followed by a finite enumeration, for a problem that is a
  step from the problem \<open>dps0\<close> of the root:
\<close>

lemma au_fin:
  assumes cfg: "cfg_alg cfg = alg"
  shows "nat (int_of_integer (cfg_search_bound cfg + 1 - td)) = n \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow>
    sinv A K X env dps \<Longrightarrow> A0 \<subseteq> A \<Longrightarrow> tnew A0 env0 A env \<Longrightarrow> dstep env0 dps0 env dps \<Longrightarrow> nfree env \<Longrightarrow>
    lfin cfg R (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x) \<Longrightarrow>
    lfin cfg (S_AddUnify td env dps R) (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x)"
proof (induction n arbitrary: td A K X env dps R rule: less_induct)
  case (less n)
  note fin = less.prems(2,3) and si = less.prems(4) and A0 = less.prems(5) and tn0 = less.prems(6)
    and d0 = less.prems(7) and nf = less.prems(8) and fR = less.prems(9)
  let ?Q = "\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x"
  have post: "sinv A K X env' (frs @ ffs)" "\<forall>dp\<in>set ffs. ff_shape env' dp" "\<forall>dp\<in>set frs. fr_shape env' dp"
    "dstep env0 dps0 env' (frs @ ffs)" "maxidx env0 \<le> maxidx env'" "tnew A0 env0 A env'"
    if ok: "okW (SIMPL alg env dps) (env', ffs, frs)" and sp: "simpl_post A K X env (env', ffs, frs)"
    for env' ffs frs
  proof -
    from sp show si': "sinv A K X env' (frs @ ffs)" and "\<forall>dp\<in>set ffs. ff_shape env' dp"
      and "\<forall>dp\<in>set frs. fr_shape env' dp" by (auto simp: simpl_post_def)
    from sp have ss: "sstep A K X env env'" by (auto simp: simpl_post_def)
    show d1: "dstep env0 dps0 env' (frs @ ffs)" by (rule dstep_trans[OF d0 SIMPL_sound[OF ok]])
    show "maxidx env0 \<le> maxidx env'" by (rule extends_maxidx[OF dstepD(1)[OF d1]])
    have "tnew A env A env'" using ss by (simp add: sstep_def)
    then show "tnew A0 env0 A env'" by (rule tnew_trans[OF tn0 _ extends_maxidx[OF dstepD(1)[OF d0]]])
  qed
  show ?case
  proof (rule lfin_AddUnify[where cfg = cfg, unfolded cfg, OF fR SIMPL_term[OF fin si nf]])
    fix env' ffs
    assume ok: "okW (SIMPL alg env dps) (env', ffs, [])" and sp: "simpl_post A K X env (env', ffs, [])"
      and nf': "nfree env'"
    note p = post[OF ok sp]
    have siff: "sinv A K X env' ffs" using p(1) by simp
    show "lxokE (\<lambda>_. False) fst (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. ?Q (El_R (fst r) (snd r)))"
    proof (rule lxokE_mono_ok[OF SIMPL_add_ffpair_ok[OF fin si ok nf']])
      fix r assume r0': "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        and pr: "case r of (env'', tps) \<Rightarrow> finv A K env' env'' \<and>
          (\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env') \<union> A) \<and>
          (\<forall>(t, u)\<in>set tps. flexb env' t \<and> flexb env' u)"
      obtain e1 tps where r: "r = (e1, tps)" by (cases r)
      note r0 = r0'[unfolded r]
      from pr r have fv: "finv A K env' e1"
        and tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env') \<union> A"
        and fl: "\<forall>(t, u)\<in>set tps. flexb env' t \<and> flexb env' u" by auto
      have "rres A0 env0 (El_R e1 tps)"
        unfolding rres_def using fin A0 p(6) siff p(2) r0 fv tk fl by blast
      moreover have "elem_ok (GR env0 dps0) (El_R e1 tps)"
        using dstep_trans[OF p(4)[unfolded append_Nil] foldrW_add_ffpair_sound[OF r0, unfolded list.map append_Nil2]]
        by simp
      ultimately show "?Q (El_R (fst r) (snd r))" by (simp add: r)
    qed
  next
    fix env' ffs dp frs'
    assume ok: "okW (SIMPL alg env dps) (env', ffs, dp # frs')"
      and sp: "simpl_post A K X env (env', ffs, dp # frs')" and nf': "nfree env'"
      and False: "\<not> td > cfg_search_bound cfg"
    note p = post[OF ok sp]
    have siM: "sinv A K X env' (dp # (frs' @ ffs))" using p(1) by simp
    have frM: "fr_shape env' dp" using p(3) by simp
    have mo: "MATCH_ok env' dp"
    proof -
      obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
      have "frs_shape dp" by (rule SIMPL_frs_shape[OF ok])
      from sinv_MATCH_ok[OF this[unfolded dp] siM[unfolded dp]] show ?thesis by (simp add: dp)
    qed
    show "lxokS (\<lambda>e. e = CANTUNIFY) (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. lfin cfg (S_ItRight (td + 1) ms R) ?Q)"
    proof (rule lxokE_mono_ok[OF MATCH_fin[OF cfg fin siM frM mo nf']])
      fix ms assume okm: "okW (MATCH cfg env' dp (frs' @ ffs)) ms" and fm: "lfin cfg ms (mres A env')"
      have lt: "nat (int_of_integer (cfg_search_bound cfg + 1 - (td + 1))) < n"
        using depth_measure[OF False] less.prems(1) by simp
      have sq: "seqinv (GE env' (dp # frs' @ ffs)) ms" by (rule MATCH_sound[OF okm mo])
      have fM: "lfin cfg ms (\<lambda>x. mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x)"
        by (rule lfin_ev_conj[OF fm ev_sound[OF _ sq]])
      have IH: "lfin cfg (S_AddUnify (td + 1) env2 dps2 R2) ?Q"
        if "mres A env' (El_E env2 dps2)" "elem_ok (GE env' (dp # frs' @ ffs)) (El_E env2 dps2)"
          "lfin cfg R2 ?Q" "nfree env2" for env2 dps2 R2
      proof -
        from that(1) obtain A2 K2 X2 where "finite X2" "finite K2" "sinv A2 K2 X2 env2 dps2" "A \<subseteq> A2"
          and tn2: "tnew A env' A2 env2"
          by (auto simp: mres_def)
        moreover have "tnew A0 env0 A2 env2" by (rule tnew_trans[OF p(6) tn2 p(5)])
        moreover have "dstep env0 dps0 env2 dps2" using dstep_trans[OF p(4)] that(2) by simp
        ultimately show ?thesis using less.IH[OF lt refl, of X2 K2 A2 env2 dps2 R2] that(3,4) A0 by blast
      qed
      show "lfin cfg (S_ItRight (td + 1) ms R) ?Q"
      proof (rule lfin_ItRight[OF _ fR])
        show "lfin cfg ms (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
            (\<forall>R. lfin cfg R ?Q \<longrightarrow> lfin cfg (S_AddUnify (td + 1) env dps R) ?Q))"
        proof (rule lfin_mono_nf[OF fM])
          fix x assume nfx: "nfree (eenv x)" and x: "mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x"
          then obtain env2 dps2 where x2: "x = El_E env2 dps2" by (auto simp: mres_def)
          with x nfx IH[of env2 dps2] show "\<exists>env dps. x = El_E env dps \<and>
              (\<forall>R. lfin cfg R ?Q \<longrightarrow> lfin cfg (S_AddUnify (td + 1) env dps R) ?Q)" by auto
        qed
      qed
    qed
  qed
qed

text \<open>
  The search terminates with finitely many unifiers, each of which is a step from the input pairs
  to its flex-flex pairs. With loose names, this holds for the unifiers whose environment binds no
  loose name.
\<close>

theorem hounifiers_fin_sound:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "lfin cfg (hounifiers rb env tus) (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
  unfolding hounifiers_def
proof (rule lfin_nfree[where ?e0.0 = env])
  assume nf: "nfree env"
  show "lfin cfg (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) S_Empty)
      (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
    by (rule au_fin[OF assms(1) refl assms(2-4) order_refl tnew_refl dstep_refl nf lfin_Empty])
next
  show "sext env (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) S_Empty)"
    by (auto intro: sext.intros extends_refl)
qed

theorem hounifiers_fin:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "lfin cfg (hounifiers rb env tus) (rres A env)"
  by (rule lfin_mono[OF hounifiers_fin_sound[OF assms]]) simp

end

text \<open>Without loose names:\<close>

context pure_sig
begin

theorem hounifiers_fin_sound:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
  using hounifiers_fin_sound[OF assms] by (simp add: lfin_strict)

theorem hounifiers_fin:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (rres A env)"
  using hounifiers_fin[OF assms] by (simp add: lfin_strict)

end

end
