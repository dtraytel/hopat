section \<open>Finiteness of the Search\<close>

theory Unify_Pull_Fin
  imports Unify_Mc_Fin Unify_Ffeta Unify_Pull_Sound
begin

text \<open>
  The search of \<^const>\<open>hounifiers\<close> terminates without an exception, after finitely many
  unifiers: the depth of the search is bounded by \<^const>\<open>cfg_search_bound\<close>, each node simplifies
  its problem (\<^const>\<open>SIMPL\<close>, theorem @{thm [source] pure_sig.SIMPL_term}) and enumerates finitely
  many new problems by \<^const>\<open>MATCH\<close> (theorem @{thm [source] pure_sig.MATCH_fin}). A leaf
  without flex-rigid pairs returns a unifier after the treatment of its flex-flex pairs by
  \<^const>\<open>add_ffpair\<close>, which raises no exception on the flex-flex pairs of \<^const>\<open>SIMPL\<close>
  (theorem @{thm [source] pure_sig.SIMPL_add_ffpair_ok}).

  The same induction gives the soundness of the search: the invariant gives the hypothesis of
  \<^const>\<open>MATCH\<close> (theorem \<open>sinv_MATCH_ok\<close> below), whose new problems are then steps
  from the problem of the node (theorem @{thm [source] pure_sig.MATCH_sound}).
\<close>

context pure_sig
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
  assumes "resW (pull cfg s) (UOk (Some (x, s')))" "Q x" "fin cfg s' Q"
  shows "fin cfg s Q"
proof -
  from assms(3) obtain xs where xs: "evals cfg s' xs" "\<forall>y\<in>set xs. Q y" by (auto simp: fin_def)
  from assms(1) obtain evs where "pull cfg s = Some (evs, UOk (Some (x, s')))" by (auto simp: resW_def)
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
  assumes "m = Some (evs, UErr e)"
  shows "resW (handleW (bindW m f) h) r \<longleftrightarrow> resW (h e) r"
proof -
  have "bindW m f = Some (evs, UErr e)" using assms by (simp add: bindW_def)
  then show ?thesis by (rule resW_handleW_err)
qed

text \<open>
  A node of the search at depth \<open>td\<close>, followed by a finite enumeration, for a problem that is a
  step from the problem \<open>dps0\<close> of the root:
\<close>

lemma au_fin:
  assumes cfg: "cfg_alg cfg = alg"
  shows "nat (int_of_integer (cfg_search_bound cfg + 1 - td)) = n \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow>
    sinv A K X env dps \<Longrightarrow> A0 \<subseteq> A \<Longrightarrow> tnew A0 env0 A env \<Longrightarrow> dstep env0 dps0 env dps \<Longrightarrow>
    fin cfg R (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x) \<Longrightarrow>
    fin cfg (S_AddUnify td env dps R) (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x)"
proof (induction n arbitrary: td A K X env dps R rule: less_induct)
  case (less n)
  note fin = less.prems(2,3) and si = less.prems(4) and A0 = less.prems(5) and tn0 = less.prems(6)
    and d0 = less.prems(7) and fR = less.prems(8)
  let ?Q = "\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x"
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have eq: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow>
      resW (handleW (bindW (SIMPL alg env dps) (au_cont cfg td R)) ?h) r" for r
    using resW_pull_AddUnify[of cfg td env dps R r] by (simp add: cfg)
  from SIMPL_term[OF fin si] consider (cu) evs where "SIMPL alg env dps = Some (evs, UErr CANTUNIFY)"
    | (ok) st where "okW (SIMPL alg env dps) st" "simpl_post A K X env st"
    unfolding xokW_def by blast
  then show ?case
  proof cases
    case cu
    have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
      unfolding eq resW_handleW_bindW_err[OF cu] by simp
    from fin_res[OF this fR] show ?thesis .
  next
    case (ok st)
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    from ok(2) st have si': "sinv A K X env' (frs @ ffs)" and ff: "\<forall>dp\<in>set ffs. ff_shape env' dp"
      and fr: "\<forall>dp\<in>set frs. fr_shape env' dp" and ss: "sstep A K X env env'"
      by (auto simp: simpl_post_def)
    have d1: "dstep env0 dps0 env' (frs @ ffs)"
      by (rule dstep_trans[OF d0 SIMPL_sound[OF ok(1)[unfolded st]]])
    have mx1: "maxidx env0 \<le> maxidx env'" by (rule extends_maxidx[OF dstepD(1)[OF d1]])
    have "tnew A env A env'" using ss by (simp add: sstep_def)
    then have tn1: "tnew A0 env0 A env'" by (rule tnew_trans[OF tn0 _ extends_maxidx[OF dstepD(1)[OF d0]]])
    have eq1: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?h) r" for r
      unfolding eq resW_handleW_bindW_ok[OF ok(1)] ..
    show ?thesis
    proof (cases frs)
      case Nil
      have siff: "sinv A K X env' ffs" using si' Nil by simp
      from SIMPL_add_ffpair_ok[OF fin si ok(1)[unfolded st Nil]] obtain e1 tps where
        r0: "okW (foldrW (add_ffpair alg) ffs (env', [])) (e1, tps)" and fv: "finv A K env' e1"
        and tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env') \<union> A"
        and fl: "\<forall>(t, u)\<in>set tps. flexb env' t \<and> flexb env' u" by blast
      have ok2: "okW (au_cont cfg td R st) (Some (El_R e1 tps, R))"
        unfolding st Nil au_cont_def using r0 by (auto simp: cfg)
      have r1: "resW (pull cfg (S_AddUnify td env dps R)) (UOk (Some (El_R e1 tps, R)))"
        unfolding eq1 resW_handleW_ok[OF ok2] by simp
      have "rres A0 env0 (El_R e1 tps)"
        unfolding rres_def using fin A0 tn1 siff ff r0 fv tk fl by blast
      moreover have "elem_ok (GR env0 dps0) (El_R e1 tps)"
        using dstep_trans[OF d1[unfolded Nil append_Nil] foldrW_add_ffpair_sound[OF r0, unfolded list.map append_Nil2]]
        by simp
      ultimately have "?Q (El_R e1 tps)" by simp
      from fin_Cons[OF r1 this fR] show ?thesis .
    next
      case (Cons dp frs')
      show ?thesis
      proof (cases "td > cfg_search_bound cfg")
        case True
        have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
          unfolding eq1 st Cons au_cont_def using True
          by (simp add: resW_handleW_emit resW_handleW_fin[OF _ fR])
        from fin_res[OF this fR] show ?thesis .
      next
        case False
        let ?m = "bindW (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. pull cfg (S_ItRight (td + 1) ms R))"
        have eq2: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW ?m ?h) r" for r
          unfolding eq1 st Cons au_cont_def using False by (simp add: resW_handleW_whenW)
        have siM: "sinv A K X env' (dp # (frs' @ ffs))" using si' Cons by simp
        have frM: "fr_shape env' dp" using fr Cons by simp
        have mo: "MATCH_ok env' dp"
        proof -
          obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
          have "frs_shape dp" by (rule SIMPL_frs_shape[OF ok(1)[unfolded st Cons]])
          from sinv_MATCH_ok[OF this[unfolded dp] siM[unfolded dp]] show ?thesis by (simp add: dp)
        qed
        from MATCH_fin[OF cfg fin siM frM mo] consider (cu) evs where "MATCH cfg env' dp (frs' @ ffs) = Some (evs, UErr CANTUNIFY)"
          | (ok) ms where "okW (MATCH cfg env' dp (frs' @ ffs)) ms" "fin cfg ms (mres A env')"
          unfolding xokW_def by blast
        then show ?thesis
        proof cases
          case cu
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
            unfolding eq2 resW_handleW_bindW_err[OF cu] by simp
          from fin_res[OF this fR] show ?thesis .
        next
          case (ok ms)
          have lt: "nat (int_of_integer (cfg_search_bound cfg + 1 - (td + 1))) < n"
            using depth_measure[OF False] less.prems(1) by simp
          have sq: "seqinv (GE env' (dp # frs' @ ffs)) ms" by (rule MATCH_sound[OF ok(1) mo])
          have fM: "fin cfg ms (\<lambda>x. mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x)"
            by (rule fin_ev_conj[OF ok(2) ev_sound[OF _ sq]])
          have IH: "fin cfg (S_AddUnify (td + 1) env2 dps2 R2) ?Q"
            if "mres A env' (El_E env2 dps2)" "elem_ok (GE env' (dp # frs' @ ffs)) (El_E env2 dps2)"
              "fin cfg R2 ?Q" for env2 dps2 R2
          proof -
            from that(1) obtain A2 K2 X2 where "finite X2" "finite K2" "sinv A2 K2 X2 env2 dps2" "A \<subseteq> A2"
              and tn2: "tnew A env' A2 env2"
              by (auto simp: mres_def)
            moreover have "tnew A0 env0 A2 env2" by (rule tnew_trans[OF tn1 tn2 mx1])
            moreover have "dstep env0 dps0 env2 dps2" using dstep_trans[OF d1] that(2) Cons by simp
            ultimately show ?thesis using less.IH[OF lt refl, of X2 K2 A2 env2 dps2 R2] that(3) A0 by blast
          qed
          have fI: "fin cfg (S_ItRight (td + 1) ms R) ?Q"
          proof (rule fin_ItRight[OF _ fR])
            show "fin cfg ms (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
                (\<forall>R. fin cfg R ?Q \<longrightarrow> fin cfg (S_AddUnify (td + 1) env dps R) ?Q))"
            proof (rule fin_mono[OF fM])
              fix x assume x: "mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x"
              then obtain env2 dps2 where x2: "x = El_E env2 dps2" by (auto simp: mres_def)
              with x IH[of env2 dps2] show "\<exists>env dps. x = El_E env dps \<and>
                  (\<forall>R. fin cfg R ?Q \<longrightarrow> fin cfg (S_AddUnify (td + 1) env dps R) ?Q)" by blast
            qed
          qed
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            unfolding eq2 by (rule resW_handleW_fin[OF _ fI]) (simp add: resW_bindW_ok[OF ok(1)])
          from fin_res[OF this fI] show ?thesis .
        qed
      qed
    qed
  qed
qed

text \<open>
  The search terminates with finitely many unifiers, each of which is a step from the input pairs
  to its flex-flex pairs:
\<close>

theorem hounifiers_fin_sound:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
  unfolding hounifiers_def by (rule au_fin[OF assms(1) refl assms(2-4) order_refl tnew_refl dstep_refl fin_Empty])

theorem hounifiers_fin:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (rres A env)"
  by (rule fin_mono[OF hounifiers_fin_sound[OF assms]]) simp

end

end
