section \<open>Finiteness of the Search\<close>

theory Unify_Pull_Fin
  imports Unify_Match_Fin
begin

text \<open>
  The search of \<^const>\<open>hounifiers\<close> terminates without an exception, after finitely many
  unifiers: the depth of the search is bounded by \<^const>\<open>cfg_search_bound\<close>, each node simplifies
  its problem (\<^const>\<open>SIMPL\<close>, theorem @{thm [source] pure_sig.SIMPL_term}) and enumerates finitely
  many new problems by \<^const>\<open>MATCH\<close> (theorem @{thm [source] match_fin.MATCH_fin}). A leaf
  without flex-rigid pairs returns a unifier after the treatment of its flex-flex pairs by
  \<^const>\<open>add_ffpair\<close>, whose termination is a hypothesis here.
\<close>

locale pull_fin = match_fin +
  assumes ff_term: "\<And>A K X env ffs. finite X \<Longrightarrow> finite K \<Longrightarrow> sinv A K X env ffs \<Longrightarrow>
    (\<forall>dp\<in>set ffs. ff_shape env dp) \<Longrightarrow> \<exists>r. okW (foldrW (add_ffpair alg) ffs (env, [])) r"
begin

text \<open>The unifiers: the results of \<^const>\<open>add_ffpair\<close> on the flex-flex pairs of a simplified problem.\<close>

definition rres :: "elem \<Rightarrow> bool" where
  "rres x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> (\<exists>A K X env ffs. finite X \<and> finite K \<and> sinv A K X env ffs \<and>
    (\<forall>dp\<in>set ffs. ff_shape env dp) \<and> okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps)))"

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

text \<open>A node of the search at depth \<open>td\<close>, followed by a finite enumeration:\<close>

lemma au_fin:
  assumes cfg: "cfg_alg cfg = alg"
  shows "nat (int_of_integer (cfg_search_bound cfg + 1 - td)) = n \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow>
    sinv A K X env dps \<Longrightarrow> fin cfg R rres \<Longrightarrow> fin cfg (S_AddUnify td env dps R) rres"
proof (induction n arbitrary: td A K X env dps R rule: less_induct)
  case (less n)
  note fin = less.prems(2,3) and si = less.prems(4) and fR = less.prems(5)
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have eq: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow>
      resW (handleW (bindW (SIMPL alg env dps) (au_cont cfg td R)) ?h) r" for r
    using resW_pull_AddUnify[of cfg td env dps R r] by (simp add: cfg)
  from SIMPL_term[OF fin si] consider (cu) evs where "SIMPL alg env dps = Some (evs, UErr CANTUNIFY)"
    | (ok) st where "okW (SIMPL alg env dps) st" "simpl_post A K X env st"
    unfolding cuok_def by blast
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
      and fr: "\<forall>dp\<in>set frs. fr_shape env' dp"
      by (auto simp: simpl_post_def)
    have eq1: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?h) r" for r
      unfolding eq resW_handleW_bindW_ok[OF ok(1)] ..
    show ?thesis
    proof (cases frs)
      case Nil
      have siff: "sinv A K X env' ffs" using si' Nil by simp
      from ff_term[OF fin siff ff] obtain r0 where r0: "okW (foldrW (add_ffpair alg) ffs (env', [])) r0" by blast
      obtain e1 tps where r0e: "r0 = (e1, tps)" by (cases r0)
      have ok2: "okW (au_cont cfg td R st) (Some (El_R e1 tps, R))"
        unfolding st Nil au_cont_def using r0 r0e by (auto simp: cfg)
      have "resW (pull cfg (S_AddUnify td env dps R)) (UOk (Some (El_R e1 tps, R)))"
        unfolding eq1 resW_handleW_ok[OF ok2] by simp
      moreover have "rres (El_R e1 tps)"
        unfolding rres_def using fin siff ff r0 r0e by blast
      ultimately show ?thesis by (rule fin_Cons[OF _ _ fR])
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
        from MATCH_fin[OF cfg fin siM frM] consider (cu) evs where "MATCH cfg env' dp (frs' @ ffs) = Some (evs, UErr CANTUNIFY)"
          | (ok) ms where "okW (MATCH cfg env' dp (frs' @ ffs)) ms" "fin cfg ms mres"
          unfolding cuok_def by blast
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
          have IH: "fin cfg (S_AddUnify (td + 1) env2 dps2 R2) rres"
            if "mres (El_E env2 dps2)" "fin cfg R2 rres" for env2 dps2 R2
          proof -
            from that(1) obtain A2 K2 X2 where "finite X2" "finite K2" "sinv A2 K2 X2 env2 dps2"
              by (auto simp: mres_def)
            from less.IH[OF lt refl this that(2)] show ?thesis .
          qed
          have fI: "fin cfg (S_ItRight (td + 1) ms R) rres"
          proof (rule fin_ItRight[OF _ fR])
            show "fin cfg ms (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
                (\<forall>R. fin cfg R rres \<longrightarrow> fin cfg (S_AddUnify (td + 1) env dps R) rres))"
            proof (rule fin_mono[OF ok(2)])
              fix x assume "mres x"
              then obtain env2 dps2 where x: "x = El_E env2 dps2" by (auto simp: mres_def)
              with \<open>mres x\<close> IH[of env2 dps2] show "\<exists>env dps. x = El_E env dps \<and>
                  (\<forall>R. fin cfg R rres \<longrightarrow> fin cfg (S_AddUnify (td + 1) env dps R) rres)" by blast
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

theorem hounifiers_fin:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) rres"
  unfolding hounifiers_def by (rule au_fin[OF assms(1) refl assms(2-4) fin_Empty])

corollary hounifiers_fin':
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps)"
  by (rule fin_mono[OF hounifiers_fin[OF assms]]) (auto simp: rres_def)

end

end
