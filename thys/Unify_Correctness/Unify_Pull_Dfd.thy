section \<open>Finiteness of the Search with Names at Two Types\<close>

theory Unify_Pull_Dfd
  imports Unify_Mc_Dfd Unify_Pull_Fin
begin

text \<open>
  The search of \<^const>\<open>hounifiers\<close> terminates after finitely many unifiers, without a hypothesis
  on the names: pulling the sequence repeatedly ends at its end, or with the clash of
  \<^const>\<open>var_clash\<close> or \<open>TERM\<close> from \<open>add_ffpair\<close>. The unifiers it returns before are steps from
  the input pairs to their flex-flex pairs, as in theory
  \<^theory>\<open>Unify_Correctness.Unify_Pull_Fin\<close>.
\<close>

context pure_sig_gen
begin

lemma evalx_ev_set: "evalx cfg s xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> ev cfg s x"
proof (induction rule: evalx.induct)
  case (Cons s evs y s' xs)
  note p = pull_some_ev[OF Cons.hyps(1), of y s', simplified]
  show ?case
  proof (cases "x = y")
    case True
    with p show ?thesis by simp
  next
    case False
    with Cons.prems have "x \<in> set xs" by simp
    with Cons.IH p show ?thesis by blast
  qed
qed simp_all

lemma cfin_ev_conj: "cfin cfg s P \<Longrightarrow> (\<And>x. ev cfg s x \<Longrightarrow> Q x) \<Longrightarrow> cfin cfg s (\<lambda>x. P x \<and> Q x)"
  unfolding cfin_def using evalx_ev_set by blast

lemma cfin_Cons:
  assumes "resW (pull cfg s) (Ok (Some (x, s')))" "Q x" "cfin cfg s' Q"
  shows "cfin cfg s Q"
proof -
  from assms(3) obtain xs where xs: "evalx cfg s' xs" "\<forall>y\<in>set xs. Q y" by (auto simp: cfin_def)
  from assms(1) obtain evs where "pull cfg s = Some (evs, Ok (Some (x, s')))" by (auto simp: resW_def)
  from evalx.Cons[OF this xs(1)] xs(2) assms(2) show ?thesis
    unfolding cfin_def by (intro exI[of _ "x # xs"]) simp
qed

lemma cfin_pull: "cfin cfg X Q \<Longrightarrow> (\<exists>v. resW (pull cfg X) (Ok v)) \<or> (\<exists>e. resW (pull cfg X) (Err e) \<and> gexn e)"
  by (auto simp: cfin_def resW_def elim: evalx.cases)

text \<open>A handler of \<open>CANTUNIFY\<close> is not invoked when the computation behaves like a finite enumeration:\<close>

lemma resW_handleW_cfin:
  assumes "\<And>r. resW m r \<longleftrightarrow> resW (pull cfg X) r" "cfin cfg X Q"
  shows "resW (handleW m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> k | _ \<Rightarrow> raiseW e)) r \<longleftrightarrow> resW (pull cfg X) r"
proof -
  from cfin_pull[OF assms(2)] consider v where "resW (pull cfg X) (Ok v)"
    | e where "resW (pull cfg X) (Err e)" "gexn e" by blast
  then show ?thesis
  proof cases
    case 1
    with assms(1) obtain evs where "m = Some (evs, Ok v)" by (auto simp: resW_def)
    then show ?thesis using assms(1) by (simp add: handleW_def)
  next
    case 2
    with assms(1) obtain evs where m: "m = Some (evs, Err e)" by (auto simp: resW_def)
    from gexn_PExn[OF 2(2)] obtain x where "e = PExn x" by blast
    then show ?thesis using assms(1) m by (auto simp: handleW_def raiseW_def resW_def)
  qed
qed

lemma cfin_raise_res: "resW (pull cfg s) (Err e) \<Longrightarrow> gexn e \<Longrightarrow> cfin cfg s Q"
  by (auto simp: resW_def intro: cfin_raise)

text \<open>A node of the search:\<close>

lemma cfin_AddUnify:
  assumes fR: "cfin cfg R Q"
    and S: "ccuok (SIMPL (cfg_alg cfg) env dps) P"
    and N: "\<And>env' ffs. okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, []) \<Longrightarrow> P (env', ffs, []) \<Longrightarrow>
      cxokE gexn (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) (\<lambda>r. Q (El_R (fst r) (snd r)))"
    and C: "\<And>env' ffs dp frs'. okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs') \<Longrightarrow>
      P (env', ffs, dp # frs') \<Longrightarrow> \<not> td > cfg_search_bound cfg \<Longrightarrow>
      ccuok (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. cfin cfg (S_ItRight (td + 1) ms R) Q)"
  shows "cfin cfg (S_AddUnify td env dps R) Q"
proof -
  let ?h = "\<lambda>e. case e of CANTUNIFY \<Rightarrow> pull cfg R | _ \<Rightarrow> raiseW e"
  have eq: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow>
      resW (handleW (bindW (SIMPL (cfg_alg cfg) env dps) (au_cont cfg td R)) ?h) r" for r
    by (rule resW_pull_AddUnify)
  have hraise: "resW (handleW (Some (evs, Err e)) ?h) (Err e)" if "gexn e" for evs e
    using gexn_PExn[OF that] by (auto simp: handleW_def raiseW_def resW_def)
  from S consider (cu) evs where "SIMPL (cfg_alg cfg) env dps = Some (evs, Err CANTUNIFY)"
    | (cl) evs e where "SIMPL (cfg_alg cfg) env dps = Some (evs, Err e)" "clashW e"
    | (ok) st where "okW (SIMPL (cfg_alg cfg) env dps) st" "P st"
    unfolding cxokE_def by blast
  then show ?thesis
  proof cases
    case cu
    have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
      unfolding eq resW_handleW_bindW_err[OF cu] by simp
    from cfin_res[OF this fR] show ?thesis .
  next
    case cl
    have "resW (pull cfg (S_AddUnify td env dps R)) (Err e)"
      unfolding eq resW_handleW_bindW_err[OF cl(1)] using hraise[OF gexn_clashW[OF cl(2)], of "[]"]
      by (auto simp: resW_def handleW_def)
    from cfin_raise_res[OF this gexn_clashW[OF cl(2)]] show ?thesis .
  next
    case (ok st)
    obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
    have eq1: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW (au_cont cfg td R st) ?h) r" for r
      unfolding eq resW_handleW_bindW_ok[OF ok(1)] ..
    show ?thesis
    proof (cases frs)
      case Nil
      from N[OF ok(1)[unfolded st Nil] ok(2)[unfolded st Nil]]
      consider (err) evs e where "foldrW (add_ffpair (cfg_alg cfg)) ffs (env', []) = Some (evs, Err e)" "gexn e \<or> clashW e"
        | (okr) r0 where "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env', [])) r0" "Q (El_R (fst r0) (snd r0))"
        unfolding cxokE_def by blast
      then show ?thesis
      proof cases
        case err
        have ge: "gexn e" using err(2) by (auto intro: gexn_clashW)
        have "au_cont cfg td R st = Some (evs, Err e)"
          unfolding st Nil au_cont_def using err(1) by (simp add: bindW_def)
        then have "resW (pull cfg (S_AddUnify td env dps R)) (Err e)"
          unfolding eq1 using hraise[OF ge, of evs] by simp
        from cfin_raise_res[OF this ge] show ?thesis .
      next
        case okr
        have ok2: "okW (au_cont cfg td R st) (Some (El_R (fst r0) (snd r0), R))"
          unfolding st Nil au_cont_def using okr(1) by auto
        have r1: "resW (pull cfg (S_AddUnify td env dps R)) (Ok (Some (El_R (fst r0) (snd r0), R)))"
          unfolding eq1 resW_handleW_ok[OF ok2] by simp
        from cfin_Cons[OF r1 okr(2) fR] show ?thesis .
      qed
    next
      case (Cons dp frs')
      show ?thesis
      proof (cases "td > cfg_search_bound cfg")
        case True
        have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
          unfolding eq1 st Cons au_cont_def using True
          by (simp add: resW_handleW_emit resW_handleW_cfin[OF _ fR])
        from cfin_res[OF this fR] show ?thesis .
      next
        case False
        let ?m = "bindW (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. pull cfg (S_ItRight (td + 1) ms R))"
        have eq2: "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (handleW ?m ?h) r" for r
          unfolding eq1 st Cons au_cont_def using False by (simp add: resW_handleW_whenW)
        from C[OF ok(1)[unfolded st Cons] ok(2)[unfolded st Cons] False]
        consider (cu) evs where "MATCH cfg env' dp (frs' @ ffs) = Some (evs, Err CANTUNIFY)"
          | (cl) evs e where "MATCH cfg env' dp (frs' @ ffs) = Some (evs, Err e)" "clashW e"
          | (ok) ms where "okW (MATCH cfg env' dp (frs' @ ffs)) ms" "cfin cfg (S_ItRight (td + 1) ms R) Q"
          unfolding cxokE_def by blast
        then show ?thesis
        proof cases
          case cu
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg R) r" for r
            unfolding eq2 resW_handleW_bindW_err[OF cu] by simp
          from cfin_res[OF this fR] show ?thesis .
        next
          case cl
          have ge: "gexn e" by (rule gexn_clashW[OF cl(2)])
          have "resW (pull cfg (S_AddUnify td env dps R)) (Err e)"
            unfolding eq2 resW_handleW_bindW_err[OF cl(1)] using gexn_PExn[OF ge]
            by (auto simp: raiseW_def resW_def)
          from cfin_raise_res[OF this ge] show ?thesis .
        next
          case (ok ms)
          note fI = ok(2)
          have "resW (pull cfg (S_AddUnify td env dps R)) r \<longleftrightarrow> resW (pull cfg (S_ItRight (td + 1) ms R)) r" for r
            unfolding eq2 by (rule resW_handleW_cfin[OF _ fI]) (simp add: resW_bindW_ok[OF ok(1)])
          from cfin_res[OF this fI] show ?thesis .
        qed
      qed
    qed
  qed
qed

text \<open>
  A node of the search at depth \<open>td\<close>, followed by a finite enumeration, for a problem that is a
  step from the problem \<open>dps0\<close> of the root:
\<close>

lemma au_cfin:
  assumes cfg: "cfg_alg cfg = alg"
  shows "nat (int_of_integer (cfg_search_bound cfg + 1 - td)) = n \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow>
    sinv A K X env dps \<Longrightarrow> A0 \<subseteq> A \<Longrightarrow> tnew A0 env0 A env \<Longrightarrow> dstep env0 dps0 env dps \<Longrightarrow>
    cfin cfg R (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x) \<Longrightarrow>
    cfin cfg (S_AddUnify td env dps R) (\<lambda>x. rres A0 env0 x \<and> elem_ok (GR env0 dps0) x)"
proof (induction n arbitrary: td A K X env dps R rule: less_induct)
  case (less n)
  note fin = less.prems(2,3) and si = less.prems(4) and A0 = less.prems(5) and tn0 = less.prems(6)
    and d0 = less.prems(7) and fR = less.prems(8)
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
  proof (rule cfin_AddUnify[where cfg = cfg, unfolded cfg, OF fR SIMPL_dfd[OF fin si]])
    fix env' ffs
    assume ok: "okW (SIMPL alg env dps) (env', ffs, [])" and sp: "simpl_post A K X env (env', ffs, [])"
    note p = post[OF ok sp]
    have siff: "sinv A K X env' ffs" using p(1) by simp
    have gen: "cxokE gexn (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>(env'', tps').
          ffres A K (X \<union> dvars (tdps tps')) env'' tps' \<and> extends env' env'' \<and> tyenv env'' = tyenv env' \<and>
          iflex env' env'' \<and> (\<forall>(t, u)\<in>set tps'. flexb env' t \<and> flexb env' u) \<and> dstep env' ffs env'' (tdps tps'))"
    proof (cases "loose = {}")
      case False
      from foldrW_add_ffpair_gen_Nil[OF siff p(2)] show ?thesis
        by (rule cxokE_mono_exn) (use False in \<open>auto intro: gexn_ffexn\<close>)
    next
      case True
      from SIMPL_add_ffpair_ok[OF fin si ok nfree_strict[OF True]] obtain r where
        "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        by (subst (asm) lxokE_strict[OF True]) auto
      with foldrW_add_ffpair_gen_Nil[OF siff p(2)] show ?thesis by (auto simp: cxokE_def)
    qed
    show "cxokE gexn (foldrW (add_ffpair alg) ffs (env', [])) (\<lambda>r. ?Q (El_R (fst r) (snd r)))"
    proof (rule cxokE_mono_ok[OF gen])
      fix r assume r0': "okW (foldrW (add_ffpair alg) ffs (env', [])) r"
        and pr: "case r of (env'', tps') \<Rightarrow>
          ffres A K (X \<union> dvars (tdps tps')) env'' tps' \<and> extends env' env'' \<and> tyenv env'' = tyenv env' \<and>
          iflex env' env'' \<and> (\<forall>(t, u)\<in>set tps'. flexb env' t \<and> flexb env' u) \<and> dstep env' ffs env'' (tdps tps')"
      obtain e1 tps where r: "r = (e1, tps)" by (cases r)
      note r0 = r0'[unfolded r]
      from pr r have ff: "ffres A K (X \<union> dvars (tdps tps)) e1 tps" and ex: "extends env' e1"
        and th: "tyenv e1 = tyenv env'" and fi: "iflex env' e1"
        and fl: "\<forall>(t, u)\<in>set tps. flexb env' t \<and> flexb env' u" by auto
      have si1: "sinv A K (X \<union> dvars (tdps tps)) e1 (tdps tps)" using ff by (simp add: ffres_sinv)
      have ei1: "einv A K e1" using si1 by (simp add: sinv_def)
      have fv: "finv A K env' e1" using ei1 th ex fi by (simp add: finv_def)
      have tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env') \<union> A"
      proof (intro ballI)
        fix q assume q: "q \<in> set tps"
        obtain t u where tu: "q = (t, u)" by (cases q)
        from q tu have "([], t, u) \<in> set (tdps tps)" by force
        with si1 have "upok A e1 [] (X \<union> dvars (tdps tps)) t u" by (auto simp: sinv_def)
        from upokD(3,4)[OF this] th show "case q of (t, u) \<Rightarrow> ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env') \<union> A"
          by (simp add: tu)
      qed
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
      and sp: "simpl_post A K X env (env', ffs, dp # frs')"
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
    show "ccuok (MATCH cfg env' dp (frs' @ ffs)) (\<lambda>ms. cfin cfg (S_ItRight (td + 1) ms R) ?Q)"
    proof (rule cxokE_mono_ok[OF MATCH_fin_c[OF cfg fin siM frM mo]])
      fix ms assume okm: "okW (MATCH cfg env' dp (frs' @ ffs)) ms" and fm: "cfin cfg ms (mres A env')"
      have lt: "nat (int_of_integer (cfg_search_bound cfg + 1 - (td + 1))) < n"
        using depth_measure[OF False] less.prems(1) by simp
      have sq: "seqinv (GE env' (dp # frs' @ ffs)) ms" by (rule MATCH_sound[OF okm mo])
      have fM: "cfin cfg ms (\<lambda>x. mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x)"
        by (rule cfin_ev_conj[OF fm ev_sound[OF _ sq]])
      have IH: "cfin cfg (S_AddUnify (td + 1) env2 dps2 R2) ?Q"
        if "mres A env' (El_E env2 dps2)" "elem_ok (GE env' (dp # frs' @ ffs)) (El_E env2 dps2)"
          "cfin cfg R2 ?Q" for env2 dps2 R2
      proof -
        from that(1) obtain A2 K2 X2 where "finite X2" "finite K2" "sinv A2 K2 X2 env2 dps2" "A \<subseteq> A2"
          and tn2: "tnew A env' A2 env2"
          by (auto simp: mres_def)
        moreover have "tnew A0 env0 A2 env2" by (rule tnew_trans[OF p(6) tn2 p(5)])
        moreover have "dstep env0 dps0 env2 dps2" using dstep_trans[OF p(4)] that(2) by simp
        ultimately show ?thesis using less.IH[OF lt refl, of X2 K2 A2 env2 dps2 R2] that(3) A0 by blast
      qed
      show "cfin cfg (S_ItRight (td + 1) ms R) ?Q"
      proof (rule cfin_ItRight[OF _ fR])
        show "cfin cfg ms (\<lambda>x. \<exists>env dps. x = El_E env dps \<and>
            (\<forall>R. cfin cfg R ?Q \<longrightarrow> cfin cfg (S_AddUnify (td + 1) env dps R) ?Q))"
        proof (rule cfin_mono[OF fM])
          fix x assume x: "mres A env' x \<and> elem_ok (GE env' (dp # frs' @ ffs)) x"
          then obtain env2 dps2 where x2: "x = El_E env2 dps2" by (auto simp: mres_def)
          with x IH[of env2 dps2] show "\<exists>env dps. x = El_E env dps \<and>
              (\<forall>R. cfin cfg R ?Q \<longrightarrow> cfin cfg (S_AddUnify (td + 1) env dps R) ?Q)" by auto
        qed
      qed
    qed
  qed
qed

text \<open>
  The search terminates after finitely many unifiers, each of which is a step from the input pairs
  to its flex-flex pairs, at the end of the sequence or with the clash or \<open>TERM\<close> from
  \<open>add_ffpair\<close> (\<^const>\<open>gexn\<close>). There is no hypothesis on the names.
\<close>

theorem hounifiers_cfin:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "cfin cfg (hounifiers rb env tus) (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
  unfolding hounifiers_def
  by (rule au_cfin[OF assms(1) refl assms(2-4) order_refl tnew_refl dstep_refl cfin_Empty])

end


subsection \<open>The statements of theory \<open>Unify_Pull_Fin\<close>\<close>

context pure_sig_gen
begin

theorem hounifiers_fin_sound:
  assumes "cfg_alg cfg = alg" "finite X" "finite K" "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "lfin cfg (hounifiers rb env tus) (\<lambda>x. rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x)"
  by (rule lfin_cfin[OF hounifiers_cfin[OF assms]])

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
