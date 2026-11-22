section \<open>The Pattern Case of the Unifiers for Names with Several Types\<close>

theory Unify_Typed_Pattern
  imports Unify_Sound Pattern_Correctness.Pattern_Typed_Unifier
begin

text \<open>
  \<^const>\<open>unifiers\<close> solves a list of pattern problems by pattern unification, one pair after the
  other. If that succeeds, the resulting environment has a typed solution that unifies every
  pair, with no hypothesis on the types of the names (compare
  @{thm [source] pure_sig.unifiers_pattern_bound_names}, which asks for one type per bound
  name): the corollary of @{thm [source] pure_sig.unify_typed_unifier} for lists.
\<close>

context pure_sig
begin

theorem unifiers_pattern_typed:
  assumes f: "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) tus env) env'"
    and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env') \<rho>" and wte: "wt_env \<rho> env"
    and ty: "\<forall>(t, u)\<in>set tus. closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T)"
    and bl: "below (maxidx env) ((\<Union>(t, u)\<in>set tus. vars t \<union> vars u) \<union> evars env)"
    and ac: "acyc env"
  shows "unifiers alg' env tus = Some (Ok (S_Single (El_R env' [])))"
    and "\<exists>\<sigma>. solution \<rho> \<sigma> env' \<and> (\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"
proof -
  show "unifiers alg' env tus = Some (Ok (S_Single (El_R env' [])))"
    using f by (simp add: unifiers_def handle_def bindM_def return_def)
  interpret G: pure_sig_gen alg ar ctab "UNIV :: indexname set"
    by (rule pure_sig_gen_axioms)
  have vb: "G.vinv \<rho> env1 Z \<longleftrightarrow> below (maxidx env1) (Z \<union> evars env1)" for env1 Z
    by (simp add: G.vinv_def G.vcons_def)
  have ext_fold: "extends env1 env2" if "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) ps env1) env2"
    for ps env1 env2
    using foldM_unif_extends[of alg' "[]" ps env1 env2] that by (simp add: unify_def)
  have main: "acyc env2 \<and> wt_env \<rho> env2 \<and> below (maxidx env2) (X \<union> evars env2) \<and>
      (\<forall>(t, u)\<in>set ps. \<exists>e. eqv (G.ebinds \<rho> env2) e (inst \<rho> t) (inst \<rho> u))"
    if "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) ps env1) env2" "extends env2 env'"
      "\<forall>(t, u)\<in>set ps. closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T)"
      "acyc env1" "wt_env \<rho> env1" "below (maxidx env1) (X \<union> (\<Union>(t, u)\<in>set ps. vars t \<union> vars u) \<union> evars env1)"
    for ps env1 env2 X
    using that
  proof (induction ps arbitrary: env1 X)
    case Nil
    then show ?case by simp
  next
    case (Cons p ps)
    obtain t u where p: "p = (t, u)" by force
    from Cons.prems(1) p obtain env3 where u1: "ok (unify alg' t u env1) env3"
      and r: "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) ps env3) env2"
      by auto
    let ?Y = "\<Union>(t, u)\<in>set ps. vars t \<union> vars u"
    from Cons.prems(3) p obtain e T where ct: "closed t" "closed u"
      and tt: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
      by auto
    have ext32: "extends env3 env2" by (rule ext_fold[OF r])
    have tsol3: "tsol (tyenv env3) \<rho>" using extends_tsol[OF \<rho>(2) extends_trans[OF ext32 Cons.prems(2)]] .
    have bl1: "below (maxidx env1) ((X \<union> ?Y) \<union> vars t \<union> vars u \<union> evars env1)"
      using Cons.prems(6) p by (simp add: Un_ac)
    have st: "G.step_okg env1 [] t u env3" using G.unif_gsound[of alg' "[]" t u env1] u1 by (simp add: unify_def)
    have "wt_env \<rho> env3 \<and> G.vinv \<rho> env3 (X \<union> ?Y) \<and> eqv (G.ebinds \<rho> env3) e (inst \<rho> t) (inst \<rho> u)"
    proof (rule G.step_okgD(2)[OF st tsol3 extends_refl Cons.prems(5) _ tt])
      show "bs_env \<rho> e []" by (simp add: bs_env_def)
      show "G.vinv \<rho> env1 ((X \<union> ?Y) \<union> vars t \<union> vars u)" using bl1 by (simp add: vb Un_ac)
      show "\<not> loose_bvar t (ilength [])" "\<not> loose_bvar u (ilength [])" using ct by (simp_all add: closed_def)
    qed
    then have r1: "wt_env \<rho> env3" "below (maxidx env3) ((X \<union> ?Y) \<union> evars env3)"
      and e1: "eqv (G.ebinds \<rho> env3) e (inst \<rho> t) (inst \<rho> u)"
      by (simp_all add: vb)
    have "step_ac env1 t u env3" using unif_acyc[of alg' "[]" t u env1] u1 by (simp add: unify_def)
    from step_acD[OF this Cons.prems(4) bl1] have ac3: "acyc env3" by blast
    have bl3: "below (maxidx env3) (X \<union> ?Y \<union> evars env3)" using r1(2) by simp
    have ty': "\<forall>(t, u)\<in>set ps. closed t \<and> closed u \<and> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T)"
      using Cons.prems(3) by simp
    note IH = Cons.IH[OF r Cons.prems(2) ty' ac3 r1(1) bl3]
    have "eqv (G.ebinds \<rho> env2) e (inst \<rho> t) (inst \<rho> u)"
      by (rule eqv_mono[OF e1 G.ebinds_extends[OF ext32]])
    with IH show ?case by (auto simp: p)
  qed
  from main[OF f extends_refl ty ac wte, of "{}"] bl
  have ac': "acyc env'" and wte': "wt_env \<rho> env'"
    and eqs: "\<forall>(t, u)\<in>set tus. \<exists>e. eqv (G.ebinds \<rho> env') e (inst \<rho> t) (inst \<rho> u)"
    by simp_all
  have sol: "solution \<rho> (G.gsol \<rho> env') env'" by (rule G.gsol_solution[OF ac' wte' \<rho>])
  have "ap \<rho> (G.gsol \<rho> env') t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (G.gsol \<rho> env') u" if "(t, u) \<in> set tus" for t u
  proof -
    from eqs that obtain e where eq: "eqv (G.ebinds \<rho> env') e (inst \<rho> t) (inst \<rho> u)" by blast
    show ?thesis
      unfolding ap_def
      by (rule eqv_vsubst[OF G.eqv_typed_pairs[OF eq] solutionD(3)[OF sol]])
        (auto intro: G.gsol_ebinds[OF ac' wte' \<rho>])
  qed
  with sol show "\<exists>\<sigma>. solution \<rho> \<sigma> env' \<and> (\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"
    by blast
qed

end


subsection \<open>The search, without termination\<close>

text \<open>
  The soundness of the search of \<^const>\<open>hounifiers\<close> in theory \<open>Unify_Search_Inv\<close> is proved
  together with its termination, by an invariant (\<open>sinv\<close>) whose preservation is proved
  only for results that bind no loose name. Here the search is treated by induction on the
  evaluation \<open>ev\<close>, which needs no termination: every element of the enumeration is a step
  from the input pairs (\<open>dstep\<close>, which makes no hypothesis on the names since the steps were
  generalized), for any invariant \<open>NI\<close> of the nodes of the search that gives the hypothesis
  \<open>MATCH_ok\<close> of \<^const>\<open>MATCH\<close> and is kept by a step of the search.
\<close>

context pure_sig_gen
begin

inductive sgood :: "(env \<Rightarrow> dpair list \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> seq \<Rightarrow> bool"
  for NI cfg env0 dps0 where
  Empty: "sgood NI cfg env0 dps0 S_Empty"
| AddUnify: "dstep env0 dps0 env dps \<Longrightarrow> NI env dps \<Longrightarrow> sgood NI cfg env0 dps0 R \<Longrightarrow>
    sgood NI cfg env0 dps0 (S_AddUnify td env dps R)"
| ItRight: "(\<And>y. ev cfg xq y \<Longrightarrow> \<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps) \<Longrightarrow>
    sgood NI cfg env0 dps0 R \<Longrightarrow> sgood NI cfg env0 dps0 (S_ItRight td xq R)"

inductive_cases sgood_AddUnifyE: "sgood NI cfg env0 dps0 (S_AddUnify td env dps R)"
inductive_cases sgood_ItRightE: "sgood NI cfg env0 dps0 (S_ItRight td xq R)"

lemma ev_sgood:
  assumes NI_match: "\<And>env dps env' ffs dp frs. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
    and NI_step: "\<And>env dps env' ffs dp frs ms env2 dps2. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> NI env2 dps2"
  shows "ev cfg s x \<Longrightarrow> sgood NI cfg env0 dps0 s \<Longrightarrow> elem_ok (GR env0 dps0) x"
proof (induction rule: ev.induct)
  case (au_tail reseq x td env dps)
  from au_tail.prems show ?case by (rule sgood_AddUnifyE) (rule au_tail.IH)
next
  case (au_res env dps env' ffs r td reseq)
  from au_res.prems have d0: "dstep env0 dps0 env dps" by (rule sgood_AddUnifyE)
  obtain e1 tps where r: "r = (e1, tps)" by (cases r)
  have d1: "dstep env dps env' ffs" using SIMPL_sound[OF au_res.hyps(1)] by simp
  have d2: "dstep env' ffs e1 (tdps tps)" using foldrW_add_ffpair_sound[OF au_res.hyps(2)[unfolded r]] by simp
  from dstep_trans[OF dstep_trans[OF d0 d1] d2] show ?case by (simp add: r)
next
  case (au_match env dps env' ffs dp frs td ms reseq x)
  from au_match.prems obtain d0: "dstep env0 dps0 env dps" and ni: "NI env dps" and sR: "sgood NI cfg env0 dps0 reseq"
    by (rule sgood_AddUnifyE) blast
  have d1: "dstep env dps env' (dp # frs @ ffs)" using SIMPL_sound[OF au_match.hyps(1)] by simp
  have mo: "MATCH_ok env' dp" by (rule NI_match[OF ni au_match.hyps(1)])
  have sq: "seqinv (GE env' (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF au_match.hyps(3) mo])
  have "sgood NI cfg env0 dps0 (S_ItRight (td + 1) ms reseq)"
  proof (rule sgood.ItRight[OF _ sR])
    fix y assume y: "ev cfg ms y"
    from ev_sound[OF y sq] obtain env2 dps2 where y2: "y = El_E env2 dps2" and d2: "dstep env' (dp # frs @ ffs) env2 dps2"
      by (cases y) auto
    have "NI env2 dps2" by (rule NI_step[OF ni au_match.hyps(1,3) y[unfolded y2]])
    with y2 dstep_trans[OF dstep_trans[OF d0 d1] d2]
    show "\<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps" by blast
  qed
  then show ?case by (rule au_match.IH)
next
  case (ir_tail yq x td xq)
  from ir_tail.prems show ?case by (rule sgood_ItRightE) (rule ir_tail.IH)
next
  case (ir_head xq env dps td x yq)
  from ir_head.prems obtain h: "\<And>y. ev cfg xq y \<Longrightarrow> \<exists>env dps. y = El_E env dps \<and> dstep env0 dps0 env dps \<and> NI env dps"
    by (rule sgood_ItRightE) blast
  from h[OF ir_head.hyps(1)] have "dstep env0 dps0 env dps" "NI env dps" by auto
  then have "sgood NI cfg env0 dps0 (S_AddUnify td env dps S_Empty)" by (intro sgood.AddUnify sgood.Empty)
  from ir_head.IH(2)[OF this] show ?case .
qed (auto elim: sgood.cases)

theorem hounifiers_ev_sound:
  assumes NI0: "NI env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and NI_match: "\<And>env dps env' ffs dp frs. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
    and NI_step: "\<And>env dps env' ffs dp frs ms env2 dps2. NI env dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env' dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> NI env2 dps2"
    and ev: "ev cfg (hounifiers rb env tus) x"
  shows "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
proof (rule ev_sgood[OF NI_match NI_step ev[unfolded hounifiers_def]])
  show "sgood NI cfg env (map (\<lambda>(t, u). (rb, t, u)) tus) (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) S_Empty)"
    by (intro sgood.AddUnify sgood.Empty dstep_refl NI0)
qed

end

text \<open>
  Without loose names, the invariant of the termination proof is such an invariant, so the
  theorem above gives back the soundness of the search (compare
  @{thm [source] pure_sig.hounifiers_fin_sound}):
\<close>

context pure_sig
begin

theorem hounifiers_ev_sound_sinv:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)" and ev: "ev cfg (hounifiers rb env tus) x"
  shows "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
proof (rule hounifiers_ev_sound[OF _ _ _ ev])
  let ?NI = "\<lambda>env dps. \<exists>A K X. finite X \<and> finite K \<and> sinv A K X env dps"
  show "?NI env (map (\<lambda>(t, u). (rb, t, u)) tus)" using fin si by blast
  have post: "simpl_post A K X env (env', ffs, frs)"
    if "finite X" "finite K" "sinv A K X env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, frs)"
    for A K X env dps env' ffs frs
    using SIMPL_term[OF that(1-3)] that(4) by (auto simp: cfg xokW_def)
  show "MATCH_ok env' dp"
    if "?NI env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)" for env dps env' ffs dp frs
  proof -
    from that(1) obtain A K X where f: "finite X" "finite K" and s: "sinv A K X env dps" by blast
    from post[OF f s that(2)] have si': "sinv A K X env' (dp # frs @ ffs)" by (simp add: simpl_post_def)
    obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
    have "frs_shape dp" by (rule SIMPL_frs_shape[OF that(2)])
    from sinv_MATCH_ok[OF this[unfolded dp] si'[unfolded dp]] show ?thesis by (simp add: dp)
  qed
  show "?NI env2 dps2"
    if "?NI env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
      "okW (MATCH cfg env' dp (frs @ ffs)) ms" "ev cfg ms (El_E env2 dps2)" for env dps env' ffs dp frs ms env2 dps2
  proof -
    from that(1) obtain A K X where f: "finite X" "finite K" and s: "sinv A K X env dps" by blast
    from post[OF f s that(2)] have sp: "simpl_post A K X env (env', ffs, dp # frs)" .
    then have si': "sinv A K X env' (dp # frs @ ffs)" and fr: "fr_shape env' dp" by (simp_all add: simpl_post_def)
    obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
    have "frs_shape dp" by (rule SIMPL_frs_shape[OF that(2)])
    from sinv_MATCH_ok[OF this[unfolded dp] si'[unfolded dp]] have mo: "MATCH_ok env' dp" by (simp add: dp)
    from MATCH_fin[OF cfg f si' fr mo] that(3) have "fin cfg ms (mres A env')" by (auto simp: xokW_def)
    with evals_ev that(4) have "mres A env' (El_E env2 dps2)" unfolding fin_def by blast
    then show ?thesis by (auto simp: mres_def)
  qed
qed

end

end
