section \<open>The Pattern Case and the Search with the Invariant of Termination\<close>

theory Unify_Typed_Results
  imports Unify_Results "Unify_Soundness.Unify_Typed_Pattern"
begin

text \<open>
  Two results on the unifiers that use the theories of the termination proofs: the pattern
  case of \<^const>\<open>unifiers\<close> for lists of problems, and the soundness of the search by the
  invariant of the termination proof. The typed solutions of the unifiers (\<open>gsolution\<close>,
  \<open>uresult_solves\<close>) are in theory \<open>Unify_Result_Base\<close>.
\<close>

context pure_sig
begin

text \<open>
  \<^const>\<open>unifiers\<close> solves a list of pattern problems by pattern unification, one pair after the
  other. If that succeeds, the resulting environment has a typed solution that unifies every
  pair, with no hypothesis on the types of the names (compare
  @{thm [source] pure_sig.unifiers_pattern_bound_names}, which asks for one type per bound
  name): the corollary of @{thm [source] pure_sig.unify_typed_unifier} for lists.
\<close>

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

text \<open>
  Without loose names, the invariant of the termination proof is such an invariant, so the
  theorem above gives back the soundness of the search (compare
  @{thm [source] pure_sig.hounifiers_fin_sound}):
\<close>

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
