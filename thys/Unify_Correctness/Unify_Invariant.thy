section \<open>The Invariant of the Unifiers, without Termination\<close>

theory Unify_Invariant
  imports Unify_Pattern_Inv Unify_Smash_Typed
begin

text \<open>
  Every element of the enumeration of \<^const>\<open>unifiers\<close> on a well-formed problem satisfies the
  invariant of the results (\<^const>\<open>pure_sig_gen.uresult\<close>): theorem \<open>unifiers_ev_uresult\<close>. The
  proof needs no termination of the unifiers; it combines statements that are proved by
  induction on the computations:

    \<^item> the elements are steps (\<^const>\<open>pure_sig_gen.dstep\<close>) from the input, which gives the
      typing of the bindings and of the remaining pairs for every solution of the resulting
      type environment (\<^const>\<open>pure_sig_gen.gtyped\<close>), hence closed bindings and bounded indices;
    \<^item> the type-level invariant: a well-formed type environment and known type variables, for
      pattern unification (theory \<open>Unify_Pattern_Inv\<close>), for the search (theories
      \<open>Unify_Typed_Inv\<close> and \<open>Unify_Typed_Match\<close>) and for the treatment of the
      flex-flex pairs (theory \<open>Unify_Flexflex_Typed\<close>);
    \<^item> the acyclicity of the environments (theories \<open>Pattern_Typed_Unifier\<close> and
      \<open>Unify_Acyclic\<close>).

  The rules of the kernel use only this theorem about the unifiers. The termination of the
  unifiers and the completeness are separate (theories \<open>Unify_Termination\<close>,
  \<open>Unify_Results\<close>, \<open>Unify_Complete\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>From the type-level invariant to the invariant of the results\<close>

lemma einv_tyonly: "einv A K env \<Longrightarrow> einv A K (tyonly env)"
  by (auto simp: einv_def tvinv_def closed_env_def bbelow_def acyc_def dep_def acyclic_def)

lemma einv_known_cong:
  "tvars_env (tyenv env) \<union> A = tvars_env (tyenv env) \<union> B \<Longrightarrow> einv A K env \<Longrightarrow> einv B K env"
  by (simp add: einv_def tvinv_def tinv_def)

text \<open>The invariant of an environment, from the type-level invariant, acyclicity and typing:\<close>

lemma einv_of_typed:
  assumes ei: "einv A K (tyonly env)" and kE: "etvars env \<subseteq> tvars_env (tyenv env) \<union> A"
    and ac: "acyc env" and gt: "gtyped env dps"
  shows "einv A K env"
proof -
  note r0 = einv_rho0[OF ei]
  from gt r0 have w: "wt_env (tnorm_inst (tyenv env)) env" "vinv (tnorm_inst (tyenv env)) env (dvars dps)"
    unfolding gtyped_def by simp_all
  have ce: "closed_env env" by (rule wt_env_closed_env[OF w(1)])
  have bb: "bbelow env"
    unfolding bbelow_def
  proof (intro allI impI)
    fix x b assume "vt_lookup (tenv env) x = Some b"
    then obtain U u where "vt_lookup (tenv env) x = Some (U, u)" by (cases b) auto
    then have xU: "(x, U) \<in> evars env" unfolding evars_def bnds_def by (cases x) blast
    from w(2) have "below (maxidx env) (dvars dps \<union> evars env)" by (simp add: vinv_def)
    from belowD[OF this, of x U] xU show "snd x \<le> maxidx env" by simp
  qed
  have "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  moreover have "tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using kE that unfolding etvars_def bnds_def by blast
  ultimately have tv: "tvinv A env" unfolding tvinv_def by blast
  show ?thesis using ei tv ac ce bb by (simp add: einv_def)
qed

text \<open>Closed pairs that are well-typed and whose type variables are known are well-formed:\<close>

lemma ffres_of_typed:
  assumes ei: "einv A K env" and tk: "tknown A env (tdps tps)" and gt: "gtyped env (tdps tps)"
  shows "ffres A K (dvars (tdps tps)) env tps"
proof -
  let ?X = "dvars (tdps tps)" and ?KN = "tvars_env (tyenv env) \<union> A"
  have wi: "winv env ?X" using gt unfolding winv_def gtyped_def by blast
  have kn: "ttvars t \<union> ttvars u \<subseteq> ?KN" if "(t, u) \<in> set tps" for t u
    using tk that by (auto simp: tknown_tdps)
  have vX: "vtvars ?X \<subseteq> ?KN"
  proof
    fix p assume "p \<in> vtvars ?X"
    then obtain x T where xT: "(x, T) \<in> ?X" and p: "p \<in> tvars T" by (auto simp: vtvars_def)
    from xT obtain t u where tu: "(t, u) \<in> set tps" and v: "(x, T) \<in> vars t \<union> vars u"
      by (auto simp: dvars_def)
    from v p have "p \<in> vtvars (vars t) \<union> vtvars (vars u)" by (auto simp: vtvars_def)
    with vtvars_vars[of t] vtvars_vars[of u] kn[OF tu] show "p \<in> ?KN" by blast
  qed
  have "upok A env [] ?X t u" if tu: "(t, u) \<in> set tps" for t u
    unfolding upok_def
  proof (intro conjI allI impI)
    show "vars t \<union> vars u \<subseteq> ?X \<union> evars env" using tu by (force simp: dvars_def)
    show "ttvars t \<union> ttvars u \<union> btvars [] \<union> vtvars ?X \<subseteq> tvars_env (tyenv env) \<union> A"
      using kn[OF tu] vX by (auto simp: btvars_def)
    have dt: "dtyped \<rho> [([], t, u)]" if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using gt that tu unfolding gtyped_def by (auto simp: dtyped_def)
    show "\<not> loose_bvar t (ilength [])" "\<not> loose_bvar u (ilength [])"
      using dt[OF einv_rho0[OF ei]] by (simp_all add: dtyped_def)
    fix \<rho> assume "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    from dt[OF this] show "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T"
      by (simp add: dtyped_def)
  qed
  then show ?thesis using ei wi by (auto simp: ffres_def)
qed

text \<open>
  A step from a well-typed problem to a state in the type-level invariant, with an acyclic
  environment, is a result:
\<close>

lemma uresult_of_typed:
  assumes ds: "dstep env (tdps tus) env' (tdps tps)" and gt: "gtyped env (tdps tus)"
    and fK: "finite K'" and ei': "einv A' K' (tyonly env')" and tk': "tknown A' env' (tdps tps)"
    and ac': "acyc env'"
    and lo: "tvars_env (tyenv env) \<union> A \<subseteq> tvars_env (tyenv env') \<union> A'"
    and up: "tvars_env (tyenv env') \<union> A' \<subseteq> tvars_env (tyenv env) \<union> A \<union> {p. maxidx env < snd (fst p)}"
  shows "uresult A env tus (El_R env' tps)"
proof -
  let ?B = "A' \<union> A"
  have eq: "tvars_env (tyenv env') \<union> A' = tvars_env (tyenv env') \<union> ?B" using lo by blast
  have gt': "gtyped env' (tdps tps)" by (rule gtyped_dstep[OF ds gt])
  have kE: "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A'" using tk' by (simp add: tknown_def)
  have e1: "einv A' K' env'" by (rule einv_of_typed[OF ei' kE ac' gt'])
  have eB: "einv ?B K' env'" by (rule einv_known_cong[OF eq e1])
  have tkB: "tknown ?B env' (tdps tps)" using tk' unfolding tknown_def eq[symmetric] .
  have ff: "ffres ?B K' (dvars (tdps tps)) env' tps" by (rule ffres_of_typed[OF eB tkB gt'])
  have tn: "tnew A env ?B env'" unfolding tnew_def using up by blast
  show ?thesis by (rule uresultI[OF ds finite_dvars fK _ tn ff]) simp
qed


subsection \<open>Pattern unification\<close>

text \<open>Pattern unification of a list of pairs keeps the environment acyclic:\<close>

lemma foldM_unify_acyc:
  assumes f: "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) tus env) env'" and ac: "acyc env"
    and bl: "below (maxidx env) (dvars (tdps tus) \<union> evars env)"
  shows "acyc env'"
proof -
  interpret S: pure_sig alg ar ctab by (simp add: pure_sig_iff wf_algebra_axioms)
  have main: "acyc env2 \<and> below (maxidx env2) (X \<union> evars env2)"
    if "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) ps env1) env2" "acyc env1"
      "below (maxidx env1) (X \<union> (\<Union>(t, u)\<in>set ps. vars t \<union> vars u) \<union> evars env1)" for ps env1 env2 X
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
    have bl1: "below (maxidx env1) ((X \<union> ?Y) \<union> vars t \<union> vars u \<union> evars env1)"
      using Cons.prems(3) p by (simp add: Un_ac)
    have "S.step_ac env1 t u env3" using S.unif_acyc[of alg' "[]" t u env1] u1 by (simp add: unify_def)
    from S.step_acD[OF this Cons.prems(2) bl1]
    have a3: "acyc env3" "below (maxidx env3) (X \<union> ?Y \<union> evars env3)" by blast+
    from Cons.IH[OF r a3] show ?case .
  qed
  have "dvars (tdps tus) = (\<Union>(t, u)\<in>set tus. vars t \<union> vars u)" by (force simp: dvars_def)
  with main[OF f ac, of "{}"] bl show ?thesis by simp
qed

text \<open>The invariant of pattern unification holds on a well-formed problem:\<close>

lemma sinv_pinv:
  assumes si: "sinv A K X env (tdps tus)"
  shows "pinv A K env" "\<forall>(t, u)\<in>set tus. tkn A env [] t \<and> tkn A env [] u"
proof -
  have ei: "einv A K env" and wi: "winv env X" and p: "\<forall>(t, u)\<in>set tus. upok A env [] X t u"
    using si by (auto simp: sinv_def)
  note et = einv_tyonly[OF ei] and r0 = einv_rho0[OF ei]
  let ?\<rho> = "tnorm_inst (tyenv env)" and ?KN = "tvars_env (tyenv env) \<union> A"
  have kE: "etvars env \<subseteq> ?KN" by (rule tvinv_etvars[OF einvD(1)[OF ei]])
  have w: "wt_env ?\<rho> env" using winvD[OF wi r0] by blast
  have cert: "cert_typ alg ar T" if ty: "e \<turnstile> inst ?\<rho> t : V" and T: "T \<in> ctyps t" and k: "ttvars t \<subseteq> ?KN"
    for e t V T
  proof -
    have Tt: "T \<in> typs t" using ctyps_typs T by blast
    then have "tsubst ?\<rho> T \<in> typs (inst ?\<rho> t)" by (simp add: typs_inst)
    from typing_typs[OF ty this] have c: "cert_typ alg ar (tsubst ?\<rho> T)" .
    have "tvars T \<subseteq> ?KN" using Tt k by (auto simp: ttvars_def)
    from known_cert[OF et this c] show ?thesis by (simp add: cert_typ_def)
  qed
  have "cert_typ alg ar T" if "T \<in> ectyps env" for T
  proof -
    from that obtain x U u where b: "vt_lookup (tenv env) x = Some (U, u)" and T: "T \<in> ctyps u"
      unfolding ectyps_def bnds_def by blast
    have "ttvars u \<subseteq> ?KN" using etvarsI[OF b] kE by blast
    from cert[OF wt_envD[OF w b] T this] show ?thesis .
  qed
  then show "pinv A K env" using et kE by (simp add: pinv_def)
  show "\<forall>(t, u)\<in>set tus. tkn A env [] t \<and> tkn A env [] u"
  proof (clarify)
    fix t u assume "(t, u) \<in> set tus"
    with p have pk: "upok A env [] X t u" by blast
    note d = upokD[OF pk]
    from d(9)[OF r0] obtain e V where ty: "e \<turnstile> inst ?\<rho> t : V" "e \<turnstile> inst ?\<rho> u : V" by blast
    show "tkn A env [] t \<and> tkn A env [] u"
      unfolding tkn_def using d(3,4) cert[OF ty(1) _ d(3)] cert[OF ty(2) _ d(4)] by (auto simp: btvars_def)
  qed
qed


subsection \<open>The search\<close>

theorem hounifiers_ev_uresult:
  assumes cfg: "cfg_alg cfg = alg" and fK: "finite K" and et: "einv A K (tyonly env)"
    and tk: "tknown A env (tdps tus)" and gt: "gtyped env (tdps tus)" and ac: "acyc env"
    and ev: "ev cfg (hounifiers [] env tus) x"
  shows "uresult A env tus x"
proof -
  let ?Q = "tvars_env (tyenv env) \<union> A" and ?m0 = "maxidx env" and ?dps = "tdps tus"
  let ?NI = "\<lambda>e dps. gtyped e dps \<and> tst True ?Q ?m0 ?Q e dps"
  have ni: "ninv e dps" if "?NI e dps" for e dps using that tst_tyinv unfolding ninv_def by blast
  have NI0: "?NI env ?dps"
  proof
    show "tst True ?Q ?m0 ?Q env ?dps" by (rule tstI[OF fK et tk]) (simp_all add: ac tub_def)
  qed (rule gt)
  have simpl: "\<exists>A' K'. finite K' \<and> ?Q \<subseteq> tvars_env (tyenv env1) \<union> A' \<and> einv A' K' (tyonly env1) \<and>
      tknown A' env1 (frs @ ffs) \<and> tub ?Q ?m0 A' env1 \<and> acyc env1 \<and> gtyped env1 (frs @ ffs)"
    if n: "?NI e dps" and s: "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, frs)" for e dps env1 ffs frs
  proof -
    from n obtain A' K' where g: "gtyped e dps" and fK': "finite K'" and P: "?Q \<subseteq> tvars_env (tyenv e) \<union> A'"
      and ei': "einv A' K' (tyonly e)" and tk': "tknown A' e dps" and ub': "tub ?Q ?m0 A' e" and ac': "acyc e"
      unfolding tst_def by blast
    from SIMPL_inv[OF fK' s[unfolded cfg] ei' tk' g]
    have ei1: "einv A' K' (tyonly env1)" and tk1: "tknown A' env1 (frs @ ffs)" and g1: "tgrow A' e env1"
      by auto
    have "acyc env1" using SIMPL_acyc[OF s] ac' by blast
    moreover have "gtyped env1 (frs @ ffs)" by (rule gtyped_dstep[OF SIMPL_sound[OF s] g])
    moreover have "tub ?Q ?m0 A' env1" by (rule tub_tgrow[OF ub' g1])
    moreover have "?Q \<subseteq> tvars_env (tyenv env1) \<union> A'" using P tgrowD(1)[OF g1] by blast
    ultimately show ?thesis using fK' ei1 tk1 by blast
  qed
  have NM: "\<And>e dps env1 ffs dp frs. ?NI e dps \<Longrightarrow> okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs) \<Longrightarrow>
      MATCH_ok env1 dp"
    using ninv_SIMPL_MATCH_ok[OF cfg ni] by blast
  have NS: "\<And>e dps env1 ffs dp frs ms env2 dps2. ?NI e dps \<Longrightarrow>
      okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs) \<Longrightarrow> okW (MATCH cfg env1 dp (frs @ ffs)) ms \<Longrightarrow>
      ev cfg ms (El_E env2 dps2) \<Longrightarrow> ?NI env2 dps2"
  proof -
    fix e dps env1 ffs dp frs ms env2 dps2
    assume n: "?NI e dps" and s: "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, dp # frs)"
      and m: "okW (MATCH cfg env1 dp (frs @ ffs)) ms" and e2: "ev cfg ms (El_E env2 dps2)"
    from simpl[OF n s] obtain A' K' where fK': "finite K'" and P: "?Q \<subseteq> tvars_env (tyenv env1) \<union> A'"
      and ei1: "einv A' K' (tyonly env1)" and tk1: "tknown A' env1 (dp # frs @ ffs)"
      and ub1: "tub ?Q ?m0 A' env1" and ac1: "acyc env1" and gt1: "gtyped env1 (dp # frs @ ffs)"
      by auto
    have mo: "MATCH_ok env1 dp" by (rule NM[OF n s])
    have sq: "seqinv (GE env1 (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF m mo])
    have ts: "tseq True ?Q ?m0 (tvars_env (tyenv env1) \<union> A') ms"
      by (rule MATCH_tseq[OF m mo cfg fK' ei1 tk1 gt1 _ ub1]) (simp add: ac1)
    from tseq_ev[OF cfg e2 ts sq gt1] obtain env' dps' where "El_E env2 dps2 = El_E env' dps'"
      "tst True ?Q ?m0 (tvars_env (tyenv env1) \<union> A') env' dps'" by blast
    then have "tst True ?Q ?m0 ?Q env2 dps2" using tst_mono[OF _ P] by simp
    moreover have "gtyped env2 dps2" by (rule gtyped_dstep[OF _ gt1]) (use ev_sound[OF e2 sq] in simp)
    ultimately show "?NI env2 dps2" by blast
  qed
  from hounifiers_ev_sound_loose[OF cfg ni[OF NI0] ev] obtain envR tps where x: "x = El_R envR tps"
    and ds: "dstep env ?dps envR (tdps tps)" by (cases x) auto
  have sg: "sgood ?NI cfg env ?dps (S_AddUnify 1 env ?dps S_Empty)"
    by (intro sgood.AddUnify sgood.Empty dstep_refl) (rule NI0)
  have "\<exists>e dps env1 ffs. ?NI e dps \<and> okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, []) \<and>
      okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (envR, tps)"
    by (rule ev_sgood_R[where NI = ?NI, OF NM NS ev[unfolded hounifiers_def x] sg refl])
  then obtain e dps env1 ffs where n: "?NI e dps" and s: "okW (SIMPL (cfg_alg cfg) e dps) (env1, ffs, [])"
    and f: "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (envR, tps)"
    by blast
  from simpl[OF n s] obtain A' K' where fK': "finite K'" and P: "?Q \<subseteq> tvars_env (tyenv env1) \<union> A'"
    and ei1: "einv A' K' (tyonly env1)" and tk1: "tknown A' env1 ffs" and ub1: "tub ?Q ?m0 A' env1"
    and ac1: "acyc env1" and gt1: "gtyped env1 ffs"
    by auto
  from foldrW_add_ffpair_known[OF fK' f[unfolded cfg] ei1] tk1 gt1
  have eiR: "einv A' K' (tyonly envR)" and tkR: "tknown A' envR (tdps tps)" and gR: "tgrow A' env1 envR"
    by simp_all
  have "below (maxidx env1) ({} \<union> dvars ffs \<union> evars env1)" using state_below[OF gt1 ei1] by simp
  from foldrW_add_ffpair_acyc[OF f ac1 this] have acR: "acyc envR" by simp
  have ubR: "tub ?Q ?m0 A' envR" by (rule tub_tgrow[OF ub1 gR])
  show ?thesis unfolding x
  proof (rule uresult_of_typed[OF ds gt fK' eiR tkR acR])
    show "?Q \<subseteq> tvars_env (tyenv envR) \<union> A'" using P tgrowD(1)[OF gR] by blast
    show "tvars_env (tyenv envR) \<union> A' \<subseteq> ?Q \<union> {p. maxidx env < snd (fst p)}" using ubR by (simp add: tub_def)
  qed
qed


subsection \<open>The unifiers\<close>

text \<open>
  Every element of the enumeration of \<^const>\<open>unifiers\<close> on a well-formed problem is a result in
  the invariant, whatever names its environment binds, and whether or not the enumeration is
  finite:
\<close>

theorem unifiers_ev_uresult:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and ev: "ev cfg s x"
  shows "uresult A env tus x"
proof -
  have ei: "einv A K env" and p: "\<forall>(t, u)\<in>set tus. upok A env [] X t u"
    using si by (auto simp: sinv_def)
  note et = einv_tyonly[OF ei] and gt = sinv_gtyped[OF si] and pi = sinv_pinv[OF si]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have kE: "etvars env \<subseteq> ?KN" by (rule tvinv_etvars[OF einvD(1)[OF ei]])
  have "ttvars t \<union> ttvars u \<subseteq> ?KN" if "(t, u) \<in> set tus" for t u
    using p that upokD(3,4)[of A env "[]" X t u] by blast
  with kE have tk: "tknown A env (tdps tus)" by (fastforce simp: tknown_tdps)
  have ac: "acyc env" by (rule einvD(3)[OF ei])
  let ?m = "foldM (\<lambda>(t, u) env. unify alg t u env) tus env"
  from u obtain r where r: "?m = Some r" by (cases ?m) (simp_all add: unifiers_def handle_def bindM_def)
  show ?thesis
  proof (cases r)
    case (Ok env')
    with r u have s: "s = S_Single (El_R env' [])"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    with ev have x: "x = El_R env' []" by (auto elim: ev_SingleE)
    have okm: "ok ?m env'" using r Ok by simp
    have ds: "dstep env (tdps tus) env' (tdps [])" using foldM_unify_dstep[OF okm] by simp
    from foldM_unify_typed[OF okm fin(2) pi] have p': "pinv A K env'" and g: "tgrow A env env'" by blast+
    have ac': "acyc env'" by (rule foldM_unify_acyc[OF okm ac]) (use state_below[OF gt et] in simp)
    show ?thesis unfolding x
    proof (rule uresult_of_typed[OF ds gt fin(2) pinvD(1)[OF p'] _ ac'])
      show "tknown A env' (tdps [])" using pinvD(2)[OF p'] by (simp add: tknown_def)
      show "?KN \<subseteq> tvars_env (tyenv env') \<union> A" using tgrowD(1)[OF g] by blast
      show "tvars_env (tyenv env') \<union> A \<subseteq> ?KN \<union> {p. maxidx env < snd (fst p)}"
        using tgrowD(3)[OF g] by (auto simp: tnew_def)
    qed
  next
    case (Err e)
    show ?thesis
    proof (cases "e = Pattern")
      case True
      with r u Err have s: "s = hounifiers [] env tus"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      from hounifiers_ev_uresult[OF cfg fin(2) et tk gt ac ev[unfolded s]] show ?thesis .
    next
      case False
      with r u Err have "s = S_Empty"
        by (cases e) (simp_all add: unifiers_def handle_def bindM_def return_def raise_def)
      with ev show ?thesis by (auto elim: ev_EmptyE)
    qed
  qed
qed

end

end
