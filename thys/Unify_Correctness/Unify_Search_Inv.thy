section \<open>An Invariant of the Search for Names with Several Types\<close>

theory Unify_Search_Inv
  imports Unify_Ghost Unify_Smash_Sound
begin

text \<open>
  The soundness of the search (@{thm [source] pure_sig_gen.hounifiers_ev_sound}) needs an
  invariant of the nodes that gives the hypothesis \<open>MATCH_ok\<close> of \<open>MATCH\<close>. The typing part of it
  (\<open>gtyped\<close>: the pairs are well-typed at every certified solution of the type environment) is
  kept by every step. The rest is about types only: the type environment is well-formed and the
  type variables of the pairs and of the bindings are known (\<open>tyinv\<close>). It is stated for the
  type environment alone (\<open>tyonly\<close>: the environment without its bindings), so that the term
  environment, and with it the names of the variables, plays no role.

  Proved here: the invariant gives \<open>MATCH_ok\<close> (\<open>ninv_MATCH_ok\<close>) and is kept by every result
  of \<open>SIMPL\<close> (\<open>SIMPL_inv\<close>), by induction on the computation. The soundness of the search
  (\<open>hounifiers_ev_sound_ninv\<close>) takes as a hypothesis that the elements enumerated by
  \<open>MATCH\<close> keep the type-level part; theory \<open>Unify_Match_Inv\<close> proves it
  (\<open>MATCH_tyinv\<close>, \<open>hounifiers_ev_sound_loose\<close>).
\<close>

definition tyonly :: "env \<Rightarrow> env" where
  "tyonly env = Envir (maxidx env) vt_empty (tyenv env)"

lemma tyonly_simps [simp]:
  "tenv (tyonly env) = vt_empty" "tyenv (tyonly env) = tyenv env" "maxidx (tyonly env) = maxidx env"
  by (simp_all add: tyonly_def)

subsection \<open>Computations on types depend on the type environment only\<close>

lemma body_type_tyenv_eq:
  assumes "body_type env T = Some r"
  shows "tyenv env' = tyenv env \<Longrightarrow> body_type env' T = Some r"
  using assms
proof (induction env T r rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
    using "1.hyps" "1.prems" "1.IH"
    by (subst body_type.simps) (auto simp: bindM_def split: ptyp.splits list.splits if_splits option.splits xres.splits)
qed

lemma body_type_cong:
  assumes "tyenv env' = tyenv env"
  shows "body_type env' T = body_type env T"
proof (cases "body_type env T")
  case (Some r)
  from body_type_tyenv_eq[OF Some assms] Some show ?thesis by simp
next
  case None
  show ?thesis
  proof (cases "body_type env' T")
    case (Some r)
    from body_type_tyenv_eq[OF Some assms[symmetric]] None show ?thesis by simp
  qed (use None in simp)
qed

lemma binder_types_tyenv_eq:
  assumes "binder_types env T = Some r"
  shows "tyenv env' = tyenv env \<Longrightarrow> binder_types env' T = Some r"
  using assms
proof (induction env T r rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
    using "1.hyps" "1.prems" "1.IH"
    by (subst binder_types.simps) (auto simp: bindM_def split: ptyp.splits list.splits if_splits option.splits xres.splits)
qed

lemma binder_types_cong:
  assumes "tyenv env' = tyenv env"
  shows "binder_types env' T = binder_types env T"
proof (cases "binder_types env T")
  case (Some r)
  from binder_types_tyenv_eq[OF Some assms] Some show ?thesis by simp
next
  case None
  show ?thesis
  proof (cases "binder_types env' T")
    case (Some r)
    from binder_types_tyenv_eq[OF Some assms[symmetric]] None show ?thesis by simp
  qed (use None in simp)
qed

lemma env_fastype_cong:
  assumes "tyenv env' = tyenv env"
  shows "env_fastype env' Ts t = env_fastype env Ts t"
  by (induction t arbitrary: Ts) (simp_all add: assms)

lemma fastype_cong:
  assumes "tyenv env' = tyenv env"
  shows "fastype env' rb t = fastype env rb t"
  unfolding fastype_def by (rule env_fastype_cong[OF assms])

context pure_sig_gen
begin

lemma rsat_cong:
  assumes "tyenv env' = tyenv env"
  shows "rsat env' rb t u \<longleftrightarrow> rsat env rb t u"
  using fastype_cong[OF assms] body_type_cong[OF assms] assms by (simp add: rsat_def)

lemma msat_ok_cong:
  assumes "tyenv env' = tyenv env"
  shows "msat_ok env' dp \<longleftrightarrow> msat_ok env dp"
  using binder_types_cong[OF assms] rsat_cong[OF assms] by (simp add: msat_ok_def split: prod.splits)

lemma MATCH_ok_tyonly: "MATCH_ok (tyonly env) dp \<Longrightarrow> MATCH_ok env dp"
  unfolding MATCH_ok_def
proof (intro allI impI)
  fix env2 assume m: "\<forall>env'. extends (tyonly env) env' \<longrightarrow> tenv env' = tenv (tyonly env) \<longrightarrow> msat_ok env' dp"
    and ext: "extends env env2" and te: "tenv env2 = tenv env"
  have "extends (tyonly env) (tyonly env2)" using ext by (simp add: extends_def)
  with m have "msat_ok (tyonly env2) dp" by simp
  then show "msat_ok env2 dp" by (simp only: msat_ok_cong[of "tyonly env2" env2, simplified])
qed

subsection \<open>The invariant\<close>

text \<open>The type variables of the pairs and of the bindings are known:\<close>

definition tknown :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "tknown A env dps \<longleftrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>(rb, t, u)\<in>set dps. ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A)"

definition tyinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "tyinv A K env dps \<longleftrightarrow> finite K \<and> einv A K (tyonly env) \<and> tknown A env dps"

definition ninv :: "env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "ninv env dps \<longleftrightarrow> gtyped env dps \<and> (\<exists>A K. tyinv A K env dps)"

lemma tknown_mono: "tknown A env dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> tknown A env dps'"
  unfolding tknown_def by blast

lemma wt_env_tyonly [simp]: "wt_env \<rho> (tyonly env)"
  by (simp add: wt_env_def)

lemma evars_tyonly [simp]: "evars (tyonly env) = {}"
  by (simp add: evars_def bnds_def)

text \<open>The hypothesis of \<^const>\<open>MATCH\<close> at a node of the search:\<close>

lemma ninv_MATCH_ok:
  assumes ni: "ninv env ((rb, t, u) # dps)" and sh: "frs_shape (rb, t, u)"
  shows "MATCH_ok env (rb, t, u)"
proof -
  from ni obtain A K where gt: "gtyped env ((rb, t, u) # dps)" and ti: "tyinv A K env ((rb, t, u) # dps)"
    unfolding ninv_def by blast
  from ti have fK: "finite K" and ei: "einv A K (tyonly env)" and tk: "tknown A env ((rb, t, u) # dps)"
    unfolding tyinv_def by blast+
  let ?X = "vars t \<union> vars u"
  let ?e = "tyonly env"
  have G: "wt_env \<rho> env \<and> dtyped \<rho> ((rb, t, u) # dps) \<and> vinv \<rho> env (dvars ((rb, t, u) # dps))"
    if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
    using gt that unfolding gtyped_def by blast
  have wi: "winv ?e ?X"
    unfolding winv_def
  proof (intro allI impI conjI)
    fix \<rho> assume r: "tsol (tyenv ?e) \<rho>" "cert_inst \<rho>"
    show "wt_env \<rho> ?e" by simp
    from G[OF r[simplified]] have "vinv \<rho> env (dvars ((rb, t, u) # dps))" by blast
    then show "vinv \<rho> ?e ?X" by (auto simp: vinv_def intro: vcons_mono below_mono)
  qed
  have p: "upok A ?e rb ?X t u"
    unfolding upok_def
  proof (intro conjI allI impI)
    show "vars t \<union> vars u \<subseteq> ?X \<union> evars ?e" by simp
    have "vtvars ?X \<subseteq> ttvars t \<union> ttvars u" using vtvars_vars[of t] vtvars_vars[of u] by (auto simp: vtvars_def)
    then show "ttvars t \<union> ttvars u \<union> btvars rb \<union> vtvars ?X \<subseteq> tvars_env (tyenv ?e) \<union> A"
      using tk by (auto simp: tknown_def)
    have r0: "tsol (tyenv env) (tnorm_inst (tyenv env))" "cert_inst (tnorm_inst (tyenv env))"
      using einv_rho0[OF ei] by simp_all
    from G[OF r0] show "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" by auto
    fix \<rho> assume r: "tsol (tyenv ?e) \<rho>" "cert_inst \<rho>"
    from G[OF r[simplified]] show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T" by auto
  qed
  have si: "sinv A K ?X ?e [(rb, t, u)]" using ei wi p by (simp add: sinv_def)
  from sinv_MATCH_ok[OF sh si] show ?thesis by (rule MATCH_ok_tyonly)
qed

subsection \<open>Type unification\<close>

lemma xokW_okW: "xokW E m P \<Longrightarrow> okW m x \<Longrightarrow> P x"
  by (auto simp: xokW_def)

lemma cunify_types_tyonly:
  assumes "okW (cunify_types alg' T U env) env1"
  shows "okW (cunify_types alg' T U (tyonly env)) (tyonly env1)" "tenv env1 = tenv env"
proof -
  show te: "tenv env1 = tenv env" by (rule cunify_types_sound(1)[OF assms])
  have u: "ok (unify_types alg' T U env) env1" using assms by (simp add: cunify_types_ok)
  have "ok (unify_types alg' T U (tyonly env)) (tyonly env1)"
  proof (cases "T = U")
    case True
    with u show ?thesis by (simp add: unify_types_def return_def)
  next
    case False
    have nh: False if "ok (case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U)) | _ \<Rightarrow> raise e) y"
      for e and y :: env
      using that by (cases e) auto
    with u False obtain tye' n' where tu: "ok (type_unify alg' U T (tyenv env, maxidx env)) (tye', n')"
      and e1: "env1 = Envir n' (tenv env) tye'"
      by (auto simp: unify_types_def ok_handle split: prod.splits dest: nh)
    show ?thesis using False tu by (simp add: e1 unify_types_def ok_handle tyonly_def)
  qed
  then show "okW (cunify_types alg' T U (tyonly env)) (tyonly env1)" by (simp add: cunify_types_ok)
qed

lemma known_cert:
  assumes ei: "einv A K (tyonly env)" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tsubst \<rho> T)"
  shows "wft ar T" "sorts_ok alg T"
  using cert_typ_rev[OF ei, of \<rho> T] c tv by simp_all

lemma tyinv_cunify:
  assumes cu: "okW (cunify_types alg T U env) env1" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tsubst \<rho> T)"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tsubst \<rho>' U)"
  shows "einv A K (tyonly env1)" "tenv env1 = tenv env" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    "maxidx env \<le> maxidx env1" "textends (tyenv env) (tyenv env1)"
    "\<And>\<rho>. tsol (tyenv env1) \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  note c = cunify_types_tyonly[OF cu]
  have tT: "tvars T \<subseteq> tvars_env (tyenv (tyonly env)) \<union> A" and tU: "tvars U \<subseteq> tvars_env (tyenv (tyonly env)) \<union> A"
    using T(1) U(1) by simp_all
  note kT = known_cert[OF ei T] and kU = known_cert[OF ei U]
  from xokW_okW[OF cunify_types_term[OF ei fK tT kT tU kU] c(1)]
  show "einv A K (tyonly env1)" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "maxidx env \<le> maxidx env1"
    "textends (tyenv env) (tyenv env1)" "\<And>\<rho>. tsol (tyenv env1) \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by simp_all
  show "tenv env1 = tenv env" by (rule c(2))
qed

subsection \<open>Head normalization of a pair\<close>

lemma gtyped_rho0:
  assumes "gtyped env dps" "einv A K (tyonly env)"
  shows "wt_env (tnorm_inst (tyenv env)) env" "dtyped (tnorm_inst (tyenv env)) dps"
  using assms einv_rho0[of A K "tyonly env"] unfolding gtyped_def by simp_all

lemma tknown_pair:
  "tknown A env [(rb, t, u)] \<longleftrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  by (simp add: tknown_def)

lemma tknown_ext:
  "tknown A env dps \<Longrightarrow> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<Longrightarrow> etvars env1 \<subseteq> tvars_env (tyenv env1) \<union> A \<Longrightarrow>
    tknown A env1 dps"
  unfolding tknown_def by blast

lemma etvars_tenv: "tenv env1 = tenv env \<Longrightarrow> etvars env1 = etvars env"
  by (simp add: etvars_def bnds_def)

lemma new_dpair_inv:
  "okW (new_dpair al rb t u env) ((rb', t', u'), env') \<Longrightarrow> al = alg \<Longrightarrow> finite K \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow>
    tknown A env [(rb, t, u)] \<Longrightarrow> gtyped env [(rb, t, u)] \<Longrightarrow>
    einv A K (tyonly env') \<and> tknown A env' [(rb', t', u')] \<and> tenv env' = tenv env \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof (induction al rb t u env arbitrary: rb' t' u' env' rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  note al = "1.prems"(2) and fK = "1.prems"(3) and ei = "1.prems"(4) and tk = "1.prems"(5) and gt = "1.prems"(6)
  let ?c = "if a = STR '''' then b else a"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types al T U env) env1"
    and r: "okW (new_dpair al ((?c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: Let_def)
  let ?\<rho> = "tnorm_inst (tyenv env)"
  have cT: "cert_typ alg ar (tsubst ?\<rho> T)" and cU: "cert_typ alg ar (tsubst ?\<rho> U)"
    using gtyped_rho0(2)[OF gt ei] by (auto simp del: tsubst_tnorm_inst)
  from tk have kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and kU: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    by (auto simp: tknown_pair ttvars_def)
  note c = tyinv_cunify[OF cu[unfolded al] fK ei kT cT kU cU]
  have gt1: "gtyped env1 [((?c, T) # rb, body1, body2)]"
    by (rule gtyped_dstep[OF dstep_trans[OF cunify_types_dstep[OF cu] dstep_Abs[OF refl extends_refl]] gt])
  have tk1: "tknown A env1 [((?c, T) # rb, body1, body2)]"
    using tk c(2,3) etvars_tenv[OF c(2)] by (auto simp: tknown_pair ttvars_def btvars_def)
  from "1.IH"[OF cu refl r al fK c(1) tk1 gt1] c(2,3) show ?case by auto
qed (auto simp: raiseW_def)

lemma head_norm_dpair_inv:
  assumes hn: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')" and fK: "finite K"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env [(rb, t, u)]" and gt: "gtyped env [(rb, t, u)]"
  shows "einv A K (tyonly env') \<and> tknown A env' [(rb', t', u')] \<and> tenv env' = tenv env \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof -
  from hn obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env rb t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env rb u1) u2" and
    nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def)
  have d1: "dstep env [(rb, t, u)] env [(rb, t1, u1)]"
    by (rule tconv_dstep[OF head_norm_tconv[OF ht] head_norm_tconv[OF hu]])
  have gt1: "gtyped env [(rb, t1, u1)]" by (rule gtyped_dstep[OF d1 gt])
  have d2: "dstep env [(rb, t1, u1)] env [(rb, t2, u2)]"
    by (rule tconv_dstep[OF eta_norm_tconv[OF et] eta_norm_tconv[OF eu]])
  have gt2: "gtyped env [(rb, t2, u2)]" by (rule gtyped_dstep[OF d2 gt1])
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have kE: "etvars env \<subseteq> ?KN" using tk by (simp add: tknown_def)
  have k1: "ttvars t1 \<union> btvars rb \<subseteq> ?KN" "ttvars u1 \<union> btvars rb \<subseteq> ?KN"
    using head_norm_ttvars[OF ht refl] head_norm_ttvars[OF hu refl] tk kE by (auto simp: tknown_pair)
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  from gtyped_rho0(2)[OF gt1 ei] obtain e T where bs: "bs_env (tnorm_inst (tyenv env)) e rb"
    and ty: "e \<turnstile> inst (tnorm_inst (tyenv env)) t1 : T" "e \<turnstile> inst (tnorm_inst (tyenv env)) u1 : T"
    and lb: "\<not> loose_bvar t1 (ilength rb)" "\<not> loose_bvar u1 (ilength rb)"
    by auto
  from eta_norm_term[OF ti refl ty(1) bs lb(1) k1(1)] et have k2t: "ttvars t2 \<subseteq> ?KN" by (auto simp: return_def)
  from eta_norm_term[OF ti refl ty(2) bs lb(2) k1(2)] eu have k2u: "ttvars u2 \<subseteq> ?KN" by (auto simp: return_def)
  have tk2: "tknown A env [(rb, t2, u2)]" using k2t k2u k1 kE by (auto simp: tknown_pair)
  from new_dpair_inv[OF nd refl fK ei tk2 gt2] show ?thesis .
qed

subsection \<open>Assignments\<close>

lemma etvars_update:
  "ok (update (F, T) b env) env' \<Longrightarrow> etvars env' = tvars T \<union> ttvars b \<union> etvars env"
  by (auto simp: etvars_def bnds_update)

lemma tyonly_update: "ok (update (F, T) b env) env' \<Longrightarrow> tyonly env' = tyonly env"
  using ok_update(3,4)[of F T b env env'] by (simp add: tyonly_def)

lemma assignment_inv:
  assumes a: "okW (assignment alg rb t u env) env'" and fK: "finite K"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env [(rb, t, u)]" and gt: "gtyped env [(rb, t, u)]"
  shows "einv A K (tyonly env') \<and> etvars env' \<subseteq> tvars_env (tyenv env') \<union> A \<and>
    tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof -
  have "\<exists>v T T1 T2 env1. okW (get_eta_var rb 0 t) (v, T) \<and> ok (body_type env T) T1 \<and>
      ok (fastype env rb u) T2 \<and> okW (cunify_types alg T1 T2 env) env1 \<and>
      ok (update (v, T) (rlist_abs rb u) env1) env'"
    using a by (auto simp: assignment_def split: occ.split_asm) (metis occ.exhaust)
  then obtain v T T1 T2 env1 where gev: "okW (get_eta_var rb 0 t) (v, T)" and bt: "ok (body_type env T) T1"
    and ft: "ok (fastype env rb u) T2" and cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by blast
  let ?\<theta> = "tyenv env" and ?\<rho> = "tnorm_inst (tyenv env)" and ?KN = "tvars_env (tyenv env) \<union> A"
  have ti: "tinv ar (maxidx env) ?\<theta> A" using einvD(2)[OF ei] by simp
  define "is" where "is = rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb])"
  have t: "t = app (Var v T) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have kt: "ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> ?KN" and kE: "etvars env \<subseteq> ?KN"
    using tk by (simp_all add: tknown_pair)
  have kT: "tvars T \<subseteq> ?KN" using kt by (auto simp: t ttvars_def app_apps typs_apps)
  from gtyped_rho0(2)[OF gt ei] obtain e0 W where bs: "bs_env ?\<rho> e0 rb"
    and tyt: "e0 \<turnstile> inst ?\<rho> t : W" and tyu: "e0 \<turnstile> inst ?\<rho> u : W"
    and lbu: "\<not> loose_bvar u (ilength rb)"
    by auto
  from body_type_term[OF ti refl kT] bt have kT1: "tvars T1 \<subseteq> ?KN" by (auto simp: return_def)
  have tvu: "ttvars u \<union> btvars rb \<subseteq> ?KN" using kt by blast
  from env_fastype_term[OF ti refl tyu bs lbu tvu] ft obtain T2' where
    f2: "env_fastype env (map snd rb) u = return T2'" "tvars T2' \<subseteq> ?KN" "tnorm ?\<theta> T2' = W"
    by blast
  have T2: "T2 = T2'" using ft f2(1) by (simp add: fastype_def return_def)
  have kT2: "tvars T2 \<subseteq> ?KN" using f2(2) T2 by simp
  have c2: "cert_typ alg ar (tsubst ?\<rho> T2)" using bs_env_cert[OF bs tyu lbu] f2(3) T2 by simp
  from binder_types_term[OF ti refl kT] obtain Ts where bts: "binder_types env T = return Ts" by blast
  have r0: "tsol ?\<theta> ?\<rho>" using einv_rho0(1)[OF ei] by simp
  have "tsubst ?\<rho> T = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> T1"
    by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt r0])
  moreover have "cert_typ alg ar (tsubst ?\<rho> T)"
  proof -
    from tyt obtain Us where "e0 \<turnstile> Var v (tsubst ?\<rho> T) : Us"
      by (auto simp: t app_apps inst_apps dest!: list_app_typeD)
    then show ?thesis by auto
  qed
  ultimately have c1: "cert_typ alg ar (tsubst ?\<rho> T1)" by (simp add: cert_typ_funs)
  note c = tyinv_cunify[OF cu fK ei kT1 c1 kT2 c2]
  have ei': "einv A K (tyonly env')" using c(1) tyonly_update[OF upd] by simp
  have te': "tyenv env' = tyenv env1" using ok_update(3)[OF upd] .
  have "btvars (rev rb) = btvars rb" by (simp add: btvars_def)
  then have "ttvars (rlist_abs rb u) \<subseteq> ?KN" using kt by (auto simp: rlist_abs_abs_list ttvars_abs_list)
  then have "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A"
    using etvars_update[OF upd] etvars_tenv[OF c(2)] kE kT c(3) te' by auto
  with ei' c(3) te' show ?thesis by simp
qed

subsection \<open>Simplification\<close>

lemma gtyped_swap: "gtyped env [(bs, t, u)] \<Longrightarrow> gtyped env [(bs, u, t)]"
  by (rule gtyped_dstep[OF dstep_swap_out[OF dstep_refl[of env "[(bs, t, u)]"]]])

lemma tknown_append: "tknown A env xs \<Longrightarrow> tknown A env ys \<Longrightarrow> tknown A env (xs @ ys)"
  unfolding tknown_def by auto

lemma tknown_perm: "tknown A env xs \<Longrightarrow> set ys = set xs \<Longrightarrow> tknown A env ys"
  by (rule tknown_mono) auto

lemma tknown_swap: "tknown A env [(bs, t, u)] \<Longrightarrow> tknown A env [(bs, u, t)]"
  by (auto simp: tknown_pair)

lemma head_body_cert:
  assumes ei: "einv A K (tyonly env)" and kt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and hd: "head_of t = Var v T" and ty: "e \<turnstile> inst (tnorm_inst (tyenv env)) t : W"
    and bt: "ok (body_type env T) T'"
  shows "tvars T' \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tsubst (tnorm_inst (tyenv env)) T')"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  have ti: "tinv ar (maxidx env) (tyenv env) A" using einvD(2)[OF ei] by simp
  have kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using ttvars_head[of t] hd kt by (auto simp: ttvars_def)
  from body_type_term[OF ti refl kT] bt show "tvars T' \<subseteq> tvars_env (tyenv env) \<union> A" by (auto simp: return_def)
  from binder_types_term[OF ti refl kT] obtain Ts where bts: "binder_types env T = return Ts" by blast
  have r0: "tsol (tyenv env) ?\<rho>" using einv_rho0(1)[OF ei] by simp
  have "tsubst ?\<rho> T = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> T'"
    by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt r0])
  moreover have "cert_typ alg ar (tsubst ?\<rho> T)"
  proof -
    have "t = Var v T \<degree>\<degree> snd (strip_comb t)" using t_apps[of t] hd by simp
    with ty obtain Us where "e \<turnstile> Var v (tsubst ?\<rho> T) : Us"
      by (metis inst_apps inst.simps(3) list_app_typeD)
    then show ?thesis by auto
  qed
  ultimately show "cert_typ alg ar (tsubst ?\<rho> T')" by (simp add: cert_typ_funs)
qed

lemma gtyped_args:
  assumes gt: "gtyped env [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]" and len: "length ss = length ts"
    and heads: "\<And>\<rho> e U U'. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> e \<turnstile> inst \<rho> h : U \<Longrightarrow> e \<turnstile> inst \<rho> h' : U' \<Longrightarrow>
      inst \<rho> h = inst \<rho> h'"
  shows "gtyped env (dzip bs ss ts)"
  unfolding gtyped_def
proof (intro allI impI conjI)
  fix \<rho> assume r: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  from gt r have w: "wt_env \<rho> env" and d: "dtyped \<rho> [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]"
    and v: "vinv \<rho> env (dvars [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)])"
    unfolding gtyped_def by blast+
  show "wt_env \<rho> env" by (rule w)
  from d[unfolded dtyped_simps] obtain e T where bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T"
    and tyt: "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T" and lbs: "\<not> loose_bvar (h \<degree>\<degree> ss) (ilength bs)"
    and lbt: "\<not> loose_bvar (h' \<degree>\<degree> ts) (ilength bs)"
    by blast
  from tys obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" and tss: "e \<tturnstile> map (inst \<rho>) ss : Us"
    by (auto simp: inst_apps elim: list_app_typeE)
  from tyt obtain Us' where th': "e \<turnstile> inst \<rho> h' : Us' \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
    by (auto simp: inst_apps elim: list_app_typeE)
  have hh: "inst \<rho> h = inst \<rho> h'" by (rule heads[OF r th th'])
  from typings_nth[OF tss] typings_nth[OF tts] len have lens: "length Us = length Us'" by simp
  from typing_unique[OF th th'[folded hh]] funs_eq[OF lens] have UU: "Us = Us'" by simp
  show "dtyped \<rho> (dzip bs ss ts)"
    unfolding dtyped_def
  proof (intro ballI)
    fix p assume "p \<in> set (dzip bs ss ts)"
    then obtain i where i: "i < length ss" and p: "p = (bs, ss ! i, ts ! i)" using len by (auto simp: set_zip)
    have "e \<turnstile> inst \<rho> (ss ! i) : Us ! i" "e \<turnstile> inst \<rho> (ts ! i) : Us ! i"
      using typings_nth[OF tss] typings_nth[OF tts] UU i len by auto
    moreover have "\<not> loose_bvar (ss ! i) (ilength bs)" "\<not> loose_bvar (ts ! i) (ilength bs)"
      using lbs lbt i len by (auto simp: loose_bvar_apps)
    ultimately show "case p of (rb, t, u) \<Rightarrow> (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
        \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)"
      using bs p by auto
  qed
  have "dvars (dzip bs ss ts) \<subseteq> dvars [(bs, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)]"
    by (auto simp: dvars_def vars_apps dest: set_zip_leftD set_zip_rightD)
  then show "vinv \<rho> env (dvars (dzip bs ss ts))" by (rule vinv_mono[OF v])
qed

lemma head_cert:
  assumes "head_of t = c T" "e \<turnstile> inst \<rho> t : W" "c = Const a \<or> c = Free a"
  shows "cert_typ alg ar (tsubst \<rho> T)"
proof -
  have "t = c T \<degree>\<degree> snd (strip_comb t)" using t_apps[of t] assms(1) by simp
  with assms(2) obtain Us where "e \<turnstile> inst \<rho> (c T) : Us" by (metis inst_apps list_app_typeD)
  with assms(3) show ?thesis by auto
qed

context
  fixes A K :: "(indexname \<times> psort) set" assumes fK: "finite K"
begin

lemma simrands_inv:
  assumes IH: "\<And>dp env ffs frs env' ffs' frs'. okW (f dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      einv A K (tyonly env) \<Longrightarrow> tknown A env [dp] \<Longrightarrow> gtyped env [dp] \<Longrightarrow>
      \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b) \<and> einv A K (tyonly env') \<and>
        tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "okW (simrands f bs u0 s t st) st' \<Longrightarrow> einv A K (tyonly (fst st)) \<Longrightarrow> tknown A (fst st) [(bs, s, t)] \<Longrightarrow>
    (\<forall>ss ts. s = head_of s \<degree>\<degree> ss \<longrightarrow> t = head_of t \<degree>\<degree> ts \<longrightarrow> length ss = length ts \<longrightarrow>
      gtyped (fst st) (dzip bs ss ts)) \<Longrightarrow>
    \<exists>a b ss ts. s = head_of s \<degree>\<degree> ss \<and> t = head_of t \<degree>\<degree> ts \<and> length ss = length ts \<and>
      fst (snd st') = a @ fst (snd st) \<and> snd (snd st') = b @ snd (snd st) \<and>
      dstep (fst st) (dzip bs ss ts) (fst st') (a @ b) \<and> einv A K (tyonly (fst st')) \<and>
      tknown A (fst st') (a @ b) \<and> tvars_env (tyenv (fst st)) \<subseteq> tvars_env (tyenv (fst st'))"
  using IH
proof (induction f bs u0 s t st arbitrary: st' rule: simrands.induct)
  case (1 f bs u0 f1 s1 g1 t1 st)
  note IH = "1.prems"(5) and ei = "1.prems"(2) and tk = "1.prems"(3) and gp = "1.prems"(4)
  from "1.prems"(1) obtain st1 where r1: "okW (simrands f bs u0 f1 g1 st) st1"
    and r2: "okW (f (bs, s1, t1) st1) st'"
    by auto
  have hf: "head_of (f1 $ s1) = head_of f1" "head_of (g1 $ t1) = head_of g1" by simp_all
  have tk1: "tknown A (fst st) [(bs, f1, g1)]" using tk by (auto simp: tknown_pair ttvars_def)
  have gp1: "\<forall>ss ts. f1 = head_of f1 \<degree>\<degree> ss \<longrightarrow> g1 = head_of g1 \<degree>\<degree> ts \<longrightarrow> length ss = length ts \<longrightarrow>
      gtyped (fst st) (dzip bs ss ts)"
  proof (intro allI impI)
    fix ss ts assume a: "f1 = head_of f1 \<degree>\<degree> ss" "g1 = head_of g1 \<degree>\<degree> ts" "length ss = length ts"
    have w: "f1 $ s1 = head_of (f1 $ s1) \<degree>\<degree> (ss @ [s1])" "g1 $ t1 = head_of (g1 $ t1) \<degree>\<degree> (ts @ [t1])"
      using a(1,2) by (metis foldl_Cons foldl_Nil foldl_append head_of.simps(1))+
    have "length (ss @ [s1]) = length (ts @ [t1])" using a(3) by simp
    from gp[rule_format, OF w this] have "gtyped (fst st) (dzip bs (ss @ [s1]) (ts @ [t1]))" .
    then show "gtyped (fst st) (dzip bs ss ts)"
      by (rule gtyped_mono) (use a(3) in auto)
  qed
  from "1.IH"[OF r1 ei tk1 gp1 IH] obtain a1 b1 ss ts where
    ss: "f1 = head_of f1 \<degree>\<degree> ss" "g1 = head_of g1 \<degree>\<degree> ts" "length ss = length ts"
    and st1: "fst (snd st1) = a1 @ fst (snd st)" "snd (snd st1) = b1 @ snd (snd st)"
    and d1: "dstep (fst st) (dzip bs ss ts) (fst st1) (a1 @ b1)" and ei1: "einv A K (tyonly (fst st1))"
    and tk1': "tknown A (fst st1) (a1 @ b1)" and m1: "tvars_env (tyenv (fst st)) \<subseteq> tvars_env (tyenv (fst st1))"
    by blast
  have whole: "f1 $ s1 = head_of (f1 $ s1) \<degree>\<degree> (ss @ [s1])" "g1 $ t1 = head_of (g1 $ t1) \<degree>\<degree> (ts @ [t1])"
    using ss(1,2) by (metis foldl_Cons foldl_Nil foldl_append head_of.simps(1))+
  have "length (ss @ [s1]) = length (ts @ [t1])" using ss(3) by simp
  from gp[rule_format, OF whole this] ss(3) have g0: "gtyped (fst st) (dzip bs ss ts @ [(bs, s1, t1)])"
    by simp
  have gl: "gtyped (fst st1) [(bs, s1, t1)]"
  proof -
    have "gtyped (fst st1) ((a1 @ b1) @ [(bs, s1, t1)])" by (rule gtyped_dstep[OF dstep_frame[OF d1] g0])
    then show ?thesis by (rule gtyped_mono) auto
  qed
  have tkl: "tknown A (fst st1) [(bs, s1, t1)]"
    using tk tk1' m1 by (auto simp: tknown_pair tknown_def ttvars_def)
  obtain env1 ffs1 frs1 where st1e: "st1 = (env1, ffs1, frs1)" by (cases st1)
  obtain env' ffs' frs' where st'e: "st' = (env', ffs', frs')" by (cases st')
  have r2': "okW (f (bs, s1, t1) (env1, ffs1, frs1)) (env', ffs', frs')" using r2 st1e st'e by simp
  have ei1': "einv A K (tyonly env1)" and tkl': "tknown A env1 [(bs, s1, t1)]" and gl': "gtyped env1 [(bs, s1, t1)]"
    using ei1 tkl gl st1e by simp_all
  from IH[OF r2' ei1' tkl' gl'] obtain a2 b2 where
    a2: "ffs' = a2 @ ffs1" "frs' = b2 @ frs1" and d2: "dstep env1 [(bs, s1, t1)] env' (a2 @ b2)"
    and ei2: "einv A K (tyonly env')" and tk2: "tknown A env' (a2 @ b2)"
    and m2: "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env')"
    by blast
  have d2': "dstep (fst st1) [(bs, s1, t1)] (fst st') (a2 @ b2)" using d2 st1e st'e by simp
  have "dstep (fst st) (dzip bs (ss @ [s1]) (ts @ [t1])) (fst st') ((a2 @ a1) @ (b2 @ b1))"
    by (rule dstep_seq[OF d1 d2']) (use ss(3) in auto)
  moreover have "tknown A (fst st') ((a2 @ a1) @ (b2 @ b1))"
  proof -
    have "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A" using tk2 by (simp add: tknown_def)
    then have "tknown A env' (a1 @ b1)" using tknown_ext[OF tk1'[unfolded st1e, simplified] m2] by blast
    with tk2 have "tknown A env' ((a2 @ b2) @ (a1 @ b1))" by (rule tknown_append)
    then have "tknown A env' ((a2 @ a1) @ (b2 @ b1))" by (rule tknown_perm) auto
    then show ?thesis using st'e by simp
  qed
  ultimately show ?case
    using whole ss(3) st1 a2 st1e st'e ei2 m1 m2 by (intro exI[of _ "a2 @ a1"] exI[of _ "b2 @ b1"] exI[of _ "ss @ [s1]"]
      exI[of _ "ts @ [t1]"]) auto
qed (auto simp: dstep_refl tknown_def)

lemma SIMPL0_rest_inv:
  assumes IHd: "\<And>dp env ffs frs env' ffs' frs'. okW (simpl alg dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)"
    and IH: "\<And>dp env ffs frs env' ffs' frs'. okW (simpl alg dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      einv A K (tyonly env) \<Longrightarrow> tknown A env [dp] \<Longrightarrow> gtyped env [dp] \<Longrightarrow>
      \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b) \<and> einv A K (tyonly env') \<and>
        tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    and r: "okW (SIMPL0_rest simpl alg bs t u env ffs frs) (env', ffs', frs')"
    and ei: "einv A K (tyonly env)" and tk: "tknown A env [(bs, t, u)]" and gt: "gtyped env [(bs, t, u)]"
  shows "\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> einv A K (tyonly env') \<and>
    tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof -
  let ?\<rho> = "tnorm_inst (tyenv env)"
  from gtyped_rho0(2)[OF gt ei] obtain e0 W where tyt: "e0 \<turnstile> inst ?\<rho> t : W" and tyu: "e0 \<turnstile> inst ?\<rho> u : W"
    by auto
  have kt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    using tk by (auto simp: tknown_pair)
  have asg: ?thesis
    if h: "okW (handleW (do {env' \<leftarrow> assignment alg bs t' u' env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t', u') # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      and tk': "tknown A env [(bs, t', u')]" and gt': "gtyped env [(bs, t', u')]" for t' u'
  proof -
    from h[unfolded okW_handleW] consider
      (ok) "okW (do {env' \<leftarrow> assignment alg bs t' u' env; returnW (env', ffs, frs)}) (env', ffs', frs')"
    | (err) e where "okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t', u') # frs) | _ \<Rightarrow> raiseW e) (env', ffs', frs')"
      by blast
    then show ?thesis
    proof cases
      case ok
      then obtain env1 where a: "okW (assignment alg bs t' u' env) env1" and e: "env' = env1" "ffs' = ffs" "frs' = frs"
        by auto
      from assignment_inv[OF a fK ei tk' gt'] e show ?thesis
        by (intro exI[of _ "[]"]) (auto simp: tknown_def)
    next
      case err
      then have "e = ASSIGN" by (cases e) auto
      with err have "env' = env" "ffs' = ffs" "frs' = (bs, t', u') # frs" by simp_all
      with ei tk' show ?thesis by (intro exI[of _ "[]"] exI[of _ "[(bs, t', u')]"]) simp
    qed
  qed
  have rigid: ?thesis
    if sr: "okW (simrands (simpl alg) bs u t u (env1, ffs, frs)) (env', ffs', frs')"
      and ei1: "einv A K (tyonly env1)" and te: "tenv env1 = tenv env" and ext: "extends env env1"
      and m1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
      and heads: "\<And>\<rho> e U U'. tsol (tyenv env1) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> e \<turnstile> inst \<rho> (head_of t) : U \<Longrightarrow>
        e \<turnstile> inst \<rho> (head_of u) : U' \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
    for env1
  proof -
    have gt1: "gtyped env1 [(bs, t, u)]"
      by (rule gtyped_dstep[OF dstep_tenv[OF te ext] gt])
    have tk1: "tknown A env1 [(bs, t, u)]" using tk m1 etvars_tenv[OF te] by (auto simp: tknown_def)
    have gp: "\<forall>ss ts. t = head_of t \<degree>\<degree> ss \<longrightarrow> u = head_of u \<degree>\<degree> ts \<longrightarrow> length ss = length ts \<longrightarrow>
        gtyped env1 (dzip bs ss ts)"
    proof (intro allI impI)
      fix ss ts assume a: "t = head_of t \<degree>\<degree> ss" "u = head_of u \<degree>\<degree> ts" "length ss = length ts"
      have "gtyped env1 [(bs, head_of t \<degree>\<degree> ss, head_of u \<degree>\<degree> ts)]" using gt1 a(1,2) by simp
      from gtyped_args[OF this a(3) heads] show "gtyped env1 (dzip bs ss ts)" .
    qed
    have "\<exists>a b ss ts. t = head_of t \<degree>\<degree> ss \<and> u = head_of u \<degree>\<degree> ts \<and> length ss = length ts \<and>
      fst (snd (env', ffs', frs')) = a @ fst (snd (env1, ffs, frs)) \<and> snd (snd (env', ffs', frs')) = b @ snd (snd (env1, ffs, frs)) \<and>
      dstep (fst (env1, ffs, frs)) (dzip bs ss ts) (fst (env', ffs', frs')) (a @ b) \<and> einv A K (tyonly (fst (env', ffs', frs'))) \<and>
      tknown A (fst (env', ffs', frs')) (a @ b) \<and> tvars_env (tyenv (fst (env1, ffs, frs))) \<subseteq> tvars_env (tyenv (fst (env', ffs', frs')))"
      by (rule simrands_inv[OF IH sr]) (use ei1 tk1 gp in simp_all)
    then obtain a b where
      "ffs' = a @ ffs" "frs' = b @ frs" "einv A K (tyonly env')" "tknown A env' (a @ b)"
      "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env')"
      by auto
    with m1 show ?thesis by blast
  qed
  have CF: ?thesis if ht: "head_of t = c T" and hu: "head_of u = c U" and c: "c = Const a0 \<or> c = Free a0"
    and cu: "okW (cunify_types alg T U env) env1"
    and sr: "okW (simrands (simpl alg) bs u t u (env1, ffs, frs)) (env', ffs', frs')" for c a0 T U env1
  proof -
    have "tvars T \<subseteq> ttvars t" "tvars U \<subseteq> ttvars u"
      using ttvars_head[of t] ttvars_head[of u] ht hu c by (auto simp: ttvars_def)
    then have kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
      using kt by blast+
    note cT = head_cert[OF ht tyt c] and cU = head_cert[OF hu tyu c]
    note cc = tyinv_cunify[OF cu fK ei kT(1) cT kT(2) cU]
    show ?thesis
    proof (rule rigid[OF sr cc(1,2) _ cc(3)])
      show "extends env env1" by (rule cunify_types_sound(2)[OF cu])
      fix \<rho> e V V' assume "tsol (tyenv env1) \<rho>" "cert_inst \<rho>"
      with cc(6) have "tsubst \<rho> T = tsubst \<rho> U" by blast
      then show "inst \<rho> (head_of t) = inst \<rho> (head_of u)" using ht hu c by auto
    qed
  qed
  show ?thesis
  proof (cases "head_of t")
    case tV: (Var x T)
    show ?thesis
    proof (cases "is_Var (head_of u)")
      case True
      then obtain y U where uV: "head_of u = Var y U" by (cases "head_of u") auto
      have "\<exists>T' U'. ok (body_type env T) T' \<and> ok (body_type env U) U' \<and> okW (cunify_types alg T' U' env) env' \<and>
          ffs' = (bs, t, u) # ffs \<and> frs' = frs"
        using r tV uV by (simp add: SIMPL0_rest_def)
      then obtain T' U' where bT: "ok (body_type env T) T'" and bU: "ok (body_type env U) U'"
        and cu: "okW (cunify_types alg T' U' env) env'" and st': "ffs' = (bs, t, u) # ffs" "frs' = frs"
        by blast
      note hT = head_body_cert[OF ei kt(1) tV tyt bT] and hU = head_body_cert[OF ei kt(2) uV tyu bU]
      note cc = tyinv_cunify[OF cu fK ei hT hU]
      have "tknown A env' [(bs, t, u)]" using tk cc(2,3) etvars_tenv[OF cc(2)] by (auto simp: tknown_def)
      with cc st' show ?thesis by (intro exI[of _ "[(bs, t, u)]"] exI[of _ "[]"]) simp
    next
      case False
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs t u env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t, u) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tV False by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
      from asg[OF this tk gt] show ?thesis .
    qed
  next
    case tC: (Const a0 T)
    show ?thesis
    proof (cases "head_of u")
      case (Const b U)
      from r tC Const obtain env1 where ab: "a0 = b" and cu: "okW (cunify_types alg T U env) env1"
        and sr: "okW (simrands (simpl alg) bs u t u (env1, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule CF[OF tC Const[folded ab] disjI1[OF refl] cu sr])
    next
      case (Var y U)
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs u t env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tC Var by (simp add: SIMPL0_rest_def)
      from asg[OF this tknown_swap[OF tk] gtyped_swap[OF gt]] show ?thesis by (auto simp: tknown_def)
    qed (use r tC in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tF: (Free a0 T)
    show ?thesis
    proof (cases "head_of u")
      case (Free b U)
      from r tF Free obtain env1 where ab: "a0 = b" and cu: "okW (cunify_types alg T U env) env1"
        and sr: "okW (simrands (simpl alg) bs u t u (env1, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule CF[OF tF Free[folded ab] disjI2[OF refl] cu sr])
    next
      case (Var y U)
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs u t env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tF Var by (simp add: SIMPL0_rest_def)
      from asg[OF this tknown_swap[OF tk] gtyped_swap[OF gt]] show ?thesis by (auto simp: tknown_def)
    qed (use r tF in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tB: (Bound i)
    show ?thesis
    proof (cases "head_of u")
      case (Bound j)
      from r tB Bound have ij: "i = j"
        and sr: "okW (simrands (simpl alg) bs u t u (env, ffs, frs)) (env', ffs', frs')"
        by (auto simp: SIMPL0_rest_def split: if_splits)
      show ?thesis by (rule rigid[OF sr ei refl extends_refl order_refl]) (simp add: tB Bound ij)
    next
      case (Var y U)
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs u t env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tB Var by (simp add: SIMPL0_rest_def)
      from asg[OF this tknown_swap[OF tk] gtyped_swap[OF gt]] show ?thesis by (auto simp: tknown_def)
    qed (use r tB in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tA: (Abs a0 T s)
    show ?thesis
    proof (cases "head_of u")
      case (Var y U)
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs u t env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tA Var by (simp add: SIMPL0_rest_def)
      from asg[OF this tknown_swap[OF tk] gtyped_swap[OF gt]] show ?thesis by (auto simp: tknown_def)
    qed (use r tA in \<open>simp_all add: SIMPL0_rest_def\<close>)
  next
    case tA: (App f s)
    show ?thesis
    proof (cases "head_of u")
      case (Var y U)
      have "okW (handleW (do {env' \<leftarrow> assignment alg bs u t env; returnW (env', ffs, frs)})
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
        using r tA Var by (simp add: SIMPL0_rest_def)
      from asg[OF this tknown_swap[OF tk] gtyped_swap[OF gt]] show ?thesis by (auto simp: tknown_def)
    qed (use r tA in \<open>simp_all add: SIMPL0_rest_def\<close>)
  qed
qed

lemma SIMPL0_inv_aux:
  assumes "SIMPL0 alg' dp st = Some r"
  shows "alg' = alg \<Longrightarrow> snd r = Ok (env', ffs', frs') \<Longrightarrow> st = (env, ffs, frs) \<Longrightarrow>
    (\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)) \<and>
    (einv A K (tyonly env) \<longrightarrow> tknown A env [dp] \<longrightarrow> gtyped env [dp] \<longrightarrow>
      (\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b) \<and> einv A K (tyonly env') \<and>
        tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')))"
  using assms
proof (induction alg' dp st r arbitrary: env ffs frs env' ffs' frs' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 simpl alg' dp0 st r)
  note aeq = "1.prems"(1)
  have IHd: "\<exists>a b. ffs2 = a @ ffs1 \<and> frs2 = b @ frs1 \<and> dstep env1 [dp] env2 (a @ b)"
    if "okW (simpl alg dp (env1, ffs1, frs1)) (env2, ffs2, frs2)" for dp env1 ffs1 frs1 env2 ffs2 frs2
  proof -
    from that aeq obtain evs where "simpl alg' dp (env1, ffs1, frs1) = Some (evs, Ok (env2, ffs2, frs2))" by auto
    from "1.IH"[OF this] aeq show ?thesis by simp
  qed
  have IH: "\<exists>a b. ffs2 = a @ ffs1 \<and> frs2 = b @ frs1 \<and> dstep env1 [dp] env2 (a @ b) \<and> einv A K (tyonly env2) \<and>
      tknown A env2 (a @ b) \<and> tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env2)"
    if "okW (simpl alg dp (env1, ffs1, frs1)) (env2, ffs2, frs2)" "einv A K (tyonly env1)"
      "tknown A env1 [dp]" "gtyped env1 [dp]" for dp env1 ffs1 frs1 env2 ffs2 frs2
  proof -
    from that(1) aeq obtain evs where "simpl alg' dp (env1, ffs1, frs1) = Some (evs, Ok (env2, ffs2, frs2))" by auto
    from "1.IH"[OF this] that(2-4) aeq show ?thesis by simp
  qed
  have "\<exists>bs t u env1. okW (head_norm_dpair alg' env dp0) ((bs, t, u), env1) \<and>
      okW (SIMPL0_rest simpl alg' bs t u env1 ffs frs) (env', ffs', frs')"
    using okW_of_Some[OF "1.hyps" "1.prems"(2)] "1.prems"(3) by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain bs t u env1 where hn: "okW (head_norm_dpair alg env dp0) ((bs, t, u), env1)"
    and rest: "okW (SIMPL0_rest simpl alg bs t u env1 ffs frs) (env', ffs', frs')"
    using aeq
    by blast
  from SIMPL0_rest_sound[OF IHd rest] obtain a b where
    ab: "ffs' = a @ ffs" "frs' = b @ frs" and d: "dstep env1 [(bs, t, u)] env' (a @ b)"
    by blast
  have hd: "dstep env [dp0] env1 [(bs, t, u)]" by (rule head_norm_dpair_sound(2)[OF hn])
  have d0: "dstep env [dp0] env' (a @ b)" by (rule dstep_trans[OF hd d])
  show ?case
  proof (intro conjI impI)
    show "\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp0] env' (a @ b)" using ab d0 by blast
    assume ei: "einv A K (tyonly env)" and tk: "tknown A env [dp0]" and gt: "gtyped env [dp0]"
    obtain rb0 t0 u0 where dp0: "dp0 = (rb0, t0, u0)" by (cases dp0)
    from head_norm_dpair_inv[OF hn[unfolded dp0] fK ei tk[unfolded dp0] gt[unfolded dp0]]
    have ei1: "einv A K (tyonly env1)" and tk1: "tknown A env1 [(bs, t, u)]"
      and m1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" by auto
    have gt1: "gtyped env1 [(bs, t, u)]" by (rule gtyped_dstep[OF hd gt])
    from SIMPL0_rest_inv[OF IHd IH rest ei1 tk1 gt1] obtain a' b' where
      ab': "ffs' = a' @ ffs" "frs' = b' @ frs" and ei': "einv A K (tyonly env')" and tk': "tknown A env' (a' @ b')"
      and m2: "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env')"
      by blast
    from ab ab' have "a' = a" "b' = b" by simp_all
    with d0 ab ei' tk' m1 m2 show "\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp0] env' (a @ b) \<and>
        einv A K (tyonly env') \<and> tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
      by blast
  qed
qed

lemma SIMPL0_inv:
  "okW (SIMPL0 alg dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow> tknown A env [dp] \<Longrightarrow>
    gtyped env [dp] \<Longrightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b) \<and> einv A K (tyonly env') \<and>
      tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  using SIMPL0_inv_aux[OF _ refl] by fastforce

lemma foldrW_SIMPL0_inv:
  "okW (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow>
    tknown A env dps \<Longrightarrow> gtyped env dps \<Longrightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env dps env' (a @ b) \<and> einv A K (tyonly env') \<and>
      tknown A env' (a @ b) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
proof (induction dps arbitrary: env' ffs' frs')
  case Nil
  then show ?case using dstep_refl[of env "[]"] by (simp add: tknown_def)
next
  case (Cons dp dps)
  from Cons.prems(1) obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (env1, ffs1, frs1)"
    and s: "okW (SIMPL0 alg dp (env1, ffs1, frs1)) (env', ffs', frs')"
    by auto
  have tkd: "tknown A env dps" by (rule tknown_mono[OF Cons.prems(3)]) auto
  have gtd: "gtyped env dps" by (rule gtyped_mono[OF Cons.prems(4)]) auto
  from Cons.IH[OF f Cons.prems(2) tkd gtd] obtain a1 b1 where ab1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs"
    and d1: "dstep env dps env1 (a1 @ b1)" and ei1: "einv A K (tyonly env1)" and tk1: "tknown A env1 (a1 @ b1)"
    and m1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    by blast
  have "gtyped env1 ((a1 @ b1) @ [dp])"
    by (rule gtyped_dstep[OF dstep_frame[OF d1]]) (rule gtyped_mono[OF Cons.prems(4)], auto)
  then have gt1: "gtyped env1 [dp]" by (rule gtyped_mono) auto
  have "etvars env1 \<subseteq> tvars_env (tyenv env1) \<union> A" using tk1 by (simp add: tknown_def)
  then have tkp: "tknown A env1 [dp]"
    using tknown_ext[OF tknown_mono[OF Cons.prems(3), of "[dp]"] m1] by auto
  from SIMPL0_inv[OF s ei1 tkp gt1] obtain a2 b2 where ab2: "ffs' = a2 @ ffs1" "frs' = b2 @ frs1"
    and d2: "dstep env1 [dp] env' (a2 @ b2)" and ei2: "einv A K (tyonly env')" and tk2: "tknown A env' (a2 @ b2)"
    and m2: "tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env')"
    by blast
  have d: "dstep env (dp # dps) env' ((a2 @ a1) @ (b2 @ b1))" by (rule dstep_seq[OF d1 d2 refl])
  have "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A" using tk2 by (simp add: tknown_def)
  then have "tknown A env' (a1 @ b1)" using tknown_ext[OF tk1 m2] by blast
  with tk2 have "tknown A env' ((a2 @ b2) @ (a1 @ b1))" by (rule tknown_append)
  then have "tknown A env' ((a2 @ a1) @ (b2 @ b1))" by (rule tknown_perm) auto
  with d ab1 ab2 ei2 m1 m2 show ?case
    by (intro exI[of _ "a2 @ a1"] exI[of _ "b2 @ b1"]) auto
qed

lemma SIMPL_inv_aux:
  assumes "SIMPL alg' env dps = Some r"
  shows "alg' = alg \<Longrightarrow> snd r = Ok (env', ffs, frs) \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow> tknown A env dps \<Longrightarrow> gtyped env dps \<Longrightarrow>
    einv A K (tyonly env') \<and> tknown A env' (frs @ ffs) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  using assms
proof (induction alg' env dps r arbitrary: env' ffs frs rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl alg' env dps r)
  note aeq = "1.prems"(1)
  have IH: "einv A K (tyonly env2) \<and> tknown A env2 (frs2 @ ffs2) \<and> tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env2)"
    if "okW (simpl alg env1 dps1) (env2, ffs2, frs2)" "einv A K (tyonly env1)" "tknown A env1 dps1"
      "gtyped env1 dps1" for env1 dps1 env2 ffs2 frs2
  proof -
    from that(1) aeq obtain evs where "simpl alg' env1 dps1 = Some (evs, Ok (env2, ffs2, frs2))" by auto
    from "1.IH"[OF this] that(2-4) aeq show ?thesis by simp
  qed
  have "\<exists>env1 ffs1 frs1. okW (foldrW (SIMPL0 alg') dps (env, [], [])) (env1, ffs1, frs1) \<and>
      (okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1))"
    using okW_of_Some[OF "1.hyps" "1.prems"(2)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) (env1, ffs1, frs1)"
    and rest: "okW (simpl alg env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1)"
    using aeq by blast
  from foldrW_SIMPL0_inv[OF f "1.prems"(3-5)] obtain a b where ab: "ffs1 = a" "frs1 = b"
    and d: "dstep env dps env1 (a @ b)" and ei1: "einv A K (tyonly env1)" and tk1: "tknown A env1 (a @ b)"
    and m1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    by auto
  have tk1': "tknown A env1 (frs1 @ ffs1)" using tk1 ab by (rule_tac tknown_perm) auto
  have gt1: "gtyped env1 (frs1 @ ffs1)"
    by (rule gtyped_mono[OF gtyped_dstep[OF d "1.prems"(5)]]) (use ab in auto)
  from rest show ?case
  proof
    assume "okW (simpl alg env1 (frs1 @ ffs1)) (env', ffs, frs)"
    from IH[OF this ei1 tk1' gt1] m1 show ?thesis by auto
  qed (use ei1 tk1' m1 in auto)
qed

theorem SIMPL_inv:
  "okW (SIMPL alg env dps) (env', ffs, frs) \<Longrightarrow> einv A K (tyonly env) \<Longrightarrow> tknown A env dps \<Longrightarrow> gtyped env dps \<Longrightarrow>
    einv A K (tyonly env') \<and> tknown A env' (frs @ ffs) \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  using SIMPL_inv_aux[OF _ refl] by fastforce


end

subsection \<open>The search\<close>

text \<open>
  The invariant holds after simplification, so it gives the hypothesis of \<^const>\<open>MATCH\<close> at
  every node; the typing part of the invariant (\<^const>\<open>gtyped\<close>) holds for the elements of
  \<^const>\<open>MATCH\<close> since they are steps. What remains is the type part (\<^const>\<open>tyinv\<close>) for the
  elements of \<^const>\<open>MATCH\<close>, as a hypothesis (\<open>MT\<close>), proved in theory \<open>Unify_Match_Inv\<close>:
\<close>

lemma ninv_SIMPL:
  assumes cfg: "cfg_alg cfg = alg" and ni: "ninv env dps"
    and r: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
  shows "ninv env' (dp # frs @ ffs)"
proof -
  from ni obtain A K where gt: "gtyped env dps" and fK: "finite K" and ei: "einv A K (tyonly env)"
    and tk: "tknown A env dps"
    unfolding ninv_def tyinv_def by blast
  from SIMPL_inv[OF fK r[unfolded cfg] ei tk gt]
  have "einv A K (tyonly env')" "tknown A env' ((dp # frs) @ ffs)" by auto
  moreover have "gtyped env' ((dp # frs) @ ffs)" by (rule gtyped_dstep[OF SIMPL_sound[OF r] gt])
  ultimately show ?thesis using fK unfolding ninv_def tyinv_def by auto
qed

lemma ninv_SIMPL_MATCH_ok:
  assumes cfg: "cfg_alg cfg = alg" and ni: "ninv env dps"
    and r: "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
  shows "MATCH_ok env' dp"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have "frs_shape dp" by (rule SIMPL_frs_shape[OF r])
  from ninv_MATCH_ok[OF ninv_SIMPL[OF cfg ni r, unfolded dp] this[unfolded dp]] show ?thesis by (simp add: dp)
qed

theorem hounifiers_ev_sound_ninv:
  assumes cfg: "cfg_alg cfg = alg"
    and NI0: "ninv env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and MT: "\<And>env' dp dps ms env2 dps2. ninv env' (dp # dps) \<Longrightarrow> frs_shape dp \<Longrightarrow>
      okW (MATCH cfg env' dp dps) ms \<Longrightarrow> ev cfg ms (El_E env2 dps2) \<Longrightarrow> \<exists>A K. tyinv A K env2 dps2"
    and ev: "ev cfg (hounifiers rb env tus) x"
  shows "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x"
proof (rule hounifiers_ev_sound[where NI = ninv, OF NI0 _ _ ev])
  show "MATCH_ok env' dp"
    if "ninv env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)" for env dps env' ffs dp frs
    by (rule ninv_SIMPL_MATCH_ok[OF cfg that])
  show "ninv env2 dps2"
    if "ninv env dps" "okW (SIMPL (cfg_alg cfg) env dps) (env', ffs, dp # frs)"
      "okW (MATCH cfg env' dp (frs @ ffs)) ms" "ev cfg ms (El_E env2 dps2)" for env dps env' ffs dp frs ms env2 dps2
  proof -
    have ni: "ninv env' (dp # frs @ ffs)" by (rule ninv_SIMPL[OF cfg that(1,2)])
    have sh: "frs_shape dp" by (rule SIMPL_frs_shape[OF that(2)])
    have mo: "MATCH_ok env' dp" by (rule ninv_SIMPL_MATCH_ok[OF cfg that(1,2)])
    have sq: "seqinv (GE env' (dp # frs @ ffs)) ms" by (rule MATCH_sound[OF that(3) mo])
    from ev_sound[OF that(4) sq] have d: "dstep env' (dp # frs @ ffs) env2 dps2" by simp
    have "gtyped env2 dps2" by (rule gtyped_dstep[OF d]) (use ni in \<open>simp add: ninv_def\<close>)
    with MT[OF ni sh that(3,4)] show ?thesis unfolding ninv_def by blast
  qed
qed


end

end
