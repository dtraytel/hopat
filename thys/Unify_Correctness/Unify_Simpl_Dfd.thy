section \<open>Termination of \<open>SIMPL\<close> with Names at Two Types\<close>

theory Unify_Simpl_Dfd
  imports Unify_Unfc
begin

text \<open>
  The termination proof of theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close> measures pairs
  by the type-blind unfolding \<open>unf\<close>, which is well-typed only if the environment binds no name
  that occurs at a second type; with loose names it therefore gives only partial results. Here the
  measure uses \<open>unfc\<close> instead, which unfolds exactly the occurrences that \<open>lookup\<close>
  follows, and the statements are total: a computation terminates, and it returns a result that
  satisfies the postcondition, or raises one of the expected exceptions or the exception of
  \<^const>\<open>var_clash\<close>. There is no hypothesis on the names.
\<close>

context pure_sig_gen
begin

subsection \<open>Computations that terminate, possibly with a clash\<close>

definition clashW :: "uexn \<Rightarrow> bool" where
  "clashW e \<longleftrightarrow> (\<exists>x. e = PExn x \<and> clashx x)"

definition cxokE :: "(uexn \<Rightarrow> bool) \<Rightarrow> 'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "cxokE Xe m P \<longleftrightarrow> (\<exists>evs e. m = Some (evs, Err e) \<and> (Xe e \<or> clashW e)) \<or> (\<exists>x. okW m x \<and> P x)"

abbreviation ccuok :: "'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ccuok \<equiv> cxokE (\<lambda>e. e = CANTUNIFY)"

lemma clashW_simps [simp]: "\<not> clashW CANTUNIFY" "\<not> clashW ASSIGN" "\<not> clashW CHANGE_FAIL" "\<not> clashW Bind"
  "clashW (PExn x) \<longleftrightarrow> clashx x"
  by (simp_all add: clashW_def)

lemma cxokE_mono: "cxokE Xe m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> cxokE Xe m Q"
  unfolding cxokE_def by blast

lemma cxokE_mono_ok: "cxokE Xe m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> cxokE Xe m Q"
  unfolding cxokE_def by blast

lemma cxokE_mono_exn: "cxokE Xe m P \<Longrightarrow> (\<And>e. Xe e \<Longrightarrow> Ye e) \<Longrightarrow> cxokE Ye m P"
  unfolding cxokE_def by blast

lemma cxokE_xokW: "xokW E m P \<Longrightarrow> Xe E \<Longrightarrow> cxokE Xe m P"
  unfolding cxokE_def xokW_def by blast

lemma cxokE_okI: "okW m x \<Longrightarrow> P x \<Longrightarrow> cxokE Xe m P"
  unfolding cxokE_def by blast

lemma cxokE_returnW [simp]: "cxokE Xe (returnW x) P \<longleftrightarrow> P x"
  by (auto simp: cxokE_def returnW_def)

lemma cxokE_raiseW [simp]: "Xe e \<Longrightarrow> cxokE Xe (raiseW e) P"
  by (auto simp: cxokE_def raiseW_def)

lemma cxokE_bindW:
  assumes m: "cxokE Xe m P" and k: "\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> cxokE Xe (k x) Q"
  shows "cxokE Xe (bindW m k) Q"
proof -
  from m consider (err) evs e where "m = Some (evs, Err e)" "Xe e \<or> clashW e" | (ok) x where "okW m x" "P x"
    unfolding cxokE_def by blast
  then show ?thesis
  proof cases
    case err
    then show ?thesis by (auto simp: cxokE_def bindW_def)
  next
    case ok
    from k[OF ok] ok(1) show ?thesis by (auto simp: cxokE_def bindW_def)
  qed
qed

lemma cxokE_liftM:
  assumes "dfd m" "\<And>x. m = return x \<Longrightarrow> P x"
  shows "cxokE Xe (liftM m) P"
  using assms by (elim dfd_cases) (auto simp: cxokE_def liftM_def return_def clashW_def)

lemma cxokE_handleW:
  assumes m: "cxokE (\<lambda>e. e = E) m Q" and hE: "cxokE Xe (h E) Q"
    and hr: "\<And>e. clashW e \<Longrightarrow> h e = raiseW e"
  shows "cxokE Xe (handleW m h) Q"
proof -
  from m consider (err) evs where "m = Some (evs, Err E)" | (cl) evs e where "m = Some (evs, Err e)" "clashW e"
    | (ok) x where "okW m x" "Q x"
    unfolding cxokE_def by blast
  then show ?thesis
  proof cases
    case err
    from hE show ?thesis using err
      by (auto simp: cxokE_def handleW_def split: option.splits xres.splits)
  next
    case cl
    then show ?thesis using hr[OF cl(2)]
      by (auto simp: cxokE_def handleW_def raiseW_def)
  next
    case ok
    then show ?thesis by (auto simp: cxokE_def handleW_def)
  qed
qed

text \<open>
  The clash occurs only with loose names, so a computation that terminates with the clash or a
  result satisfies the statements of theory \<open>Unify_Simpl_Term\<close> for results that bind no loose name:
\<close>

lemma cxokE_lxokE: "cxokE Xe m P \<Longrightarrow> lxokE Xe f m P"
  unfolding cxokE_def lxokE_def by (auto simp: clashW_def clashx_def)

lemma cxokE_okW_P: "cxokE Xe m P \<Longrightarrow> okW m x \<Longrightarrow> P x"
  unfolding cxokE_def by auto

lemma cxokE_defined: "cxokE Xe m P \<Longrightarrow> m \<noteq> None"
  unfolding cxokE_def by auto

subsection \<open>The measure of a pair\<close>

definition LMc :: "tinst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "LMc \<rho> env e t = lsz e (bnorm (inst \<rho> (unfc env t)))"

definition dmc :: "env \<Rightarrow> dpair \<Rightarrow> nat" where
  "dmc env dp = (case dp of (rb, t, u) \<Rightarrow>
    LMc (rho0 env) env (benv (rho0 env) rb) t + LMc (rho0 env) env (benv (rho0 env) rb) u)"

lemma LMc_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "e' \<turnstile> inst \<rho> (unfc env t) : T"
  shows "LMc \<rho> env e t' = LMc \<rho> env e t"
  unfolding LMc_def
  using bnorm_typed_reds[OF assms(4) inst_reds[OF head_norm_unfc[OF assms(1) refl assms(2,3)]]] by simp

lemma LMc_Abs:
  "e' \<turnstile> inst \<rho> (unfc env (Abs a U t)) : T \<Longrightarrow> LMc \<rho> env e (Abs a U t) = LMc \<rho> env (e\<langle>0:tsubst \<rho> U\<rangle>) t + 2"
  unfolding LMc_def by (simp add: bnorm_Abs_typed)


lemma dmc_same:
  assumes "tenv env1 = tenv env" "tyenv env1 = tyenv env"
  shows "dmc env1 = dmc env"
  using unfc_same[OF assms] assms(2) by (simp add: dmc_def[abs_def] LMc_def[abs_def])


lemma LMc_rigid:
  assumes "rigid h" "e \<turnstile> inst \<rho> (unfc env (h \<degree>\<degree> ts)) : T"
  shows "LMc \<rho> env e (h \<degree>\<degree> ts) = tsz T + sum_list (map (LMc \<rho> env e) ts)"
proof -
  have i: "inst \<rho> (unfc env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> map (inst \<rho> \<circ> unfc env) ts"
    using assms(1) by (simp add: unfc_apps inst_apps unfc_rigid)
  have r: "rigid (inst \<rho> h)" by (rule inst_rigid[OF assms(1)])
  then have at: "atom (inst \<rho> h)" by (simp add: rigid_iff)
  note b = bnorm_ahd[OF at assms(2)[unfolded i]]
  have nA: "\<not> is_Abs (inst \<rho> h \<degree>\<degree> map bnorm (map (inst \<rho> \<circ> unfc env) ts))"
    by (rule not_App_apps_Abs) (use r in \<open>cases "inst \<rho> h", simp_all\<close>)
  have "LMc \<rho> env e (h \<degree>\<degree> ts) = lsz e (inst \<rho> h \<degree>\<degree> map bnorm (map (inst \<rho> \<circ> unfc env) ts))"
    by (simp add: LMc_def i b(1))
  also have "\<dots> = tsz T + sum_list (map (lsz e) (map bnorm (map (inst \<rho> \<circ> unfc env) ts)))"
    using lsz_rigid_apps[OF r] spine_type_typing[OF b(2,3) nA] by simp
  also have "\<dots> = tsz T + sum_list (map (LMc \<rho> env e) ts)" by (simp add: LMc_def[abs_def] comp_def)
  finally show ?thesis .
qed

lemma unfc_ahd_head: "acyc env \<Longrightarrow> rigid h \<or> (\<exists>F U. h = Var F U \<and> vt_lookup (tenv env) F = None) \<Longrightarrow> unfc env h = h"
  by (auto simp: unfc_rigid unfc_Var)

lemma LMc_eta:
  assumes ac: "acyc env" and cl: "closed_env env"
    and h: "rigid h \<or> (\<exists>F U. h = Var F U \<and> vt_lookup (tenv env) F = None)"
    and ty: "e \<turnstile> inst \<rho> (unfc env (h \<degree>\<degree> ts)) : A \<rightarrow>\<^sub>T B"
  shows "LMc \<rho> env (e\<langle>0:A\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) + 2 = LMc \<rho> env e (h \<degree>\<degree> ts)"
proof -
  have uh: "unfc env h = h" by (rule unfc_ahd_head[OF ac h])
  let ?h = "inst \<rho> h" and ?xs = "map (inst \<rho> \<circ> unfc env) ts"
  have i: "inst \<rho> (unfc env (h \<degree>\<degree> ts)) = ?h \<degree>\<degree> ?xs" by (simp add: unfc_apps inst_apps uh)
  have hv: "rigid ?h \<or> (\<exists>x T. ?h = Var x T)" using h inst_rigid by auto
  then have at: "atom ?h" by (auto simp: rigid_iff)
  note b = bnorm_ahd[OF at ty[unfolded i]]
  let ?N = "?h \<degree>\<degree> map bnorm ?xs"
  have nA: "\<not> is_Abs ?N" by (rule not_App_apps_Abs) (use at in \<open>cases ?h, simp_all\<close>)
  let ?X = "inst \<rho> (unfc env (h \<degree>\<degree> ts))"
  have "unfc env (lift (h \<degree>\<degree> ts) 0) = lift (unfc env (h \<degree>\<degree> ts)) 0" by (rule unfc_lift[OF ac cl]) simp
  then have u: "inst \<rho> (unfc env (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0)) = lift ?X 0 $ Bound 0"
    by (simp only: incr_boundvars_1 unfc_simps inst.simps inst_lift)
  have tyl: "e\<langle>0:A\<rangle> \<turnstile> lift ?X 0 : A \<rightarrow>\<^sub>T B" by (rule lift_type[OF ty]) simp
  have bl: "bnorm (lift ?X 0) = lift ?N 0" using bnorm_lift[OF ty, of 0] b(1) i by simp
  have "lift ?X 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift ?N 0" using bnorm_typed[OF tyl] bl by simp
  then have r: "lift ?X 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift ?N 0 $ Bound 0" by (rule rtrancl_beta_AppL)
  have nAl: "\<not> is_Abs (lift ?N 0)" using nA by (cases ?N) simp_all
  have "no_redex (lift ?N 0)" using b(3) no_redex_incr_bv by blast
  then have nr: "no_redex (lift ?N 0 $ Bound 0)" using nAl by simp
  have "bnorm (lift ?X 0 $ Bound 0) = lift ?N 0 $ Bound 0" by (rule bnorm_eqI[OF r nr])
  then have "LMc \<rho> env (e\<langle>0:A\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) = lsz (e\<langle>0:A\<rangle>) (lift ?N 0 $ Bound 0)"
    by (simp only: LMc_def u)
  moreover have "LMc \<rho> env e (h \<degree>\<degree> ts) = lsz e ?N" by (simp only: LMc_def i b(1))
  ultimately show ?thesis using lsz_eta[OF hv b(2,3)] by simp
qed

lemma inst_unfc_incr:
  "acyc env \<Longrightarrow> closed_env env \<Longrightarrow>
    inst \<rho> (unfc env (incr_boundvars 1 t $ Bound 0)) = lift (inst \<rho> (unfc env t)) 0 $ Bound 0"
proof -
  assume ac: "acyc env" and cl: "closed_env env"
  have "unfc env (lift t 0) = lift (unfc env t) 0" by (rule unfc_lift[OF ac cl]) simp
  then show ?thesis by (simp only: incr_boundvars_1 unfc_simps inst.simps inst_lift)
qed

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma LMc_etif:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> ok (etif \<theta> T t) t' \<Longrightarrow> ahd env t \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t') : tnorm \<theta> T \<and> LMc (tnorm_inst \<theta>) env e t' = LMc (tnorm_inst \<theta>) env e t"
proof -
  let ?\<rho> = "tnorm_inst \<theta>"
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<forall>t t' e. ok (etif \<theta> T t) t' \<longrightarrow> ahd env t \<longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unfc env t) : tnorm \<theta> T \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unfc env t') : tnorm \<theta> T \<and> LMc ?\<rho> env e t' = LMc ?\<rho> env e t"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (intro allI impI)
      fix t t' e
      assume ok: "ok (etif \<theta> (Type a Ts) t) t'" and ah: "ahd env t" and c: "cert_typ alg ar (tnorm \<theta> (Type a Ts))"
        and ty: "e \<turnstile> inst ?\<rho> (unfc env t) : tnorm \<theta> (Type a Ts)"
      show "e \<turnstile> inst ?\<rho> (unfc env t') : tnorm \<theta> (Type a Ts) \<and> LMc ?\<rho> env e t' = LMc ?\<rho> env e t"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
        let ?t = "incr_boundvars 1 t $ Bound 0"
        from ok Ts a obtain u where u: "ok (etif \<theta> U ?t) u" and t': "t' = Abs STR '''' T1 u"
          by (subst (asm) etif.simps) auto
        from c Ts a have c1: "cert_typ alg ar (tnorm \<theta> T1)" and c2: "cert_typ alg ar (tnorm \<theta> U)"
          by (simp_all add: cert_typ_fun)
        have ty1: "e \<turnstile> inst ?\<rho> (unfc env t) : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U" using ty Ts a by simp
        have "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> lift (inst ?\<rho> (unfc env t)) 0 : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U"
          by (rule lift_type[OF ty1]) simp
        then have tyt: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unfc env ?t) : tnorm \<theta> U"
          by (simp only: inst_unfc_incr[OF ac cl]) (rule typing.App, auto)
        have aht: "ahd env ?t" using ahd_lift[OF ah] by (simp add: incr_boundvars_1)
        from Type(1)[of U] Ts u aht c2 tyt
        have IH: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unfc env u) : tnorm \<theta> U"
          "LMc ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) u = LMc ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) ?t"
          by auto
        have tyt': "e \<turnstile> inst ?\<rho> (unfc env t') : tnorm \<theta> (Type a Ts)" using IH(1) c1 t' Ts a by auto
        have "LMc ?\<rho> env e t' = LMc ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) u + 2"
          using LMc_Abs[OF tyt'[unfolded t']] t' by simp
        also have "\<dots> = LMc ?\<rho> env e t"
        proof -
          define h where "h = head_of t"
          define ts where "ts = snd (strip_comb t)"
          have tt: "t = h \<degree>\<degree> ts" unfolding h_def ts_def by (rule t_apps)
          have "LMc ?\<rho> env (e\<langle>0:tnorm \<theta> T1\<rangle>) (incr_boundvars 1 (h \<degree>\<degree> ts) $ Bound 0) + 2 = LMc ?\<rho> env e (h \<degree>\<degree> ts)"
            by (rule LMc_eta[OF ac cl ahd_head[OF ah, folded h_def] ty1[unfolded tt]])
          with IH(2) tt show ?thesis by simp
        qed
        finally show ?thesis using tyt' by blast
      next
        case False
        with ok have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits)
        with ty show ?thesis by simp
      qed
    qed
  next
    case (Unbound v S)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok)
  next
    case (Bound v S U)
    then show ?case by (subst etif.simps) (simp add: type_lookup_ok tnorm_TVar[OF ti_ac[OF ti]])
  qed
  then show "ok (etif \<theta> T t) t' \<Longrightarrow> ahd env t \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unfc env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unfc env t') : tnorm \<theta> T \<and> LMc ?\<rho> env e t' = LMc ?\<rho> env e t"
    using tinv_tcons[OF ti tv] by blast
qed

lemma LMc_eta_norm_nonAbs:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env" and nA: "\<not> is_Abs t"
    and ok: "ok (eta_norm env bs t) t'" and ty: "e \<turnstile> inst (tnorm_inst \<theta>) t : T" and bs: "bs_env (tnorm_inst \<theta>) e bs"
    and lb: "\<not> loose_bvar t (ilength bs)" and tv: "ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A"
    and tyu: "e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t) : T" and h: "hnf env t"
  shows "e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t') : T \<and> LMc (tnorm_inst \<theta>) env e t' = LMc (tnorm_inst \<theta>) env e t"
proof -
  from ok nA obtain T0 where T0: "ok (fastype env bs t) T0" and et: "ok (etif \<theta> T0 t) t'"
    by (auto simp: eta_norm_nonAbs th)
  have "tsubst (tnorm_inst \<theta>) T0 = T"
    by (rule fastype_sound[OF T0 _ bs ty]) (simp add: th tsol_tnorm[OF ti_ac[OF ti]])
  then have tT: "tnorm \<theta> T0 = T" by simp
  from env_fastype_term[OF ti th ty bs lb tv] T0 have tv0: "tvars T0 \<subseteq> tvars_env \<theta> \<union> A"
    by (auto simp: fastype_def return_def)
  have c: "cert_typ alg ar T" by (rule bs_env_cert[OF bs ty lb])
  from LMc_etif[OF th ac cl tv0 et _ _ tyu[folded tT]] c h nA tT show ?thesis by (simp add: hnf_nonAbs)
qed

lemma LMc_eta_norm:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "ok (eta_norm env bs t) t' \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t) : T \<Longrightarrow> hnf env t \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unfc env t') : T \<and> LMc (tnorm_inst \<theta>) env e t' = LMc (tnorm_inst \<theta>) env e t"
proof (induction t arbitrary: e T bs t')
  case (Abs a B0 b)
  let ?\<rho> = "tnorm_inst \<theta>"
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, B0) # bs) b) b'" and t': "t' = Abs a B0 b'" by auto
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst ?\<rho> B0)"
    and tb: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> b : W" and T: "T = tsubst ?\<rho> B0 \<rightarrow>\<^sub>T W"
    by auto
  from Abs.prems(6) T have tbu: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unfc env b) : W" by auto
  have lb: "\<not> loose_bvar b (ilength ((a, B0) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, B0) # bs) \<subseteq> tvars_env \<theta> \<union> A" using Abs.prems(5) by (auto simp: btvars_def)
  have hb: "hnf env b" using Abs.prems(7) by simp
  from Abs.IH[OF b' tb bs_env_Cons[OF Abs.prems(3) c] lb tv tbu hb]
  have IH: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unfc env b') : W"
    "LMc ?\<rho> env (e\<langle>0:tsubst ?\<rho> B0\<rangle>) b' = LMc ?\<rho> env (e\<langle>0:tsubst ?\<rho> B0\<rangle>) b"
    by blast+
  have ty': "e \<turnstile> inst ?\<rho> (unfc env t') : T" using IH(1) c T t' by auto
  show ?case using ty' LMc_Abs[OF ty'[unfolded t']] LMc_Abs[OF Abs.prems(6)] IH(2) t' by simp
qed (rule LMc_eta_norm_nonAbs[OF th ac cl], simp, assumption+)+

end

subsection \<open>Typing and definedness of the unfolding under the invariants\<close>




lemma upok_unfc:
  assumes "einv A K env" "winv env X" "upok A env rb X t u"
  shows "\<exists>T. bs_env (rho0 env) (benv (rho0 env) rb) rb \<and> benv (rho0 env) rb \<turnstile> inst (rho0 env) t : T \<and>
    benv (rho0 env) rb \<turnstile> inst (rho0 env) u : T \<and> benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env t) : T \<and>
    benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env u) : T"
proof -
  from upok_benv[OF assms(3) einv_rho0[OF assms(1)]] obtain T where
    T: "bs_env (rho0 env) (benv (rho0 env) rb) rb" "benv (rho0 env) rb \<turnstile> inst (rho0 env) t : T"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) u : T" by blast
  with typing_unfc0[OF assms(1,2) T(2)] typing_unfc0[OF assms(1,2) T(3)] show ?thesis by blast
qed

text \<open>Head normalization of a well-formed pair terminates, and raises at most a clash:\<close>


subsection \<open>Normalization of pairs\<close>

definition hpostc :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair \<Rightarrow> dpair \<Rightarrow> env \<Rightarrow> bool" where
  "hpostc A K X env dp dp' env' \<longleftrightarrow> (case dp' of (rb', t', u') \<Rightarrow>
    einv A K env' \<and> winv env' X \<and> upok A env' rb' X t' u' \<and> tenv env' = tenv env \<and> sstep A K X env env' \<and>
    (tyenv env' = tyenv env \<longrightarrow> dmc env' dp' \<le> dmc env dp) \<and> ahd env' t' \<and> ahd env' u')"

lemma hpostc_refl:
  "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> upok A env rb X t u \<Longrightarrow> ahd env t \<Longrightarrow> ahd env u \<Longrightarrow>
    hpostc A K X env (rb, t, u) (rb, t, u) env"
  by (simp add: hpostc_def sstep_refl)

lemma dmc_Abs:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X (Abs a T b1) (Abs b U b2)"
    and eq: "tsubst (rho0 env) T = tsubst (rho0 env) U"
  shows "dmc env ((c, T) # rb, b1, b2) + 4 = dmc env (rb, Abs a T b1, Abs b U b2)"
proof -
  from upok_unfc[OF ei wi p] obtain W where
    W: "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env (Abs a T b1)) : W"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env (Abs b U b2)) : W"
    by blast
  show ?thesis using LMc_Abs[OF W(1)] LMc_Abs[OF W(2)] eq by (simp add: dmc_def)
qed

lemma new_dpair_dfd:
  assumes finK: "finite K"
  shows "al = alg \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> upok A env rb X t u \<Longrightarrow> nabs t = nabs u \<Longrightarrow>
    hnf env t \<Longrightarrow> hnf env u \<Longrightarrow>
    cuok (new_dpair al rb t u env) (\<lambda>(dp', env'). hpostc A K X env (rb, t, u) dp' env')"
proof (induction al rb t u env rule: new_dpair.induct)
  case (1 al rb a T body1 b U body2 env)
  note al = "1.prems"(1)
  note IH = "1.IH"[unfolded al]
  note ei = "1.prems"(2) and wi = "1.prems"(3) and p = "1.prems"(4)
  let ?c = "if a = STR '''' then b else a"
  let ?\<rho> = "rho0 env"
  note pd = upokD[OF p] and r0 = einv_rho0[OF ei]
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> (Abs a T body1) : T0" "e0 \<turnstile> inst ?\<rho> (Abs b U body2) : T0"
    using pd(9)[OF r0] by blast
  from ty0(1) have cT: "cert_typ alg ar (tsubst ?\<rho> T)" by auto
  from ty0(2) have cU: "cert_typ alg ar (tsubst ?\<rho> U)" by auto
  have kT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" and kU: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3,4) by (auto simp: ttvars_def)
  have nd: "new_dpair alg rb (Abs a T body1) (Abs b U body2) env =
      bindW (cunify_types alg T U env) (\<lambda>env'. new_dpair alg ((?c, T) # rb) body1 body2 env')"
    by simp
  note cu = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
  show ?case unfolding al nd
  proof (rule xokW_bindW[OF cu])
    fix env1 assume ok1: "okW (cunify_types alg T U env) env1" and P1: "einv A K env1 \<and> tenv env1 = tenv env \<and>
      textends (tyenv env) (tyenv env1) \<and> maxidx env \<le> maxidx env1 \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and> tnew A env A env1 \<and> (\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K))"
    then have ei1: "einv A K env1" and te: "tenv env1 = tenv env" and tx: "textends (tyenv env) (tyenv env1)"
      and mx: "maxidx env \<le> maxidx env1" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" and tn: "tnew A env A env1"
      and sol: "\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
      and card: "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
      by blast+
    have wi1: "winv env1 X" by (rule winv_tyext[OF wi te tx mx])
    have st1: "sstep A K X env env1" by (rule sstep_tyext[OF te tx mx tv tn card])
    have p0: "upok A env1 rb X (Abs a T body1) (Abs b U body2)" by (rule upok_mono[OF p sstepD(1)[OF st1] tv])
    have p1: "upok A env1 ((?c, T) # rb) X body1 body2" by (rule upok_Abs[OF p0 sol])
    have h1: "hnf env1 body1" "hnf env1 body2" using "1.prems"(6,7) hnf_tenv[OF te] by simp_all
    have n1: "nabs body1 = nabs body2" using "1.prems"(5) by simp
    from IH[OF ok1 refl refl ei1 wi1 p1 n1 h1]
    show "cuok (new_dpair alg ((?c, T) # rb) body1 body2 env1)
        (\<lambda>(dp', env'). hpostc A K X env (rb, Abs a T body1, Abs b U body2) dp' env')"
    proof (rule xokW_mono)
      fix x assume x0: "case x of (dp', env') \<Rightarrow> hpostc A K X env1 ((?c, T) # rb, body1, body2) dp' env'"
      obtain rb' t' u' env' where x: "x = ((rb', t', u'), env')" by (cases x) auto
      from x0 x have h: "einv A K env'" "winv env' X" "upok A env' rb' X t' u'" "tenv env' = tenv env1"
        "sstep A K X env1 env'" "tyenv env' = tyenv env1 \<Longrightarrow> dmc env' (rb', t', u') \<le> dmc env1 ((?c, T) # rb, body1, body2)"
        "ahd env' t'" "ahd env' u'"
        by (simp_all add: hpostc_def)
      have "dmc env' (rb', t', u') \<le> dmc env (rb, Abs a T body1, Abs b U body2)" if e': "tyenv env' = tyenv env"
      proof -
        have e1: "tyenv env1 = tyenv env" by (rule extends_mid(1)[OF sstepD(1)[OF st1] sstepD(1)[OF h(5)] e'])
        have "tsubst ?\<rho> T = tsubst ?\<rho> U" using sol einv_rho0(1)[OF ei1] e1 by auto
        then have "dmc env ((?c, T) # rb, body1, body2) + 4 = dmc env (rb, Abs a T body1, Abs b U body2)"
          by (rule dmc_Abs[OF ei wi p])
        moreover have "dmc env1 = dmc env" by (rule dmc_same[OF te e1])
        ultimately show ?thesis using h(6) e' e1 by simp
      qed
      then show "case x of (dp', env') \<Rightarrow> hpostc A K X env (rb, Abs a T body1, Abs b U body2) dp' env'"
        using h x te sstep_trans[OF st1 h(5)] by (simp add: hpostc_def)
    qed
  qed
qed (auto intro!: hpostc_refl simp: hnf_nonAbs)


lemma upok_left: "upok A env bs X s t \<Longrightarrow> upok A env bs X s s"
  unfolding upok_def by blast

lemma head_norm_dpair_ok:
  assumes finK: "finite K" and ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and h: "head_norm env t = return t1" "head_norm env u = return u1"
  shows "cuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp', env'). hpostc A K X env (rb, t, u) dp' env')"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env" and ?e = "benv (rho0 env) rb"
  note e = einvD[OF ei]
  have h3: "upok A env rb X t1 u1"
    using hn_dfd(3)[OF ei wi p, of t1 u1] h by (simp add: return_def)
  have hf: "hnf env t1" "hnf env u1"
    using head_norm_hnf[OF h(1)[unfolded return_def] refl] head_norm_hnf[OF h(2)[unfolded return_def] refl] .
  from upok_unfc[OF ei wi h3] obtain T where T: "bs_env ?\<rho> ?e rb" "?e \<turnstile> inst ?\<rho> t1 : T"
    "?e \<turnstile> inst ?\<rho> u1 : T" "?e \<turnstile> inst ?\<rho> (unfc env t1) : T" "?e \<turnstile> inst ?\<rho> (unfc env u1) : T" by blast
  from upok_unfc[OF ei wi p] obtain T' where T': "?e \<turnstile> inst ?\<rho> (unfc env t) : T'" "?e \<turnstile> inst ?\<rho> (unfc env u) : T'"
    by blast
  note pd1 = upokD[OF h3]
  have tv1: "ttvars t1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" "ttvars u1 \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using pd1(3-5) by blast+
  from eta_norm_term[OF e(2) refl T(2) T(1) pd1(7) tv1(1)] hf(1) obtain t2 where
    t2: "eta_norm env rb t1 = return t2" "ttvars t2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs t2 = arity T" "hnf env t2"
    by blast
  from eta_norm_term[OF e(2) refl T(3) T(1) pd1(8) tv1(2)] hf(2) obtain u2 where
    u2: "eta_norm env rb u1 = return u2" "ttvars u2 \<subseteq> tvars_env ?\<theta> \<union> A" "nabs u2 = arity T" "hnf env u2"
    by blast
  have Lt: "LMc ?\<rho> env ?e t2 = LMc ?\<rho> env ?e t"
    using LMc_eta_norm[OF e(2) refl e(3) e(4) t2(1)[unfolded return_def] T(2) T(1) pd1(7) tv1(1) T(4) hf(1)]
      LMc_head_norm[OF h(1)[unfolded return_def] e(3,4) T'(1)] by simp
  have Lu: "LMc ?\<rho> env ?e u2 = LMc ?\<rho> env ?e u"
    using LMc_eta_norm[OF e(2) refl e(3) e(4) u2(1)[unfolded return_def] T(3) T(1) pd1(8) tv1(2) T(5) hf(2)]
      LMc_head_norm[OF h(2)[unfolded return_def] e(3,4) T'(2)] by simp
  have dmeq: "dmc env (rb, t2, u2) = dmc env (rb, t, u)" using Lt Lu by (simp add: dmc_def)
  have p2: "upok A env rb X t2 u2"
    using upok_sym[OF upok_eta_norm[OF upok_sym[OF upok_eta_norm[OF h3 t2(1)[unfolded return_def] t2(2)]]
      u2(1)[unfolded return_def] u2(2)]] .
  have hd: "head_norm_dpair alg env (rb, t, u) = new_dpair alg rb t2 u2 env"
    by (simp add: head_norm_dpair_def h(1,2) t2(1) u2(1))
  show ?thesis unfolding hd
  proof (rule xokW_mono[OF new_dpair_dfd[OF finK refl ei wi p2 _ t2(4) u2(4)]])
    show "nabs t2 = nabs u2" using t2(3) u2(3) by simp
    fix x assume "case x of (dp', env') \<Rightarrow> hpostc A K X env (rb, t2, u2) dp' env'"
    then show "case x of (dp', env') \<Rightarrow> hpostc A K X env (rb, t, u) dp' env'"
      using dmeq by (auto simp: hpostc_def split: prod.splits)
  qed
qed

theorem head_norm_dpair_dfd:
  assumes finK: "finite K" and ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
  shows "ccuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp', env'). hpostc A K X env (rb, t, u) dp' env')"
proof -
  note e = einvD[OF ei]
  show ?thesis
  proof (rule dfd_cases[OF hn_dfd(1)[OF ei wi p]])
    fix x assume "head_norm env t = Some (Err x)" "clashx x"
    then show ?thesis by (simp add: head_norm_dpair_def liftM_def bindW_def cxokE_def)
  next
    fix t1 assume ht: "head_norm env t = Some (Ok t1)"
    let ?\<rho> = "rho0 env" and ?e = "benv (rho0 env) rb"
    have h1: "upok A env rb X t1 t1"
      using hn_dfd(3)[OF ei wi upok_left[OF p], of t1 t1] ht by simp
    from upok_unfc[OF ei wi h1] obtain T where T: "bs_env ?\<rho> ?e rb" "?e \<turnstile> inst ?\<rho> t1 : T" by blast
    note pd1 = upokD[OF h1]
    from eta_norm_term[OF e(2) refl T(2) T(1) pd1(7)] pd1(3,5) obtain t2 where
      t2: "eta_norm env rb t1 = return t2" by blast
    show ?thesis
    proof (rule dfd_cases[OF hn_dfd(2)[OF ei wi p]])
      fix x assume "head_norm env u = Some (Err x)" "clashx x"
      then show ?thesis using ht t2 by (simp add: head_norm_dpair_def liftM_def bindW_def cxokE_def return_def)
    next
      fix u1 assume hu: "head_norm env u = Some (Ok u1)"
      show ?thesis
        by (rule cxokE_xokW[OF head_norm_dpair_ok[OF finK ei wi p ht[folded return_def] hu[folded return_def]]]) simp
    qed
  qed
qed

lemma head_norm_dpair_okW_hn:
  assumes "okW (head_norm_dpair al env (rb, t, u)) r"
  shows "\<exists>t1 u1. head_norm env t = return t1 \<and> head_norm env u = return u1"
  using assms by (auto simp: head_norm_dpair_def liftM_def bindW_def return_def
    split: option.splits xres.splits prod.splits)



subsection \<open>Assignments\<close>

theorem assignment_dfd:
  assumes finX: "finite X" and finK: "finite K" and ei: "einv A K env" and wi: "winv env X"
    and p: "upok A env rb X t u" and ah: "ahd env t"
  shows "cxokE (\<lambda>e. e = ASSIGN \<or> e = CANTUNIFY) (assignment alg rb t u env) (apost A K X env)"
proof (cases "get_eta_var rb 0 t = raiseW ASSIGN")
  case True
  then have "assignment alg rb t u env = raiseW ASSIGN" by (simp add: assignment_def raiseW_def bindW_def)
  then show ?thesis by simp
next
  case False
  with get_eta_var_cases[of rb 0 t] obtain v T where gv: "get_eta_var rb 0 t = returnW (v, T)" by blast
  then have gev: "okW (get_eta_var rb 0 t) (v, T)" by simp
  let ?\<theta> = "tyenv env" and ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  define "is" where "is = rev (map (\<lambda>j. 0 + integer_of_nat j) [0..<length rb])"
  have t: "t = app (Var v T) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have hv: "head_of t = Var v T" by (simp add: t app_apps head_of_apps)
  with ah have v0: "vt_lookup (tenv env) v = None" by (simp add: ahd_def)
  have vT: "(v, T) \<in> X \<union> evars env" using pd(1) by (auto simp: t app_apps vars_apps)
  have kT: "tvars T \<subseteq> tvars_env ?\<theta> \<union> A" using pd(3) by (simp add: t ttvars_def app_apps typs_apps)
  have vk: "tok env (vars u \<union> evars env)" using tok_mono[OF tok_einv[OF ei wi pd(6)]] pd(2) by blast
  from pd(9)[OF r0] obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
    by blast
  have w0: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi r0] by blast+
  have dro: "dfd (rigid_occurs_term env v u)"
    by (rule rigid_occurs_term_dfd[OF e(6,7,3,4) vk termip_unfc0[OF ei wi ty0(3)]])
  show ?thesis
  proof (rule dfd_cases[OF dro])
    fix x assume "rigid_occurs_term env v u = Some (Err x)" "clashx x"
    then show ?thesis using gv by (simp add: assignment_def liftM_def bindW_def cxokE_def returnW_def)
  next
  fix oc assume oc0: "rigid_occurs_term env v u = Some (Ok oc)"
  have oc: "rigid_occurs_term env v u = return oc" "oc = NoOcc \<longrightarrow> (\<forall>y\<in>fst ` vars u. (v, y) \<notin> (dep env)\<^sup>*)"
    using oc0 rigid_occurs_term_sound[of env v u, OF _ e(3)] by (auto simp: return_def)
  show ?thesis
  proof (cases oc)
    case Rigid
    then have "assignment alg rb t u env = raiseW CANTUNIFY" using gv oc(1) by (simp add: assignment_def)
    then show ?thesis by simp
  next
    case Nonrigid
    then have "assignment alg rb t u env = raiseW ASSIGN" using gv oc(1) by (simp add: assignment_def)
    then show ?thesis by simp
  next
    case NoOcc
    from body_type_term[OF e(2) refl kT] obtain T1 where bt: "body_type env T = return T1" "tvars T1 \<subseteq> tvars_env ?\<theta> \<union> A"
      by blast
    have tvu: "ttvars u \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A" using pd(4,5) by blast
    from env_fastype_term[OF e(2) refl ty0(3,1) pd(8) tvu] obtain T2 where
      ft: "env_fastype env (map snd rb) u = return T2" "tvars T2 \<subseteq> tvars_env ?\<theta> \<union> A" "tnorm ?\<theta> T2 = T0"
      by blast
    have c2: "cert_typ alg ar (tsubst ?\<rho> T2)" using bs_env_cert[OF ty0(1,3) pd(8)] ft(3) by simp
    from binder_types_term[OF e(2) refl kT] obtain Ts where bts: "binder_types env T = return Ts" by blast
    have "tsubst ?\<rho> T = map (tsubst ?\<rho>) Ts \<Rrightarrow> tsubst ?\<rho> T1"
      by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt(1)[unfolded return_def] r0(1)])
    moreover have "cert_typ alg ar (tsubst ?\<rho> T)"
    proof -
      from ty0(2) obtain Us where "e0 \<turnstile> Var v (tsubst ?\<rho> T) : Us"
        by (auto simp: t app_apps inst_apps dest!: list_app_typeD)
      then show ?thesis by auto
    qed
    ultimately have c1: "cert_typ alg ar (tsubst ?\<rho> T1)" by (simp add: cert_typ_funs)
    note cu = cunify_types_term[OF ei finK bt(2) cert_typ_rev[OF ei c1 bt(2)] ft(2) cert_typ_rev[OF ei c2 ft(2)]]
    have asg: "assignment alg rb t u env =
        bindW (cunify_types alg T1 T2 env) (\<lambda>env'. liftM (update (v, T) (rlist_abs rb u) env'))"
      using gv oc(1) bt(1) ft(1) NoOcc by (simp add: assignment_def fastype_def)
    show ?thesis
      unfolding asg
    proof (rule cxokE_bindW[OF cxokE_xokW[OF cu]])
      fix env1 assume "okW (cunify_types alg T1 T2 env) env1" and P1: "einv A K env1 \<and> tenv env1 = tenv env \<and>
        textends (tyenv env) (tyenv env1) \<and> maxidx env \<le> maxidx env1 \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1) \<and> tnew A env A env1 \<and> (\<forall>\<rho>. tsol (tyenv env1) \<rho> \<longrightarrow> tsubst \<rho> T1 = tsubst \<rho> T2) \<and>
        (tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K))"
      then have ei1: "einv A K env1" and te: "tenv env1 = tenv env" and tx: "textends (tyenv env) (tyenv env1)"
        and mx: "maxidx env \<le> maxidx env1" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" and tn: "tnew A env A env1"
        and card: "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
        by blast+
      have wi1: "winv env1 X" by (rule winv_tyext[OF wi te tx mx])
      have st1: "sstep A K X env env1" by (rule sstep_tyext[OF te tx mx tv tn card])
      have p1: "upok A env1 rb X t u" by (rule upok_mono[OF p sstepD(1)[OF st1] tv])
      let ?b = "rlist_abs rb u"
      have v1: "vt_lookup (tenv env1) v = None" using v0 te by simp
      obtain env' where upd: "update (v, T) ?b env1 = return env'" using update_ok[OF v1] by blast
      note upd' = upd[unfolded return_def]
      have vb: "vars ?b = vars u" by (simp add: rlist_abs_abs_list)
      have dep1: "dep env1 = dep env" using te by (simp add: dep_def)
      have ei': "einv A K env'"
      proof (rule einv_update[OF ei1 upd'])
        fix y U assume "(y, U) \<in> vars ?b"
        then have "(y, U) \<in> vars u" using vb by simp
        then have "y \<in> fst ` vars u" by (rule image_eqI[of _ fst "(y, U)", rotated]) simp
        from oc(2)[rule_format, OF NoOcc this] dep1 show "(v, y) \<notin> (dep env1)\<^sup>*" by simp
      next
        show "closed ?b" unfolding rlist_abs_abs_list
          by (rule closed_abs_list) (use pd(8) in \<open>simp add: ilength_eq\<close>)
      next
        have "vinv ?\<rho> env X" using winvD[OF wi r0] by blast
        then have "snd v \<le> maxidx env" using vT unfolding vinv_def by (blast dest: belowD)
        then show "snd v \<le> maxidx env1" using mx by simp
      next
        have "btvars (rev rb) = btvars rb" by (simp add: btvars_def)
        then show "tvars T \<union> ttvars ?b \<subseteq> tvars_env (tyenv env1) \<union> A"
          using kT pd(4,5) tv by (auto simp: rlist_abs_abs_list ttvars_abs_list)
      qed
      have wi': "winv env' X" by (rule winv_stepg[OF eta_var_step[OF gev upd'] wi1 p1])
      have Fin: "v \<in> fst ` (X \<union> evars env1)" using vT evars_extends[OF sstepD(1)[OF st1]] by force
      have lt: "card (ubv env' X) < card (ubv env1 X)"
        by (rule card_ubv_update(1)[OF finX upd' Fin]) (use vb pd(2) evars_extends[OF sstepD(1)[OF st1]] in auto)
      have st2: "sstep A K X env1 env'"
        using lt extends_update[OF upd'] ok_update(3)[OF upd'] by (simp add: sstep_def tnew_tyenv)
      have "tenv env' \<noteq> tenv env" using ok_update(2)[OF upd'] v0 te
        by (metis option.distinct(1) vt_lookup_update)
      then show "cxokE (\<lambda>e. e = ASSIGN \<or> e = CANTUNIFY) (liftM (update (v, T) ?b env1)) (apost A K X env)"
        using upd ei' wi' sstep_trans[OF st1 st2] by (intro cxokE_okI[of _ env']) (simp_all add: apost_def)
    qed simp
  qed
  qed
qed


subsection \<open>Results of simplification\<close>

lemma ccuok_handle_assign:
  assumes m: "cxokE (\<lambda>e. e = ASSIGN \<or> e = CANTUNIFY) m P" and P: "\<And>x. P x \<Longrightarrow> Q (f x)" and r: "Q r"
  shows "ccuok (handleW (bindW m (\<lambda>x. returnW (f x))) (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
  using m P r unfolding cxokE_def
  by (auto simp: handleW_def bindW_def returnW_def raiseW_def clashW_def split: option.splits xres.splits uexn.splits)

definition smeasc :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> dpair \<Rightarrow> nat \<times> nat \<times> nat" where
  "smeasc K X env dp = (card (uvarsA (tyenv env) K), card (ubv env X), dmc env dp)"

lemma dmc_args:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    and rh: "rigid h" "rigid h'" and len: "length ss = length ts"
  shows "sum_list (map (dmc env) (dzip rb ss ts)) < dmc env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
proof -
  let ?L = "LMc (rho0 env) env (benv (rho0 env) rb)"
  from upok_unfc[OF ei wi p] obtain T where
    T: "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env (h \<degree>\<degree> ss)) : T"
      "benv (rho0 env) rb \<turnstile> inst (rho0 env) (unfc env (h' \<degree>\<degree> ts)) : T"
    by blast
  have s: "sum_list (map (dmc env) (dzip rb ss ts)) = sum_list (map ?L ss) + sum_list (map ?L ts)"
    using len by (induction ss ts rule: list_induct2) (simp_all add: dmc_def)
  have "dmc env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts) = tsz T + sum_list (map ?L ss) + (tsz T + sum_list (map ?L ts))"
    using LMc_rigid[OF rh(1) T(1)] LMc_rigid[OF rh(2) T(2)] by (simp add: dmc_def)
  with s tsz_pos[of T] show ?thesis by simp
qed


lemma fr_case_dfd:
  assumes finX: "finite X" and finK: "finite K" and ei: "einv A K env" and wi: "winv env X"
    and p: "upok A env rb X t u" and aht: "ahd env t" and ahu: "ahd env u"
    and hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)"
  shows "ccuok (handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
    (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) (spost A K X env ffs frs)"
proof (rule ccuok_handle_assign[OF assignment_dfd[OF finX finK ei wi p aht]])
  fix env' assume "apost A K X env env'"
  then show "spost A K X env ffs frs (env', ffs, frs)" by (simp add: apost_def spost_def sinv_def)
next
  have "sinv A K X env ([] @ [(rb, t, u)])" by (simp add: sinv_def ei wi p)
  moreover have "frs0 (rb, t, u)" using ahd_nonAbs[OF aht] ahd_nonAbs[OF ahu] hv hr by (simp add: frs0_def)
  moreover have "hunb env (rb, t, u)" using aht hv hr by (auto simp: hunb_def ahd_def)
  ultimately show "spost A K X env ffs frs (env, ffs, (rb, t, u) # frs)"
    using spost_new[of A K X env "[]" "[(rb, t, u)]" env ffs frs] sstep_refl by simp
qed

context
  fixes A K X B
  assumes IH: "\<And>env1 dp1 ffs1 frs1. (smeasc K X env1 dp1, B) \<in> ulex \<Longrightarrow> sinv A K X env1 [dp1] \<Longrightarrow>
      ccuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)"
    and finX: "finite X" and finK: "finite K"
begin

lemma simrands_dfd:
  assumes hh: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
    and B: "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)"
  shows "length ss = length ts \<Longrightarrow> sinv A K X env (dzip rb ss ts) \<Longrightarrow> sstep A K X env0 env \<Longrightarrow>
    (tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> sum_list (map (dmc env) (dzip rb ss ts)) < d0) \<Longrightarrow>
    ccuok (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) (env, ffs, frs)) (spost A K X env ffs frs)"
proof (induction ss arbitrary: ts ffs frs env rule: rev_induct)
  case Nil
  then have "ts = []" by simp
  with Nil show ?case using simrands_atoms[OF hh] spost_refl by simp
next
  case (snoc s ss)
  from snoc.prems(1) obtain ts' t where ts: "ts = ts' @ [t]" and len: "length ss = length ts'"
    by (cases ts rule: rev_exhaust) auto
  have dz: "dzip rb (ss @ [s]) ts = dzip rb ss ts' @ [(rb, s, t)]" using len ts by simp
  have si0: "sinv A K X env (dzip rb ss ts')" by (rule sinv_mono[OF snoc.prems(2)[unfolded dz]]) auto
  have lt0: "sum_list (map (dmc env) (dzip rb ss ts')) < d0"
    if "tyenv env = tyenv env0" "tenv env = tenv env0" using snoc.prems(4)[OF that, unfolded dz] by simp
  have r0: "ccuok (simrands (SIMPL0 alg) rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts') (env, ffs, frs)) (spost A K X env ffs frs)"
    by (rule snoc.IH[OF len si0 snoc.prems(3) lt0])
  show ?case unfolding ts simrands_snoc
  proof (rule cxokE_bindW[OF r0])
    fix st1 assume sp1: "spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from sp1 st1 obtain a1 b1 where s1: "sinv A K X env1 (a1 @ b1)" "sstep A K X env env1"
      unfolding spost_def by auto
    have si1: "sinv A K X env1 [(rb, s, t)]"
    proof (rule sinv_ext[OF sinv_mono[OF snoc.prems(2)] _ _ s1(2)])
      show "set [(rb, s, t)] \<subseteq> set (dzip rb (ss @ [s]) ts)" unfolding dz by simp
    qed (use s1(1) in \<open>simp_all add: sinv_def\<close>)
    have m: "(smeasc K X env1 (rb, s, t), B) \<in> ulex" unfolding smeasc_def B
    proof (rule ulex_sstep[OF sstep_trans[OF snoc.prems(3) s1(2)]])
      assume e1: "tyenv env1 = tyenv env0" "tenv env1 = tenv env0"
      have e0: "tyenv env = tyenv env0" "tenv env = tenv env0"
        using extends_mid[OF sstepD(1)[OF snoc.prems(3)] sstepD(1)[OF s1(2)]] e1 by auto
      then have "dmc env1 = dmc env" using e1 dmc_same[of env1 env] by simp
      with snoc.prems(4)[OF e0, unfolded dz] show "dmc env1 (rb, s, t) < d0" by simp
    qed
    from IH[OF m si1, of ffs1 frs1] show "ccuok (SIMPL0 alg (rb, s, t) st1) (spost A K X env ffs frs)"
      unfolding st1 by (rule cxokE_mono) (rule spost_trans[OF sp1[unfolded st1]])
  qed
qed

lemma rigid_rigid_dfd:
  assumes hp: "hpostc A K X env0 dp0 (rb, t, u) env" and B: "B = smeasc K X env0 dp0"
    and st2: "sstep A K X env env2" and te2: "tenv env2 = tenv env" and ei2: "einv A K env2" and wi2: "winv env2 X"
    and rh: "rigid (head_of t)" "rigid (head_of u)"
    and hh: "\<And>\<rho>. tsol (tyenv env2) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> inst \<rho> (head_of t) = inst \<rho> (head_of u)"
  shows "ccuok (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (spost A K X env ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and st0: "sstep A K X env0 env" and dmle: "tyenv env = tyenv env0 \<Longrightarrow> dmc env (rb, t, u) \<le> dmc env0 dp0"
    by (simp_all add: hpostc_def)
  define h where "h = head_of t"
  define ss where "ss = snd (strip_comb t)"
  define h' where "h' = head_of u"
  define ts where "ts = snd (strip_comb u)"
  have tt: "t = h \<degree>\<degree> ss" unfolding h_def ss_def by (rule t_apps)
  have uu: "u = h' \<degree>\<degree> ts" unfolding h'_def ts_def by (rule t_apps)
  have p2: "upok A env2 rb X (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts)"
    using upok_mono[OF p sstepD(1,2)[OF st2]] tt uu by simp
  note ra = rigid_args_pok[OF p2 rh[folded h_def h'_def] hh[folded h_def h'_def] einv_rho0[OF ei2]]
  have si2: "sinv A K X env2 (dzip rb ss ts)" by (rule sinv_dzip[OF ei2 wi2 ra(2)])
  have B': "B = (card (uvarsA (tyenv env0) K), card (ubv env0 X), dmc env0 dp0)" by (simp add: B smeasc_def)
  have lt: "sum_list (map (dmc env2) (dzip rb ss ts)) < dmc env0 dp0"
    if e: "tyenv env2 = tyenv env0" "tenv env2 = tenv env0"
  proof -
    have e1: "tyenv env = tyenv env0" by (rule extends_mid(1)[OF sstepD(1)[OF st0] sstepD(1)[OF st2] e(1)])
    then have "dmc env2 = dmc env" using e(1) dmc_same[OF te2] by simp
    moreover have "sum_list (map (dmc env) (dzip rb ss ts)) < dmc env (rb, h \<degree>\<degree> ss, h' \<degree>\<degree> ts)"
      by (rule dmc_args[OF ei wi p[unfolded tt uu] rh[folded h_def h'_def] ra(1)])
    ultimately show ?thesis using dmle[OF e1] tt uu by simp
  qed
  have hA: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u'. h' = f $ u')" unfolding h_def h'_def by (simp_all add: head_of_not_App)
  from simrands_dfd[OF hA B' ra(1) si2 sstep_trans[OF st0 st2] lt, of u0 ffs frs]
  have "ccuok (simrands (SIMPL0 alg) rb u0 t u (env2, ffs, frs)) (spost A K X env2 ffs frs)"
    unfolding tt uu .
  then show ?thesis
  proof (rule cxokE_mono)
    have "spost A K X env ffs frs (env2, [] @ ffs, [] @ frs)"
      by (rule spost_new) (use ei2 wi2 st2 in \<open>simp_all add: sinv_def\<close>)
    then show "spost A K X env2 ffs frs x \<Longrightarrow> spost A K X env ffs frs x" for x by (simp add: spost_trans)
  qed
qed

lemma SIMPL0_rest_dfd:
  assumes hp: "hpostc A K X env0 dp0 (rb, t, u) env" and B: "B = smeasc K X env0 dp0"
  shows "ccuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
proof -
  from hp have ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
    and aht: "ahd env t" and ahu: "ahd env u"
    by (simp_all add: hpostc_def)
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 rb" "e0 \<turnstile> inst ?\<rho> t : T0" "e0 \<turnstile> inst ?\<rho> u : T0"
    using pd(9)[OF r0] by blast
  have tvh: "ttvars (head_of t) \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars (head_of u) \<subseteq> tvars_env (tyenv env) \<union> A"
    using ttvars_head[of t] ttvars_head[of u] pd(3,4) by blast+
  have FR: "ccuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if hv: "head_of t = Var F Ft" and hr: "rigid (head_of u)" for F Ft
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb t u env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    with fr_case_dfd[OF finX finK ei wi p aht ahu hv hr] show ?thesis by simp
  qed
  have RF: "ccuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if hv: "head_of u = Var F Fu" and hr: "rigid (head_of t)" for F Fu
  proof -
    have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
      handleW (bindW (assignment alg rb u t env) (\<lambda>env'. returnW (env', ffs, frs)))
        (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)"
      using hv hr by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    with fr_case_dfd[OF finX finK ei wi upok_sym[OF p] ahu aht hv hr] show ?thesis by simp
  qed
  have CF: "ccuok (SIMPL0_rest SIMPL0 alg rb t u env ffs frs) (spost A K X env ffs frs)"
    if ht: "head_of t = hc" and hu: "head_of u = hd"
      and c: "(hc = Const a Tc \<and> hd = Const a Tu) \<or> (hc = Free a Tc \<and> hd = Free a Tu)"
      and eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
        bindW (cunify_types alg Tc Tu env) (\<lambda>env'. simrands (SIMPL0 alg) rb u t u (env', ffs, frs))"
    for hc hd a Tc Tu
  proof -
    have cT: "cert_typ alg ar (tsubst ?\<rho> Tc)"
      using c head_Const_cert[OF ty0(2)] head_Free_cert[OF ty0(2)] ht by blast
    have cU: "cert_typ alg ar (tsubst ?\<rho> Tu)"
      using c head_Const_cert[OF ty0(3)] head_Free_cert[OF ty0(3)] hu by blast
    have kT: "tvars Tc \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht c by auto
    have kU: "tvars Tu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu c by auto
    note cu = cunify_types_term[OF ei finK kT cert_typ_rev[OF ei cT kT] kU cert_typ_rev[OF ei cU kU]]
    show ?thesis unfolding eq
    proof (rule cxokE_bindW[OF cxokE_xokW[OF cu refl]])
      fix env2 assume P: "einv A K env2 \<and> tenv env2 = tenv env \<and>
        textends (tyenv env) (tyenv env2) \<and> maxidx env \<le> maxidx env2 \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and> tnew A env A env2 \<and> (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu) \<and>
        (tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K))"
      then have ei2: "einv A K env2" and te: "tenv env2 = tenv env" and tx: "textends (tyenv env) (tyenv env2)"
        and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and tn: "tnew A env A env2"
        and sol: "\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> Tc = tsubst \<rho> Tu"
        and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
        by blast+
      have rh: "rigid (head_of t)" "rigid (head_of u)" using ht hu c by auto
      have hh: "inst \<rho> (head_of t) = inst \<rho> (head_of u)" if "tsol (tyenv env2) \<rho>" for \<rho>
        using sol that ht hu c by auto
      show "ccuok (simrands (SIMPL0 alg) rb u t u (env2, ffs, frs)) (spost A K X env ffs frs)"
        by (rule rigid_rigid_dfd[OF hp B sstep_tyext[OF te tx mx tv tn card] te ei2 winv_tyext[OF wi te tx mx] rh hh])
    qed
  qed
  from ahd_head[OF aht] show ?thesis
  proof
    assume rt: "rigid (head_of t)"
    from ahd_head[OF ahu] show ?thesis
    proof
      assume ru: "rigid (head_of u)"
      show ?thesis
      proof (cases "head_of t")
        case (Const a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Const a Tb")
          case True
          then obtain Tb where hb: "head_of u = Const a Tb" by blast
          show ?thesis
            by (rule CF[OF Const hb]) (simp_all add: SIMPL0_rest_def Const hb)
        next
          case False
          then show ?thesis using Const ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Free a Ta)
        show ?thesis
        proof (cases "\<exists>Tb. head_of u = Free a Tb")
          case True
          then obtain Tb where hb: "head_of u = Free a Tb" by blast
          show ?thesis
            by (rule CF[OF Free hb]) (simp_all add: SIMPL0_rest_def Free hb)
        next
          case False
          then show ?thesis using Free ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      next
        case (Bound i)
        show ?thesis
        proof (cases "head_of u = Bound i")
          case True
          have "SIMPL0_rest SIMPL0 alg rb t u env ffs frs = simrands (SIMPL0 alg) rb u t u (env, ffs, frs)"
            by (simp add: SIMPL0_rest_def Bound True)
          moreover have "ccuok (simrands (SIMPL0 alg) rb u t u (env, ffs, frs)) (spost A K X env ffs frs)"
            by (rule rigid_rigid_dfd[OF hp B sstep_refl refl ei wi rt ru]) (simp add: Bound True)
          ultimately show ?thesis by simp
        next
          case False
          then show ?thesis using Bound ru by (cases "head_of u") (auto simp: SIMPL0_rest_def)
        qed
      qed (use rt in simp_all)
    next
      assume "\<exists>F U. head_of u = Var F U \<and> vt_lookup (tenv env) F = None"
      then obtain F U where "head_of u = Var F U" by blast
      from RF[OF this rt] show ?thesis .
    qed
  next
    assume "\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None"
    then obtain F Ft where ht: "head_of t = Var F Ft" by blast
    from ahd_head[OF ahu] show ?thesis
    proof
      assume "rigid (head_of u)"
      from FR[OF ht this] show ?thesis .
    next
      assume "\<exists>G U. head_of u = Var G U \<and> vt_lookup (tenv env) G = None"
      then obtain G Gu where hu: "head_of u = Var G Gu" by blast
      have kF: "tvars Ft \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(1) ht by simp
      have kG: "tvars Gu \<subseteq> tvars_env (tyenv env) \<union> A" using tvh(2) hu by simp
      from body_type_ok[OF ei kF head_Var_cert[OF ty0(2) ht]] obtain B1 where
        b1: "body_type env Ft = return B1" "tvars B1 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B1" "sorts_ok alg B1"
        by blast
      from body_type_ok[OF ei kG head_Var_cert[OF ty0(3) hu]] obtain B2 where
        b2: "body_type env Gu = return B2" "tvars B2 \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar B2" "sorts_ok alg B2"
        by blast
      have eq: "SIMPL0_rest SIMPL0 alg rb t u env ffs frs =
          bindW (cunify_types alg B1 B2 env) (\<lambda>env'. returnW (env', (rb, t, u) # ffs, frs))"
        by (simp add: SIMPL0_rest_def ht hu b1(1) b2(1))
      show ?thesis unfolding eq
      proof (rule cxokE_bindW[OF cxokE_xokW[OF cunify_types_term[OF ei finK b1(2-4) b2(2-4)] refl]])
        fix env2 assume P: "einv A K env2 \<and> tenv env2 = tenv env \<and>
          textends (tyenv env) (tyenv env2) \<and> maxidx env \<le> maxidx env2 \<and>
          tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2) \<and> tnew A env A env2 \<and> (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> B1 = tsubst \<rho> B2) \<and>
          (tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K))"
        then have ei2: "einv A K env2" and te: "tenv env2 = tenv env" and tx: "textends (tyenv env) (tyenv env2)"
          and mx: "maxidx env \<le> maxidx env2" and tv: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" and tn: "tnew A env A env2"
          and card: "tyenv env2 = tyenv env \<or> card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)"
          by blast+
        have st2: "sstep A K X env env2" by (rule sstep_tyext[OF te tx mx tv tn card])
        have wi2: "winv env2 X" by (rule winv_tyext[OF wi te tx mx])
        have "sinv A K X env2 ([(rb, t, u)] @ [])"
          using upok_mono[OF p sstepD(1,2)[OF st2]] ei2 wi2 by (simp add: sinv_def)
        moreover have "ffs0 (rb, t, u)" using ahd_nonAbs[OF aht] ahd_nonAbs[OF ahu] ht hu by (simp add: ffs0_def)
        moreover have "hunb env2 (rb, t, u)" using aht ahu ht hu te by (auto simp: hunb_def ahd_def)
        ultimately have "spost A K X env ffs frs (env2, [(rb, t, u)] @ ffs, [] @ frs)"
          using spost_new[of A K X env2 "[(rb, t, u)]" "[]" env ffs frs] st2 by simp
        then show "ccuok (returnW (env2, (rb, t, u) # ffs, frs)) (spost A K X env ffs frs)" by simp
      qed
    qed
  qed
qed

lemma SIMPL0_step_dfd:
  assumes B: "B = smeasc K X env0 dp0" and si: "sinv A K X env0 [dp0]"
  shows "ccuok (SIMPL0 alg dp0 (env0, ffs, frs)) (spost A K X env0 ffs frs)"
proof -
  obtain rb t u where dp0: "dp0 = (rb, t, u)" by (cases dp0)
  from si dp0 have ei: "einv A K env0" and wi: "winv env0 X" and p: "upok A env0 rb X t u"
    by (simp_all add: sinv_def)
  show ?thesis unfolding SIMPL0_unfold
  proof (rule cxokE_bindW[OF head_norm_dpair_dfd[OF finK ei wi p, folded dp0]])
    fix x assume hp0: "case x of (dp', env') \<Rightarrow> hpostc A K X env0 dp0 dp' env'"
    obtain rb' t' u' env where x: "x = ((rb', t', u'), env)" by (cases x) auto
    from hp0 x have hp: "hpostc A K X env0 dp0 (rb', t', u') env" by simp
    have r: "ccuok (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (spost A K X env ffs frs)"
      by (rule SIMPL0_rest_dfd[OF hp B])
    have "spost A K X env0 ffs frs (env, [] @ ffs, [] @ frs)"
      by (rule spost_new) (use hp in \<open>simp_all add: hpostc_def sinv_def\<close>)
    then have "ccuok (SIMPL0_rest SIMPL0 alg rb' t' u' env ffs frs) (spost A K X env0 ffs frs)"
      using cxokE_mono[OF r spost_trans] by simp
    then show "ccuok ((\<lambda>(dp, env'). case dp of (rb, t, u) \<Rightarrow> SIMPL0_rest SIMPL0 alg rb t u env' ffs frs) x)
        (spost A K X env0 ffs frs)" by (simp add: x)
  qed
qed

end

subsection \<open>Termination of \<open>SIMPL0\<close>\<close>

text \<open>
  \<^const>\<open>SIMPL0\<close> terminates on a well-formed pair, raising at most \<open>CANTUNIFY\<close>. The new pairs keep
  the invariant, are flex-flex or flex-rigid, and their head variables are unbound unless the
  term environment changed. The measure is \<^const>\<open>smeasc\<close>.
\<close>

theorem SIMPL0_dfd:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env [dp]"
  shows "ccuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)"
proof -
  have "\<forall>env dp ffs frs. smeasc K X env dp = m \<longrightarrow> sinv A K X env [dp] \<longrightarrow>
      ccuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)" for m
  proof (induction m rule: wf_induct_rule[OF wf_ulex])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dp ffs frs assume m: "smeasc K X env dp = m" and si: "sinv A K X env [dp]"
      show "ccuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)"
      proof (rule SIMPL0_step_dfd[OF _ fin m[symmetric] si])
        fix env1 dp1 ffs1 frs1 assume "(smeasc K X env1 dp1, m) \<in> ulex" "sinv A K X env1 [dp1]"
        then show "ccuok (SIMPL0 alg dp1 (env1, ffs1, frs1)) (spost A K X env1 ffs1 frs1)" using "1.IH" by blast
      qed
    qed
  qed
  with si show ?thesis by blast
qed

lemma foldrW_SIMPL0_dfd:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env dps \<Longrightarrow>
    ccuok (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (spost A K X env ffs frs)"
proof (induction dps)
  case Nil
  then show ?case using spost_refl[of A K X env ffs frs] by (simp add: sinv_def)
next
  case (Cons dp dps)
  have r: "ccuok (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (spost A K X env ffs frs)"
    by (rule Cons.IH[OF sinv_mono[OF Cons.prems(1)]]) auto
  show ?case unfolding foldrW.simps
  proof (rule cxokE_bindW[OF r])
    fix st1 assume sp1: "spost A K X env ffs frs st1"
    obtain env1 ffs1 frs1 where st1: "st1 = (env1, ffs1, frs1)" by (cases st1)
    from sp1 st1 obtain a1 b1 where s1: "sinv A K X env1 (a1 @ b1)" "sstep A K X env env1"
      unfolding spost_def by auto
    have "sinv A K X env1 [dp]"
      by (rule sinv_ext[OF sinv_mono[OF Cons.prems(1)] _ _ s1(2)]) (use s1(1) in \<open>simp_all add: sinv_def\<close>)
    from SIMPL0_dfd[OF fin this, of ffs1 frs1]
    show "ccuok (SIMPL0 alg dp st1) (spost A K X env ffs frs)"
      unfolding st1 by (rule cxokE_mono) (rule spost_trans[OF sp1[unfolded st1]])
  qed
qed

subsection \<open>Termination of \<open>SIMPL\<close>\<close>

lemma changed_dfd:
  assumes ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "tok env (vars t \<union> evars env) \<Longrightarrow> dfd (changed env t) \<and> (\<forall>b. ok (changed env t) b \<longrightarrow> b = chd env t)"
proof (induction t)
  case (Var x T)
  have lk: "lookup env x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
    | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
    by (rule lookup_def_tok[OF ac tc]) (use Var in \<open>auto intro: tok_mono\<close>)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    then show ?thesis using lk by (simp add: chd_def bindM_def return_def)
  next
    case (Some p)
    obtain U u where p: "p = (U, u)" by force
    have cl: "loose \<noteq> {}" if "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U"
      by (rule tok_clash_ne[OF Var.prems _ Some[unfolded p] that]) auto
    show ?thesis using lk Some p cl
      by (cases "tnorm (tyenv env) T = tnorm (tyenv env) U") (simp_all add: chd_def bindM_def return_def var_clash_def raise_def clashx_def)
  qed
next
  case (App f u)
  then have "dfd (changed env f) \<and> (\<forall>b. ok (changed env f) b \<longrightarrow> b = chd env f)" by (auto intro: tok_mono)
  then show ?case by (simp add: chd_def)
qed (simp_all add: chd_def return_def)

lemma existsM_dfd:
  "(\<And>x. x \<in> set xs \<Longrightarrow> dfd (P x) \<and> (\<forall>b. ok (P x) b \<longrightarrow> b = Q x)) \<Longrightarrow>
    dfd (existsM P xs) \<and> (\<forall>b. ok (existsM P xs) b \<longrightarrow> b = (\<exists>x\<in>set xs. Q x))"
proof (induction xs)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons x xs)
  have h: "dfd (P x)" "\<And>b. ok (P x) b \<Longrightarrow> b = Q x" using Cons.prems[of x] by auto
  have IH: "dfd (existsM P xs)" "\<And>b. ok (existsM P xs) b \<Longrightarrow> b = (\<exists>x\<in>set xs. Q x)"
    using Cons.IH Cons.prems by auto
  show ?case
  proof (rule dfd_cases[OF h(1)])
    fix e assume "P x = Some (Err e)" "clashx e"
    then show ?thesis by (simp add: bindM_def)
  next
    fix b assume b: "P x = Some (Ok b)"
    with h(2) have "b = Q x" by simp
    with b IH show ?thesis by (cases b) (auto simp: bindM_def return_def)
  qed
qed

theorem SIMPL_dfd:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env dps"
  shows "ccuok (SIMPL alg env dps) (simpl_post A K X env)"
proof -
  have "\<forall>env dps. (card (uvarsA (tyenv env) K), card (ubv env X)) = m \<longrightarrow> sinv A K X env dps \<longrightarrow>
      ccuok (SIMPL alg env dps) (simpl_post A K X env)" for m
  proof (induction m rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
    case (1 m)
    show ?case
    proof (intro allI impI)
      fix env dps assume m: "(card (uvarsA (tyenv env) K), card (ubv env X)) = m" and si: "sinv A K X env dps"
      show "ccuok (SIMPL alg env dps) (simpl_post A K X env)"
      proof (subst SIMPL.simps, rule cxokE_bindW[OF foldrW_SIMPL0_dfd[OF fin si]])
        fix st assume sp: "spost A K X env [] [] st"
        obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
        from sp st have ab: "sinv A K X env' (ffs @ frs)" "\<forall>dp\<in>set ffs. ffs0 dp" "\<forall>dp\<in>set frs. frs0 dp"
          "tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (ffs @ frs). hunb env' dp)" "sstep A K X env env'"
          unfolding spost_def by auto
        have si': "sinv A K X env' (frs @ ffs)" by (rule sinv_mono[OF ab(1)]) auto
        then have ei': "einv A K env'" and wi': "winv env' X" by (simp_all add: sinv_def)
        note e' = einvD[OF ei']
        let ?ch = "chd env'"
        let ?P = "\<lambda>(_, t, u). do {b \<leftarrow> changed env' t; if b then return True else changed env' u}"
        have ex: "dfd (existsM ?P (frs @ ffs)) \<and> (\<forall>b. ok (existsM ?P (frs @ ffs)) b \<longrightarrow>
            b = (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u))"
        proof (rule existsM_dfd)
          fix dp assume dp: "dp \<in> set (frs @ ffs)"
          obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
          from si' have "\<forall>x\<in>set (frs @ ffs). case x of (rb, t, u) \<Rightarrow> upok A env' rb X t u" by (simp add: sinv_def)
          from bspec[OF this dp] dpe have p: "upok A env' rb X t u" by simp
          note pd = upokD[OF p]
          have vk: "tok env' (X \<union> evars env')" by (rule tok_einv[OF ei' wi' pd(6)])
          have ct: "dfd (changed env' t) \<and> (\<forall>b. ok (changed env' t) b \<longrightarrow> b = ?ch t)"
            by (rule changed_dfd[OF e'(6,7) tok_mono[OF vk]]) (use pd(1) in blast)
          have cu: "dfd (changed env' u) \<and> (\<forall>b. ok (changed env' u) b \<longrightarrow> b = ?ch u)"
            by (rule changed_dfd[OF e'(6,7) tok_mono[OF vk]]) (use pd(2) in blast)
          show "dfd (?P dp) \<and> (\<forall>b. ok (?P dp) b \<longrightarrow> b = (case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u))"
          proof (rule dfd_cases[OF conjunct1[OF ct]])
            fix e assume "changed env' t = Some (Err e)" "clashx e"
            then show ?thesis by (simp add: dpe bindM_def)
          next
            fix b assume b: "changed env' t = Some (Ok b)"
            with ct have "b = ?ch t" by simp
            with b cu show ?thesis by (cases b) (auto simp: dpe bindM_def return_def)
          qed
        qed
        have ex': "ok (existsM ?P (frs @ ffs)) b \<Longrightarrow> b = (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)" for b
          using ex by blast
        show "ccuok ((\<lambda>st. case st of (env', ffs, frs) \<Rightarrow> let dps = frs @ ffs in
              bindW (liftM (existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps))
                (\<lambda>b. if b then SIMPL alg env' dps else returnW st)) st) (simpl_post A K X env)"
        unfolding st prod.case Let_def
        proof (rule cxokE_bindW[OF cxokE_liftM[OF conjunct1[OF ex]]])
          fix b assume "existsM ?P (frs @ ffs) = return b"
          then have bb: "b = (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)"
            using ex' by (simp add: return_def)
          then show "b = (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)" .
        next
        fix b assume "okW (liftM (existsM ?P (frs @ ffs))) b"
          and bb: "b = (\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u)"
        show "ccuok (if b then SIMPL alg env' (frs @ ffs) else returnW (env', ffs, frs)) (simpl_post A K X env)"
        proof (cases "\<exists>dp\<in>set (frs @ ffs). case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u")
          case True
          have "tenv env' \<noteq> tenv env"
          proof
            assume "tenv env' = tenv env"
            with ab(4) have hu: "\<forall>dp\<in>set (frs @ ffs). hunb env' dp" by auto
            from True obtain dp where dp: "dp \<in> set (frs @ ffs)" "case dp of (_, t, u) \<Rightarrow> ?ch t \<or> ?ch u" by blast
            obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
            from bspec[OF hu dp(1)] dp(2) dpe show False by (simp add: hunb_chd)
          qed
          then have lt: "((card (uvarsA (tyenv env') K), card (ubv env' X)), m) \<in> less_than <*lex*> less_than"
            using sstepD(3,4)[OF ab(5)] m by (cases "tyenv env' = tyenv env") auto
          have "ccuok (SIMPL alg env' (frs @ ffs)) (simpl_post A K X env')" using "1.IH"[OF lt] si' by blast
          then have "ccuok (SIMPL alg env' (frs @ ffs)) (simpl_post A K X env)"
            by (rule cxokE_mono) (rule simpl_post_trans[OF ab(5)])
          then show ?thesis using True bb by simp
        next
          case False
          have "simpl_post A K X env (env', ffs, frs)"
            unfolding simpl_post_def prod.case
          proof (intro conjI ballI)
            show "sinv A K X env' (frs @ ffs)" by (rule si')
            show "sstep A K X env env'" by (rule ab(5))
            fix dp
            have hu: "hunb env' dp" if "dp \<in> set (frs @ ffs)"
            proof -
              obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
              from False that dpe have "\<not> ?ch t" "\<not> ?ch u" by auto
              then show ?thesis by (simp add: hunb_chd dpe)
            qed
            show "ff_shape env' dp" if "dp \<in> set ffs" using hu that ab(2) by (simp add: ff_shape_def)
            show "fr_shape env' dp" if "dp \<in> set frs" using hu that ab(3) by (simp add: fr_shape_def)
          qed
          then show ?thesis using False bb by simp
        qed
        qed
      qed
    qed
  qed
  with si show ?thesis by blast
qed


end


subsection \<open>Without loose names\<close>

text \<open>
  Without loose names, the clash cannot occur, and the statements above say that the computations
  terminate without exceptions other than the given ones.
\<close>

context pure_sig
begin

lemma clashx_pure [simp]: "\<not> clashx e"
  by (simp add: clashx_def)

lemma clashW_pure [simp]: "\<not> clashW e"
  by (simp add: clashW_def)

lemma cxokE_pure: "cxokE (\<lambda>e. e = E) m P \<longleftrightarrow> xokW E m P"
  by (simp add: cxokE_def xokW_def)

lemma dfd_pure: "dfd m \<longleftrightarrow> (\<exists>x. m = Some (Ok x))"
proof (cases m)
  case (Some a)
  then show ?thesis by (cases a) (auto simp: dfd_def)
qed (simp add: dfd_def)

theorem head_norm_dpair_term:
  assumes finK: "finite K" and ei: "einv A K env" and wi: "winv env X" and p: "upok A env rb X t u"
  shows "cuok (head_norm_dpair alg env (rb, t, u)) (\<lambda>(dp', env'). hpostc A K X env (rb, t, u) dp' env')"
  using head_norm_dpair_dfd[OF assms] by (simp add: cxokE_pure)

theorem assignment_term:
  assumes finX: "finite X" and finK: "finite K" and ei: "einv A K env" and wi: "winv env X"
    and p: "upok A env rb X t u" and ah: "ahd env t"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, Err ASSIGN)) \<or>
    cuok (assignment alg rb t u env) (apost A K X env)"
  using assignment_dfd[OF assms] by (auto simp: cxokE_def xokW_def)

theorem SIMPL0_term:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env [dp]"
  shows "cuok (SIMPL0 alg dp (env, ffs, frs)) (spost A K X env ffs frs)"
  using SIMPL0_dfd[OF assms] by (simp add: cxokE_pure)

lemma foldrW_SIMPL0_term:
  assumes fin: "finite X" "finite K"
  shows "sinv A K X env dps \<Longrightarrow> cuok (foldrW (SIMPL0 alg) dps (env, ffs, frs)) (spost A K X env ffs frs)"
  using foldrW_SIMPL0_dfd[OF assms] by (simp add: cxokE_pure)

theorem SIMPL_term:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env dps"
  shows "cuok (SIMPL alg env dps) (simpl_post A K X env)"
  using SIMPL_dfd[OF assms] by (simp add: cxokE_pure)

end

end
