section \<open>Finiteness of the Copies of \<open>mc\<close>\<close>

theory Unify_Mc_Fin
  imports Unify_Match_Fin Unify_Shape_Sound
begin

text \<open>
  The copies of the rigid side of a flex-rigid pair (\<^const>\<open>mc\<close>) form a finite enumeration of
  new problems in the invariant of the termination of \<^const>\<open>SIMPL\<close>. Each step of the copy is a
  step in the sense of the soundness proof, which keeps the typings of the invariant; the
  bindings of the copy are to terms over new, unbound variables, which keeps the environment
  acyclic. The copy recurses on the arguments of an imitation, normalized in the environment
  \<open>envM\<close> of \<open>MATCH\<close>: the measure is the number of rigid atoms of the \<open>\<beta>\<close>-normal form of the
  unfolding in \<open>envM\<close>, which is fixed during the copy.
\<close>

context pure_sig
begin

subsection \<open>Counting rigid atoms\<close>

text \<open>
  The measure of a term is the number of constants and free variables of the \<open>\<beta>\<close>-normal form of
  its unfolding. It does not depend on types, and \<open>\<eta>\<close>-expansion does not change it.
\<close>

fun rcnt :: "pterm \<Rightarrow> nat" where
  "rcnt (Const c T) = 1"
| "rcnt (Free x T) = 1"
| "rcnt (s $ t) = rcnt s + rcnt t"
| "rcnt (Abs a T t) = rcnt t"
| "rcnt (Var x T) = 0"
| "rcnt (Bound i) = 0"

lemma rcnt_incr_bv [simp]: "rcnt (incr_bv n k t) = rcnt t"
  by (induction n k t rule: incr_bv.induct) auto

lemma rcnt_subst: "rcnt s = 0 \<Longrightarrow> rcnt (t[s/k]) = rcnt t"
  by (induction t arbitrary: s k) (auto simp: subst_Bound)

lemma rcnt_inst [simp]: "rcnt (inst \<rho> t) = rcnt t"
  by (induction t) auto

lemma rcnt_apps: "rcnt (h \<degree>\<degree> ts) = rcnt h + sum_list (map rcnt ts)"
  by (induction ts arbitrary: h) simp_all

definition rsz :: "env \<Rightarrow> pterm \<Rightarrow> nat" where
  "rsz env t = rcnt (bnorm (unf env t))"

lemma no_redex_inst [simp]: "no_redex (inst \<rho> t) \<longleftrightarrow> no_redex t"
proof (induction t)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma bnorm_inst: "termip beta t \<Longrightarrow> bnorm (inst \<rho> t) = inst \<rho> (bnorm t)"
  using bnorm[of t] by (intro bnorm_eqI) (auto simp: inst_reds)

lemma rsz_inst: "termip beta (inst \<rho> (unf env t)) \<Longrightarrow> rsz env t = rcnt (bnorm (inst \<rho> (unf env t)))"
  using bnorm_inst[OF termip_inst[OF _ refl]] by (simp add: rsz_def)

lemma rsz_typed: "e \<turnstile> inst \<rho> (unf env t) : T \<Longrightarrow> rsz env t = rcnt (bnorm (inst \<rho> (unf env t)))"
  by (rule rsz_inst[OF type_implies_termi])

lemma termip_typed_unf: "e \<turnstile> inst \<rho> (unf env t) : T \<Longrightarrow> termip beta (unf env t)"
  by (rule termip_inst[OF type_implies_termi refl])

lemma rsz_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "termip beta (unf env t)"
  shows "rsz env t' = rsz env t"
proof -
  have "unf env t \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'" using head_norm_unf[of env t "Ok t'" t'] assms(1-3) by auto
  from bnorm_reds[OF assms(4) this] show ?thesis by (simp add: rsz_def)
qed

lemma rsz_Abs: "termip beta (unf env (Abs a T b)) \<Longrightarrow> rsz env (Abs a T b) = rsz env b"
  by (simp add: rsz_def bnorm_Abs)

lemma lift_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> lift s 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift t 0"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma rcnt_bnorm_eta:
  assumes sn: "termip beta s"
  shows "rcnt (bnorm (lift s 0 $ Bound 0)) = rcnt (bnorm s)"
proof -
  from bnorm[OF sn] have r: "s \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm s" and n: "no_redex (bnorm s)" by blast+
  have l: "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* lift (bnorm s) 0 $ Bound 0"
    by (rule rtrancl_beta_AppL[OF lift_reds[OF r]])
  show ?thesis
  proof (cases "is_Abs (bnorm s)")
    case True
    then obtain a A b where nb: "bnorm s = Abs a A b" by (cases "bnorm s") auto
    have "lift (bnorm s) 0 $ Bound 0 = Abs a A (incr_bv 1 1 b) $ Bound 0" by (simp add: nb)
    then have "lift (bnorm s) 0 $ Bound 0 \<rightarrow>\<^sub>\<beta> (incr_bv 1 1 b)[Bound 0/0]" by (simp only:) (rule beta.beta)
    moreover have "(incr_bv 1 1 b)[Bound 0/0] = b" by simp
    ultimately have "lift s 0 $ Bound 0 \<rightarrow>\<^sub>\<beta>\<^sup>* b" using l by (metis rtranclp.rtrancl_into_rtrancl)
    moreover have "no_redex b" using n nb by simp
    ultimately have "bnorm (lift s 0 $ Bound 0) = b" by (rule bnorm_eqI)
    then show ?thesis using nb by simp
  next
    case False
    then have "\<not> is_Abs (lift (bnorm s) 0)" by (cases "bnorm s") auto
    then have "no_redex (lift (bnorm s) 0 $ Bound 0)" using n by (simp add: no_redex_lift)
    from bnorm_eqI[OF l this] show ?thesis by simp
  qed
qed

text \<open>The arguments of an imitation have smaller measures:\<close>

lemma rsz_rigid_arg:
  assumes h: "h = Const c C \<or> h = Free c C" and ty: "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> ts)) : T"
    and t: "t \<in> set ts"
  shows "rsz env t < rsz env (h \<degree>\<degree> ts)"
proof -
  let ?xs = "map (inst \<rho> \<circ> unf env) ts"
  have i: "inst \<rho> (unf env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> ?xs"
    using h by (auto simp: unf_apps inst_apps)
  have at: "atom (inst \<rho> h)" using h by auto
  have b: "bnorm (inst \<rho> h \<degree>\<degree> ?xs) = inst \<rho> h \<degree>\<degree> map bnorm ?xs"
    by (rule bnorm_atom_apps[OF at ty[unfolded i]])
  have rh: "rcnt h = 1" using h by auto
  from typing_args[OF ty[unfolded i], of "inst \<rho> (unf env t)"] t obtain U where
    tyt: "e \<turnstile> inst \<rho> (unf env t) : U" by auto
  have "rcnt (bnorm (inst \<rho> (unf env t))) \<le> sum_list (map rcnt (map bnorm ?xs))"
    using t by (intro member_le_sum_list) auto
  then show ?thesis
    using rsz_typed[OF ty] rsz_typed[OF tyt] by (simp add: i b rcnt_apps rh)
qed

text \<open>Unfolding in an extension that keeps the reachable unbound variables unbound:\<close>

text \<open>\<open>\<eta>\<close>-expansion does not change the measure:\<close>

context
  fixes \<theta> A n assumes ti: "tinv ar n \<theta> A"
begin

lemma rsz_etif:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "tvars T \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> ok (etif \<theta> T t) t' \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
proof -
  let ?\<rho> = "tnorm_inst \<theta>"
  assume tv: "tvars T \<subseteq> tvars_env \<theta> \<union> A"
  have "tcons \<theta> T \<Longrightarrow> \<forall>t t' e. ok (etif \<theta> T t) t' \<longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
  proof (induction rule: tnorm_induct[OF ti_ac[OF ti] ti_tc[OF ti], consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) simp
  next
    case (Type a Ts)
    show ?case
    proof (intro allI impI)
      fix t t' e
      assume ok: "ok (etif \<theta> (Type a Ts) t) t'" and c: "cert_typ alg ar (tnorm \<theta> (Type a Ts))"
        and ty: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> (Type a Ts)"
      show "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts) \<and> rsz env t' = rsz env t"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
        let ?t = "incr_boundvars 1 t $ Bound 0"
        from ok Ts a obtain u where u: "ok (etif \<theta> U ?t) u" and t': "t' = Abs STR '''' T1 u"
          by (subst (asm) etif.simps) auto
        from c Ts a have c1: "cert_typ alg ar (tnorm \<theta> T1)" and c2: "cert_typ alg ar (tnorm \<theta> U)"
          by (simp_all add: cert_typ_fun)
        have ty1: "e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U" using ty Ts a by simp
        have "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> lift (inst ?\<rho> (unf env t)) 0 : tnorm \<theta> T1 \<rightarrow>\<^sub>T tnorm \<theta> U"
          by (rule lift_type[OF ty1]) simp
        then have tyt: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env ?t) : tnorm \<theta> U"
          by (simp only: inst_unf_incr[OF ac cl]) (rule typing.App, auto)
        from Type(1)[of U] Ts u c2 tyt
        have IH: "e\<langle>0:tnorm \<theta> T1\<rangle> \<turnstile> inst ?\<rho> (unf env u) : tnorm \<theta> U" "rsz env u = rsz env ?t"
          by auto
        have tyt': "e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> (Type a Ts)" using IH(1) c1 t' Ts a by auto
        have "rsz env t' = rsz env u"
          by (rule rsz_Abs[OF termip_typed_unf[OF tyt'[unfolded t']], folded t'])
        also have "\<dots> = rsz env t"
        proof -
          have "unf env ?t = lift (unf env t) 0 $ Bound 0"
            by (simp add: incr_boundvars_1 unf_lift[OF ac cl])
          then have "rsz env ?t = rcnt (bnorm (unf env t))"
            using rcnt_bnorm_eta[OF termip_typed_unf[OF ty]] by (simp add: rsz_def)
          with IH(2) show ?thesis by (simp add: rsz_def)
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
  then show "ok (etif \<theta> T t) t' \<Longrightarrow> cert_typ alg ar (tnorm \<theta> T) \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t) : tnorm \<theta> T \<Longrightarrow>
    e \<turnstile> inst ?\<rho> (unf env t') : tnorm \<theta> T \<and> rsz env t' = rsz env t"
    using tinv_tcons[OF ti tv] by blast
qed

lemma rsz_eta_norm_nonAbs:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env" and nA: "\<not> is_Abs t"
    and ok: "ok (eta_norm env bs t) t'" and ty: "e \<turnstile> inst (tnorm_inst \<theta>) t : T" and bs: "bs_env (tnorm_inst \<theta>) e bs"
    and lb: "\<not> loose_bvar t (ilength bs)" and tv: "ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A"
    and tyu: "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T"
  shows "e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> rsz env t' = rsz env t"
proof -
  from ok nA obtain T0 where T0: "ok (fastype env bs t) T0" and et: "ok (etif \<theta> T0 t) t'"
    by (auto simp: eta_norm_nonAbs th)
  have "tsubst (tnorm_inst \<theta>) T0 = T"
    by (rule fastype_sound[OF T0 _ bs ty]) (simp add: th tsol_tnorm[OF ti_ac[OF ti]])
  then have tT: "tnorm \<theta> T0 = T" by simp
  from env_fastype_term[OF ti th ty bs lb tv] T0 have tv0: "tvars T0 \<subseteq> tvars_env \<theta> \<union> A"
    by (auto simp: fastype_def return_def)
  have c: "cert_typ alg ar T" by (rule bs_env_cert[OF bs ty lb])
  from rsz_etif[OF th ac cl tv0 et _ tyu[folded tT]] c tT show ?thesis by simp
qed

lemma rsz_eta_norm:
  assumes th: "tyenv env = \<theta>" and ac: "acyc env" and cl: "closed_env env"
  shows "ok (eta_norm env bs t) t' \<Longrightarrow> e \<turnstile> inst (tnorm_inst \<theta>) t : T \<Longrightarrow> bs_env (tnorm_inst \<theta>) e bs \<Longrightarrow>
    \<not> loose_bvar t (ilength bs) \<Longrightarrow> ttvars t \<union> btvars bs \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t) : T \<Longrightarrow>
    e \<turnstile> inst (tnorm_inst \<theta>) (unf env t') : T \<and> rsz env t' = rsz env t"
proof (induction t arbitrary: e T bs t')
  case (Abs a B0 b)
  let ?\<rho> = "tnorm_inst \<theta>"
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, B0) # bs) b) b'" and t': "t' = Abs a B0 b'" by auto
  from Abs.prems(2) obtain W where c: "cert_typ alg ar (tsubst ?\<rho> B0)"
    and tb: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> b : W" and T: "T = tsubst ?\<rho> B0 \<rightarrow>\<^sub>T W"
    by auto
  from Abs.prems(6) T have tbu: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b) : W" by auto
  have lb: "\<not> loose_bvar b (ilength ((a, B0) # bs))" using Abs.prems(4) by (simp add: algebra_simps)
  have tv: "ttvars b \<union> btvars ((a, B0) # bs) \<subseteq> tvars_env \<theta> \<union> A" using Abs.prems(5) by (auto simp: btvars_def)
  from Abs.IH[OF b' tb bs_env_Cons[OF Abs.prems(3) c] lb tv tbu]
  have IH: "e\<langle>0:tsubst ?\<rho> B0\<rangle> \<turnstile> inst ?\<rho> (unf env b') : W" "rsz env b' = rsz env b"
    by blast+
  have ty': "e \<turnstile> inst ?\<rho> (unf env t') : T" using IH(1) c T t' by auto
  show ?case
    using ty' rsz_Abs[OF termip_typed_unf[OF ty'[unfolded t']]] rsz_Abs[OF termip_typed_unf[OF Abs.prems(6)]]
      IH(2) t' by simp
qed (rule rsz_eta_norm_nonAbs[OF th ac cl], simp, assumption+)+

end

subsection \<open>The invariant after a step\<close>

text \<open>
  A step from a problem in the invariant keeps the typings; the rest of the invariant concerns
  the environment and the type variables.
\<close>

lemma sinv_dtyped0:
  assumes "sinv A K X env dps" "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  shows "dtyped \<rho> dps"
  unfolding dtyped_def
proof (intro ballI, clarify)
  fix rb t u assume "(rb, t, u) \<in> set dps"
  with assms(1) have p: "pok A env rb X t u" by (auto simp: sinv_def)
  from pokD(9)[OF p assms(2,3)] pokD(7,8)[OF p]
  show "(\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
      \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb)" by blast
qed

lemma sinv_dvars0: "sinv A K X env dps \<Longrightarrow> dvars dps \<subseteq> X \<union> evars env"
  unfolding sinv_def dvars_def by (fastforce dest: pokD(1,2))

lemma sinv_dstep:
  assumes si: "sinv A K X env dps" and d: "dstep env dps env' dps'" and ei': "einv A' K' env'"
    and vX: "vtvars X \<subseteq> tvars_env (tyenv env') \<union> A'"
    and tt: "\<forall>(rb, t, u)\<in>set dps'. ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env') \<union> A'"
    and vt: "vtvars (dvars dps') \<subseteq> tvars_env (tyenv env') \<union> A'"
  shows "sinv A' K' (X \<union> dvars dps') env' dps'"
proof -
  have ext: "extends env env'" by (rule dstepD(1)[OF d])
  have wi: "winv env X" using si by (simp add: sinv_def)
  have R: "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps')"
    if \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    have \<rho>0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF \<rho>(1) ext])
    from winvD[OF wi \<rho>0 \<rho>(2)] have w: "wt_env \<rho> env" and v: "vinv \<rho> env X" by blast+
    have "vinv \<rho> env (X \<union> evars env)" using vinv_absorb[of "evars env" env \<rho> X] v by simp
    then have v': "vinv \<rho> env (X \<union> dvars dps)" by (rule vinv_mono) (use sinv_dvars0[OF si] in blast)
    from dstepD(2)[OF d \<rho>(1) extends_refl w sinv_dtyped0[OF si \<rho>0 \<rho>(2)] v'] show ?thesis by blast
  qed
  have "winv env' (X \<union> dvars dps')" unfolding winv_def using R by blast
  moreover have "pok A' env' rb (X \<union> dvars dps') t u" if m: "(rb, t, u) \<in> set dps'" for rb t u
    unfolding pok_def
  proof (intro conjI allI impI)
    show "vars t \<union> vars u \<subseteq> X \<union> dvars dps' \<union> evars env'" using m by (auto simp: dvars_def)
    show "ttvars t \<union> ttvars u \<union> btvars rb \<union> vtvars (X \<union> dvars dps') \<subseteq> tvars_env (tyenv env') \<union> A'"
      using tt m vX vt by (auto simp: vtvars_def)
    from R[OF einv_rho0[OF ei']] m have "dtyped (tnorm_inst (tyenv env')) [(rb, t, u)]"
      by (auto simp: dtyped_def)
    then show "\<not> loose_bvar t (ilength rb)" "\<not> loose_bvar u (ilength rb)" by simp_all
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    from R[OF \<rho>] m show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T"
      by (auto simp: dtyped_def)
  qed
  ultimately show ?thesis using ei' by (auto simp: sinv_def)
qed

subsection \<open>The invariant of the copies\<close>

text \<open>
  The environment \<open>envM\<close> of \<open>MATCH\<close> is acyclic, with consistent variables \<open>VM\<close>, which include the
  variables of the copied terms. A state of the copy is a problem in the invariant, with the
  pending pairs \<open>F\<close> of the further arguments of imitations.
\<close>

definition menv :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "menv envM VM \<longleftrightarrow> acyc envM \<and> closed_env envM \<and> tacyc (tyenv envM) \<and> tcons_env (tyenv envM) \<and>
    vok envM VM \<and> evars envM \<subseteq> VM"

definition cpinvX :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow>
    bool" where
  "cpinvX A0 envM VM F A K X env dps \<longleftrightarrow> finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 envM A env \<and>
    maxidx envM \<le> maxidx env \<and> extends envM env \<and> VM \<subseteq> X \<union> evars env \<and>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and> sinv A K X env (F @ dps)"

definition cpinv :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> bool" where
  "cpinv A0 envM VM F env dps \<longleftrightarrow> (\<exists>A K X. cpinvX A0 envM VM F A K X env dps)"

lemma cpinvXI:
  assumes "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 envM A env" "maxidx envM \<le> maxidx env" "extends envM env"
    "VM \<subseteq> X \<union> evars env" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" "sinv A K X env (F @ dps)"
  shows "cpinvX A0 envM VM F A K X env dps"
  using assms unfolding cpinvX_def by blast

lemma cpinvI:
  assumes "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 envM A env" "maxidx envM \<le> maxidx env" "extends envM env"
    "VM \<subseteq> X \<union> evars env" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" "sinv A K X env (F @ dps)"
  shows "cpinv A0 envM VM F env dps"
  using cpinvXI[OF assms] unfolding cpinv_def by blast

lemma cpinv_set: "cpinv A0 envM VM F env dps \<Longrightarrow> set (F @ dps) = set (F' @ dps') \<Longrightarrow> cpinv A0 envM VM F' env dps'"
  unfolding cpinv_def cpinvX_def by (metis sinv_mono order_refl)

lemma cpinvX_set:
  "cpinvX A0 envM VM F A K X env dps \<Longrightarrow> set (F @ dps) = set (F' @ dps') \<Longrightarrow> cpinvX A0 envM VM F' A K X env dps'"
  unfolding cpinvX_def by (metis sinv_mono order_refl)

lemma cpinv_mres: "cpinv A0 envM VM [] env dps \<Longrightarrow> mres A0 envM (El_E env dps)"
  unfolding cpinv_def cpinvX_def mres_def by auto

lemma vtvars_evars: "tvinv A env \<Longrightarrow> vtvars (evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  assume "tvinv A env"
  then have "etvars env \<subseteq> tvars_env (tyenv env) \<union> A" by (rule etvars_known)
  moreover have "vtvars (evars env) \<subseteq> etvars env"
  proof
    fix p assume "p \<in> vtvars (evars env)"
    then obtain x T where xT: "(x, T) \<in> evars env" "p \<in> tvars T" by (auto simp: vtvars_def)
    from xT(1) obtain y U u where b: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
      unfolding evars_def bnds_def by blast
    then show "p \<in> etvars env"
    proof (elim disjE)
      assume "(x, T) = (y, U)"
      with b(1) xT(2) show ?thesis unfolding etvars_def bnds_def by blast
    next
      assume "(x, T) \<in> vars u"
      then have "tvars T \<subseteq> ttvars u" by (induction u) auto
      with b(1) xT(2) show ?thesis unfolding etvars_def bnds_def by blast
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma update_unbound:
  assumes "vt_lookup (tenv env) v = None"
  shows "ok (update (v, T) t env) (Envir (maxidx env) (vt_update (v, (T, t)) (tenv env)) (tyenv env))"
  using assms by (cases env) (simp add: update_def ok_update_new)

text \<open>The two cases of \<^const>\<open>mc\<close>:\<close>

lemma mc_assigned:
  "lookup env v TX = return (Some r) \<Longrightarrow>
    mc cfg vname envM (v, TX) rb targs u env dps =
      returnW (S_Single (El_E env ((rb, list_comb (Var v TX) targs, u) # dps)))"
  by (subst mc.simps) (simp add: liftM_def return_def bindW_def returnW_def)

lemma mc_unassigned:
  assumes "lookup env v TX = return None" "fastype env rb (fst (strip_comb u)) = return T0"
    "body_type env T0 = return base" "mapM (fastype env rb) targs = return Ts"
  shows "mc cfg vname envM (v, TX) rb targs u env dps =
    (case fst (strip_comb u) of
      Abs a T body \<Rightarrow> do {
        B \<leftarrow> liftM (fastype env ((a, T) # rb) body);
        (case genvar vname env (foldr fun_type (Ts @ [T]) B) of (env', Y) \<Rightarrow> do {
          Y' \<leftarrow> dest_Var Y;
          env'' \<leftarrow> liftM (update (v, TX) (types_abs Ts (Abs a T (combound Y 0 (Suc (length Ts))))) env');
          mc cfg vname envM Y' ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body
            env'' dps})}
    | Var w _ \<Rightarrow>
        (case genvar (fst w) env (foldr fun_type Ts base) of (env', newhd) \<Rightarrow> do {
          env'' \<leftarrow> liftM (update (v, TX) (types_abs Ts (combound newhd 0 (length Ts))) env');
          returnW (S_Single (El_E env'' ((rb, list_comb newhd targs, u) # dps)))})
    | _ \<Rightarrow> do {
        projs \<leftarrow> make_projs u targs Ts targs;
        matchfun cfg vname envM rb targs u env dps (v, TX) (fst (strip_comb u)) (snd (strip_comb u)) base Ts (rev projs)})"
  by (subst mc.simps) (simp add: Let_def assms liftM_def return_def bindW_def returnW_def option.map_id)

text \<open>The types of a pair in the invariant:\<close>

lemma pair_types:
  assumes ei: "einv A K env" and p: "pok A env rb X (Var v TX \<degree>\<degree> targs) u"
  shows "\<exists>T0 base Ts. fastype env rb (fst (strip_comb u)) = return T0 \<and> body_type env T0 = return base \<and>
    tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A \<and> tvars base \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    mapM (fastype env rb) targs = return Ts \<and> (\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A)"
proof -
  let ?\<theta> = "tyenv env" and ?h = "fst (strip_comb u)" and ?\<rho> = "rho0 env"
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  from pd(9)[OF r0] obtain e0 U where bs: "bs_env ?\<rho> e0 rb" and tyt: "e0 \<turnstile> inst ?\<rho> (Var v TX \<degree>\<degree> targs) : U"
    and tyu: "e0 \<turnstile> inst ?\<rho> u : U" by blast
  have u: "u = ?h \<degree>\<degree> snd (strip_comb u)" by (rule strip_comb_apps) simp
  from tyu[unfolded u[THEN arg_cong[of _ _ "inst ?\<rho>"]] inst_apps] obtain Vs where
    tyh: "e0 \<turnstile> inst ?\<rho> ?h : Vs \<Rrightarrow> U" by (rule list_app_typeE)
  have lbh: "\<not> loose_bvar ?h (ilength rb)" using pd(8) u by (metis loose_bvar_apps)
  have tvh: "ttvars ?h \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof -
    have "ttvars ?h \<subseteq> ttvars u" by (subst (2) u) (simp add: ttvars_apps)
    then show ?thesis using pd(4,5) by blast
  qed
  from env_fastype_term[OF x(2) refl tyh bs lbh tvh] obtain T0 where
    T0: "env_fastype env (map snd rb) ?h = return T0" "tvars T0 \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  from body_type_term[OF x(2) refl T0(2)] obtain base where
    base: "body_type env T0 = return base" "tvars base \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  from tyt[unfolded inst_apps] obtain Ws where tya: "e0 \<tturnstile> map (inst ?\<rho>) targs : Ws" by (rule list_app_typeE)
  have "\<forall>s\<in>set targs. \<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof
    fix s assume s: "s \<in> set targs"
    then obtain i where i: "i < length targs" "s = targs ! i" by (auto simp: in_set_conv_nth)
    have "e0 \<turnstile> inst ?\<rho> s : Ws ! i" using typings_nth[OF tya] i by auto
    moreover have "\<not> loose_bvar s (ilength rb)" using pd(7) s by (auto simp: loose_bvar_apps)
    moreover have "ttvars s \<subseteq> tvars_env ?\<theta> \<union> A" using pd(3) s by (auto simp: ttvars_apps)
    ultimately show "\<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
        ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
      using bs pd(5) by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Ts where
    Ts: "mapM (fastype env rb) targs = return Ts" "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  with T0 base show ?thesis by (auto simp: fastype_def)
qed

text \<open>Head normalization in the environment of \<open>MATCH\<close>:\<close>

lemma hnM:
  assumes M: "menv envM VM" and ext: "extends envM env" and ei: "einv A K env" and wi: "winv env X"
    and VX: "VM \<subseteq> X \<union> evars env" and vt: "vars t \<subseteq> VM"
    and ty: "e \<turnstile> inst (rho0 env) t : T"
  shows "\<exists>t'. head_norm envM t = return t' \<and> vars t' \<subseteq> VM \<and> ttvars t' \<subseteq> ttvars t \<union> etvars envM \<and>
    termip beta (unf envM t) \<and>
    (\<forall>\<rho> e T. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow>
      e \<turnstile> inst \<rho> t' : T \<and> e \<turnstile> inst \<rho> (unf envM t) : T) \<and>
    (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar t k \<longrightarrow> \<not> loose_bvar t' k)"
proof -
  let ?\<rho> = "rho0 env"
  have m: "acyc envM" "closed_env envM" "tacyc (tyenv envM)" "tcons_env (tyenv envM)" "vok envM VM"
    "evars envM \<subseteq> VM" using M by (simp_all add: menv_def)
  note r0 = einv_rho0[OF ei]
  have tyunf: "e \<turnstile> inst \<rho> (unf envM t) : T"
    if \<rho>: "tsol (tyenv env) \<rho>" "wt_env \<rho> env" "vinv \<rho> env X" and tyt: "e \<turnstile> inst \<rho> t : T" for \<rho> e T
  proof (rule typing_unf[OF m(1) wt_env_extends[OF \<rho>(2) ext] _ tyt])
    have "vcons \<rho> (X \<union> evars env)" using \<rho>(3) by (simp add: vinv_def)
    then show "vcons \<rho> (vars t \<union> evars envM)"
      by (rule vcons_mono) (use vt VX m(6) in blast)
  qed
  have w0: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi r0] by blast+
  have tu0: "e \<turnstile> inst ?\<rho> (unf envM t) : T" by (rule tyunf[OF r0(1) w0 ty])
  have sn: "termip beta (unf envM t)" by (rule termip_typed_unf[OF tu0])
  have "\<exists>t'. head_norm envM t = return t'"
  proof (rule head_norm_term[OF m(1-4)])
    show "vok envM (vars t \<union> evars envM)" by (rule vok_mono[OF m(5)]) (use vt m(6) in blast)
    show "termip (sup beta subt) (unf envM t)" by (rule termip_beta_subt[OF sn])
  qed
  then obtain t' where h: "head_norm envM t = return t'" by blast
  note h' = h[unfolded return_def]
  have "vars t' \<subseteq> VM" using head_norm_vars[OF h' refl] vt m(6) by blast
  moreover have "ttvars t' \<subseteq> ttvars t \<union> etvars envM" by (rule head_norm_ttvars[OF h' refl])
  moreover have "e \<turnstile> inst \<rho> t' : T \<and> e \<turnstile> inst \<rho> (unf envM t) : T"
    if \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" and tyt: "e \<turnstile> inst \<rho> t : T" for \<rho> e T
  proof -
    from winvD[OF wi \<rho>] have w: "wt_env \<rho> env" "vinv \<rho> env X" by blast+
    have \<rho>M: "tsol (tyenv envM) \<rho>" by (rule extends_tsol[OF \<rho>(1) ext])
    have wM: "wt_env \<rho> envM" by (rule wt_env_extends[OF w(1) ext])
    show ?thesis using head_norm_sound[OF h' refl \<rho>M wM tyt] tyunf[OF \<rho>(1) w tyt] by blast
  qed
  moreover have "\<not> loose_bvar t' k" if "0 \<le> k" "\<not> loose_bvar t k" for k
    by (rule head_norm_loose[OF h' refl wt_env_extends[OF w0(1) ext] that])
  ultimately show ?thesis using h sn by blast
qed

text \<open>\<open>\<eta>\<close>-normalization depends only on the type environment:\<close>

lemma eta_norm_tyenv:
  assumes "tyenv env' = tyenv env"
  shows "eta_norm env' rb t = eta_norm env rb t"
proof (induction t arbitrary: rb)
  case (Abs a T b)
  then show ?case by simp
qed (simp_all add: fastype_tyenv[OF assms] assms)

subsection \<open>Bindings to new variables\<close>

text \<open>Binding an unbound variable to a term over unbound variables keeps the environment invariant:\<close>

lemma einv_bind:
  assumes ei: "einv A K env" and te: "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and upd: "ok (update (v, T) t env') env''"
    and fresh: "\<And>y U. (y, U) \<in> vars t \<Longrightarrow> vt_lookup (tenv env) y = None \<and> y \<noteq> v"
    and cl: "closed t" and vb: "snd v \<le> maxidx env" and tv: "tvars T \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "einv A K env''"
proof -
  have ei': "einv A K env'" by (rule einv_maxidx[OF ei te])
  show ?thesis
  proof (rule einv_update[OF ei' upd _ cl])
    show "(v, y) \<notin> (dep env')\<^sup>*" if "(y, U) \<in> vars t" for y U
      using fresh[OF that] te(1) by (intro not_dep_unbound) auto
    show "snd v \<le> maxidx env'" using vb te(3) by simp
    show "tvars T \<union> ttvars t \<subseteq> tvars_env (tyenv env') \<union> A" using tv te(2) by simp
  qed
qed

text \<open>A step on the pairs of the copy keeps the pending pairs \<open>F\<close> in the invariant:\<close>

lemma sinv_frame_step:
  assumes si: "sinv A K X env (F @ dps)" and d: "dstep env dps env' dps'" and ei': "einv A' K' env'"
    and tvs: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and tt: "\<forall>(rb, t, u)\<in>set dps'. ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env') \<union> A'"
    and vt: "vtvars (dvars dps') \<subseteq> tvars_env (tyenv env') \<union> A'"
    and AA: "A \<subseteq> A'"
  shows "sinv A' K' (X \<union> dvars (F @ dps')) env' (F @ dps')"
proof (rule sinv_dstep[OF si _ ei'])
  show "dstep env (F @ dps) env' (F @ dps')"
    by (rule dstep_set[OF dstep_frame[OF d, where fs = F]]) auto
  show "vtvars X \<subseteq> tvars_env (tyenv env') \<union> A'" using vX tvs AA by blast
  have ei: "einv A K env" using si by (simp add: sinv_def)
  have pF: "\<forall>(rb, t, u)\<in>set F. pok A env rb X t u" using si by (auto simp: sinv_def)
  have "ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env') \<union> A'"
    if m: "(rb, t, u) \<in> set (F @ dps')" for rb t u
  proof (cases "(rb, t, u) \<in> set F")
    case True
    with pF have "pok A env rb X t u" by blast
    from pokD(3,4,5)[OF this] tvs AA show ?thesis by blast
  next
    case False
    with m tt show ?thesis by auto
  qed
  then show "\<forall>(rb, t, u)\<in>set (F @ dps'). ttvars t \<union> ttvars u \<union> btvars rb \<subseteq> tvars_env (tyenv env') \<union> A'"
    by blast
  have "dvars F \<subseteq> X \<union> evars env" using sinv_dvars0[OF sinv_mono[OF si]] by auto
  then have "vtvars (dvars F) \<subseteq> vtvars X \<union> vtvars (evars env)" by (auto simp: vtvars_def)
  also have "\<dots> \<subseteq> tvars_env (tyenv env') \<union> A'"
    using vX vtvars_evars[OF einvD(1)[OF ei]] tvs AA by blast
  finally show "vtvars (dvars (F @ dps')) \<subseteq> tvars_env (tyenv env') \<union> A'" using vt by simp
qed

subsection \<open>The hypothesis of the copies\<close>

text \<open>The hypothesis of a copy of \<open>u\<close> into the variable \<open>X0\<close> applied to \<open>targs\<close>:\<close>

definition mcpre :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow>
    (indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> env \<Rightarrow> binders \<Rightarrow>
    indexname \<times> ptyp \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> dpair list \<Rightarrow> pterm option \<Rightarrow> bool" where
  "mcpre A0 envM VM F A K X env rb X0 targs u dps ot \<longleftrightarrow> finite X \<and> finite K \<and> A0 \<subseteq> A \<and>
    tnew A0 envM A env \<and> maxidx envM \<le> maxidx env \<and> extends envM env \<and> VM \<subseteq> X \<union> evars env \<and>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    sinv A K X env (F @ (rb, Var (fst X0) (snd X0) \<degree>\<degree> targs, u) # dps) \<and> vars u \<subseteq> VM \<and>
    msat ot env rb u \<and> (\<forall>t. ot = Some t \<longrightarrow> t = Var (fst X0) (snd X0) \<degree>\<degree> targs)"

lemma mcpreI:
  "cpinvX A0 envM VM F A K X env ((rb, Var (fst X0) (snd X0) \<degree>\<degree> targs, u) # dps) \<Longrightarrow> vars u \<subseteq> VM \<Longrightarrow>
    msat ot env rb u \<Longrightarrow> (\<forall>t. ot = Some t \<longrightarrow> t = Var (fst X0) (snd X0) \<degree>\<degree> targs) \<Longrightarrow>
    mcpre A0 envM VM F A K X env rb X0 targs u dps ot"
  by (simp add: mcpre_def cpinvX_def)

lemma mcpre_cpinvX:
  "mcpre A0 envM VM F A K X env rb X0 targs u dps ot \<Longrightarrow>
    cpinvX A0 envM VM F A K X env ((rb, Var (fst X0) (snd X0) \<degree>\<degree> targs, u) # dps)"
  by (simp add: mcpre_def cpinvX_def)

abbreviation CQ :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow> elem \<Rightarrow> bool" where
  "CQ A0 envM VM F \<equiv> \<lambda>x. \<exists>e d. x = El_E e d \<and> cpinv A0 envM VM F e d"

lemma okW_liftM_return: "m = return x \<Longrightarrow> okW (f x) s \<Longrightarrow> okW (bindW (liftM m) f) s"
  by (simp add: liftM_def return_def bindW_def)

lemma tnew_same: "tvars_env (tyenv env') = tvars_env (tyenv env) \<Longrightarrow> tnew A env A env'"
  by (auto simp: tnew_def)

lemma ttvars_combound: "ttvars (combound t m k) = ttvars t"
  by (simp add: combound_apps ttvars_apps)

text \<open>The unfolding of a copied term in \<open>envM\<close> is well-typed:\<close>

lemma unfM_typed:
  assumes M: "menv envM VM" and ext: "extends envM env" and wi: "winv env X" and VX: "VM \<subseteq> X \<union> evars env"
    and vt: "vars t \<subseteq> VM" and \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>" and ty: "e \<turnstile> inst \<rho> t : T"
  shows "e \<turnstile> inst \<rho> (unf envM t) : T"
proof -
  have m: "acyc envM" "evars envM \<subseteq> VM" using M by (simp_all add: menv_def)
  from winvD[OF wi \<rho>] have w: "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  have "vcons \<rho> (X \<union> evars env)" using w(2) by (simp add: vinv_def)
  then have "vcons \<rho> (vars t \<union> evars envM)" by (rule vcons_mono) (use vt VX m(2) in blast)
  from typing_unf[OF m(1) wt_env_extends[OF w(1) ext] this ty] show ?thesis .
qed

lemma ttvars_types_abs [simp]: "ttvars (types_abs Ts u) = (\<Union>T\<in>set Ts. tvars T) \<union> ttvars u"
  by (induction Ts) auto

lemma finite_dvars [simp]: "finite (dvars dps)"
  by (auto simp: dvars_def)

lemma vtvars_mono: "Y \<subseteq> Z \<Longrightarrow> vtvars Y \<subseteq> vtvars Z"
  by (auto simp: vtvars_def)

subsection \<open>The enumerations of projections and imitation\<close>

lemma cuok_noCU: "cuok m P \<Longrightarrow> noCU m \<Longrightarrow> \<exists>x. okW m x \<and> P x"
  unfolding cuok_def noCU_def by auto

lemma projenv_fin:
  assumes g: "gentvars p env = (env0, Cs)" and P: "cuok (proj_unify cfg base bary Cs env0) P"
    and R: "\<And>env' env1 args. okW (proj_unify cfg base bary Cs env0) env' \<Longrightarrow> P env' \<Longrightarrow>
      make_args vname Ts env' (Us @ Cs) = (env1, args) \<Longrightarrow>
      \<exists>env2. ok (update X (types_abs Ts (list_comb head args)) env1) env2 \<and>
        cuok (SIMPL (cfg_alg cfg) env2
          ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (\<lambda>(env3, fr1, ff1). Q (El_E env3 (fr1 @ ff1)))"
    and t: "fin cfg tail Q"
  shows "cuok (projenv cfg vname rb targs u env dps X base Ts head (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q)"
  unfolding projenv_def g prod.case
proof (rule cuok_handle_CANTUNIFY_ret[OF cuok_bindW[OF P]])
  fix env' assume ok: "okW (proj_unify cfg base bary Cs env0) env'" and Pe: "P env'"
  obtain env1 args where ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
    by (cases "make_args vname Ts env' (Us @ Cs)")
  from R[OF ok Pe ma] obtain env2 where up: "ok (update X (types_abs Ts (list_comb head args)) env1) env2"
    and s: "cuok (SIMPL (cfg_alg cfg) env2
      ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
      (\<lambda>(env3, fr1, ff1). Q (El_E env3 (fr1 @ ff1)))" by blast
  show "cuok (returnW (S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ X tail)) (\<lambda>s. fin cfg s Q)"
    using fin_Proj[OF ma up s t] by simp
qed (use t in simp_all)

lemma foldrW_cuok_fin:
  assumes "\<And>x b. x \<in> set xs \<Longrightarrow> fin cfg b Q \<Longrightarrow> cuok (f x b) (\<lambda>s. fin cfg s Q)" "fin cfg b0 Q"
  shows "cuok (foldrW f xs b0) (\<lambda>s. fin cfg s Q)"
  using assms(1) by (induction xs) (auto intro: assms(2) cuok_bindW)

lemma matchfun_fin:
  assumes PF: "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. strip_type env T = return (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail Q \<longrightarrow>
        cuok (projenv cfg vname rb targs u env dps X base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q))"
    and imit: "cuok (case uhead of
        Const _ _ \<Rightarrow> imitate vname env0 rb targs env dps X Ts uhead uargs
      | Free _ _ \<Rightarrow> imitate vname env0 rb targs env dps X Ts uhead uargs
      | _ \<Rightarrow> returnW S_Empty) (\<lambda>s. fin cfg s Q)"
  shows "cuok (matchfun cfg vname env0 rb targs u env dps X uhead uargs base Ts projs) (\<lambda>s. fin cfg s Q)"
  using PF
proof (induction projs)
  case Nil
  with imit show ?case by simp
next
  case (Cons q projs)
  obtain bv T targ where q: "q = (bv, T, targ)" by (cases q)
  from Cons.prems q obtain Us bary where st: "strip_type env T = return (Us, bary)"
    and gs: "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail Q \<longrightarrow>
        cuok (projenv cfg vname rb targs u env dps X base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s Q)"
    by auto
  have IH: "cuok (matchfun cfg vname env0 rb targs u env dps X uhead uargs base Ts projs) (\<lambda>s. fin cfg s Q)"
    using Cons.IH Cons.prems by simp
  show ?case unfolding q matchfun.simps
    by (rule cuok_liftM_return[OF st], rule cuok_bindW[OF IH], simp,
        rule foldrW_cuok_fin[where Q = Q]) (use gs in auto)
qed

text \<open>The copies of the arguments of an imitation, each pending in the frame of the others:\<close>

lemma copyargs_fin:
  assumes CC: "\<And>F e rb targs G uarg d. cpinv A0 envM VM F e ((rb, G \<degree>\<degree> targs, uarg) # d) \<Longrightarrow> vars uarg \<subseteq> VM \<Longrightarrow>
      \<exists>x U. G = Var x U \<Longrightarrow> rsz envM uarg < N \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname envM rb targs G uarg e d) cs \<and> fin cfg cs (CQ A0 envM VM F)"
  shows "cpinv A0 envM VM F e (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ dps) \<Longrightarrow>
    \<forall>(G, uarg)\<in>set gus. (\<exists>x U. G = Var x U) \<and> vars uarg \<subseteq> VM \<and> rsz envM uarg < N \<Longrightarrow>
    fin cfg (copyargs vname envM rb targs gus e dps) (CQ A0 envM VM F)"
proof (induction gus arbitrary: F)
  case Nil
  then show ?case unfolding copyargs.simps by (intro fin_Single) auto
next
  case (Cons gu gus)
  obtain G uarg where gu: "gu = (G, uarg)" by (cases gu)
  let ?p = "(rb, G \<degree>\<degree> targs, uarg)"
  have c: "cpinv A0 envM VM (F @ [?p]) e (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) gus @ dps)"
    by (rule cpinv_set[OF Cons.prems(1)]) (auto simp: gu)
  have IH: "fin cfg (copyargs vname envM rb targs gus e dps) (CQ A0 envM VM (F @ [?p]))"
    by (rule Cons.IH[OF c]) (use Cons.prems(2) in auto)
  from Cons.prems(2) gu have a: "\<exists>x U. G = Var x U" "vars uarg \<subseteq> VM" "rsz envM uarg < N" by auto
  show ?case unfolding gu copyargs.simps
  proof (rule fin_Maps, rule fin_mono[OF IH])
    fix x assume "CQ A0 envM VM (F @ [?p]) x"
    then obtain e' d where x: "x = El_E e' d" and ci: "cpinv A0 envM VM (F @ [?p]) e' d" by blast
    have ci': "cpinv A0 envM VM F e' (?p # d)" by (rule cpinv_set[OF ci]) auto
    from CC[OF ci' a(2,1,3)] x show "\<exists>env dps cs. x = El_E env dps \<and>
        okW (copycons cfg vname envM rb targs G uarg env dps) cs \<and> fin cfg cs (CQ A0 envM VM F)"
      by blast
  qed
qed

text \<open>\<^const>\<open>SIMPL\<close> on pairs of the copy keeps the invariant of the copies:\<close>

lemma simpl_post_cpinvX:
  assumes c: "cpinvX A0 envM VM F A K X env dps" and sp: "simpl_post A K X env (env3, fr1, ff1)"
  shows "cpinvX A0 envM VM F A K X env3 (fr1 @ ff1)"
proof -
  from c have finX: "finite X" and finK: "finite K" and A0A: "A0 \<subseteq> A" and tn: "tnew A0 envM A env"
    and mx: "maxidx envM \<le> maxidx env" and extM: "extends envM env" and VX: "VM \<subseteq> X \<union> evars env"
    and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" and si: "sinv A K X env (F @ dps)"
    unfolding cpinvX_def by blast+
  from sp have si3: "sinv A K X env3 (ff1 @ fr1)" and ss: "sstep A K X env env3"
    by (auto simp: simpl_post_def)
  note sd = sstepD[OF ss]
  have ei3: "einv A K env3" and wi3: "winv env3 X" using si3 by (simp_all add: sinv_def)
  have siF: "sinv A K X env3 F" by (rule sinv_ext[OF sinv_mono[OF si] ei3 wi3 ss]) auto
  have si3': "sinv A K X env3 (F @ fr1 @ ff1)" by (rule sinv_union[OF siF si3]) auto
  show ?thesis
  proof (rule cpinvXI[OF finX finK A0A _ _ _ _ _ si3'])
    show "tnew A0 envM A env3" by (rule tnew_trans[OF tn sd(5) mx])
    show "maxidx envM \<le> maxidx env3" using mx extends_maxidx[OF sd(1)] by simp
    show "extends envM env3" by (rule extends_trans[OF extM sd(1)])
    show "VM \<subseteq> X \<union> evars env3" using VX evars_extends[OF sd(1)] by blast
    show "vtvars X \<subseteq> tvars_env (tyenv env3) \<union> A" using vX sd(2) by blast
  qed
qed

lemma simpl_cq:
  assumes c: "cpinvX A0 envM VM F A K X env dps"
  shows "cuok (SIMPL alg env dps) (\<lambda>(env3, fr, ff). CQ A0 envM VM F (El_E env3 (fr @ ff)))"
proof -
  from c have fin: "finite X" "finite K" and si: "sinv A K X env (F @ dps)" unfolding cpinvX_def by blast+
  show ?thesis
  proof (rule cuok_mono[OF SIMPL_term[OF fin sinv_mono[OF si]]])
    show "set dps \<subseteq> set (F @ dps)" by auto
    fix st assume sp: "simpl_post A K X env st"
    obtain env3 fr1 ff1 where ste: "st = (env3, fr1, ff1)" by (cases st)
    have "cpinvX A0 envM VM F A K X env3 (fr1 @ ff1)" by (rule simpl_post_cpinvX[OF c sp[unfolded ste]])
    then show "case st of (env3, fr1, ff1) \<Rightarrow> CQ A0 envM VM F (El_E env3 (fr1 @ ff1))"
      unfolding ste prod.case cpinv_def by blast
  qed
qed

subsection \<open>The steps of a copy\<close>

text \<open>
  The steps of a copy into an unassigned variable: each is a step of the soundness proof, and the
  new state is in the invariant of the copies, for the variables of the old state and the new
  pairs.
\<close>

context
  fixes A0 envM VM F A K X env rb v TX targs u dps ot T0 base Ts
  assumes pre: "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot"
    and vN: "vt_lookup (tenv env) v = None"
    and ty0: "fastype env rb (fst (strip_comb u)) = return T0" "body_type env T0 = return base"
      "mapM (fastype env rb) targs = return Ts"
begin

lemma mcs_pre:
  shows "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 envM A env" "maxidx envM \<le> maxidx env" "extends envM env"
    "VM \<subseteq> X \<union> evars env" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    "sinv A K X env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)" "vars u \<subseteq> VM" "msat ot env rb u"
    "\<forall>t. ot = Some t \<longrightarrow> t = Var v TX \<degree>\<degree> targs"
  using pre by (simp_all add: mcpre_def)

lemma mcs_inv:
  shows "einv A K env" "winv env X" "pok A env rb X (Var v TX \<degree>\<degree> targs) u"
  using mcs_pre(9) by (auto simp: sinv_def)

lemma mcs_facts:
  shows "tvars TX \<subseteq> tvars_env (tyenv env) \<union> A" "snd v \<le> maxidx env"
    "vars u \<subseteq> X \<union> evars env" "lvars targs \<subseteq> X \<union> evars env"
    "vtvars (X \<union> evars env) \<subseteq> tvars_env (tyenv env) \<union> A" "vtvars (dvars F) \<subseteq> tvars_env (tyenv env) \<union> A"
    "dvars (F @ dps) \<subseteq> X \<union> evars env"
    "\<forall>(rb', t', u')\<in>set (F @ dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
    "ok (mapM (fastype env rb) targs) Ts" "length Ts = length targs"
    "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  note si = mcs_pre(9) and pd = pokD[OF mcs_inv(3)] and e = einvD[OF mcs_inv(1)]
  show "tvars TX \<subseteq> tvars_env (tyenv env) \<union> A" using pd(3) by (auto simp: ttvars_apps)
  show "snd v \<le> maxidx env" by (rule below_head[OF si]) (use pd(1) in \<open>auto simp: vars_apps\<close>)
  show "vars u \<subseteq> X \<union> evars env" by (rule pd(2))
  show "lvars targs \<subseteq> X \<union> evars env" using pd(1) by (auto simp: vars_apps)
  show vtXE: "vtvars (X \<union> evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
    using mcs_pre(8) vtvars_evars[OF e(1)] by simp
  show dvF: "dvars (F @ dps) \<subseteq> X \<union> evars env" using sinv_dvars0[OF sinv_mono[OF si]] by auto
  then show "vtvars (dvars F) \<subseteq> tvars_env (tyenv env) \<union> A"
    using vtvars_mono[of "dvars F" "X \<union> evars env"] vtXE by auto
  show "\<forall>(rb', t', u')\<in>set (F @ dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
    using si by (fastforce simp: sinv_def dest: pokD(3,4,5))
  show Tsok: "ok (mapM (fastype env rb) targs) Ts" using ty0(3) by (simp add: return_def)
  show "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF Tsok])
  from pair_types[OF mcs_inv(1,3)] obtain T0' base' Ts' where ty: "fastype env rb (fst (strip_comb u)) = return T0'"
    "body_type env T0' = return base'" "tvars base' \<subseteq> tvars_env (tyenv env) \<union> A"
    "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    by blast
  have "T0' = T0" "Ts' = Ts" using ty(1,4) ty0(1,3) by (simp_all add: return_def)
  moreover from this(1) have "base' = base" using ty(2) ty0(2) by (simp add: return_def)
  ultimately show "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    using ty(3,5) by simp_all
qed

lemma mcs_bse:
  assumes na: "\<not> is_Abs (fst (strip_comb u))" and \<rho>: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e rb"
    and tyt: "e \<turnstile> inst \<rho> (Var v TX \<degree>\<degree> targs) : U" and tyu: "e \<turnstile> inst \<rho> u : U"
  shows "U = tsubst \<rho> base"
proof (cases ot)
  case None
  with mcs_pre(11) have sat: "satd env rb u" by (simp add: msat_def)
  show ?thesis by (rule satd_base[OF na sat _ _ \<rho> bs tyu]) (use ty0(1,2) in \<open>simp_all add: return_def\<close>)
next
  case (Some t)
  with mcs_pre(11,12) have "rsat env rb (Var v TX \<degree>\<degree> targs) u" by (simp add: msat_def)
  from this[unfolded rsat_def] ty0(1,2) \<rho> bs tyt tyu show ?thesis by (simp add: return_def)
qed

lemma mcs_lookup: "ok (lookup env v TX) None"
  using lookup_unbound[OF vN] by (simp add: return_def)

text \<open>An abstraction: the body is copied into a new variable \<open>Y\<close>.\<close>

lemma mcs_abs_type:
  assumes Abs: "fst (strip_comb u) = Abs a Ta body"
  obtains B where "u = Abs a Ta body" "satd env rb u" "fastype env ((a, Ta) # rb) body = return B"
    "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  note pd = pokD[OF mcs_inv(3)] and e = einvD[OF mcs_inv(1)] and r0 = einv_rho0[OF mcs_inv(1)]
  have sat: "satd env rb u" using mcs_pre(11,12) Abs by (cases ot) (simp_all add: msat_def)
  from satd_Abs[OF Abs sat] have na: "snd (strip_comb u) = []" by simp
  have "strip_comb u = (Abs a Ta body, [])" using Abs na by (metis prod.collapse)
  then have u: "u = Abs a Ta body" using strip_comb_apps by fastforce
  from pd(9)[OF r0] obtain e0 U0 where bs0: "bs_env (rho0 env) e0 rb" and tyu0: "e0 \<turnstile> inst (rho0 env) u : U0"
    by blast
  from tyu0[unfolded u] obtain W where cA: "cert_typ alg ar (tsubst (rho0 env) Ta)"
    and tyb: "e0\<langle>0:tsubst (rho0 env) Ta\<rangle> \<turnstile> inst (rho0 env) body : W"
    by auto
  have bs1: "bs_env (rho0 env) (e0\<langle>0:tsubst (rho0 env) Ta\<rangle>) ((a, Ta) # rb)" by (rule bs_env_Cons[OF bs0 cA])
  have lbb: "\<not> loose_bvar body (ilength ((a, Ta) # rb))" using pd(8) by (simp add: u algebra_simps)
  have tvb: "ttvars body \<union> btvars ((a, Ta) # rb) \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(4,5) by (auto simp: u btvars_def)
  from env_fastype_term[OF e(2) refl tyb bs1 lbb tvb] obtain B where
    fB0: "env_fastype env (map snd ((a, Ta) # rb)) body = return B" and tvB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A"
    by blast
  have "fastype env ((a, Ta) # rb) body = return B" using fB0 by (simp add: fastype_def)
  moreover have "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A" using tvb by (auto simp: btvars_def)
  ultimately show ?thesis using that u sat tvB by blast
qed

lemma mcs_abs:
  assumes Abs: "fst (strip_comb u) = Abs a Ta body" and fB: "fastype env ((a, Ta) # rb) body = return B"
    and tvB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A"
    and g: "genvar vname env (foldr fun_type (Ts @ [Ta]) B) = (env', Y)"
    and up: "ok (update (v, TX) (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) env') env''"
  shows "u = Abs a Ta body" "Y = Var (vname, maxidx env + 1) (foldr fun_type (Ts @ [Ta]) B)"
    "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      (((a, Ta) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps)"
    "tyenv env'' = tyenv env" "extends env env''"
    "mcpre A0 envM VM F A K (X \<union> dvars (F @ ((a, Ta) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps))
      env'' ((a, Ta) # rb) ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)
      (map (incr_boundvars 1) targs @ [Bound 0]) body dps None"
proof -
  note finX = mcs_pre(1) and finK = mcs_pre(2) and A0A = mcs_pre(3) and tn = mcs_pre(4) and mx = mcs_pre(5)
    and extM = mcs_pre(6) and VX = mcs_pre(7) and vX = mcs_pre(8) and si = mcs_pre(9) and vu = mcs_pre(10)
    and tvX = mcs_facts(1) and vb = mcs_facts(2) and vuE = mcs_facts(3) and vaE = mcs_facts(4)
    and vtXE = mcs_facts(5) and vtF = mcs_facts(6) and dvF = mcs_facts(7) and tvF = mcs_facts(8)
    and Tsok = mcs_facts(9) and ty6 = mcs_facts(12)
  note ei = mcs_inv(1) and pd = pokD[OF mcs_inv(3)]
  note e = einvD[OF ei]
  obtain B' where u: "u = Abs a Ta body" and sat: "satd env rb u" and fB': "fastype env ((a, Ta) # rb) body = return B'"
    and tvTa: "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A"
    by (rule mcs_abs_type[OF Abs])
  have tvb: "ttvars body \<union> btvars ((a, Ta) # rb) \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(4,5) by (auto simp: u btvars_def)
  note gs = genvar_simps[OF g]
  define Y' where "Y' = ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)"
  have dv: "okW (dest_Var Y) Y'" by (simp add: gs(4) Y'_def)
  have fBo: "ok (fastype env ((a, Ta) # rb) body) B" using fB by (simp add: return_def)
  note st = mc_abs_step[OF mcs_lookup Abs Tsok fBo g dv up sat]
  define targs1 where "targs1 = map (\<lambda>t. lift t 0) targs @ [Bound 0]"
  define pb where "pb = ((a, Ta) # rb, Y \<degree>\<degree> targs1, body)"
  let ?s0 = "types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))"
  have clY: "closed Y" by (simp add: gs(4) closed_def)
  have vY: "vars Y = {((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)}" by (simp add: gs(4))
  have Ynew: "vt_lookup (tenv env) (vname, maxidx env + 1) = None"
    using bbelowD[OF e(5), of "(vname, maxidx env + 1)"] by (cases "vt_lookup (tenv env) (vname, maxidx env + 1)") auto
  have tvY: "ttvars Y \<subseteq> tvars_env (tyenv env) \<union> A" using ty6 tvTa tvB by (auto simp: gs(4) tvars_funs)
  have cb: "combound Y 0 (Suc (length Ts)) = Y \<degree>\<degree> bvs (Suc (length Ts))" by (rule combound_bvs)
  have lbs: "\<not> loose_bvar (Y \<degree>\<degree> bvs (Suc (length Ts))) (ilength Ts + 1)"
    using loose_bvar_bvs_ilength[of "Ts @ [Ta]" "Suc (length Ts)"] clY
    by (simp add: loose_bvar_apps closed_loose_bvar)
  have ei'': "einv A K env''"
  proof (rule einv_bind[OF ei gs(1,2) _ up])
    show "maxidx env \<le> maxidx env'" using gs(3) by simp
    show "vt_lookup (tenv env) y = None \<and> y \<noteq> v" if "(y, U) \<in> vars ?s0" for y U
      using that Ynew vb by (auto simp: combound_apps vars_apps vY)
    show "closed ?s0" by (rule closed_types_abs) (use lbs cb in simp)
    show "snd v \<le> maxidx env" by (fact vb)
    show "tvars TX \<union> ttvars ?s0 \<subseteq> tvars_env (tyenv env) \<union> A"
      using tvX ty6 tvTa tvY by (auto simp: ttvars_combound)
  qed
  have tt: "\<forall>(rb', t', u')\<in>set (pb # dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env'') \<union> A"
  proof -
    have "ttvars (Y \<degree>\<degree> targs1) \<subseteq> tvars_env (tyenv env) \<union> A"
      using tvY pd(3) by (auto simp: targs1_def ttvars_apps)
    then show ?thesis using tvF tvb st(4) by (auto simp: pb_def)
  qed
  have vt: "vtvars (dvars (pb # dps)) \<subseteq> tvars_env (tyenv env'') \<union> A"
  proof -
    have "dvars (pb # dps) \<subseteq> vars Y \<union> (X \<union> evars env)"
      using vaE vuE dvF by (auto simp: pb_def targs1_def vars_apps u)
    then have "vtvars (dvars (pb # dps)) \<subseteq> vtvars (vars Y) \<union> vtvars (X \<union> evars env)"
      by (auto simp: vtvars_def)
    moreover have "vtvars (vars Y) \<subseteq> tvars_env (tyenv env) \<union> A"
      using ty6 tvTa tvB by (auto simp: vY vtvars_def tvars_funs)
    ultimately show ?thesis using vtXE st(4) by auto
  qed
  have si'': "sinv A K (X \<union> dvars (F @ pb # dps)) env'' (F @ pb # dps)"
    by (rule sinv_frame_step[OF si st(3)[folded targs1_def, folded pb_def] ei'' _ vX tt vt order_refl])
      (simp add: st(4))
  have t1: "map (incr_boundvars 1) targs @ [Bound 0] = targs1" by (simp add: targs1_def map_incr_boundvars_lift)
  have mx'': "maxidx env \<le> maxidx env''" using extends_maxidx[OF st(5)] .
  show "u = Abs a Ta body" by (fact u)
  show "Y = Var (vname, maxidx env + 1) (foldr fun_type (Ts @ [Ta]) B)" by (simp add: gs(4))
  show "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      (((a, Ta) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps)" by (rule st(3))
  show "tyenv env'' = tyenv env" by (rule st(4))
  show "extends env env''" by (rule st(5))
  show "mcpre A0 envM VM F A K (X \<union> dvars (F @ ((a, Ta) # rb, Y \<degree>\<degree> (map (\<lambda>t. lift t 0) targs @ [Bound 0]), body) # dps))
      env'' ((a, Ta) # rb) ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)
      (map (incr_boundvars 1) targs @ [Bound 0]) body dps None"
    unfolding mcpre_def targs1_def[symmetric] pb_def[symmetric]
  proof (intro conjI)
    show "finite (X \<union> dvars (F @ pb # dps))" using finX by simp
    show "tnew A0 envM A env''" by (rule tnew_trans[OF tn tnew_same mx]) (simp add: st(4))
    show "maxidx envM \<le> maxidx env''" using mx mx'' by simp
    show "extends envM env''" by (rule extends_trans[OF extM st(5)])
    show "VM \<subseteq> X \<union> dvars (F @ pb # dps) \<union> evars env''" using VX evars_extends[OF st(5)] by blast
    show "vtvars (X \<union> dvars (F @ pb # dps)) \<subseteq> tvars_env (tyenv env'') \<union> A"
      using vX vt vtF st(4) by simp
    show "sinv A K (X \<union> dvars (F @ pb # dps)) env'' (F @ ((a, Ta) # rb,
        Var (fst ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B))
          (snd ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)) \<degree>\<degree>
          (map (incr_boundvars 1) targs @ [Bound 0]), body) # dps)"
      using si'' t1 by (simp add: pb_def gs(4))
    show "vars body \<subseteq> VM" using vu by (simp add: u)
    show "msat None env'' ((a, Ta) # rb) body" by (simp add: msat_def st(6))
  qed (use finK A0A t1 in simp_all)
qed

text \<open>A flexible head: the variable is bound to a new variable applied to the bound variables.\<close>

lemma mcs_var:
  assumes Var: "fst (strip_comb u) = Var w W" and g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)"
    and up: "ok (update (v, TX) (types_abs Ts (combound newhd 0 (length Ts))) env') env''"
  shows "newhd = Var (fst w, maxidx env + 1) (foldr fun_type Ts base)"
    "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
    "tyenv env'' = tyenv env" "extends env env''"
    "cpinvX A0 envM VM F A K (X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps)) env''
      ((rb, newhd \<degree>\<degree> targs, u) # dps)"
proof -
  note finX = mcs_pre(1) and finK = mcs_pre(2) and A0A = mcs_pre(3) and tn = mcs_pre(4) and mx = mcs_pre(5)
    and extM = mcs_pre(6) and VX = mcs_pre(7) and vX = mcs_pre(8) and si = mcs_pre(9)
    and tvX = mcs_facts(1) and vb = mcs_facts(2) and vuE = mcs_facts(3) and vaE = mcs_facts(4)
    and vtXE = mcs_facts(5) and vtF = mcs_facts(6) and dvF = mcs_facts(7) and tvF = mcs_facts(8)
    and Tsok = mcs_facts(9) and tvbase = mcs_facts(11) and ty6 = mcs_facts(12)
  note ei = mcs_inv(1) and pd = pokD[OF mcs_inv(3)]
  note e = einvD[OF ei]
  have na: "\<not> is_Abs (fst (strip_comb u))" using Var by simp
  note gs = genvar_simps[OF g]
  let ?s0 = "types_abs Ts (combound newhd 0 (length Ts))"
  have T0': "ok (fastype env rb (Var w W)) T0" and base': "ok (body_type env T0) base"
    using ty0(1,2) Var by (simp_all add: return_def)
  have d: "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)"
    by (rule mc_var_step[OF mcs_lookup Var T0' base' Tsok g up]) (rule mcs_bse[OF na])
  have cln: "closed newhd" by (simp add: gs(4) closed_def)
  have vN: "vars newhd = {((fst w, maxidx env + 1), foldr fun_type Ts base)}" by (simp add: gs(4))
  have Nnew: "vt_lookup (tenv env) (fst w, maxidx env + 1) = None"
    using bbelowD[OF e(5), of "(fst w, maxidx env + 1)"] by (cases "vt_lookup (tenv env) (fst w, maxidx env + 1)") auto
  have tvN: "ttvars newhd \<subseteq> tvars_env (tyenv env) \<union> A" using tvbase ty6 by (auto simp: gs(4) tvars_funs)
  have ext'': "extends env env''" by (rule extends_trans[OF extends_genvar[OF g] extends_update[OF up]])
  have ty'': "tyenv env'' = tyenv env" using ok_update(3)[OF up] gs(2) by simp
  have ei'': "einv A K env''"
  proof (rule einv_bind[OF ei gs(1,2) _ up])
    show "maxidx env \<le> maxidx env'" using gs(3) by simp
    show "vt_lookup (tenv env) y = None \<and> y \<noteq> v" if "(y, U) \<in> vars ?s0" for y U
      using that Nnew vb by (auto simp: combound_apps vars_apps vN)
    show "closed ?s0"
      by (rule closed_types_abs) (use loose_bvar_bvs_ilength[of Ts, OF refl] cln in
        \<open>simp add: combound_bvs loose_bvar_apps closed_loose_bvar\<close>)
    show "snd v \<le> maxidx env" by (fact vb)
    show "tvars TX \<union> ttvars ?s0 \<subseteq> tvars_env (tyenv env) \<union> A"
      using tvX ty6 tvN by (auto simp: ttvars_combound)
  qed
  have tt: "\<forall>(rb', t', u')\<in>set ((rb, newhd \<degree>\<degree> targs, u) # dps).
      ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env'') \<union> A"
    using tvF tvN pd(3,4,5) ty'' by (auto simp: ttvars_apps)
  have vt: "vtvars (dvars ((rb, newhd \<degree>\<degree> targs, u) # dps)) \<subseteq> tvars_env (tyenv env'') \<union> A"
  proof -
    have "dvars ((rb, newhd \<degree>\<degree> targs, u) # dps) \<subseteq> vars newhd \<union> (X \<union> evars env)"
      using vaE vuE dvF by (auto simp: vars_apps)
    then have "vtvars (dvars ((rb, newhd \<degree>\<degree> targs, u) # dps)) \<subseteq> vtvars (vars newhd) \<union> vtvars (X \<union> evars env)"
      by (auto simp: vtvars_def)
    moreover have "vtvars (vars newhd) \<subseteq> tvars_env (tyenv env) \<union> A"
      using tvbase ty6 by (auto simp: vN vtvars_def tvars_funs)
    ultimately show ?thesis using vtXE ty'' by auto
  qed
  have si'': "sinv A K (X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps)) env''
      (F @ (rb, newhd \<degree>\<degree> targs, u) # dps)"
    by (rule sinv_frame_step[OF si d ei'' _ vX tt vt order_refl]) (simp add: ty'')
  show "newhd = Var (fst w, maxidx env + 1) (foldr fun_type Ts base)" by (simp add: gs(4))
  show "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env'' ((rb, newhd \<degree>\<degree> targs, u) # dps)" by (fact d)
  show "tyenv env'' = tyenv env" by (fact ty'')
  show "extends env env''" by (fact ext'')
  show "cpinvX A0 envM VM F A K (X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps)) env''
      ((rb, newhd \<degree>\<degree> targs, u) # dps)"
  proof (rule cpinvXI[OF _ finK A0A _ _ _ _ _ si''])
    show "finite (X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps))" using finX by simp
    show "tnew A0 envM A env''" by (rule tnew_trans[OF tn tnew_same mx]) (simp add: ty'')
    show "maxidx envM \<le> maxidx env''" using mx extends_maxidx[OF ext''] by simp
    show "extends envM env''" by (rule extends_trans[OF extM ext''])
    show "VM \<subseteq> X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps) \<union> evars env''"
      using VX evars_extends[OF ext''] by blast
    show "vtvars (X \<union> dvars (F @ (rb, newhd \<degree>\<degree> targs, u) # dps)) \<subseteq> tvars_env (tyenv env'') \<union> A"
      using vX vt vtF ty'' by simp
  qed
qed

text \<open>A projection, after the type unification, with new variables for the arguments:\<close>

lemma mcs_proj:
  assumes nAb: "\<not> is_Abs (fst (strip_comb u))"
    and g: "gentvars p env = (env0, Cs)" and pu0: "okW (proj_unify cfg base bary Cs env0) env'"
    and post: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)"
      "tenv env' = tenv env0" "extends env0 env'" "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
      "tnew (A \<union> ntv Cs) env0 (A \<union> ntv Cs) env'"
    and st: "ok (strip_type env T) (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
    and hk: "k < length targs" "head = Bound (integer_of_nat (length targs - 1 - k))" "targ = targs ! k"
      "T = Ts ! k"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
    and up: "ok (update (v, TX) (types_abs Ts (list_comb head args)) env1) env2"
  shows "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env2
      ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
    "tyenv env2 = tyenv env'" "extends env env2"
    "cpinvX A0 envM VM F (A \<union> ntv Cs) (K \<union> ntv Cs)
      (X \<union> dvars (F @ (rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) env2
      ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)"
proof -
  note finX = mcs_pre(1) and finK = mcs_pre(2) and A0A = mcs_pre(3) and tn = mcs_pre(4) and mx = mcs_pre(5)
    and extM = mcs_pre(6) and VX = mcs_pre(7) and vX = mcs_pre(8) and si = mcs_pre(9)
    and Tsok = mcs_facts(9) and tvTs = mcs_facts(12)
  let ?A = "A \<union> ntv Cs" and ?K = "K \<union> ntv Cs" and ?P = "(rb, Var v TX \<degree>\<degree> targs, u)"
  let ?lhs = "list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args)"
  note gs = gentvars_simps[OF g]
  have ei: "einv A K env" using si by (simp add: sinv_def)
  note e = einvD[OF ei]
  have p: "pok A env rb X (Var v TX \<degree>\<degree> targs) u" using si by (auto simp: sinv_def)
  note pd = pokD[OF p]
  have te': "tenv env' = tenv env" using post(2) gs(1) by simp
  have ext0: "extends env env0" using gs by (simp add: extends_def)
  have ext': "extends env env'" by (rule extends_trans[OF ext0 post(3)])
  have tve': "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" using post(4) gs(2) by simp
  have tvTs': "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env') \<union> ?A" using tvTs tve' by blast
  have tvUC: "\<forall>U\<in>set (Us @ Cs). tvars U \<subseteq> tvars_env (tyenv env') \<union> ?A"
    using tvUs tve' by (auto simp: ntv_def)
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs (Us @ Cs)"
    and ma': "tenv env1 = tenv env'" "tyenv env1 = tyenv env'" "maxidx env' \<le> maxidx env1"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
    and si1: "sinv ?A ?K (mlvars Gs \<union> X) env1 (F @ ?P # dps)"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> ?A"
    by (rule sinv_make_args[OF post(1) ma tvTs' tvUC])
  have Gv: "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U" using Gi by blast
  have te1: "tenv env1 = tenv env" using ma'(1) te' by simp
  have mx0: "maxidx env \<le> maxidx env'" by (rule extends_maxidx[OF ext'])
  have vN1: "vt_lookup (tenv env1) v = None" using vN te1 by simp
  have ei1: "einv ?A ?K env1" using si1 by (simp add: sinv_def)
  have vaE: "lvars targs \<subseteq> X \<union> evars env" using pd(1) by (auto simp: vars_apps)
  have vb: "snd v \<le> maxidx env" by (rule below_head[OF si]) (use pd(1) in \<open>auto simp: vars_apps\<close>)
  have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF Tsok])
  note na = new_args_props[OF Gs refl args]
  have vh: "vars (list_comb head args) = mlvars Gs" using na(2) hk(2) by (simp add: list_comb_apps vars_apps)
  have j: "integer_of_nat (length targs - 1 - k) < ilength Ts"
    using hk(1) lTs by (simp add: ilength_eq integer_less_iff integer_of_nat.rep_eq)
  have clh: "closed (types_abs Ts (list_comb head args))"
    by (rule closed_types_abs) (use na(1) j hk(2) in \<open>auto simp: list_comb_apps loose_bvar_apps\<close>)
  have tvh: "ttvars (list_comb head args) = vtvars (mlvars Gs)"
    using na(3) ttvars_mlvars_Gs[OF Gv] hk(2) by (simp add: list_comb_apps ttvars_apps)
  have ei2: "einv ?A ?K env2"
  proof (rule einv_bind[OF ei1 refl refl order_refl up])
    show "vt_lookup (tenv env1) y = None \<and> y \<noteq> v" if "(y, U) \<in> vars (types_abs Ts (list_comb head args))" for y U
    proof -
      from that vh obtain G where "G \<in> set Gs" "(y, U) \<in> vars G" by auto
      with Gi have y: "snd y = maxidx env' + 1" by auto
      have "vt_lookup (tenv env) y = None"
        using bbelowD[OF e(5), of y] y mx0 by (cases "vt_lookup (tenv env) y") auto
      then show ?thesis using te1 y vb mx0 by auto
    qed
    show "closed (types_abs Ts (list_comb head args))" by (fact clh)
    show "snd v \<le> maxidx env1" using vb mx0 ma'(3) by simp
    show "tvars TX \<union> ttvars (types_abs Ts (list_comb head args)) \<subseteq> tvars_env (tyenv env1) \<union> ?A"
      using pd(3) tvTs' vG tvh ma'(2) tve' by (auto simp: ttvars_apps)
  qed
  have "dstep env ((rb, Var (fst (v, TX)) (snd (v, TX)) \<degree>\<degree> targs, u) # dps) env2 ((rb, ?lhs, u) # dps)"
    by (rule proj_dstep[OF pu0 g st pg hk Tsok _ ma up]) (use mcs_bse[OF nAb] in simp)
  then have d: "dstep env (?P # dps) env2 ((rb, ?lhs, u) # dps)" by simp
  have hargs: "map (\<lambda>arg. list_comb (head_of arg) targs) args = map (\<lambda>G. G \<degree>\<degree> targs) Gs"
    using Gv by (auto simp: args list_comb_apps head_of_apps)
  have lhs: "?lhs = targ \<degree>\<degree> map (\<lambda>G. G \<degree>\<degree> targs) Gs" unfolding hargs by (simp add: list_comb_apps)
  have targk: "targ \<in> set targs" using hk(1,3) by simp
  have vlhs: "vars ?lhs \<subseteq> mlvars Gs \<union> lvars targs" using Gv targk by (auto simp: lhs vars_apps)
  have tlhs: "ttvars ?lhs \<subseteq> vtvars (mlvars Gs) \<union> (\<Union>t\<in>set targs. ttvars t)"
    using ttvars_mlvars_Gs[OF Gv] targk by (auto simp: lhs ttvars_apps)
  have ty2: "tyenv env2 = tyenv env'" using ok_update(3)[OF up] ma'(2) by simp
  have tve2: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env2)" using tve' ty2 by simp
  have tvF: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
    using si by (fastforce simp: sinv_def dest: pokD(3,4,5))
  have tt: "\<forall>(rb', t', u')\<in>set ((rb, ?lhs, u) # dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env2) \<union> ?A"
  proof -
    have "(\<Union>t\<in>set targs. ttvars t) \<subseteq> tvars_env (tyenv env) \<union> A" using pd(3) by (auto simp: ttvars_apps)
    then have "(\<Union>t\<in>set targs. ttvars t) \<subseteq> tvars_env (tyenv env') \<union> ?A" using tve' by blast
    then have "ttvars ?lhs \<subseteq> tvars_env (tyenv env2) \<union> ?A"
      unfolding ty2 by (rule order_trans[OF tlhs Un_least[OF vG]])
    then show ?thesis using tvF tve2 pd(4,5) by fastforce
  qed
  have dvF: "dvars (F @ ?P # dps) \<subseteq> X \<union> evars env" by (rule sinv_dvars0[OF si])
  have vtXE: "vtvars (X \<union> evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
    using vX vtvars_evars[OF e(1)] by simp
  have vt: "vtvars (dvars ((rb, ?lhs, u) # dps)) \<subseteq> tvars_env (tyenv env2) \<union> ?A"
  proof -
    have "dvars ((rb, ?lhs, u) # dps) \<subseteq> mlvars Gs \<union> (X \<union> evars env)"
      using vlhs vaE dvF by auto
    then have "vtvars (dvars ((rb, ?lhs, u) # dps)) \<subseteq> vtvars (mlvars Gs) \<union> vtvars (X \<union> evars env)"
      by (metis vtvars_mono vtvars_Un)
    moreover have "vtvars (X \<union> evars env) \<subseteq> tvars_env (tyenv env') \<union> ?A" using vtXE tve' by blast
    ultimately show ?thesis unfolding ty2 by (rule order_trans[OF _ Un_least[OF vG]])
  qed
  let ?X2 = "X \<union> dvars (F @ (rb, ?lhs, u) # dps)"
  have si2: "sinv ?A ?K ?X2 env2 (F @ (rb, ?lhs, u) # dps)"
    by (rule sinv_frame_step[OF si d ei2 tve2 vX tt vt Un_upper1])
  have ext2: "extends env env2" by (rule dstepD(1)[OF d])
  have tn2: "tnew A0 envM ?A env2"
  proof -
    have "tnew A env ?A env'" by (rule tnew_trans[OF tnew_gentvars[OF g] post(5) gs(3)])
    then have "tnew A env ?A env2" using ty2 by (simp add: tnew_def)
    then show ?thesis by (rule tnew_trans[OF tn _ mx])
  qed
  have vtF: "vtvars (dvars F) \<subseteq> tvars_env (tyenv env) \<union> A"
    using vtvars_mono[of "dvars F" "X \<union> evars env"] dvF vtXE by auto
  show "dstep env (?P # dps) env2 ((rb, ?lhs, u) # dps)" by (fact d)
  show "tyenv env2 = tyenv env'" by (fact ty2)
  show "extends env env2" by (fact ext2)
  show "cpinvX A0 envM VM F ?A ?K ?X2 env2 ((rb, ?lhs, u) # dps)"
  proof (rule cpinvXI[OF _ _ _ tn2 _ _ _ _ si2])
    show "finite ?X2" using finX by simp
    show "finite ?K" using finK by simp
    show "A0 \<subseteq> ?A" using A0A by blast
    show "maxidx envM \<le> maxidx env2" using mx extends_maxidx[OF ext2] by simp
    show "extends envM env2" by (rule extends_trans[OF extM ext2])
    show "VM \<subseteq> ?X2 \<union> evars env2" using VX evars_extends[OF ext2] by blast
    show "vtvars ?X2 \<subseteq> tvars_env (tyenv env2) \<union> ?A" using vX vtF vt tve2 by auto
  qed
qed

lemma proj_cq:
  assumes nAb: "\<not> is_Abs (fst (strip_comb u))"
    and g: "gentvars p env = (env0, Cs)" and pu0: "okW (proj_unify cfg base bary Cs env0) env'"
    and post: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)"
      "tenv env' = tenv env0" "extends env0 env'" "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
      "tnew (A \<union> ntv Cs) env0 (A \<union> ntv Cs) env'"
    and st: "ok (strip_type env T) (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
    and hk: "k < length targs" "head = Bound (integer_of_nat (length targs - 1 - k))" "targ = targs ! k"
      "T = Ts ! k"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
  shows "\<exists>env2. ok (update (v, TX) (types_abs Ts (list_comb head args)) env1) env2 \<and>
      cuok (SIMPL alg env2 ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
        (\<lambda>(env3, fr, ff). CQ A0 envM VM F (El_E env3 (fr @ ff)))"
proof -
  have te1: "tenv env1 = tenv env'" by (rule mf_make_args_props[OF ma]) blast
  have vN1: "vt_lookup (tenv env1) v = None" using vN te1 post(2) gentvars_simps(1)[OF g] by simp
  obtain env2 where up: "ok (update (v, TX) (types_abs Ts (list_comb head args)) env1) env2"
    using update_unbound[OF vN1] by blast
  note s = mcs_proj[OF nAb g pu0 post st pg hk tvUs ma up]
  show ?thesis by (intro exI conjI, rule up, rule simpl_cq[OF s(4)])
qed

text \<open>The argument types of an imitation:\<close>

lemma mcs_Us:
  assumes u: "u = uhead \<degree>\<degree> uargs"
  obtains Us where "mapM (fastype env rb) uargs = return Us" "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  have ei: "einv A K env" by (rule mcs_inv(1))
  note r0 = einv_rho0[OF ei] and pd = pokD[OF mcs_inv(3)]
  from pd(9)[OF r0] obtain e0 U0 where bs0: "bs_env (rho0 env) e0 rb"
    and tyu0: "e0 \<turnstile> inst (rho0 env) u : U0" by blast
  from tyu0[unfolded u inst_apps] obtain Vs where tyas: "e0 \<tturnstile> map (inst (rho0 env)) uargs : Vs"
    by (rule list_app_typeE)
  have "\<forall>s\<in>set uargs. \<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and>
      \<not> loose_bvar s (ilength rb) \<and> ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  proof
    fix s assume s: "s \<in> set uargs"
    then obtain i where i: "i < length uargs" "s = uargs ! i" by (auto simp: in_set_conv_nth)
    have "e0 \<turnstile> inst (rho0 env) s : Vs ! i" using typings_nth[OF tyas] i by auto
    moreover have "\<not> loose_bvar s (ilength rb)" using pd(8) s by (auto simp: u loose_bvar_apps)
    moreover have "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" using pd(4) s by (auto simp: u ttvars_apps)
    ultimately show "\<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and>
        \<not> loose_bvar s (ilength rb) \<and> ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
      using bs0 pd(5) by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Us where Usr: "mapM (fastype env rb) uargs = return Us"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  with that show ?thesis by blast
qed

text \<open>Imitation: the variable is bound to the head applied to new variables, into which the arguments
  are copied.\<close>

lemma mcs_imit:
  assumes u: "u = uhead \<degree>\<degree> uargs" and h: "uhead = Const c C \<or> uhead = Free c C"
    and Usok: "ok (mapM (fastype env rb) uargs) Us" and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and ma: "make_args vname Ts env Us = (env', args)"
    and up: "ok (update (v, TX) (types_abs Ts (list_comb uhead args)) env') env''"
  shows "dstep env ((rb, Var v TX \<degree>\<degree> targs, u) # dps) env''
      (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip (map head_of args) uargs) @ dps)"
    "tyenv env'' = tyenv env" "extends env env''"
    "cpinvX A0 envM VM F A K (X \<union> dvars (F @ map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip (map head_of args) uargs) @ dps))
      env'' (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) (zip (map head_of args) uargs) @ dps)"
    "\<forall>(G, uarg)\<in>set (zip (map head_of args) uargs). (\<exists>x U. G = Var x U) \<and> uarg \<in> set uargs"
proof -
  note finX = mcs_pre(1) and finK = mcs_pre(2) and A0A = mcs_pre(3) and tn = mcs_pre(4) and mx = mcs_pre(5)
    and extM = mcs_pre(6) and VX = mcs_pre(7) and vX = mcs_pre(8) and si = mcs_pre(9)
    and Tsok = mcs_facts(9) and tvTs = mcs_facts(12)
  let ?P = "(rb, Var v TX \<degree>\<degree> targs, u)"
  have ei: "einv A K env" by (rule mcs_inv(1))
  note e = einvD[OF ei] and pd = pokD[OF mcs_inv(3)]
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    and si1: "sinv A K (mlvars Gs \<union> X) env' (F @ ?P # dps)"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
    by (rule sinv_make_args[OF si ma tvTs tvUs])
  have Gv: "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U" using Gi by blast
  have vN1: "vt_lookup (tenv env') v = None" using vN ma'(1) by simp
  have ei1: "einv A K env'" using si1 by (simp add: sinv_def)
  have vaE: "lvars targs \<subseteq> X \<union> evars env" using pd(1) by (auto simp: vars_apps)
  have vb: "snd v \<le> maxidx env" by (rule below_head[OF si]) (use pd(1) in \<open>auto simp: vars_apps\<close>)
  note na = new_args_props[OF Gs refl args]
  have ch: "closed uhead" "vars uhead = {}" "ttvars uhead \<subseteq> ttvars u"
    using h by (auto simp: closed_def u ttvars_apps)
  have vh: "vars (list_comb uhead args) = mlvars Gs" using na(2) ch(2) by (simp add: list_comb_apps vars_apps)
  have ei'': "einv A K env''"
  proof (rule einv_bind[OF ei1 refl refl order_refl up])
    show "vt_lookup (tenv env') y = None \<and> y \<noteq> v" if "(y, U) \<in> vars (types_abs Ts (list_comb uhead args))" for y U
    proof -
      from that vh obtain G where "G \<in> set Gs" "(y, U) \<in> vars G" by auto
      with Gi have y: "snd y = maxidx env + 1" by auto
      have "vt_lookup (tenv env) y = None"
        using bbelowD[OF e(5), of y] y by (cases "vt_lookup (tenv env) y") auto
      then show ?thesis using ma'(1) y vb by auto
    qed
    show "closed (types_abs Ts (list_comb uhead args))"
      by (rule closed_types_abs) (use na(1) ch(1) in \<open>auto simp: list_comb_apps loose_bvar_apps closed_loose_bvar\<close>)
    show "snd v \<le> maxidx env'" using vb ma'(3) by simp
    have "ttvars (list_comb uhead args) \<subseteq> ttvars u \<union> vtvars (mlvars Gs)"
      using na(3) ttvars_mlvars_Gs[OF Gv] ch(3) by (auto simp: list_comb_apps ttvars_apps)
    then show "tvars TX \<union> ttvars (types_abs Ts (list_comb uhead args)) \<subseteq> tvars_env (tyenv env') \<union> A"
      using pd(3,4) tvTs vG ma'(2) by (auto simp: ttvars_apps)
  qed
  let ?gus = "zip (map head_of args) uargs"
  let ?ps = "map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) ?gus"
  have "dstep env ((rb, Var (fst (v, TX)) (snd (v, TX)) \<degree>\<degree> targs, u) # dps) env'' (?ps @ dps)"
    by (rule imit_dstep[OF Usok ma up u ch(1,2) Tsok])
  then have d: "dstep env (?P # dps) env'' (?ps @ dps)" by simp
  have hd: "map head_of args = Gs" using Gv by (auto simp: args head_of_apps intro!: map_idI)
  have ty'': "tyenv env'' = tyenv env" using ok_update(3)[OF up] ma'(2) by simp
  have tvF: "\<forall>(rb', t', u')\<in>set (F @ ?P # dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env) \<union> A"
    using si by (fastforce simp: sinv_def dest: pokD(3,4,5))
  have gus: "(G, uarg) \<in> set ?gus \<Longrightarrow> G \<in> set Gs \<and> uarg \<in> set uargs" for G uarg
    unfolding hd by (auto dest: set_zip_leftD set_zip_rightD)
  have tvGs: "ttvars G \<subseteq> tvars_env (tyenv env) \<union> A" if "G \<in> set Gs" for G
    using that vG ttvars_mlvars_Gs[OF Gv] by blast
  have tt: "\<forall>(rb', t', u')\<in>set (?ps @ dps). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv env'') \<union> A"
  proof -
    have "(\<Union>t\<in>set targs. ttvars t) \<subseteq> tvars_env (tyenv env) \<union> A" using pd(3) by (auto simp: ttvars_apps)
    moreover have "ttvars uarg \<subseteq> tvars_env (tyenv env) \<union> A" if "uarg \<in> set uargs" for uarg
      using pd(4) that by (auto simp: u ttvars_apps)
    ultimately show ?thesis using tvF pd(5) tvGs gus unfolding ty'' by (fastforce simp: ttvars_apps)
  qed
  have dvF: "dvars (F @ ?P # dps) \<subseteq> X \<union> evars env" by (rule sinv_dvars0[OF si])
  have vtXE: "vtvars (X \<union> evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
    using vX vtvars_evars[OF e(1)] by simp
  have vt: "vtvars (dvars (?ps @ dps)) \<subseteq> tvars_env (tyenv env'') \<union> A"
  proof -
    have "dvars (?ps @ dps) \<subseteq> mlvars Gs \<union> (X \<union> evars env)"
    proof -
      have "vars uarg \<subseteq> X \<union> evars env" if "uarg \<in> set uargs" for uarg
        using pd(2) that by (auto simp: u vars_apps)
      then show ?thesis using gus vaE dvF by (fastforce simp: dvars_def vars_apps)
    qed
    then have "vtvars (dvars (?ps @ dps)) \<subseteq> vtvars (mlvars Gs) \<union> vtvars (X \<union> evars env)"
      by (metis vtvars_mono vtvars_Un)
    then show ?thesis unfolding ty'' by (rule order_trans[OF _ Un_least[OF vG vtXE]])
  qed
  let ?X2 = "X \<union> dvars (F @ ?ps @ dps)"
  have si2: "sinv A K ?X2 env'' (F @ ?ps @ dps)"
    by (rule sinv_frame_step[OF si d ei'' _ vX tt vt order_refl]) (simp add: ty'')
  have ext'': "extends env env''" by (rule dstepD(1)[OF d])
  have vtF: "vtvars (dvars F) \<subseteq> tvars_env (tyenv env) \<union> A"
    using vtvars_mono[of "dvars F" "X \<union> evars env"] dvF vtXE by auto
  show "dstep env (?P # dps) env'' (?ps @ dps)" by (fact d)
  show "tyenv env'' = tyenv env" by (fact ty'')
  show "extends env env''" by (fact ext'')
  show "cpinvX A0 envM VM F A K ?X2 env'' (?ps @ dps)"
  proof (rule cpinvXI[OF _ finK A0A _ _ _ _ _ si2])
    show "finite ?X2" using finX by simp
    show "tnew A0 envM A env''" by (rule tnew_trans[OF tn tnew_same mx]) (simp add: ty'')
    show "maxidx envM \<le> maxidx env''" using mx extends_maxidx[OF ext''] by simp
    show "extends envM env''" by (rule extends_trans[OF extM ext''])
    show "VM \<subseteq> ?X2 \<union> evars env''" using VX evars_extends[OF ext''] by blast
    show "vtvars ?X2 \<subseteq> tvars_env (tyenv env'') \<union> A"
      using vX vtF vt ty'' by auto
  qed
  show "\<forall>(G, uarg)\<in>set ?gus. (\<exists>x U. G = Var x U) \<and> uarg \<in> set uargs" using gus Gv by blast
qed

lemma imit_fin:
  assumes CC: "\<And>F e rb targs G uarg d. cpinv A0 envM VM F e ((rb, G \<degree>\<degree> targs, uarg) # d) \<Longrightarrow> vars uarg \<subseteq> VM \<Longrightarrow>
      \<exists>x U. G = Var x U \<Longrightarrow> rsz envM uarg < N \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname envM rb targs G uarg e d) cs \<and> fin cfg cs (CQ A0 envM VM F)"
    and u: "u = uhead \<degree>\<degree> uargs" and h: "uhead = Const c C \<or> uhead = Free c C"
    and N: "rsz envM u \<le> N" and tuu: "e1 \<turnstile> inst \<rho>1 (unf envM u) : W"
  shows "\<exists>s. okW (imitate vname envM rb targs env dps (v, TX) Ts uhead uargs) s \<and> fin cfg s (CQ A0 envM VM F)"
proof -
  obtain Us where Usr: "mapM (fastype env rb) uargs = return Us"
    and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A" by (rule mcs_Us[OF u])
  have Usok: "ok (mapM (fastype env rb) uargs) Us" using Usr by (simp add: return_def)
  obtain env' args where ma: "make_args vname Ts env Us = (env', args)" by fastforce
  have te': "tenv env' = tenv env" by (rule mf_make_args_props[OF ma]) blast
  have vN1: "vt_lookup (tenv env') v = None" using vN te' by simp
  obtain env'' where up: "ok (update (v, TX) (types_abs Ts (list_comb uhead args)) env') env''"
    using update_unbound[OF vN1] by blast
  note st = mcs_imit[OF u h Usok tvUs ma up]
  let ?gus = "zip (map head_of args) uargs"
  have ci: "cpinv A0 envM VM F env'' (map (\<lambda>(G, uarg). (rb, G \<degree>\<degree> targs, uarg)) ?gus @ dps)"
    using st(4) unfolding cpinv_def by blast
  have ar: "\<forall>(G, uarg)\<in>set ?gus. (\<exists>x U. G = Var x U) \<and> vars uarg \<subseteq> VM \<and> rsz envM uarg < N"
  proof (clarify)
    fix G uarg assume m: "(G, uarg) \<in> set ?gus"
    with st(5) have G: "\<exists>x U. G = Var x U" and a: "uarg \<in> set uargs" by blast+
    have "rsz envM uarg < rsz envM (uhead \<degree>\<degree> uargs)" by (rule rsz_rigid_arg[OF h tuu[unfolded u] a])
    then have "rsz envM uarg < N" using N u by simp
    moreover have "vars uarg \<subseteq> VM" using mcs_pre(10) a by (auto simp: u vars_apps)
    ultimately show "(\<exists>x U. G = Var x U) \<and> vars uarg \<subseteq> VM \<and> rsz envM uarg < N" using G by blast
  qed
  have fc: "fin cfg (copyargs vname envM rb targs ?gus env'' dps) (CQ A0 envM VM F)"
    by (rule copyargs_fin[OF CC ci ar])
  have up': "update (v, TX) (types_abs Ts (list_comb uhead args)) env' = return env''"
    using up by (simp add: return_def)
  have "okW (imitate vname envM rb targs env dps (v, TX) Ts uhead uargs) (copyargs vname envM rb targs ?gus env'' dps)"
    by (simp add: imitate_def Usr ma up' liftM_def return_def bindW_def returnW_def)
  with fc show ?thesis by blast
qed

end

subsection \<open>The copies are finite\<close>

lemma mc_fin_aux:
  assumes cfg: "cfg_alg cfg = alg" and M: "menv envM VM"
    and CC: "\<And>F e rb targs G uarg d. cpinv A0 envM VM F e ((rb, G \<degree>\<degree> targs, uarg) # d) \<Longrightarrow> vars uarg \<subseteq> VM \<Longrightarrow>
      \<exists>x U. G = Var x U \<Longrightarrow> rsz envM uarg < N \<Longrightarrow>
      \<exists>cs. okW (copycons cfg vname envM rb targs G uarg e d) cs \<and> fin cfg cs (CQ A0 envM VM F)"
  shows "mcpre A0 envM VM F A K X env rb (v, TX) targs u dps ot \<Longrightarrow> rsz envM u \<le> N \<Longrightarrow>
    \<exists>s. okW (mc cfg vname envM (v, TX) rb targs u env dps) s \<and> fin cfg s (CQ A0 envM VM F)"
proof (induction "size u" arbitrary: F A K X env rb v TX targs u dps ot rule: less_induct)
  case less
  note pre = less.prems(1) and N = less.prems(2)
  from pre have finX: "finite X" and finK: "finite K" and A0A: "A0 \<subseteq> A"
    and tn: "tnew A0 envM A env" and mx: "maxidx envM \<le> maxidx env" and extM: "extends envM env"
    and VX: "VM \<subseteq> X \<union> evars env" and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and si: "sinv A K X env (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)" and vu: "vars u \<subseteq> VM"
    by (simp_all add: mcpre_def)
  have ei: "einv A K env" and wi: "winv env X" using si by (simp_all add: sinv_def)
  have p: "pok A env rb X (Var v TX \<degree>\<degree> targs) u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  have vk: "vok env (X \<union> evars env)" by (rule vok_winv[OF ei wi vX])
  have vT: "(v, TX) \<in> X \<union> evars env" using pd(1) by (auto simp: vars_apps)
  have lk: "lookup env v TX = return (map_option snd (vt_lookup (tenv env) v))"
    by (rule lookup_ok[OF e(6) e(7)]) (rule vok_mono[OF vk], use vT in blast)
  from pd(9)[OF r0] obtain e0 U0 where bs0: "bs_env (rho0 env) e0 rb"
    and tyt0: "e0 \<turnstile> inst (rho0 env) (Var v TX \<degree>\<degree> targs) : U0" and tyu0: "e0 \<turnstile> inst (rho0 env) u : U0" by blast
  have tuu: "e0 \<turnstile> inst (rho0 env) (unf envM u) : U0" by (rule unfM_typed[OF M extM wi VX vu r0 tyu0])
  show ?case
  proof (cases "vt_lookup (tenv env) v")
    case (Some b)
    then have lkS: "lookup env v TX = return (Some (snd b))" using lk by simp
    let ?s = "S_Single (El_E env ((rb, list_comb (Var v TX) targs, u) # dps))"
    have "okW (mc cfg vname envM (v, TX) rb targs u env dps) ?s" by (simp add: mc_assigned[OF lkS])
    moreover have "fin cfg ?s (CQ A0 envM VM F)"
      by (rule fin_Single) (auto simp: list_comb_apps intro!: cpinvI[OF finX finK A0A tn mx extM VX vX si])
    ultimately show ?thesis by blast
  next
    case None
    then have lkN: "lookup env v TX = return None" using lk by simp
    from pair_types[OF ei p] obtain T0 base Ts where ty: "fastype env rb (fst (strip_comb u)) = return T0"
      "body_type env T0 = return base" "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "mapM (fastype env rb) targs = return Ts"
      "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
      by blast
    note mcu = mc_unassigned[OF lkN ty(1) ty(2) ty(5)]
    have Tsok: "ok (mapM (fastype env rb) targs) Ts" using ty(5) by (simp add: return_def)
    have lTs: "length Ts = length targs" by (rule mapM_fastype_sound(1)[OF Tsok])
    have rigid: ?thesis if nAb: "\<not> is_Abs (fst (strip_comb u))" and nV: "\<not> is_Var (fst (strip_comb u))"
    proof -
      let ?h = "fst (strip_comb u)" and ?as = "snd (strip_comb u)"
      let ?Q = "CQ A0 envM VM F"
      have u2: "u = ?h \<degree>\<degree> ?as" by (rule strip_comb_apps) simp
      from make_projs_term[OF lTs, of u targs] obtain projs where mp: "okW (make_projs u targs Ts targs) projs"
        by blast
      note mpp = mf_make_projs_props[OF mp]
      have mcR: "mc cfg vname envM (v, TX) rb targs u env dps = bindW (make_projs u targs Ts targs)
          (\<lambda>projs. matchfun cfg vname envM rb targs u env dps (v, TX) ?h ?as base Ts (rev projs))"
        unfolding mcu using nAb nV by (cases ?h) simp_all
      note bse' = mcs_bse[OF pre None ty(1,2,5) nAb]
      have cbase: "cert_typ alg ar (tnorm (tyenv env) base)"
        using bse'[OF r0(1) bs0 tyt0 tyu0] bs_env_cert[OF bs0 tyu0 pd(8)] by simp
      from tyt0[unfolded inst_apps] obtain Ws where tya: "e0 \<tturnstile> map (inst (rho0 env)) targs : Ws"
        by (rule list_app_typeE)
      have tya': "e0 \<tturnstile> map (inst (rho0 env)) targs : map (tsubst (rho0 env)) Ts"
        using tya mapM_fastype_sound(2)[OF Tsok r0(1) bs0 tya] by simp
      have cTs0: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst (rho0 env) T)"
        by (rule mf_cert_targs[OF bs0 tya']) (use pd(7) in \<open>auto simp: loose_bvar_apps\<close>)
      have finK': "finite (K \<union> ntv Cs)" for Cs using finK by simp
      have PF: "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. strip_type env T = return (Us, bary) \<and>
          (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
            cuok (projenv cfg vname rb targs u env dps (v, TX) base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q))"
      proof (clarify)
        fix bv T targ assume "(bv, T, targ) \<in> set (rev projs)"
        then obtain k where hk: "k < length targs" "bv = Bound (integer_of_nat (length targs - 1 - k))"
          "targ = targs ! k" "T = Ts ! k"
          using mpp by fastforce
        have tvT: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using ty(6) hk(1,4) lTs by simp
        from binder_types_term[OF e(2) refl tvT] obtain Us where bU: "binder_types env T = return Us"
          by blast
        from body_type_term[OF e(2) refl tvT] obtain bary where
          bB: "body_type env T = return bary" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A" by blast
        have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
          using mf_binder_types_sound[OF bU[unfolded return_def] refl e(6)] tvT by blast
        have sT: "strip_type env T = return (Us, bary)" using bU bB by (simp add: strip_type_def)
        have stT: "ok (strip_type env T) (Us, bary)" using sT by (simp add: return_def)
        have cbary: "cert_typ alg ar (tnorm (tyenv env) bary)"
        proof -
          have "cert_typ alg ar (tsubst (rho0 env) T)" using cTs0 hk(1,4) lTs by simp
          moreover have "tsubst (rho0 env) T = map (tsubst (rho0 env)) Us \<Rrightarrow> tsubst (rho0 env) bary"
            by (rule strip_type_sound[OF stT r0(1)])
          ultimately show ?thesis by (simp add: cert_typ_funs)
        qed
        have "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
            cuok (projenv cfg vname rb targs u env dps (v, TX) base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q)"
        proof (intro ballI allI impI)
          fix p tail assume pg: "p \<in> set (arity_guesses cfg bary)" and t: "fin cfg tail ?Q"
          obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
          note gs = gentvars_simps[OF g]
          have si0: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env0 (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)"
            by (rule sinv_gentvars[OF si g])
          have ei0: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env0" using si0 by (simp add: sinv_def)
          have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
          proof
            fix C assume "C \<in> set Cs"
            then obtain a' where "C = TVar a' []" using gs(6) by blast
            then have "cert_typ alg ar C" by (simp add: cert_typ_def sort_ok_def)
            then show "cert_typ alg ar (tnorm (tyenv env0) C)" by (rule cert_tnorm[OF ei0])
          qed
          have Pc: "cuok (proj_unify cfg base bary Cs env0) (\<lambda>env'.
              sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) \<and>
              tenv env' = tenv env0 \<and> extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
              tnew (A \<union> ntv Cs) env0 (A \<union> ntv Cs) env' \<and>
              (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
            by (rule proj_unify_sinv[OF cfg finK' si0])
              (use ty(4) bB(2) gs(2) cbase cbary cC in \<open>auto simp: ntv_def\<close>)
          show "cuok (projenv cfg vname rb targs u env dps (v, TX) base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q)"
          proof (rule projenv_fin[OF g Pc _ t])
            fix env' env1 args
            assume ok: "okW (proj_unify cfg base bary Cs env0) env'"
              and P: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps) \<and>
              tenv env' = tenv env0 \<and> extends env0 env' \<and> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and>
              tnew (A \<union> ntv Cs) env0 (A \<union> ntv Cs) env' \<and>
              (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base))"
              and ma: "make_args vname Ts env' (Us @ Cs) = (env1, args)"
            from P have post: "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' (F @ (rb, Var v TX \<degree>\<degree> targs, u) # dps)"
              "tenv env' = tenv env0" "extends env0 env'" "tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env')"
              "tnew (A \<union> ntv Cs) env0 (A \<union> ntv Cs) env'" by blast+
            from proj_cq[OF pre None ty(1,2,5) nAb g ok post stT pg hk tvUs ma]
            show "\<exists>env2. ok (update (v, TX) (types_abs Ts (list_comb bv args)) env1) env2 \<and>
                cuok (SIMPL (cfg_alg cfg) env2
                  ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps))
                (\<lambda>(env3, fr, ff). ?Q (El_E env3 (fr @ ff)))" unfolding cfg .
          qed
        qed
        with sT show "\<exists>Us bary. strip_type env T = return (Us, bary) \<and>
            (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>tail. fin cfg tail ?Q \<longrightarrow>
              cuok (projenv cfg vname rb targs u env dps (v, TX) base Ts bv (Us, bary) targ p tail) (\<lambda>s. fin cfg s ?Q))"
          by blast
      qed
      have imit: "cuok (case ?h of
          Const _ _ \<Rightarrow> imitate vname envM rb targs env dps (v, TX) Ts ?h ?as
        | Free _ _ \<Rightarrow> imitate vname envM rb targs env dps (v, TX) Ts ?h ?as
        | _ \<Rightarrow> returnW S_Empty) (\<lambda>s. fin cfg s ?Q)"
      proof (cases "\<exists>c0 C. ?h = Const c0 C \<or> ?h = Free c0 C")
        case True
        then obtain c0 C where h: "?h = Const c0 C \<or> ?h = Free c0 C" by blast
        from imit_fin[OF pre None ty(1,2,5) CC u2 h N tuu]
        obtain s where "okW (imitate vname envM rb targs env dps (v, TX) Ts ?h ?as) s" "fin cfg s ?Q"
          by blast
        then have "cuok (imitate vname envM rb targs env dps (v, TX) Ts ?h ?as) (\<lambda>s. fin cfg s ?Q)"
          by (rule cuok_okW)
        then show ?thesis using h by auto
      next
        case False
        then show ?thesis by (cases ?h) auto
      qed
      have "cuok (matchfun cfg vname envM rb targs u env dps (v, TX) ?h ?as base Ts (rev projs)) (\<lambda>s. fin cfg s ?Q)"
        by (rule matchfun_fin[OF PF imit])
      from cuok_noCU[OF this noCU_matchfun] obtain s where
        "okW (matchfun cfg vname envM rb targs u env dps (v, TX) ?h ?as base Ts (rev projs)) s" "fin cfg s ?Q"
        by blast
      then show ?thesis unfolding mcR using mp by auto
    qed
    show ?thesis
    proof (cases "fst (strip_comb u)")
      case (Abs a Ta body)
      obtain B where u: "u = Abs a Ta body" and fB: "fastype env ((a, Ta) # rb) body = return B"
        and tvB: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A"
        by (rule mcs_abs_type[OF pre None ty(1,2,5) Abs])
      obtain env' Y where g: "genvar vname env (foldr fun_type (Ts @ [Ta]) B) = (env', Y)" by fastforce
      note gs = genvar_simps[OF g]
      have vN': "vt_lookup (tenv env') v = None" using None gs(1) by simp
      obtain env'' where up: "ok (update (v, TX) (types_abs Ts (Abs a Ta (combound Y 0 (Suc (length Ts))))) env') env''"
        using update_unbound[OF vN'] by blast
      note st = mcs_abs[OF pre None ty(1,2,5) Abs fB tvB g up]
      define Y' where "Y' = ((vname, maxidx env + 1), foldr fun_type (Ts @ [Ta]) B)"
      have IH: "\<exists>s. okW (mc cfg vname envM Y' ((a, Ta) # rb) (map (incr_boundvars 1) targs @ [Bound 0])
          body env'' dps) s \<and> fin cfg s (CQ A0 envM VM F)"
        unfolding Y'_def
      proof (rule less.hyps[OF _ st(6)])
        show "size body < size u" by (simp add: u)
        have "rsz envM u = rsz envM body" unfolding u by (rule rsz_Abs[OF termip_typed_unf[OF tuu[unfolded u]]])
        then show "rsz envM body \<le> N" using N by simp
      qed
      then obtain s where sok: "okW (mc cfg vname envM Y' ((a, Ta) # rb)
          (map (incr_boundvars 1) targs @ [Bound 0]) body env'' dps) s" and fs: "fin cfg s (CQ A0 envM VM F)"
        by blast
      have up'': "update (v, TX) (types_abs Ts (Abs a Ta (combound Y 1 (length Ts) $ Bound 0))) env' = return env''"
        using up by (simp add: return_def)
      have fB': "fastype env ((a, Ta) # rb) body = return B" by (fact fB)
      have g': "genvar vname env (foldr fun_type Ts (Ta \<rightarrow>\<^sub>T B)) = (env', Y)" using g by simp
      have dvE: "dest_Var Y = returnW Y'" by (simp add: gs(4) Y'_def)
      have "okW (mc cfg vname envM (v, TX) rb targs u env dps) s"
        using sok unfolding mcu Abs pterm.case
        by (simp add: fB' g' dvE up'' liftM_def return_def bindW_def returnW_def)
      with fs show ?thesis by blast
    next
      case (Var w W)
      obtain env' newhd where g: "genvar (fst w) env (foldr fun_type Ts base) = (env', newhd)" by fastforce
      note gs = genvar_simps[OF g]
      have vN': "vt_lookup (tenv env') v = None" using None gs(1) by simp
      define s0 where "s0 = types_abs Ts (combound newhd 0 (length Ts))"
      obtain env'' where up: "ok (update (v, TX) s0 env') env''" using update_unbound[OF vN'] by blast
      note st = mcs_var[OF pre None ty(1,2,5) Var g up[unfolded s0_def]]
      let ?s = "S_Single (El_E env'' ((rb, list_comb newhd targs, u) # dps))"
      have up': "update (v, TX) s0 env' = return env''" using up by (simp add: return_def)
      have "okW (mc cfg vname envM (v, TX) rb targs u env dps) ?s"
        unfolding mcu Var pterm.case
        by (simp add: g up'[unfolded s0_def] liftM_def return_def bindW_def returnW_def)
      moreover have "fin cfg ?s (CQ A0 envM VM F)"
        using st(5) by (intro fin_Single) (auto simp: cpinv_def list_comb_apps)
      ultimately show ?thesis by blast
    next
      case (App f x)
      then have "strip_comb u = (f $ x, snd (strip_comb u))" by (metis prod.collapse)
      from strip_comb_head[OF this] show ?thesis by blast
    qed (use rigid in simp_all)
  qed
qed

subsection \<open>The copies of the arguments\<close>

text \<open>\<open>\<eta>\<close>-normalization keeps the variables:\<close>

lemma etif_vars_aux:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' = vars t"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with h obtain u where u: "ok (et tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl] t' show ?thesis by (simp add: incr_boundvars_def)
  next
    case False
    show ?thesis
    proof (cases T)
      case (Type a Ts)
      with False h have "t' = t" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    next
      case (TVar w S)
      with h obtain r' where r': "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with r' show ?thesis by simp
      next
        case (Some T')
        with r' have "ok (et tye T' t) t'" by simp
        from "1.IH"[OF this refl] show ?thesis .
      qed
    qed (use h in auto)
  qed
qed

lemma eta_norm_etif: "\<not> is_Abs t \<Longrightarrow> ok (eta_norm env rb t) t' \<Longrightarrow> \<exists>U. ok (etif (tyenv env) U t) t'"
  by (cases t) (auto simp: fastype_def)

lemma eta_norm_vars: "ok (eta_norm env rb t) t' \<Longrightarrow> vars t' = vars t"
proof (induction t arbitrary: rb t')
  case (Abs a A body)
  then show ?case by auto
qed (use eta_norm_etif etif_vars_aux in fastforce)+

text \<open>The \<open>\<eta>\<close>-normalization of a copied argument keeps its measure:\<close>

lemma rsz_eta_normM:
  assumes ti: "tinv ar n (tyenv en) A" and M: "menv envM VM" and ok: "ok (eta_norm en rb u1) u2"
    and ty: "e \<turnstile> inst (rho0 en) u1 : T" and bs: "bs_env (rho0 en) e rb" and lb: "\<not> loose_bvar u1 (ilength rb)"
    and tv: "ttvars u1 \<union> btvars rb \<subseteq> tvars_env (tyenv en) \<union> A"
    and tyu: "e \<turnstile> inst (rho0 en) (unf envM u1) : T"
  shows "rsz envM u2 = rsz envM u1"
proof -
  define envC where "envC = Envir (maxidx en) (tenv envM) (tyenv en)"
  have te: "tenv envC = tenv envM" and th: "tyenv envC = tyenv en" by (simp_all add: envC_def)
  have m: "acyc envM" "closed_env envM" using M by (simp_all add: menv_def)
  have ac: "acyc envC" "closed_env envC" using m te by (simp_all add: acyc_def dep_def closed_env_def)
  have uf: "unf envC = unf envM" by (rule unf_tenv[OF te])
  have okC: "ok (eta_norm envC rb u1) u2" using ok eta_norm_tyenv[OF th] by simp
  have "rsz envC u2 = rsz envC u1"
    using rsz_eta_norm[OF ti th ac okC ty bs lb tv] tyu uf by simp
  then show ?thesis by (simp add: rsz_def uf)
qed

text \<open>The normalization of a copied argument keeps the invariant of the copies:\<close>

lemma cc_inv:
  assumes M: "menv envM VM" and ci: "cpinvX A0 envM VM F A K X en ((rb, G \<degree>\<degree> targs, uarg) # d)"
    and vu: "vars uarg \<subseteq> VM"
  obtains u1 u2 B2 where "head_norm envM uarg = return u1" "eta_norm en rb u1 = return u2"
    "tconv en rb uarg u2" "vars u2 \<subseteq> VM" "rsz envM u2 = rsz envM uarg" "satd en rb u2"
    "defer_arg en rb u2 = return (is_TVar B2)"
    "dstep en ((rb, G \<degree>\<degree> targs, uarg) # d) en ((rb, G \<degree>\<degree> targs, u2) # d)"
    "cpinvX A0 envM VM F A K (X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)) en ((rb, G \<degree>\<degree> targs, u2) # d)"
proof -
  from ci have finX: "finite X" and finK: "finite K" and A0A: "A0 \<subseteq> A" and tn: "tnew A0 envM A en"
    and mx: "maxidx envM \<le> maxidx en" and extM: "extends envM en" and VX: "VM \<subseteq> X \<union> evars en"
    and vX: "vtvars X \<subseteq> tvars_env (tyenv en) \<union> A" and si: "sinv A K X en (F @ (rb, G \<degree>\<degree> targs, uarg) # d)"
    unfolding cpinvX_def by blast+
  have ei: "einv A K en" and wi: "winv en X" using si by (simp_all add: sinv_def)
  note E = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have p: "pok A en rb X (G \<degree>\<degree> targs) uarg" using si by (auto simp: sinv_def)
  note pd = pokD[OF p]
  have m: "acyc envM" "closed_env envM" using M by (simp_all add: menv_def)
  from pd(9)[OF r0] obtain e0 U0 where bs0: "bs_env (rho0 en) e0 rb" and tyu0: "e0 \<turnstile> inst (rho0 en) uarg : U0"
    by blast
  from hnM[OF M extM ei wi VX vu tyu0] obtain u1 where h: "head_norm envM uarg = return u1"
    and vu1: "vars u1 \<subseteq> VM" and tvu1: "ttvars u1 \<subseteq> ttvars uarg \<union> etvars envM"
    and sn: "termip beta (unf envM uarg)"
    and tyc: "\<forall>\<rho> e T. tsol (tyenv en) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> e \<turnstile> inst \<rho> uarg : T \<longrightarrow>
      e \<turnstile> inst \<rho> u1 : T \<and> e \<turnstile> inst \<rho> (unf envM uarg) : T"
    and lb: "\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar uarg k \<longrightarrow> \<not> loose_bvar u1 k"
    by blast
  have h1: "ok (head_norm envM uarg) u1" using h by (simp add: return_def)
  have ty1: "e0 \<turnstile> inst (rho0 en) u1 : U0" using tyc r0 tyu0 by blast
  have lb1: "\<not> loose_bvar u1 (ilength rb)" using lb pd(8) by simp
  have etM: "etvars envM \<subseteq> tvars_env (tyenv en) \<union> A"
  proof -
    have "etvars envM \<subseteq> etvars en" using extM unfolding etvars_def bnds_def extends_def by fast
    then show ?thesis using etvars_known[OF E(1)] by blast
  qed
  have tv1: "ttvars u1 \<union> btvars rb \<subseteq> tvars_env (tyenv en) \<union> A" using tvu1 pd(4,5) etM by blast
  from eta_norm_term[OF E(2) refl ty1 bs0 lb1 tv1] obtain u2 where et: "eta_norm en rb u1 = return u2"
    and tv2: "ttvars u2 \<subseteq> tvars_env (tyenv en) \<union> A" by blast
  have e2: "ok (eta_norm en rb u1) u2" using et by (simp add: return_def)
  have tc: "tconv en rb uarg u2"
    by (rule tconv_trans[OF tconv_extends[OF head_norm_tconv[OF h1] extM] eta_norm_tconv[OF e2]])
  have vu2: "vars u2 \<subseteq> VM"
    using eta_norm_vars[OF e2] vu1 by simp
  have w0: "wt_env (rho0 en) en" using winvD[OF wi r0] by blast
  have ty2: "e0 \<turnstile> inst (rho0 en) u2 : U0" and lb2: "\<not> loose_bvar u2 (ilength rb)"
    using tc r0(1) w0 bs0 tyu0 pd(8) unfolding tconv_def by blast+
  have dc: "dstep en ((rb, G \<degree>\<degree> targs, uarg) # d) en ((rb, G \<degree>\<degree> targs, u2) # d)"
    using dstep_frame[OF tconv_dstep[OF tconv_refl tc], where fs = d] by simp
  have rs: "rsz envM u2 = rsz envM uarg"
  proof -
    have "rsz envM u1 = rsz envM uarg" by (rule rsz_head_norm[OF h1 m sn])
    moreover have "rsz envM u2 = rsz envM u1"
      by (rule rsz_eta_normM[OF E(2) M e2 ty1 bs0 lb1 tv1 unfM_typed[OF M extM wi VX vu1 r0 ty1]])
    ultimately show ?thesis by simp
  qed
  have tvF: "\<forall>(rb', t', u')\<in>set (F @ (rb, G \<degree>\<degree> targs, uarg) # d). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv en) \<union> A"
    using si by (fastforce simp: sinv_def dest: pokD(3,4,5))
  have tt: "\<forall>(rb', t', u')\<in>set ((rb, G \<degree>\<degree> targs, u2) # d). ttvars t' \<union> ttvars u' \<union> btvars rb' \<subseteq> tvars_env (tyenv en) \<union> A"
    using tvF pd(3,5) tv2 by fastforce
  have dvF: "dvars (F @ (rb, G \<degree>\<degree> targs, uarg) # d) \<subseteq> X \<union> evars en" by (rule sinv_dvars0[OF si])
  have vtXE: "vtvars (X \<union> evars en) \<subseteq> tvars_env (tyenv en) \<union> A"
    using vX vtvars_evars[OF E(1)] by simp
  have dv2: "dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d) \<subseteq> X \<union> evars en" using dvF vu2 VX by auto
  have vt: "vtvars (dvars ((rb, G \<degree>\<degree> targs, u2) # d)) \<subseteq> tvars_env (tyenv en) \<union> A"
    by (rule order_trans[OF vtvars_mono vtXE]) (use dv2 in auto)
  let ?X2 = "X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)"
  have si2: "sinv A K ?X2 en (F @ (rb, G \<degree>\<degree> targs, u2) # d)"
    by (rule sinv_frame_step[OF si dc ei order_refl vX tt vt order_refl])
  have finX2: "finite ?X2" using finX by simp
  have vX2: "vtvars ?X2 \<subseteq> tvars_env (tyenv en) \<union> A"
    by (rule order_trans[OF vtvars_mono vtXE]) (use dv2 in auto)
  have VX2: "VM \<subseteq> ?X2 \<union> evars en" using VX by blast
  from env_fastype_term[OF E(2) refl ty2 bs0 lb2] tv2 pd(5) obtain A2 where
    fA: "env_fastype en (map snd rb) u2 = return A2" "tvars A2 \<subseteq> tvars_env (tyenv en) \<union> A" by blast
  have fA': "fastype en rb u2 = return A2" using fA(1) by (simp add: fastype_def)
  from body_type_term[OF E(2) refl fA(2)] obtain B2 where bB2: "body_type en A2 = return B2" by blast
  have da: "defer_arg en rb u2 = return (is_TVar B2)" by (simp add: defer_arg_def fA' bB2)
  have ci2: "cpinvX A0 envM VM F A K ?X2 en ((rb, G \<degree>\<degree> targs, u2) # d)"
    by (rule cpinvXI[OF finX2 finK A0A tn mx extM VX2 vX2 si2])
  show ?thesis
    by (rule that[OF h et tc vu2 rs head_norm_eta_norm_satd[OF h1 e2] da dc ci2])
qed

text \<open>A copy of an argument, given the finiteness of the copies of smaller measure:\<close>

lemma copycons_step:
  assumes M: "menv envM VM"
    and MC: "\<And>F A K X en rb v TX targs u dps ot. mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot \<Longrightarrow>
      rsz envM u \<le> N \<Longrightarrow>
      \<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F)"
    and ci: "cpinv A0 envM VM F en ((rb, G \<degree>\<degree> targs, uarg) # d)" and vu: "vars uarg \<subseteq> VM"
    and G: "G = Var x U" and N: "rsz envM uarg \<le> N"
  shows "\<exists>cs. okW (copycons cfg vname envM rb targs G uarg en d) cs \<and> fin cfg cs (CQ A0 envM VM F)"
proof -
  from ci obtain A K X where ciX: "cpinvX A0 envM VM F A K X en ((rb, G \<degree>\<degree> targs, uarg) # d)"
    unfolding cpinv_def by blast
  obtain u1 u2 B2 where h: "head_norm envM uarg = return u1" and et: "eta_norm en rb u1 = return u2"
    and vu2: "vars u2 \<subseteq> VM" and rs: "rsz envM u2 = rsz envM uarg" and sat: "satd en rb u2"
    and da: "defer_arg en rb u2 = return (is_TVar B2)"
    and ci2: "cpinvX A0 envM VM F A K (X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)) en ((rb, G \<degree>\<degree> targs, u2) # d)"
    by (rule cc_inv[OF M ciX vu])
  have h1: "ok (head_norm envM uarg) u1" and e2: "ok (eta_norm en rb u1) u2"
    using h et by (simp_all add: return_def)
  let ?d = "0 < cfg_arity_bound cfg \<and> is_TVar B2"
  have dW: "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg en rb u2) else returnW False) ?d"
    using da by (auto simp: return_def)
  obtain s where sok: "okW (if ?d then returnW (S_Single (El_E en ((rb, list_comb G targs, u2) # d)))
      else mc cfg vname envM (x, U) rb targs u2 en d) s"
    and fs: "fin cfg s (CQ A0 envM VM F)"
  proof (cases ?d)
    case True
    have "cpinv A0 envM VM F en ((rb, list_comb G targs, u2) # d)"
      using ci2 unfolding cpinv_def by (auto simp: list_comb_apps)
    then show ?thesis using True by (intro that[of "S_Single (El_E en ((rb, list_comb G targs, u2) # d))"]) (auto intro: fin_Single)
  next
    case False
    have "mcpre A0 envM VM F A K (X \<union> dvars (F @ (rb, G \<degree>\<degree> targs, u2) # d)) en rb (x, U) targs u2 d None"
      by (rule mcpreI) (use ci2 vu2 sat in \<open>simp_all add: G msat_def\<close>)
    from MC[OF this] rs N obtain s where s1: "okW (mc cfg vname envM (x, U) rb targs u2 en d) s"
      and s2: "fin cfg s (CQ A0 envM VM F)" by auto
    show ?thesis by (rule that[of s], simp only: if_not_P[OF False] s1, fact s2)
  qed
  have "okW (copycons cfg vname envM rb targs G uarg en d) s"
    unfolding copycons_def okW_bindW okW_liftM
    by (rule exI[of _ "(x, U)"], rule conjI, simp add: G,
        rule exI[of _ u1], rule conjI[OF h1], rule exI[of _ u2], rule conjI[OF e2],
        rule exI[of _ ?d], rule conjI[OF dW], rule sok)
  with fs show ?thesis by blast
qed

text \<open>The copies are finite, by induction on the measure of the copied term:\<close>

theorem mc_fin:
  assumes cfg: "cfg_alg cfg = alg" and M: "menv envM VM"
  shows "mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot \<Longrightarrow>
    \<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F)"
proof -
  have "\<forall>F A K X en rb v TX targs u dps ot. mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot \<longrightarrow>
      rsz envM u \<le> N \<longrightarrow>
      (\<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F))" for N
  proof (induction N rule: less_induct)
    case (less N)
    show ?case
    proof (intro allI impI)
      fix F A K X en rb v TX targs u dps ot
      assume pre: "mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot" and N: "rsz envM u \<le> N"
      show "\<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F)"
      proof (rule mc_fin_aux[OF cfg M _ pre N])
        fix F e rb targs G uarg d
        assume ci: "cpinv A0 envM VM F e ((rb, G \<degree>\<degree> targs, uarg) # d)" and vu: "vars uarg \<subseteq> VM"
          and G: "\<exists>x U. G = Var x U" and lt: "rsz envM uarg < N"
        from G obtain x U where G': "G = Var x U" by blast
        show "\<exists>cs. okW (copycons cfg vname envM rb targs G uarg e d) cs \<and> fin cfg cs (CQ A0 envM VM F)"
        proof (rule copycons_step[OF M _ ci vu G' order_refl])
          fix F A K X en rb v TX targs u dps ot
          assume "mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot" "rsz envM u \<le> rsz envM uarg"
          then show "\<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F)"
            using less.IH[OF lt] by blast
        qed
      qed
    qed
  qed
  then show "mcpre A0 envM VM F A K X en rb (v, TX) targs u dps ot \<Longrightarrow>
      \<exists>s. okW (mc cfg vname envM (v, TX) rb targs u en dps) s \<and> fin cfg s (CQ A0 envM VM F)"
    by blast
qed

subsection \<open>The enumeration of \<open>MATCH\<close>\<close>

theorem match_pair_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and st: "strip_comb t = (Var v T, targs)"
    and sat: "rsat env rb t u" and nab: "\<not> is_Abs (fst (strip_comb u))"
  shows "cuok (match_pair cfg env (rb, t, u) dps) (\<lambda>s. fin cfg s (mres A env))"
proof -
  let ?VM = "X \<union> evars env"
  have ei: "einv A K env" and wi: "winv env X" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  note E = einvD[OF ei] and pd = pokD[OF p]
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have M: "menv env ?VM" unfolding menv_def using E(3,4,6,7) vok_winv[OF ei wi pd(6)] by blast
  have pre: "mcpre A env ?VM [] A K X env rb (v, T) targs u dps (Some t)"
    unfolding mcpre_def msat_def using fin pd(2,6) si sat nab by (simp add: t)
  from mc_fin[OF cfg M pre] obtain s where s: "okW (mc cfg (fst v) env (v, T) rb targs u env dps) s"
    and fs: "fin cfg s (CQ A env ?VM [])" by blast
  have "fin cfg s (mres A env)" by (rule fin_mono[OF fs]) (auto intro: cpinv_mres)
  moreover have "okW (match_pair cfg env (rb, t, u) dps) s" using s st by (simp add: match_pair_def)
  ultimately show ?thesis by (blast intro: cuok_okW)
qed

lemma match_sat_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp" and ms: "msat_ok env dp"
  shows "cuok (match_sat cfg env dp dps) (\<lambda>s. fin cfg s (mres A env))"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  have ei: "einv A K env" and p: "pok A env rb X t u" using si dp by (auto simp: sinv_def)
  have tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    using head_tvars_strip_comb[OF st] pokD(3)[OF p] by blast
  from binder_types_term[OF einvD(2)[OF ei] refl tv] obtain Ts where bt: "binder_types env T = return Ts" by blast
  have bto: "ok (binder_types env T) Ts" using bt by (simp add: return_def)
  note ex = sinv_eta_expand[OF si[unfolded dp] st bt]
  define Es where "Es = drop (length targs) Ts"
  define targs' where "targs' = map (incr_bv (ilength Es) 0) targs @ bvs (length Es)"
  define rb' where "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  define t' where "t' = incr_bv (ilength Es) 0 t \<degree>\<degree> bvs (length Es)"
  define u' where "u' = incr_bv (ilength Es) 0 u \<degree>\<degree> bvs (length Es)"
  have ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
    by (simp add: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq rb'_def t'_def u'_def)
  have st': "strip_comb t' = (Var v T, targs')" by (simp add: t'_def targs'_def strip_comb_expand[OF st])
  from ms[unfolded msat_ok_def dp prod.case, rule_format, OF st bto] ed
  have sat: "rsat env rb' t' u'" and nab: "\<not> is_Abs (fst (strip_comb u'))" by (simp_all add: Es_def)
  have "cuok (match_pair cfg env (rb', t', u') dps) (\<lambda>s. fin cfg s (mres A env))"
    by (rule match_pair_fin[OF cfg fin _ st' sat nab]) (use ex(2) ed in \<open>simp add: Es_def\<close>)
  then show ?thesis unfolding match_sat_def dp prod.case st
    by (simp only: pterm.case) (intro cuok_liftM_return[OF bt], simp only: ed[unfolded Es_def])
qed

lemma match_eta_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
    and ms: "\<And>env'. extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> msat_ok env' dp"
    and B: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" "is_TVar B" and tl: "fin cfg tail (mres A env)"
  shows "cuok (match_eta cfg env dp dps B j tail) (\<lambda>s. fin cfg s (mres A env))"
proof (cases "j = 0")
  case True
  show ?thesis unfolding match_eta_def if_P[OF True]
    by (rule cuok_bindW[OF match_sat_fin[OF cfg fin si fr ms[OF extends_refl refl]]]) (simp add: fin_Append tl)
next
  case False
  obtain env1 Rs where g: "gentvars (Suc j) env = (env1, Rs)" by (cases "gentvars (Suc j) env")
  note gs = gentvars_simps[OF g]
  let ?A = "A \<union> ntv Rs" and ?K = "K \<union> ntv Rs"
  have si1: "sinv ?A ?K X env1 (dp # dps)" by (rule sinv_gentvars[OF si g])
  have finK: "finite ?K" using fin(2) by simp
  have th: "tyenv env1 = tyenv env" by (rule gs(2))
  have ei1: "einv ?A ?K env1" using si1 by (simp add: sinv_def)
  have ext1: "extends env env1" using gs by (simp add: extends_def)
  have Rs: "Rs \<noteq> []" using gs(4) by auto
  have tvR: "tvars (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) \<subseteq> ntv Rs"
    using Rs hd_in_set[OF Rs] list.set_sel(2)[OF Rs] by (fastforce simp: tvars_funs ntv_def)
  have cB: "cert_typ alg ar (tnorm (tyenv env1) B)"
  proof -
    obtain v S where Bv: "B = TVar v S" using B(2) by (cases B) auto
    then have "(v, S) \<in> tvars_env (tyenv env1) \<union> ?A" using B(1) th by auto
    then have "sort_ok alg S" using einvD(10)[OF ei1] tcertD by blast
    then have "cert_typ alg ar B" by (simp add: Bv cert_typ_def)
    then show ?thesis by (rule cert_tnorm[OF ei1])
  qed
  have cR: "cert_typ alg ar (tnorm (tyenv env1) (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)))"
  proof (rule cert_tnorm[OF ei1])
    have "cert_typ alg ar C" if "C \<in> set Rs" for C
      using gs(6)[OF that] by (auto simp: cert_typ_def sort_ok_def)
    then show "cert_typ alg ar (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs))"
      using Rs by (simp add: cert_typ_funs) (meson list.set_sel(1,2))
  qed
  have inner: "cuok (do {
      env2 \<leftarrow> cunify_types (cfg_alg cfg) B (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) env1;
      s \<leftarrow> match_sat cfg env2 dp dps;
      returnW (S_Append s tail)}) (\<lambda>s. fin cfg s (mres A env))"
    unfolding cfg
  proof (rule cuok_bindW[OF cunify_types_sinv[OF finK si1 _ cB _ cR]])
    show "tvars B \<subseteq> tvars_env (tyenv env1) \<union> ?A" using B(1) th by auto
    show "tvars (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)) \<subseteq> tvars_env (tyenv env1) \<union> ?A" using tvR by auto
    fix env2 assume "sinv ?A ?K X env2 (dp # dps) \<and> tenv env2 = tenv env1 \<and> extends env1 env2 \<and>
      tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env2) \<and> tnew ?A env1 ?A env2 \<and>
      (\<forall>\<rho>. tsol (tyenv env2) \<rho> \<longrightarrow> tsubst \<rho> B = tsubst \<rho> (foldr (\<rightarrow>\<^sub>T) (tl Rs) (hd Rs)))"
    then have si2: "sinv ?A ?K X env2 (dp # dps)" and te: "tenv env2 = tenv env"
      and tn2: "tnew ?A env1 ?A env2" and ext2: "extends env1 env2" using gs(1) by auto
    have tn: "tnew A env ?A env2" by (rule tnew_trans[OF tnew_gentvars[OF g] tn2 gs(3)])
    have mx: "maxidx env \<le> maxidx env2" using gs(3) extends_maxidx[OF ext2] by simp
    have fr2: "fr_shape env2 dp" using fr fr_shape_tenv[OF te] by simp
    have ms2: "msat_ok env2 dp" by (rule ms[OF extends_trans[OF ext1 ext2] te])
    show "cuok (match_sat cfg env2 dp dps \<bind> (\<lambda>s. returnW (S_Append s tail))) (\<lambda>s. fin cfg s (mres A env))"
      by (rule cuok_bindW[OF match_sat_fin[OF cfg fin(1) finK si2 fr2 ms2]])
        (simp add: fin_Append tl fin_mres_mono[of cfg _ ?A env2 A env, OF _ _ tn mx])
  qed
  show ?thesis unfolding match_eta_def if_not_P[OF False] g prod.case
    by (rule cuok_handle_CANTUNIFY_ret[OF inner]) (simp_all add: tl)
qed

lemma foldrW_match_eta_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp"
    and ms: "\<And>env'. extends env env' \<Longrightarrow> tenv env' = tenv env \<Longrightarrow> msat_ok env' dp"
    and B: "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" "is_TVar B"
  shows "cuok (foldrW (match_eta cfg env dp dps B) js S_Empty) (\<lambda>s. fin cfg s (mres A env))"
proof (induction js)
  case (Cons j js)
  show ?case by (simp, rule cuok_bindW[OF Cons.IH match_eta_fin[OF cfg fin si fr ms B]])
qed simp

theorem MATCH_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (dp # dps)" and fr: "fr_shape env dp" and mo: "MATCH_ok env dp"
  shows "cuok (MATCH cfg env dp dps) (\<lambda>ms. fin cfg ms (mres A env))"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from fr dp obtain v T targs where st: "strip_comb t = (Var v T, targs)" by (auto elim: fr_shape_strip_comb)
  have ei: "einv A K env" and p: "pok A env rb X t u" using si dp by (auto simp: sinv_def)
  have tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    using head_tvars_strip_comb[OF st] pokD(3)[OF p] by blast
  from body_type_term[OF einvD(2)[OF ei] refl tv] obtain B where
    bt: "body_type env T = return B" "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  have ms: "msat_ok env' dp" if "extends env env'" "tenv env' = tenv env" for env'
    using mo that unfolding MATCH_ok_def by blast
  have "cuok (if is_TVar B then foldrW (match_eta cfg env dp dps B) (arity_guesses cfg B) S_Empty
      else match_sat cfg env dp dps) (\<lambda>ms. fin cfg ms (mres A env))"
    using foldrW_match_eta_fin[OF cfg fin si fr ms bt(2)] match_sat_fin[OF cfg fin si fr ms[OF extends_refl refl]]
    by simp
  then show ?thesis unfolding MATCH_def dp prod.case st
    by (simp only: pterm.case) (intro cuok_liftM_return[OF bt(1)])
qed

end

end
