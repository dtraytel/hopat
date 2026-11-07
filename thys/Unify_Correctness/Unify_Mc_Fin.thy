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

definition cpinv :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> bool" where
  "cpinv A0 envM VM F env dps \<longleftrightarrow> (\<exists>A K X. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 envM A env \<and>
    maxidx envM \<le> maxidx env \<and> extends envM env \<and> VM \<subseteq> X \<union> evars env \<and>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<and> sinv A K X env (F @ dps))"

lemma cpinvI:
  assumes "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 envM A env" "maxidx envM \<le> maxidx env" "extends envM env"
    "VM \<subseteq> X \<union> evars env" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" "sinv A K X env (F @ dps)"
  shows "cpinv A0 envM VM F env dps"
  using assms unfolding cpinv_def by blast

lemma cpinv_set: "cpinv A0 envM VM F env dps \<Longrightarrow> set (F @ dps) = set (F' @ dps') \<Longrightarrow> cpinv A0 envM VM F' env dps'"
  unfolding cpinv_def by (metis sinv_mono order_refl)

lemma cpinv_mres: "cpinv A0 envM VM [] env dps \<Longrightarrow> mres A0 envM (El_E env dps)"
  unfolding cpinv_def mres_def by auto

lemma vtvars_Un: "vtvars (X \<union> Y) = vtvars X \<union> vtvars Y"
  by (auto simp: vtvars_def)

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

end

end
