section \<open>The Results of Higher-Order Unification\<close>

theory Unify_Results
  imports Unify_Pull_Fin Unify_Smash_Sound
begin

context pure_sig
begin

text \<open>
  On a well-formed problem (\<^const>\<open>sinv\<close>), \<^const>\<open>unifiers\<close> returns a sequence whose
  enumeration is finite, and every unifier \<open>El_R env' tps\<close> of it is a step from the input pairs
  to the remaining flex-flex pairs \<open>tps\<close> (\<^const>\<open>dstep\<close>), where \<open>env'\<close> and \<open>tps\<close> are well-formed
  again (\<^const>\<open>ffres\<close>). Consequences: smashing the flex-flex pairs is sound, terms that are
  well-typed in the input stay well-typed, variables that occur neither in the problem nor in
  the environment stay fresh, and the maximal index does not decrease.
\<close>

subsection \<open>The invariant of the results\<close>

definition uresult :: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> elem \<Rightarrow> bool" where
  "uresult env tus x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X. finite X \<and> finite K \<and> ffres A K X env' tps))"

lemma uresult_El_R:
  "uresult env tus (El_R env' tps) \<longleftrightarrow> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X. finite X \<and> finite K \<and> ffres A K X env' tps)"
  unfolding uresult_def by blast

lemma ur_finite_dvars: "finite (dvars dps)"
  by (induction dps) (auto simp: dvars_def)

text \<open>The unifiers of the search (\<^const>\<open>rres\<close>) are well-formed:\<close>

lemma rres_ffres:
  assumes "rres x"
  shows "\<exists>env' tps. x = El_R env' tps \<and> (\<exists>A K X. finite X \<and> finite K \<and> ffres A K X env' tps)"
proof -
  from assms obtain env' tps A K X env ffs where x: "x = El_R env' tps" and fin: "finite X" "finite K"
    and si: "sinv A K X env ffs" and f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps)"
    and fv: "finv A K env env'"
    and tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    unfolding rres_def by blast
  have wi: "winv env X" using si by (simp add: sinv_def)
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" using fv by (simp_all add: finv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps []). pok A env rb X t u" using si by (simp add: sinv_def)
  have ds: "dstep env (ffs @ tdps []) env' (tdps tps)" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winv[OF ds wi pk th]
  let ?X' = "X \<union> dvars (tdps tps)"
  have "pok A env' [] ?X' t u" if tu: "(t, u) \<in> set tps" for t u
  proof -
    have vX: "vtvars X \<subseteq> ?KN"
    proof (cases ffs)
      case Nil
      with f have "tps = []" by simp
      with tu show ?thesis by simp
    next
      case (Cons dp ffs')
      obtain rb t0 u0 where "dp = (rb, t0, u0)" by (cases dp)
      with si Cons have "pok A env rb X t0 u0" by (auto simp: sinv_def)
      then show ?thesis by (rule pokD(6))
    qed
    have vX': "vtvars ?X' \<subseteq> ?KN"
      using vX tk ff_vtvars_vars by (fastforce simp: dvars_def vtvars_def)
    have dt: "dtyped \<rho> [([], t, u)]" if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
      using dw(2)[OF that] tu by (auto simp: dtyped_def)
    show ?thesis
      unfolding pok_def
    proof (intro conjI allI impI)
      show "vars t \<union> vars u \<subseteq> ?X' \<union> evars env'" using tu by (force simp: dvars_def)
      show "ttvars t \<union> ttvars u \<union> btvars [] \<union> vtvars ?X' \<subseteq> tvars_env (tyenv env') \<union> A"
        using tk tu vX' th by (auto simp: btvars_def)
      show "\<not> loose_bvar t (ilength [])" "\<not> loose_bvar u (ilength [])"
        using dt[OF einv_rho0[OF ei']] by (simp_all add: dtyped_def)
      fix \<rho> assume "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
      from dt[OF this] show "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T"
        by (simp add: dtyped_def)
    qed
  qed
  then have "ffres A K ?X' env' tps" using ei' dw(1) by (auto simp: ffres_def)
  moreover have "finite ?X'" using fin(1) ur_finite_dvars by simp
  ultimately show ?thesis using x fin(2) by blast
qed

subsection \<open>Pattern unification of the input pairs\<close>

lemma ur_foldM_unify:
  assumes fin: "finite X" "finite K"
  shows "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> \<forall>(t, u)\<in>set tus. pok A env [] X t u \<Longrightarrow>
    \<exists>r. foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<and>
      (\<forall>e. r = Err e \<longrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X)"
proof (induction tus arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons tu tus)
  obtain t u where tu: "tu = (t, u)" by force
  have p: "pok A env [] X t u" using Cons.prems(3) tu by simp
  from unif_term[OF fin Cons.prems(1,2) p] obtain r1 where
    r1: "unif alg [] t u env = Some r1" "upost A K env X r1" by blast
  show ?case
  proof (cases r1)
    case (Err e)
    with r1 show ?thesis by (simp add: tu unify_def bindM_def)
  next
    case (Ok env1)
    note a = upost_OkD[OF r1(2)[unfolded Ok]]
    have "\<forall>(t, u)\<in>set tus. pok A env1 [] X t u"
      using Cons.prems(3) pok_mono[OF _ a(3,4)] by auto
    from Cons.IH[OF a(1,2) this] r1(1) Ok show ?thesis by (simp add: tu unify_def bindM_def)
  qed
qed


subsection \<open>Finiteness of the enumeration\<close>

theorem unifiers_fin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)" "fin cfg s (uresult env tus)"
proof -
  have ei: "einv A K env" and wi: "winv env X" and p: "\<forall>(t, u)\<in>set tus. pok A env [] X t u"
    using si by (auto simp: sinv_def)
  from ur_foldM_unify[OF fin ei wi p] obtain r where
    r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r"
      "\<forall>e. r = Err e \<longrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern"
      "\<forall>env'. r = Ok env' \<longrightarrow> einv A K env' \<and> winv env' X" by blast
  show thesis
  proof (cases r)
    case (Ok env')
    with r(1) have u: "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    have "dstep env (tdps tus) env' []" by (rule foldM_unify_dstep) (use r(1) Ok in simp)
    moreover have "ffres A K X env' []" using r(3) Ok by (simp add: ffres_def)
    ultimately have "uresult env tus (El_R env' [])" using fin unfolding uresult_def by fastforce
    then show thesis by (rule that[OF u fin_Single])
  next
    case (Err e)
    with r(2) consider "e = Pattern" | v where "e = Unif v" by blast
    then show thesis
    proof cases
      case 1
      with r(1) Err have u: "unifiers alg env tus = Some (Ok (hounifiers [] env tus))"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      from hounifiers_fin[OF cfg fin si] obtain xs where es: "evals cfg (hounifiers [] env tus) xs"
        and rs: "\<forall>x\<in>set xs. rres x"
        unfolding fin_def by blast
      have "uresult env tus x" if x: "x \<in> set xs" for x
      proof -
        from unifiers_sound[OF u es x] obtain env' tps where x': "x = El_R env' tps"
          and ds: "dstep env (tdps tus) env' (tdps tps)" by blast
        from rres_ffres[OF bspec[OF rs x]] x' ds show ?thesis unfolding uresult_def by auto
      qed
      with es have "fin cfg (hounifiers [] env tus) (uresult env tus)" unfolding fin_def by blast
      with u show thesis by (rule that)
    next
      case 2
      with r(1) Err have u: "unifiers alg env tus = Some (Ok S_Empty)"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      show thesis by (rule that[OF u fin_Empty])
    qed
  qed
qed

lemma ur_evals_det: "evals cfg s xs \<Longrightarrow> evals cfg s ys \<Longrightarrow> xs = ys"
proof (induction arbitrary: ys rule: evals.induct)
  case (Nil s evs)
  from Nil.prems show ?case
  proof cases
    case (Cons evs' y s'' ys')
    with Nil.hyps show ?thesis by simp
  qed simp
next
  case (Cons s evs x s' xs)
  from Cons.prems show ?case
  proof cases
    case (Nil evs')
    with Cons.hyps(1) show ?thesis by simp
  next
    case (Cons evs' y s'' ys')
    with Cons.hyps(1) have "y = x" "s'' = s'" by simp_all
    with Cons.IH[of ys'] Cons show ?thesis by simp
  qed
qed

text \<open>Hence every enumeration of the result consists of well-formed unifiers:\<close>

theorem unifiers_uresult:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "x \<in> set xs"
  shows "uresult env tus x"
proof -
  from unifiers_fin[OF cfg fin si] u obtain ys where "evals cfg s ys" "\<forall>y\<in>set ys. uresult env tus y"
    unfolding fin_def by auto
  with ur_evals_det[OF es] x show ?thesis by blast
qed

lemma uresultD:
  assumes "uresult env tus (El_R env' tps)"
  shows "dstep env (tdps tus) env' (tdps tps)" "extends env env'"
    and "\<exists>A K X. finite X \<and> finite K \<and> ffres A K X env' tps"
  using assms dstepD(1) unfolding uresult_def by blast+


subsection \<open>Typing of the input\<close>

lemma ur_vinv_sub: "vinv \<rho> env X \<Longrightarrow> Y \<subseteq> X \<union> evars env \<Longrightarrow> vinv \<rho> env Y"
proof -
  assume v: "vinv \<rho> env X" and Y: "Y \<subseteq> X \<union> evars env"
  then have sub: "Y \<union> evars env \<subseteq> X \<union> evars env" by blast
  from v have "vcons \<rho> (X \<union> evars env)" "below (maxidx env) (X \<union> evars env)" by (simp_all add: vinv_def)
  with sub show ?thesis unfolding vinv_def by (blast intro: vcons_mono below_mono)
qed

lemma ur_winv_sub: "winv env X \<Longrightarrow> Y \<subseteq> X \<union> evars env \<Longrightarrow> winv env Y"
  unfolding winv_def using ur_vinv_sub by blast

lemma sinv_dvars: "sinv A K X env dps \<Longrightarrow> dvars dps \<subseteq> X \<union> evars env"
  unfolding sinv_def dvars_def by (fastforce dest: pokD(1,2))

lemma sinv_dtyped: "sinv A K X env dps \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps"
  unfolding sinv_def dtyped_def by (fastforce dest: pokD(7-9))

text \<open>A well-formed problem is well-typed at the certified solutions of its type environment:\<close>

lemma sinv_gtyped:
  assumes si: "sinv A K X env dps"
  shows "gtyped env dps"
  unfolding gtyped_def
proof (intro allI impI conjI)
  fix \<rho> assume t: "tsol (tyenv env) \<rho>" and c: "cert_inst \<rho>"
  have wi: "winv env X" using si by (simp add: sinv_def)
  from winvD[OF wi t c] have "wt_env \<rho> env" "vinv \<rho> env X" by blast+
  then show "wt_env \<rho> env" "vinv \<rho> env (dvars dps)" using ur_vinv_sub sinv_dvars[OF si] by blast+
  show "dtyped \<rho> dps" by (rule sinv_dtyped[OF si t c])
qed


subsection \<open>Smashing the flex-flex pairs\<close>

lemma ffres_smash:
  assumes "ffres A K X env tps"
  shows "tacyc (tyenv env)" "tcons_env (tyenv env)" "cert_inst (tsol0 (tyenv env))" "gtyped env (tdps tps)"
proof -
  have ei: "einv A K env" using assms by (simp add: ffres_def)
  note e = einvD[OF ei]
  show "tacyc (tyenv env)" "tcons_env (tyenv env)" by (rule e(6), rule e(7))
  show "cert_inst (tsol0 (tyenv env))" by (rule tsol0(3)[OF e(2) e(12) e(9)])
  show "gtyped env (tdps tps)" by (rule sinv_gtyped) (use assms in \<open>simp add: ffres_sinv\<close>)
qed

text \<open>The hypotheses of @{thm [source] unifiers_smash_sound} hold on well-formed problems:\<close>

theorem unifiers_smash:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and sm: "okW (smash_flexflex (env', tps)) env''"
  shows "dstep env (tdps tus) env'' []"
proof -
  from uresultD(3)[OF unifiers_uresult[OF cfg fin si u es x]] obtain A' K' X' where
    ff: "ffres A' K' X' env' tps" by blast
  note h = ffres_smash[OF ff]
  show ?thesis by (rule unifiers_smash_sound[OF u es x sm sinv_gtyped[OF si] h(1-3)])
qed


subsection \<open>Further terms of the input\<close>

text \<open>
  Terms \<open>rs\<close> with types that are well-typed at the certified solutions of the type environment of
  the input stay well-typed, and their variables stay consistent with the environment and the
  flex-flex pairs of the unifiers.
\<close>

definition rtyped :: "env \<Rightarrow> (pterm \<times> ptyp) list \<Rightarrow> bool" where
  "rtyped env rs \<longleftrightarrow>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<forall>(r, T)\<in>set rs. \<forall>e. e \<turnstile> inst \<rho> r : tsubst \<rho> T))"

definition rvars :: "(pterm \<times> ptyp) list \<Rightarrow> (indexname \<times> ptyp) set" where
  "rvars rs = (\<Union>(r, T)\<in>set rs. vars r)"

lemma rtyped_extends: "rtyped env rs \<Longrightarrow> extends env env' \<Longrightarrow> rtyped env' rs"
  unfolding rtyped_def using extends_tsol by blast

theorem unifiers_winv:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and wy: "winv env (Y \<union> dvars (tdps tus))"
  shows "winv env' (Y \<union> dvars (tdps tps))"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume t': "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF unifiers_uresult[OF cfg fin si u es x]])
  have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
  from winvD[OF wy t c] have w: "wt_env \<rho> env" "vinv \<rho> env (Y \<union> dvars (tdps tus))" by blast+
  from dstepD(2)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t c] w(2)]
  show "wt_env \<rho> env' \<and> vinv \<rho> env' (Y \<union> dvars (tdps tps))" by blast
qed

theorem unifiers_rs:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and rt: "rtyped env rs" and rv: "rvars rs \<subseteq> X \<union> evars env"
  shows "rtyped env' rs" "winv env' (rvars rs \<union> dvars (tdps tps))"
proof -
  show "rtyped env' rs"
    by (rule rtyped_extends[OF rt uresultD(2)[OF unifiers_uresult[OF cfg fin si u es x]]])
  have "winv env (rvars rs \<union> dvars (tdps tus))"
    by (rule ur_winv_sub[of _ X]) (use si sinv_dvars[OF si] rv in \<open>auto simp: sinv_def\<close>)
  from unifiers_winv[OF cfg fin si u es x this] show "winv env' (rvars rs \<union> dvars (tdps tps))" .
qed


subsection \<open>Fresh variables and the maximal index\<close>

lemma ur_fun_type_neq: "T \<rightarrow>\<^sub>T T \<noteq> T"
proof
  assume "T \<rightarrow>\<^sub>T T = T"
  then have "size (T \<rightarrow>\<^sub>T T) = size T" by simp
  then show False by simp
qed

lemma ur_vinv_fresh:
  assumes "vinv \<rho> env D" "v \<notin> fst ` (D \<union> evars env)" "snd v \<le> maxidx env"
  shows "vinv \<rho> env ({(v, T)} \<union> D)"
proof -
  have vc: "vcons \<rho> (D \<union> evars env)" and bl: "below (maxidx env) (D \<union> evars env)"
    using assms(1) by (simp_all add: vinv_def)
  have "vcons \<rho> ({(v, T)} \<union> D \<union> evars env)"
    unfolding vcons_def
  proof (intro allI impI)
    fix x T1 T2 assume 1: "(x, T1) \<in> {(v, T)} \<union> D \<union> evars env" and 2: "(x, T2) \<in> {(v, T)} \<union> D \<union> evars env"
    show "tsubst \<rho> T1 = tsubst \<rho> T2"
    proof (cases "x = v")
      case True
      then have "(x, T1) \<notin> D \<union> evars env" "(x, T2) \<notin> D \<union> evars env" using assms(2) by force+
      with 1 2 show ?thesis by simp
    next
      case False
      with 1 2 have "(x, T1) \<in> D \<union> evars env" "(x, T2) \<in> D \<union> evars env" by auto
      from vconsD[OF vc this] show ?thesis .
    qed
  qed
  moreover have "below (maxidx env) ({(v, T)} \<union> D \<union> evars env)"
    using bl assms(3) by (simp add: below_def)
  ultimately show ?thesis by (simp add: vinv_def)
qed

text \<open>
  A variable that occurs neither in the problem nor in the environment, with an index that is
  not above the maximal index, is not bound by the unifiers and does not occur in their
  bindings and flex-flex pairs: it can be given any type in the problem, so its type would be
  inconsistent with a binding or an occurrence (\<^const>\<open>vinv\<close>).
\<close>

theorem unifiers_fresh:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "v \<notin> fst ` (evars env' \<union> dvars (tdps tps))"
proof
  assume vin: "v \<in> fst ` (evars env' \<union> dvars (tdps tps))"
  note r = unifiers_uresult[OF cfg fin si u es x]
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF r])
  from uresultD(3)[OF r] obtain A' K' X' where "ffres A' K' X' env' tps" by blast
  then have ei': "einv A' K' env'" by (simp add: ffres_def)
  let ?\<rho> = "tnorm_inst (tyenv env')"
  note r0 = einv_rho0[OF ei']
  have t: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF r0(1) dstepD(1)[OF ds]])
  from sinv_gtyped[OF si] t r0(2) have w: "wt_env ?\<rho> env" "dtyped ?\<rho> (tdps tus)" "vinv ?\<rho> env (dvars (tdps tus))"
    unfolding gtyped_def by blast+
  have vT: "vinv ?\<rho> env' ({(v, T)} \<union> dvars (tdps tps))" for T
  proof -
    have "vinv ?\<rho> env ({(v, T)} \<union> dvars (tdps tus))" by (rule ur_vinv_fresh[OF w(3)]) (use v in auto)
    from dstepD(2)[OF ds r0(1) extends_refl w(1,2) this] show ?thesis by blast
  qed
  from vin obtain U where U: "(v, U) \<in> evars env' \<union> dvars (tdps tps)" by force
  have "vcons ?\<rho> ({(v, U \<rightarrow>\<^sub>T U)} \<union> dvars (tdps tps) \<union> evars env')"
    using vT[of "U \<rightarrow>\<^sub>T U"] by (simp add: vinv_def)
  from vconsD[OF this, of v "U \<rightarrow>\<^sub>T U" U] U have "tsubst ?\<rho> (U \<rightarrow>\<^sub>T U) = tsubst ?\<rho> U" by blast
  with ur_fun_type_neq[of "tsubst ?\<rho> U"] show False by simp
qed

corollary unifiers_fresh_unbound:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "vt_lookup (tenv env') v = None" "\<forall>(t, u)\<in>set tps. v \<notin> fst ` (vars t \<union> vars u)"
proof -
  note f = unifiers_fresh[OF cfg fin si u es x v]
  show "vt_lookup (tenv env') v = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env') v \<noteq> None"
    then obtain U b where "vt_lookup (tenv env') v = Some (U, b)" by force
    from evarsI[OF this] f show False by force
  qed
  show "\<forall>(t, u)\<in>set tps. v \<notin> fst ` (vars t \<union> vars u)"
    using f by (force simp: dvars_def)
qed

text \<open>The maximal index of the unifiers is at least that of the problem (by soundness alone):\<close>

theorem unifiers_maxidx:
  assumes u: "unifiers alg' env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
  shows "maxidx env \<le> maxidx env'"
  using unifiers_sound[OF u es x] dstepD(1) extends_maxidx by blast

end

end
