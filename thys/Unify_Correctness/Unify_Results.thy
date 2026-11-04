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
  from Nil.prems Nil.hyps show ?case by (cases rule: evals.cases) auto
next
  case (Cons s evs x s' xs)
  from Cons.prems Cons.hyps Cons.IH show ?case by (cases rule: evals.cases) auto
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

end

end
