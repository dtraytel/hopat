section \<open>Unifiers that Bind Names with Several Types\<close>

theory Unify_Typed_Results
  imports Unify_Results "Pattern_Correctness.Pattern_Typed_Unifier"
begin

text \<open>
  The results of theory \<open>Unify_Results\<close> describe the unifiers whose environment binds no name
  that occurs with several types (\<^const>\<open>pure_sig_gen.lfin\<close>). This theory removes the restriction:
  every element of the enumeration of \<^const>\<open>unifiers\<close> on a well-formed problem satisfies the
  invariant of the results (\<open>unifiers_cfin_uresult\<close>), and a solution of its environment that also
  satisfies the bindings read at other types (\<open>gsolution\<close>) solves the problem if it solves the
  remaining flex-flex pairs (\<open>deqv_ebinds_dsolved\<close>). Such solutions exist: the typed solution
  \<^const>\<open>pure_sig_gen.gsol\<close> of an acyclic environment, composed with a substitution, is one
  (\<open>gfix_gsol\<close>, \<open>gfix_gsolution\<close> in theory \<open>Unify_Smash_Typed\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>The invariant of the results\<close>

lemma rres_ffres_g:
  assumes "rres A0 env0 x"
  shows "\<exists>env' tps. x = El_R env' tps \<and>
    (\<exists>A K X e0. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env0 A env' \<and> ffres A K X env' tps \<and>
      fflex A K e0 env' tps)"
proof -
  from assms obtain env' tps A K X env ffs where x: "x = El_R env' tps" and fin: "finite X" "finite K"
    and A0: "A0 \<subseteq> A" and tn: "tnew A0 env0 A env"
    and si: "sinv A K X env ffs" and f: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps)"
    and fv: "finv A K env env'"
    and tk: "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    and fl: "\<forall>(t, u)\<in>set tps. flexb env t \<and> flexb env u"
    unfolding rres_def by blast
  have wi: "winv env X" using si by (simp add: sinv_def)
  have ei': "einv A K env'" and th: "tyenv env' = tyenv env" using fv by (simp_all add: finv_def)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have pk: "\<forall>(rb, t, u)\<in>set (ffs @ tdps []). upok A env rb X t u" using si by (simp add: sinv_def)
  have ds: "dstep env (ffs @ tdps []) env' (tdps tps)" by (rule foldrW_add_ffpair_sound[OF f])
  note dw = dstep_winvc[OF ds wi pk th]
  let ?X' = "X \<union> dvars (tdps tps)"
  have "upok A env' [] ?X' t u" if tu: "(t, u) \<in> set tps" for t u
  proof -
    have vX: "vtvars X \<subseteq> ?KN"
    proof (cases ffs)
      case Nil
      with f have "tps = []" by simp
      with tu show ?thesis by simp
    next
      case (Cons dp ffs')
      obtain rb t0 u0 where "dp = (rb, t0, u0)" by (cases dp)
      with si Cons have "upok A env rb X t0 u0" by (auto simp: sinv_def)
      then show ?thesis by (rule upokD(6))
    qed
    have vX': "vtvars ?X' \<subseteq> ?KN"
      using vX tk vtvars_vars by (fastforce simp: dvars_def vtvars_def)
    have dt: "dtyped \<rho> [([], t, u)]" if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
      using dw(2)[OF that] tu by (auto simp: dtyped_def)
    show ?thesis
      unfolding upok_def
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
  moreover have "finite ?X'" using fin(1) finite_dvars by simp
  moreover have "fflex A K env env' tps" using fv fl by (simp add: fflex_def)
  moreover have "tnew A0 env0 A env'" using tn th by (simp add: tnew_def)
  ultimately have "finite ?X' \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env0 A env' \<and> ffres A K ?X' env' tps \<and>
      fflex A K env env' tps"
    using fin(2) A0 by blast
  note h = this
  show ?thesis unfolding x by (rule exI[of _ env'], rule exI[of _ tps], rule conjI[OF refl], rule exI[of _ A],
      rule exI[of _ K], rule exI[of _ ?X'], rule exI[of _ env]) (rule h)
qed

text \<open>Every element of the enumeration of \<open>unifiers\<close> is a well-formed unifier, whatever names its
  environment binds:\<close>

theorem unifiers_cfin_uresult:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)"
  shows "cfin cfg s (uresult A env tus)"
proof -
  have ei: "einv A K env" and wi: "winv env X" and p: "\<forall>(t, u)\<in>set tus. upok A env [] X t u"
    using si by (auto simp: sinv_def)
  let ?m = "foldM (\<lambda>(t, u) env. unify alg t u env) tus env"
  from foldM_unify_c[OF fin ei wi p] obtain r where r: "?m = Some r" "upostc A K env X r" by blast
  show ?thesis
  proof (cases r)
    case (Ok env')
    with r u have s: "s = S_Single (El_R env' [])"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    have okm: "ok ?m env'" using r Ok by simp
    have ds: "dstep env (tdps tus) env' []" by (rule foldM_unify_dstep[OF okm])
    note i = upostc_OkD[OF r(2)[unfolded Ok]]
    have "ffres A K X env' []" using i by (simp add: ffres_def)
    moreover have "fflex A K env' env' []" using i by (simp add: fflex_def finv_def iflex_refl)
    ultimately have "uresult A env tus (El_R env' [])"
      using uresultI[OF _ fin order_refl, of env tus env' "[]"] ds i(7) by simp
    then show ?thesis unfolding s by (rule cfin_Single)
  next
    case (Err e)
    show ?thesis
    proof (cases "e = Pattern")
      case True
      with r u Err have s: "s = hounifiers [] env tus"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      show ?thesis unfolding s
      proof (rule cfin_mono[OF hounifiers_cfin[OF cfg fin si]])
        fix x assume x: "rres A env x \<and> elem_ok (GR env (map (\<lambda>(t, u). ([], t, u)) tus)) x"
        from rres_ffres_g[OF conjunct1[OF x]] obtain env' tps where x': "x = El_R env' tps"
          and h: "\<exists>A' K' X' e0. finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> tnew A env A' env' \<and> ffres A' K' X' env' tps \<and>
            fflex A' K' e0 env' tps" by blast
        from x x' have "dstep env (tdps tus) env' (tdps tps)" by simp
        with h show "uresult A env tus x" unfolding x' uresult_El_R by blast
      qed
    next
      case False
      with r u Err have "s = S_Empty"
        by (cases e) (simp_all add: unifiers_def handle_def bindM_def return_def raise_def)
      then show ?thesis by simp
    qed
  qed
qed

subsection \<open>Typed solutions\<close>

text \<open>
  A solution of an environment that also satisfies the bindings read at other types, where
  these are well-typed (\<^const>\<open>ghosts\<close>). The unifiers identify the variables of a problem by
  their names, so a problem follows from the bindings and these equations (\<^const>\<open>dstep\<close>);
  such a solution therefore solves the problem if it solves the remaining pairs.
\<close>

definition gsolution :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> bool" where
  "gsolution \<rho> \<sigma> env \<longleftrightarrow> solution \<rho> \<sigma> env \<and>
    (\<forall>(l, r)\<in>ghosts \<rho> env. \<forall>e T. e \<turnstile> l : T \<longrightarrow> e \<turnstile> r : T \<longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r)"

lemma gsolutionD:
  assumes "gsolution \<rho> \<sigma> env"
  shows "solution \<rho> \<sigma> env"
    and "(l, r) \<in> ghosts \<rho> env \<Longrightarrow> e \<turnstile> l : T \<Longrightarrow> e \<turnstile> r : T \<Longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r"
  using assms unfolding gsolution_def by blast+

lemma gsolution_ebinds:
  assumes "gsolution \<rho> \<sigma> env" "(l, r) \<in> ebinds \<rho> env" "e \<turnstile> l : T" "e \<turnstile> r : T"
  shows "vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r"
  using assms(2) unfolding ebinds_def
proof
  assume "(l, r) \<in> binds \<rho> env"
  then show ?thesis by (rule solution_binds[OF gsolutionD(1)[OF assms(1)]])
next
  assume "(l, r) \<in> ghosts \<rho> env"
  then show ?thesis using assms(3,4) by (rule gsolutionD(2)[OF assms(1)])
qed

lemma solution_gsolution: "solution \<rho> \<sigma> env \<Longrightarrow> nfree env \<Longrightarrow> gsolution \<rho> \<sigma> env"
  by (simp add: gsolution_def ghosts_nfree)

lemma wt_subst_comp:
  assumes "wt_subst \<sigma>" "wt_subst \<tau>"
  shows "wt_subst (\<lambda>x T. vsubst \<sigma> (\<tau> x T))"
proof -
  have "closed (vsubst \<sigma> (\<tau> x T))" for x T
    using assms closed_substD[of \<tau> x T] by (simp add: wt_subst_def closed_def)
  moreover have "e \<turnstile> vsubst \<sigma> (\<tau> x T) : T" if "cert_typ alg ar T" for e x T
    using typing_vsubst[OF wt_subst_typing[OF assms(2) that] assms(1)] .
  ultimately show ?thesis by (auto simp: wt_subst_def closed_subst_def)
qed

text \<open>Pairs that follow from the bindings, their readings at other types and further pairs are
  solved by a typed solution that solves the further pairs:\<close>

lemma deqv_ebinds_dsolved:
  assumes de: "deqv (ebinds \<rho> env \<union> dp_eqs \<rho> dps') \<rho> dps" and gs: "gsolution \<rho> \<sigma> env"
    and dt: "dtyped \<rho> dps" and dt': "dtyped \<rho> dps'" and sd: "dsolved \<rho> \<sigma> dps'"
  shows "dsolved \<rho> \<sigma> dps"
proof -
  note sol = gsolutionD(1)[OF gs]
  have E: "vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r"
    if "(l, r) \<in> {(l, r) \<in> ebinds \<rho> env \<union> dp_eqs \<rho> dps'. \<exists>e T. e \<turnstile> l : T \<and> e \<turnstile> r : T}" for l r
  proof -
    from that obtain e T where lr: "(l, r) \<in> ebinds \<rho> env \<union> dp_eqs \<rho> dps'" "e \<turnstile> l : T" "e \<turnstile> r : T"
      by blast
    from lr(1) show ?thesis
    proof
      assume "(l, r) \<in> ebinds \<rho> env"
      from gsolution_ebinds[OF gs this lr(2,3)] show ?thesis .
    next
      assume "(l, r) \<in> dp_eqs \<rho> dps'"
      then obtain rb' t u where p: "(rb', t, u) \<in> set dps'" and l: "l = inst \<rho> (abs_list (rev rb') t)"
        and r: "r = inst \<rho> (abs_list (rev rb') u)"
        by (auto simp: dp_eqs_def)
      from sd p have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (auto simp: dsolved_def)
      from dsolved_closed[OF dtyped_mem[OF dt' p] solutionD(3)[OF sol] this] show ?thesis unfolding l r .
    qed
  qed
  have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if p: "(rb', t, u) \<in> set dps" for rb' t u
  proof -
    from dt p obtain e T where "bs_env \<rho> e rb'" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
      by (fastforce simp: dtyped_def)
    with de p have "eqv (ebinds \<rho> env \<union> dp_eqs \<rho> dps') e (inst \<rho> t) (inst \<rho> u)" by (auto simp: deqv_def)
    from eqv_vsubst[OF eqv_typed_pairs[OF this] solutionD(3)[OF sol] E] show ?thesis by (simp add: ap_def)
  qed
  then show ?thesis by (auto simp: dsolved_def)
qed

end

end
