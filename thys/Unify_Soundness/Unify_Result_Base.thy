section \<open>The Invariant of the Unifiers\<close>

text \<open>
  The invariant \<open>uresult\<close> of the unifiers that \<open>unifiers\<close> enumerates, the typing of a
  well-formed problem, and solutions that also satisfy the readings of loose names at other
  types. Theory \<open>Unify_Invariant\<close> proves the invariant for every element of the enumeration.
\<close>

theory Unify_Result_Base
  imports Unify_Search_Base Unify_Smash_Sound
begin

subsection \<open>The invariant of the results\<close>

context pure_sig_gen
begin

text \<open>
  The invariant of the results, for the type variables \<open>A0\<close> of the problem: the known type
  variables \<open>A\<close> of a result include \<open>A0\<close>, and the result introduces only type variables that are
  known in the problem or have indices above its maximal index (\<^const>\<open>tnew\<close>). This invariant
  (\<open>uresult\<close>) holds for every element of the enumeration, by induction on the computations
  (theory \<open>Unify_Invariant\<close>). The termination of smashing needs in addition that the
  flex-flex pairs are flexible (\<open>uresult_flex\<close> in theory \<open>Unify_Results\<close>), which is proved together with
  termination.
\<close>

definition uresult :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> elem \<Rightarrow> bool" where
  "uresult A0 env tus x \<longleftrightarrow> (\<exists>env' tps. x = El_R env' tps \<and> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps))"

lemma uresult_El_R:
  "uresult A0 env tus (El_R env' tps) \<longleftrightarrow> dstep env (tdps tus) env' (tdps tps) \<and>
    (\<exists>A K X. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps)"
  unfolding uresult_def by blast

lemma uresultI:
  assumes "dstep env (tdps tus) env' (tdps tps)" "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 env A env'"
    "ffres A K X env' tps"
  shows "uresult A0 env tus (El_R env' tps)"
  unfolding uresult_El_R
  by (rule conjI[OF assms(1)], rule exI[of _ A], rule exI[of _ K], rule exI[of _ X])
    (simp add: assms(2-6))

lemma uresultD:
  assumes "uresult A0 env tus (El_R env' tps)"
  shows "dstep env (tdps tus) env' (tdps tps)" "extends env env'"
    and "\<exists>A K X. finite X \<and> finite K \<and> A0 \<subseteq> A \<and> tnew A0 env A env' \<and> ffres A K X env' tps"
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

lemma sinv_dtyped: "sinv A K X env dps \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> dtyped \<rho> dps"
  unfolding sinv_def dtyped_def by (fastforce dest: upokD(7-9))

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

lemma ur_vupdate_nonVar: "\<not> (\<exists>y Y. s = Var y Y) \<Longrightarrow> vupdate aU s env = update aU s env"
  by (subst vupdate.simps) (auto split: pterm.splits)

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
    fix x T1 T2 assume nl: "x \<notin> loose"
      and 1: "(x, T1) \<in> {(v, T)} \<union> D \<union> evars env" and 2: "(x, T2) \<in> {(v, T)} \<union> D \<union> evars env"
    show "tsubst \<rho> T1 = tsubst \<rho> T2"
    proof (cases "x = v")
      case True
      then have "(x, T1) \<notin> D \<union> evars env" "(x, T2) \<notin> D \<union> evars env" using assms(2) by force+
      with 1 2 show ?thesis by simp
    next
      case False
      with 1 2 have "(x, T1) \<in> D \<union> evars env" "(x, T2) \<in> D \<union> evars env" by auto
      from vconsD[OF vc nl this] show ?thesis .
    qed
  qed
  moreover have "below (maxidx env) ({(v, T)} \<union> D \<union> evars env)"
    using bl assms(3) by (simp add: below_def)
  ultimately show ?thesis by (simp add: vinv_def)
qed

end

subsection \<open>Typed solutions\<close>

context pure_sig_gen
begin

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

text \<open>
  So an element of the enumeration of \<^const>\<open>unifiers\<close> is sound for typed solutions: a typed
  solution of its environment that solves its flex-flex pairs solves the problem.
\<close>

theorem uresult_solves:
  assumes ur: "uresult A env tus (El_R env' tps)" and si: "sinv A0 K X env (tdps tus)"
    and gs: "gsolution \<rho> \<sigma> env'" and ci: "cert_inst \<rho>"
    and ts: "\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  note sol = gsolutionD(1)[OF gs]
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF ur])
  have t': "tsol (tyenv env') \<rho>" by (rule solutionD(2)[OF sol])
  have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' uresultD(2)[OF ur]])
  from winvD[OF _ t ci] si have w: "wt_env \<rho> env" "vinv \<rho> env X" by (auto simp: sinv_def)
  have v: "vinv \<rho> env ({} \<union> dvars (tdps tus))"
    using ur_vinv_sub[OF w(2)] sinv_dvars[OF si] by simp
  note dt = sinv_dtyped[OF si t ci]
  have dt': "dtyped \<rho> (tdps tps)" using dstepDg(1)[OF ds t' extends_refl w(1) dt v] by blast
  have "dsolved \<rho> \<sigma> (tdps tps)" using ts by (simp only: dsolved_tdps)
  from deqv_ebinds_dsolved[OF dstepDg(2)[OF ds t' extends_refl w(1) dt v] gs dt dt' this]
  show ?thesis by (simp only: dsolved_tdps)
qed

end

end
