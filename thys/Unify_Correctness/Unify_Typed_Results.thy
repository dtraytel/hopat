section \<open>Typed Solutions of Unifiers\<close>

theory Unify_Typed_Results
  imports Unify_Results "Pattern_Correctness.Pattern_Typed_Unifier"
begin

text \<open>
  Every element of the enumeration of \<^const>\<open>unifiers\<close> on a well-formed problem satisfies the
  invariant of the results, whatever names its environment binds (\<open>unifiers_cfin_uresult\<close> in
  theory \<open>Unify_Results\<close>). A solution of its environment that also satisfies the bindings read
  at other types (\<open>gsolution\<close>) solves the problem if it solves the remaining flex-flex pairs
  (\<open>deqv_ebinds_dsolved\<close>). Such solutions exist: the typed solution
  \<^const>\<open>pure_sig_gen.gsol\<close> of an acyclic environment, composed with a substitution, is one
  (\<open>gfix_gsol\<close>, \<open>gfix_gsolution\<close> in theory \<open>Unify_Smash_Typed\<close>).
\<close>

context pure_sig_gen
begin

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
