section \<open>Finiteness of \<open>MATCH\<close>\<close>

theory Unify_Match_Fin
  imports Unify_Simpl_Term
begin

text \<open>
  \<^const>\<open>MATCH\<close> on a flex-rigid pair of \<^const>\<open>SIMPL\<close> terminates, raising at most
  \<open>CANTUNIFY\<close>, with a finite enumeration of new problems in the invariant of the termination of
  \<^const>\<open>SIMPL\<close> (theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>). The type unification of
  the two sides, the arity guesses and the \<open>\<eta>\<close>-expansion keep the invariant, with new type
  variables for the guesses.

  (Theory \<open>Unify_Shape_Sound\<close> cannot be imported together with
  \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>: both \<open>Unify_Match_Sound\<close>
  and \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close> define constants \<open>sinv\<close> and \<open>sstep\<close> in locale
  \<^locale>\<open>pure_sig\<close>, whose context then cannot be entered.)
\<close>

context pure_sig
begin

subsection \<open>The elements of the enumeration\<close>

text \<open>New problems in the invariant, for finite sets of variables and of type variables:\<close>

definition mres :: "elem \<Rightarrow> bool" where
  "mres x \<longleftrightarrow> (\<exists>env dps A K X. x = El_E env dps \<and> finite X \<and> finite K \<and> sinv A K X env dps)"

lemma cuok_handle_CANTUNIFY_ret:
  assumes "cuok m P" "\<And>x. P x \<Longrightarrow> Q x" "Q r"
  shows "cuok (handleW m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
  using assms unfolding cuok_def
  by (auto simp: handleW_def returnW_def split: option.splits ures.splits)

lemma cuok_liftM_return: "m = return x \<Longrightarrow> cuok (f x) Q \<Longrightarrow> cuok (bindW (liftM m) f) Q"
  by (rule cuok_bindW[of _ "\<lambda>y. y = x"]) (simp_all add: cuok_def return_def)


subsection \<open>Type unification keeps the invariant\<close>

lemma pok_Amono: "pok A env rb X t u \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> pok A' env rb X t u"
  unfolding pok_def by blast

lemma sinv_tyext:
  assumes "sinv A K X env dps" "einv A K env'" "tenv env' = tenv env" "textends (tyenv env) (tyenv env')"
    "maxidx env \<le> maxidx env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "sinv A K X env' dps"
proof -
  have ext: "extends env env'" using assms(3-5) by (simp add: extends_def)
  have "winv env' X" by (rule winv_tyext) (use assms in \<open>simp_all add: sinv_def\<close>)
  then show ?thesis using assms(1,2) pok_mono[OF _ ext assms(6)] unfolding sinv_def by blast
qed

lemma sinv_Amono: "sinv A K X env dps \<Longrightarrow> einv A' K' env \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> sinv A' K' X env dps"
  unfolding sinv_def using pok_Amono by blast

text \<open>The types of the two sides of a pair are computed, modulo the type environment equal:\<close>

lemma fastype_pair_term:
  assumes ei: "einv A K env" and p: "pok A env rb X t u"
  shows "\<exists>T1 U1. fastype env rb t = return T1 \<and> fastype env rb u = return U1 \<and>
    tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A \<and> tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    tnorm (tyenv env) T1 = tnorm (tyenv env) U1 \<and> cert_typ alg ar (tnorm (tyenv env) T1)"
proof -
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
  from pd(9)[OF r0] obtain e W where bs: "bs_env (rho0 env) e rb" and tt: "e \<turnstile> inst (rho0 env) t : W"
    and tu: "e \<turnstile> inst (rho0 env) u : W" by blast
  from env_fastype_term[OF e(2) refl tt bs pd(7)] pd(3,5) obtain T1 where
    T1: "env_fastype env (map snd rb) t = return T1" "tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) T1 = W" by blast
  from env_fastype_term[OF e(2) refl tu bs pd(8)] pd(4,5) obtain U1 where
    U1: "env_fastype env (map snd rb) u = return U1" "tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A"
      "tnorm (tyenv env) U1 = W" by blast
  have "cert_typ alg ar W" by (rule bs_env_cert[OF bs tt pd(7)])
  with T1 U1 show ?thesis by (auto simp: fastype_def)
qed

lemma cunify_types_sinv:
  assumes fin: "finite K" and si: "sinv A K X env dps"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tnorm (tyenv env) T)"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar (tnorm (tyenv env) U)"
  shows "cuok (cunify_types alg T U env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'))"
proof -
  have ei: "einv A K env" using si by (simp add: sinv_def)
  have cT: "cert_typ alg ar (tsubst (rho0 env) T)" and cU: "cert_typ alg ar (tsubst (rho0 env) U)"
    using T(2) U(2) by simp_all
  show ?thesis
    using cunify_types_term[OF ei fin T(1) cert_typ_rev[OF ei cT T(1)] U(1) cert_typ_rev[OF ei cU U(1)]]
  proof (rule cuok_mono)
    fix env' assume "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
      maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"
    then show "sinv A K X env' dps \<and> tenv env' = tenv env \<and> extends env env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
      using sinv_tyext[OF si] by (auto simp: extends_def)
  qed
qed


subsection \<open>New type variables\<close>

definition ntv :: "ptyp list \<Rightarrow> (indexname \<times> psort) set" where
  "ntv Cs = (\<Union>C\<in>set Cs. tvars C)"

lemma finite_ntv [simp]: "finite (ntv Cs)"
  by (auto simp: ntv_def)

lemma gentvars_simps:
  assumes "gentvars p env = (env1, Cs)"
  shows "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1" "length Cs = p"
    "p \<noteq> 0 \<Longrightarrow> maxidx env1 = maxidx env + 1"
    "C \<in> set Cs \<Longrightarrow> \<exists>a. C = TVar (a, maxidx env1) []"
  using assms by (auto simp: gentvars_def split: env.splits if_splits)

lemma ntv_gentvars:
  assumes "gentvars p env = (env1, Cs)" "x \<in> ntv Cs"
  shows "snd (fst x) = maxidx env + 1" "snd x = []"
proof -
  from assms(2) obtain C where C: "C \<in> set Cs" "x \<in> tvars C" by (auto simp: ntv_def)
  then have "p \<noteq> 0" using gentvars_simps(4)[OF assms(1)] by auto
  with gentvars_simps(5)[OF assms(1) this] gentvars_simps(6)[OF assms(1) C(1)] C(2)
  show "snd (fst x) = maxidx env + 1" "snd x = []" by auto
qed

lemma einv_gentvars:
  assumes ei: "einv A K env" and g: "gentvars p env = (env1, Cs)"
  shows "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env1"
proof -
  note e = einvD[OF ei] and gs = gentvars_simps[OF g] and nt = ntv_gentvars[OF g]
  let ?\<theta> = "tyenv env" and ?N = "ntv Cs"
  have ti: "tinv ar (maxidx env) ?\<theta> A" by (rule e(2))
  have old: "snd (fst q) \<le> maxidx env" if "q \<in> tvars_env ?\<theta> \<union> A" for q
    using ti that unfolding tinv_def by blast
  have ti': "tinv ar (maxidx env1) ?\<theta> (A \<union> ?N)"
    unfolding tinv_def
  proof (intro conjI)
    show "tacyc ?\<theta>" by (rule e(6))
    show "scons (tvars_env ?\<theta> \<union> (A \<union> ?N))"
      unfolding scons_def
    proof (intro allI impI)
      fix v S S' assume a: "(v, S) \<in> tvars_env ?\<theta> \<union> (A \<union> ?N)" "(v, S') \<in> tvars_env ?\<theta> \<union> (A \<union> ?N)"
      show "S = S'"
      proof (cases "(v, S) \<in> ?N \<or> (v, S') \<in> ?N")
        case True
        then have v: "snd v = maxidx env + 1" using nt(1) by fastforce
        have "(v, S) \<in> ?N" using a(1) old[of "(v, S)"] v by auto
        moreover have "(v, S') \<in> ?N" using a(2) old[of "(v, S')"] v by auto
        ultimately show ?thesis using nt(2) by fastforce
      next
        case False
        with a have "(v, S) \<in> tvars_env ?\<theta> \<union> A" "(v, S') \<in> tvars_env ?\<theta> \<union> A" by auto
        then show ?thesis using ti unfolding tinv_def scons_def by blast
      qed
    qed
    show "\<forall>q\<in>tvars_env ?\<theta> \<union> (A \<union> ?N). snd (fst q) \<le> maxidx env1"
    proof
      fix q assume "q \<in> tvars_env ?\<theta> \<union> (A \<union> ?N)"
      then show "snd (fst q) \<le> maxidx env1"
        using old[of q] nt(1)[of q] gs(3) gs(5) by (cases "p = 0") (auto simp: gs(4)[symmetric] ntv_def)
    qed
    show "\<forall>v S U. vt_lookup ?\<theta> v = Some (S, U) \<longrightarrow> wft ar U" using ti unfolding tinv_def by blast
  qed
  have tv: "tvinv (A \<union> ?N) env1"
    using ti' tvinvD(2)[OF e(1)] unfolding tvinv_def gs(1,2) by blast
  have "tcert alg ?N" unfolding tcert_def using nt(2) by (auto simp: sort_ok_def)
  then have tc: "tcert alg (tvars_env ?\<theta> \<union> (A \<union> ?N))" using e(10) by simp
  have uK: "uvarsA ?\<theta> K \<subseteq> uvarsA ?\<theta> (K \<union> ?N)" by (auto simp: uvarsA_def)
  have "tcovered ?\<theta> (K \<union> ?N) (tvars_env ?\<theta> \<union> A)"
    unfolding tcovered_def using tcoveredD[OF e(11)] uK by blast
  moreover have "tcovered ?\<theta> (K \<union> ?N) ?N" unfolding tcovered_def uvarsA_def by blast
  ultimately have cov: "tcovered ?\<theta> (K \<union> ?N) (tvars_env ?\<theta> \<union> (A \<union> ?N))" by simp
  have "bbelow env1" by (rule bbelow_mono[OF e(5) gs(1,3)])
  moreover have "acyc env1" "closed_env env1" using e(3,4) gs(1)
    by (simp_all add: acyc_def dep_def closed_env_def)
  ultimately show ?thesis using tv tc cov e(9,12) by (simp add: einv_def gs(1,2))
qed

lemma sinv_gentvars:
  assumes si: "sinv A K X env dps" and g: "gentvars p env = (env1, Cs)"
  shows "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env1 dps"
proof -
  note gs = gentvars_simps[OF g]
  have ei: "einv (A \<union> ntv Cs) (K \<union> ntv Cs) env1" by (rule einv_gentvars[OF _ g]) (use si in \<open>simp add: sinv_def\<close>)
  have ext: "extends env env1" using gs by (simp add: extends_def)
  have "winv env1 X" by (rule winv_tyext) (use si gs in \<open>simp_all add: sinv_def\<close>)
  then show ?thesis using si ei pok_mono[OF pok_Amono ext] gs(2) unfolding sinv_def by blast
qed

end

end
