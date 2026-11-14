section \<open>Finiteness of \<open>MATCH\<close>\<close>

theory Unify_Match_Fin
  imports Unify_Simpl_Term Unify_Match_Sound
begin

text \<open>
  \<^const>\<open>MATCH\<close> on a flex-rigid pair of \<^const>\<open>SIMPL\<close> terminates, raising at most
  \<open>CANTUNIFY\<close>, with a finite enumeration of new problems in the invariant of the termination of
  \<^const>\<open>SIMPL\<close> (theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>). The arity guesses and the
  \<open>\<eta>\<close>-expansion keep the invariant, with new type variables for the guesses.
\<close>

context pure_sig_gen
begin

subsection \<open>The elements of the enumeration\<close>

text \<open>New problems in the invariant, for finite sets of variables and of type variables, which
  include the type variables \<open>A0\<close> of the original problem \<open>env0\<close>, with only type variables that
  are known in the original problem or new (\<^const>\<open>tnew\<close>):\<close>

definition mres :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> elem \<Rightarrow> bool" where
  "mres A0 env0 x \<longleftrightarrow> (\<exists>env dps A K X. x = El_E env dps \<and> finite X \<and> finite K \<and> A0 \<subseteq> A \<and>
    tnew A0 env0 A env \<and> sinv A K X env dps)"

lemma mres_mono:
  assumes "mres A1 env1 x" "A0 \<subseteq> A1" "tnew A0 env0 A1 env1" "maxidx env0 \<le> maxidx env1"
  shows "mres A0 env0 x"
proof -
  from assms(1) obtain env dps A K X where x: "x = El_E env dps" "finite X" "finite K" "A1 \<subseteq> A"
    "tnew A1 env1 A env" "sinv A K X env dps"
    unfolding mres_def by blast
  have "tnew A0 env0 A env" by (rule tnew_trans[OF assms(3) x(5) assms(4)])
  with x assms(2) show ?thesis unfolding mres_def by blast
qed

lemma fin_mres_mono:
  "fin cfg s (mres A1 env1) \<Longrightarrow> A0 \<subseteq> A1 \<Longrightarrow> tnew A0 env0 A1 env1 \<Longrightarrow> maxidx env0 \<le> maxidx env1 \<Longrightarrow>
    fin cfg s (mres A0 env0)"
  by (erule fin_mono) (rule mres_mono)

lemma cuok_handle_CANTUNIFY_ret:
  assumes "cuok m P" "\<And>x. P x \<Longrightarrow> Q x" "Q r"
  shows "cuok (handleW m (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW r | _ \<Rightarrow> raiseW e)) Q"
  using assms unfolding xokW_def
  by (auto simp: handleW_def returnW_def split: option.splits xres.splits)

lemma cuok_liftM_return: "m = return x \<Longrightarrow> cuok (f x) Q \<Longrightarrow> cuok (bindW (liftM m) f) Q"
  by (rule xokW_bindW[of _ _ "\<lambda>y. y = x"]) (simp_all add: xokW_def return_def)


subsection \<open>Type unification keeps the invariant\<close>

lemma upok_Amono: "upok A env rb X t u \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> upok A' env rb X t u"
  unfolding upok_def by blast

lemma sinv_tyext:
  assumes "sinv A K X env dps" "einv A K env'" "tenv env' = tenv env" "textends (tyenv env) (tyenv env')"
    "maxidx env \<le> maxidx env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
  shows "sinv A K X env' dps"
proof -
  have ext: "extends env env'" using assms(3-5) by (simp add: extends_def)
  have "winv env' X" by (rule winv_tyext) (use assms in \<open>simp_all add: sinv_def\<close>)
  then show ?thesis using assms(1,2) upok_mono[OF _ ext assms(6)] unfolding sinv_def by blast
qed

text \<open>The types of the two sides of a pair are computed, modulo the type environment equal:\<close>

lemma fastype_pair_term:
  assumes ei: "einv A K env" and p: "upok A env rb X t u"
  shows "\<exists>T1 U1. fastype env rb t = return T1 \<and> fastype env rb u = return U1 \<and>
    tvars T1 \<subseteq> tvars_env (tyenv env) \<union> A \<and> tvars U1 \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    tnorm (tyenv env) T1 = tnorm (tyenv env) U1 \<and> cert_typ alg ar (tnorm (tyenv env) T1)"
proof -
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
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
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U))"
proof -
  have ei: "einv A K env" using si by (simp add: sinv_def)
  have cT: "cert_typ alg ar (tsubst (rho0 env) T)" and cU: "cert_typ alg ar (tsubst (rho0 env) U)"
    using T(2) U(2) by simp_all
  show ?thesis
    using cunify_types_term[OF ei fin T(1) cert_typ_rev[OF ei cT T(1)] U(1) cert_typ_rev[OF ei cU U(1)]]
  proof (rule xokW_mono)
    fix env' assume "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
      maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env' = tyenv env \<or> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"
    then show "sinv A K X env' dps \<and> tenv env' = tenv env \<and> extends env env' \<and>
        tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
        (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
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
        ultimately show ?thesis using nt(2)[of "(v, S)"] nt(2)[of "(v, S')"] by simp
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
      proof (cases "q \<in> ?N")
        case True
        then have "p \<noteq> 0" using gs(4) by (auto simp: ntv_def)
        with nt(1)[OF True] gs(5) show ?thesis by simp
      qed (use old[of q] gs(3) in auto)
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
  moreover have "upok (A \<union> ntv Cs) env1 rb X t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from si that have "upok A env rb X t u" by (auto simp: sinv_def)
    then show ?thesis by (rule upok_mono[OF upok_Amono[OF _ Un_upper1] ext]) (simp add: gs(2))
  qed
  ultimately show ?thesis using ei unfolding sinv_def by blast
qed

text \<open>The new type variables have indices above the maximal index:\<close>

lemma tnew_gentvars:
  assumes g: "gentvars p env = (env1, Cs)"
  shows "tnew A env (A \<union> ntv Cs) env1"
proof -
  have "maxidx env < snd (fst q)" if "q \<in> ntv Cs" for q using ntv_gentvars(1)[OF g that] by simp
  then show ?thesis using gentvars_simps(2)[OF g] by (auto simp: tnew_def)
qed


subsection \<open>The \<open>\<eta>\<close>-expansion of a pair\<close>

lemma mf_binder_types_sound:
  assumes bt: "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> \<exists>W. (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W) \<and>
    (\<forall>A B. tnorm (tyenv env) W \<noteq> A \<rightarrow>\<^sub>T B) \<and> (\<forall>U\<in>set Ts. tvars U \<subseteq> tvars T \<union> tvars_env (tyenv env)) \<and>
    tvars W \<subseteq> tvars T \<union> tvars_env (tyenv env)"
  using bt
proof (induction env T r arbitrary: Ts rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      from h T obtain Ts' where r: "ok (bt env U) Ts'" and Ts: "Ts = T1 # Ts'" by auto
      from "1.IH"[OF r refl "1.prems"(2)] obtain W where W: "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> U = map (tsubst \<rho>) Ts' \<Rrightarrow> tsubst \<rho> W"
        "\<forall>A B. tnorm (tyenv env) W \<noteq> A \<rightarrow>\<^sub>T B" "\<forall>U'\<in>set Ts'. tvars U' \<subseteq> tvars U \<union> tvars_env (tyenv env)"
        "tvars W \<subseteq> tvars U \<union> tvars_env (tyenv env)"
        by blast
      show ?thesis by (rule exI[of _ W]) (use W Ts T in auto)
    next
      case False
      with h Type have Ts: "Ts = []" by (auto split: list.splits if_splits)
      have "tnorm (tyenv env) T \<noteq> A \<rightarrow>\<^sub>T B" for A B using False Type by auto
      then show ?thesis by (intro exI[of _ T]) (simp add: Ts)
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest lr have Ts: "Ts = []" and vn: "vt_lookup (tyenv env) v = None"
        by (auto simp: ok_type_lookup split: option.splits)
      have "tnorm (tyenv env) T \<noteq> A \<rightarrow>\<^sub>T B" for A B using TVar vn by (simp add: tnorm_TVar[OF "1.prems"(2)])
      then show ?thesis by (intro exI[of _ T]) (simp add: Ts)
    next
      case (Some T')
      with rest have r: "ok (bt env T') Ts" by simp
      from lr Some have vb: "vt_lookup (tyenv env) v = Some (S, T')" by (auto simp: ok_type_lookup split: option.splits)
      from "1.IH"[OF r refl "1.prems"(2)] obtain W where W: "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T' = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W"
        "\<forall>A B. tnorm (tyenv env) W \<noteq> A \<rightarrow>\<^sub>T B" "\<forall>U'\<in>set Ts. tvars U' \<subseteq> tvars T' \<union> tvars_env (tyenv env)"
        "tvars W \<subseteq> tvars T' \<union> tvars_env (tyenv env)"
        by blast
      have "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" if "tsol (tyenv env) \<rho>" for \<rho>
        using W(1) that tsolD[OF that vb] TVar by simp
      moreover have "tvars T' \<subseteq> tvars_env (tyenv env)" by (rule tvars_envI2[OF vb])
      ultimately show ?thesis using W(2,3,4) by blast
    qed
  next
    case (TFree a S)
    with h have "Ts = []" by simp
    then show ?thesis using TFree by (intro exI[of _ T]) simp
  qed
qed

lemma mf_ttvars_incr_bv [simp]: "ttvars (incr_bv n k t) = ttvars t"
  by (simp add: ttvars_def)

lemma mf_ilength_rb: "ilength (rev (map f Es) @ rb) = ilength rb + ilength Es"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat add.commute)

text \<open>The \<open>\<eta>\<close>-expansion of a pair by the missing argument types of its flexible side keeps the
  invariant; the flexible side then has all its arguments.\<close>

lemma sinv_eta_expand:
  assumes si: "sinv A K X env ((rb, t, u) # dps)" and st: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts"
  shows "length targs \<le> length Ts" "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
proof -
  have ei: "einv A K env" and p: "upok A env rb X t u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  let ?\<theta> = "tyenv env"
  from mf_binder_types_sound[OF bt[unfolded return_def] refl e(6)] obtain W where
    W: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W"
      "\<And>A B. tnorm ?\<theta> W \<noteq> A \<rightarrow>\<^sub>T B" "\<And>U. U \<in> set Ts \<Longrightarrow> tvars U \<subseteq> tvars T \<union> tvars_env ?\<theta>"
    by blast
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have tyt_gen: "\<exists>Us. e \<tturnstile> map (inst \<rho>) targs : Us \<and> Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W"
    if "e \<turnstile> inst \<rho> t : U" "tsol ?\<theta> \<rho>" for e \<rho> U
  proof -
    from that(1)[unfolded t inst_apps] obtain Us where tyv: "e \<turnstile> inst \<rho> (Var v T) : Us \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) targs : Us"
      by (rule list_app_typeE)
    from tyv W(1)[OF that(2)] have "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" by auto
    with tyas show ?thesis by blast
  qed
  show len: "length targs \<le> length Ts"
  proof (rule ccontr)
    assume n: "\<not> length targs \<le> length Ts"
    from pd(9)[OF r0] obtain e U where "e \<turnstile> inst (rho0 env) t : U" by blast
    from tyt_gen[OF this r0(1)] obtain Us where Us: "e \<tturnstile> map (inst (rho0 env)) targs : Us"
      "Us \<Rrightarrow> U = map (tsubst (rho0 env)) Ts \<Rrightarrow> tsubst (rho0 env) W" by blast
    have lUs: "length Us = length targs" using typings_nth[OF Us(1)] by simp
    have "tsubst (rho0 env) W = drop (length (map (tsubst (rho0 env)) Ts)) Us \<Rrightarrow> U"
      by (rule funs_prefix[OF Us(2)[symmetric]]) (use n lUs in simp)
    then have "tnorm ?\<theta> W = drop (length Ts) Us \<Rrightarrow> U" by simp
    moreover obtain D Ds where "drop (length Ts) Us = D # Ds" using n lUs by (cases "drop (length Ts) Us") auto
    ultimately show False using W(2) by simp
  qed
  define Es where "Es = drop (length targs) Ts"
  define j where "j = length Es"
  let ?rb = "rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  let ?x = "\<lambda>x. incr_bv (ilength Es) 0 x \<degree>\<degree> bvs j"
  have lbx: "\<not> loose_bvar (?x x) (ilength ?rb)" if "\<not> loose_bvar x (ilength rb)" for x
    unfolding mf_ilength_rb
  proof -
    have "\<not> loose_bvar (incr_bv (ilength Es) 0 x) (ilength rb + ilength Es)"
      using loose_bvar_incr_bv[of "ilength Es" 0 "ilength rb" x] that by simp
    moreover have "\<not> loose_bvar b (ilength rb + ilength Es)" if "b \<in> set (bvs j)" for b
    proof -
      from that obtain x where x: "x < length Es" "b = Bound (integer_of_nat x)" by (auto simp: j_def)
      have "integer_of_nat x < ilength Es" using x by (simp add: ilength_eq integer_less_iff integer_of_nat.rep_eq)
      then have "integer_of_nat x < ilength rb + ilength Es"
        using ilength_nonneg[of rb] by (simp add: integer_less_iff integer_less_eq_iff plus_integer.rep_eq)
      then show ?thesis using x by simp
    qed
    ultimately show "\<not> loose_bvar (?x x) (ilength rb + ilength Es)" by (auto simp: loose_bvar_apps)
  qed
  have tyx: "\<exists>e' W'. bs_env \<rho> e' ?rb \<and> e' \<turnstile> inst \<rho> (?x t) : W' \<and> e' \<turnstile> inst \<rho> (?x u) : W'"
    if \<rho>: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    from pd(9)[OF \<rho>] obtain e U where bs: "bs_env \<rho> e rb" and tyt: "e \<turnstile> inst \<rho> t : U" and tyu: "e \<turnstile> inst \<rho> u : U"
      by blast
    from tyt_gen[OF tyt \<rho>(1)] obtain Us where Us: "e \<tturnstile> map (inst \<rho>) targs : Us"
      "Us \<Rrightarrow> U = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" by auto
    have lUs: "length Us = length targs" using typings_nth[OF Us(1)] by simp
    from funs_prefix[OF Us(2)] len lUs have U: "U = map (tsubst \<rho>) Es \<Rrightarrow> tsubst \<rho> W"
      by (simp add: Es_def drop_map)
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu pd(8)])
    then have cEs: "\<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T)" by (simp add: U cert_typ_funs)
    define e' where "e' = pushes e (map (tsubst \<rho>) Es)"
    have bs': "bs_env \<rho> e' ?rb" unfolding e'_def by (rule bs_env_pushes[OF bs cEs])
    have ty: "e' \<turnstile> inst \<rho> (?x x) : tsubst \<rho> W" if "e \<turnstile> inst \<rho> x : U" for x
      using list_app_typeI[OF typing_incr_pushes[OF that[unfolded U], of "map (tsubst \<rho>) Es", unfolded ilength_map]
          typings_bvs[of e "map (tsubst \<rho>) Es", unfolded length_map]]
      by (simp add: e'_def j_def inst_apps comp_def)
    show ?thesis using bs' ty[OF tyt] ty[OF tyu] by blast
  qed
  have tvT: "tvars T \<subseteq> ttvars t" using t by (simp add: ttvars_apps)
  have tvEs: "btvars ?rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof -
    have "tvars U \<subseteq> tvars_env ?\<theta> \<union> A" if "U \<in> set Es" for U
      using W(3)[of U] that tvT pd(3) by (auto simp: Es_def dest: in_set_dropD)
    then show ?thesis using pd(5) by (auto simp: btvars_def)
  qed
  have "upok A env ?rb X (?x t) (?x u)"
    unfolding upok_def
    using pd(1-4,6) lbx[OF pd(7)] lbx[OF pd(8)] tyx tvEs
    by (simp add: vars_apps ttvars_apps)
  then show "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
    using si unfolding eta_expand_dpair_eq Es_def[symmetric] j_def[symmetric] by (simp add: sinv_def)
qed


lemma cert_tnorm: "einv A K env \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> cert_typ alg ar (tnorm (tyenv env) T)"
  using cert_typ_tsubst[OF _ einv_rho0(2)] by simp

lemma is_Abs_incr_bv [simp]: "is_Abs (incr_bv n k t) \<longleftrightarrow> is_Abs t"
  by (cases t) auto

lemma rigid_incr_bv: "rigid h \<Longrightarrow> rigid (incr_bv n k h)"
  by (cases h) simp_all

lemma fr_shape_eta_expand:
  assumes "fr_shape env (rb, t, u)"
  shows "fr_shape env (eta_expand_dpair Es (rb, t, u))"
proof -
  from assms have f: "\<not> is_Abs t" "\<not> is_Abs u" "is_Var (head_of t)" "rigid (head_of u)" "hunb env (rb, t, u)"
    by (auto simp: fr_shape_def frs0_def)
  have ht: "incr_bv n 0 (head_of t) = head_of t" for n using f(3) by (cases "head_of t") auto
  have hu: "rigid (incr_bv n 0 (head_of u))" for n by (rule rigid_incr_bv[OF f(4)])
  show ?thesis using f hu unfolding eta_expand_dpair_eq fr_shape_def frs0_def hunb_def
    by (auto simp: is_Abs_apps head_of_apps head_of_incr_bv ht rigid_def split: pterm.splits)
qed

lemma fr_shape_strip_comb:
  assumes "fr_shape env (rb, t, u)"
  obtains v T targs where "strip_comb t = (Var v T, targs)"
proof -
  from assms have "is_Var (head_of t)" by (simp add: fr_shape_def frs0_def)
  then obtain v T where "head_of t = Var v T" by (cases "head_of t") auto
  then have "fst (strip_comb t) = Var v T" by (simp add: head_of_strip_comb)
  then show ?thesis using that by (cases "strip_comb t") auto
qed

lemma head_tvars_strip_comb:
  "strip_comb t = (Var v T, targs) \<Longrightarrow> tvars T \<subseteq> ttvars t"
  using ttvars_head[of t] by (simp add: head_of_strip_comb)

lemma fr_shape_tenv:
  assumes "tenv env' = tenv env" shows "fr_shape env' dp \<longleftrightarrow> fr_shape env dp"
  unfolding fr_shape_def using hunb_tenv[OF assms, of dp] by simp



subsection \<open>New variables\<close>

text \<open>The new arguments of a projection or an imitation:\<close>

lemma lookup_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> lookup env x T = return None"
  by (simp add: lookup_def)

lemma make_args_props_idx:
  assumes "make_args name Ts env Us = (env', args)"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
proof (cases "Us = []")
  case True
  with assms have "env' = env" "args = []" by (simp_all add: make_args_def)
  with True show ?thesis by (intro that[of "[]"]) simp_all
next
  case False
  obtain env1 vs where g: "genvars name env (map (\<lambda>T. Ts \<Rrightarrow> T) Us) = (env1, vs)" by fastforce
  with assms False have e: "env' = env1" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (auto simp: make_args_def List.null_iff)
  note g' = genvars_props[OF g]
  show ?thesis
  proof (rule that[of vs])
    show "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) vs" by (simp add: e combound_bvs)
    show "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) vs Us"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth)
    show "tenv env' = tenv env" "tyenv env' = tyenv env" using g' e by simp_all
    show "maxidx env \<le> maxidx env'" using g' e by (simp add: integer_arith)
    show "vinv \<rho> env' (lvars vs \<union> X)" if "vinv \<rho> env X" for \<rho> X
      using vinv_genvars[OF g that] e by simp
    show "\<forall>G\<in>set vs. \<exists>a U. G = Var (a, maxidx env + 1) U"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  qed
qed

subsection \<open>The occurs check terminates\<close>

lemma occurs_list_term:
  assumes ac: "acyc env" "tacyc (tyenv env)" "tcons_env (tyenv env)"
  shows "\<forall>t\<in>set ts. vok env (vars t \<union> evars env) \<Longrightarrow> \<exists>r. occurs_list env v seen ts = return r"
proof (induction ts arbitrary: seen)
  case (Cons t ts)
  from occur_term[OF ac order_refl, of t v seen] Cons.prems obtain b s where
    o: "occur t env v seen = return (b, s)" by auto
  from Cons.IH[of s] Cons.prems obtain r where "occurs_list env v s ts = return r" by auto
  with o show ?case by (cases b) auto
qed (auto simp: return_def)

subsection \<open>Single steps of matching\<close>

lemma einv_maxidx:
  assumes ei: "einv A K env" and e: "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
  shows "einv A K env'"
proof -
  note x = einvD[OF ei]
  have "bbelow env'" by (rule bbelow_mono[OF x(5) e(1,3)])
  moreover have "closed_env env'" "acyc env'" using x(3,4) e(1) by (simp_all add: closed_env_def acyc_def dep_def)
  moreover have "tvinv A env'" using x(1) tinv_mono[OF _ e(3)] e(1,2) unfolding tvinv_def by auto
  ultimately show ?thesis using ei by (simp add: einv_def e(2))
qed

lemma upok_Xmono:
  "upok A env rb X t u \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> vtvars X' \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> upok A env rb X' t u"
  unfolding upok_def by blast

lemma vtvars_mlvars_Var:
  "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U \<and> tvars U \<subseteq> S \<Longrightarrow> vtvars (lvars Gs) \<subseteq> S"
  by (fastforce simp: vtvars_def)

text \<open>The new variables of \<^const>\<open>make_args\<close> keep the invariant:\<close>

lemma sinv_make_args:
  assumes si: "sinv A K X env dps" and ma: "make_args name Ts env Us = (env', args)"
    and tv: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    "sinv A K (lvars Gs \<union> X) env' dps"
    "vtvars (lvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  obtain Gs where Gs: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (lvars Gs \<union> X)"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    by (rule make_args_props_idx[OF ma]) blast
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb, t, u)\<in>set dps. upok A env rb X t u"
    using si by (auto simp: sinv_def)
  have vG: "vtvars (lvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
  proof (rule vtvars_mlvars_Var, intro ballI)
    fix G assume "G \<in> set Gs"
    then obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs(2) i(1)] i obtain x where "G = Var x (Ts \<Rrightarrow> (Us ! i))" by blast
    moreover have "Us ! i \<in> set Us" using i(1) list_all2_lengthD[OF Gs(2)] by simp
    ultimately show "\<exists>x U. G = Var x U \<and> tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
      using tv by (fastforce simp: tvars_funs)
  qed
  have ei': "einv A K env'" by (rule einv_maxidx[OF ei Gs(3-5)])
  have wi': "winv env' (lvars Gs \<union> X)"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    then have "wt_env \<rho> env \<and> vinv \<rho> env X" using winvD[OF wi] Gs(4) by simp
    then show "wt_env \<rho> env' \<and> vinv \<rho> env' (lvars Gs \<union> X)" using Gs(6) wt_env_tenv[OF Gs(3)] by blast
  qed
  have ext: "extends env env'" using Gs(3-5) by (simp add: extends_def)
  have "upok A env' rb (lvars Gs \<union> X) t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from ps that have p: "upok A env rb X t u" by auto
    have "upok A env rb (lvars Gs \<union> X) t u"
      by (rule upok_Xmono[OF p]) (use vG upokD(6)[OF p] in auto)
    then show ?thesis by (rule upok_mono[OF _ ext]) (simp add: Gs(4))
  qed
  then have "sinv A K (lvars Gs \<union> X) env' dps" using ei' wi' by (auto simp: sinv_def)
  with Gs(1-5,7) vG show ?thesis using that by blast
qed

lemma tnorm_funs_mf: "tnorm \<theta> (Ts \<Rrightarrow> T) = map (tnorm \<theta>) Ts \<Rrightarrow> tnorm \<theta> T"
  by (induction Ts) simp_all

text \<open>The type unification of a projection keeps the invariant:\<close>

lemma proj_unify_sinv:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite K" and si: "sinv A K X env dps"
    and tv: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
      "\<forall>C\<in>set Cs. tvars C \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tnorm (tyenv env) base)" "cert_typ alg ar (tnorm (tyenv env) bary)"
      "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env) C)"
  shows "cuok (proj_unify cfg base bary Cs env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
proof (cases "Cs = []")
  case True
  note cu = cunify_types_sinv[OF fin si tv(1) c(1) tv(2) c(2)]
  have cu': "cuok (cunify_types alg base bary env) (\<lambda>env'. sinv A K X env' dps \<and> tenv env' = tenv env \<and>
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)))"
    by (rule xokW_mono[OF cu]) (simp add: True)
  show ?thesis
  proof (cases "cfg_trace_types cfg")
    case tt: True
    show ?thesis unfolding proj_unify_def using True tt cfg
      by (simp add: test_unify_types_def) (rule xokW_bindW[OF cu'], simp add: xokW_def okW_whenW)
  qed (use True cu' cfg in \<open>simp add: proj_unify_def\<close>)
next
  case False
  have tvC: "tvars (Cs \<Rrightarrow> base) \<subseteq> tvars_env (tyenv env) \<union> A" using tv(1,3) by (auto simp: tvars_funs)
  have cC: "cert_typ alg ar (tnorm (tyenv env) (Cs \<Rrightarrow> base))"
    using c(1,3) by (simp add: tnorm_funs_mf cert_typ_funs)
  note cu = cunify_types_sinv[OF fin si tv(2) c(2) tvC cC]
  show ?thesis unfolding proj_unify_def using False cfg cu by (simp add: List.null_iff)
qed

text \<open>The rigid side of a saturated flex-rigid pair has the body type of its head:\<close>

lemma funs_nonarrow_eq:
  "Vs \<Rrightarrow> A = Zs \<Rrightarrow> B \<Longrightarrow> (\<forall>C D. A \<noteq> C \<rightarrow>\<^sub>T D) \<Longrightarrow> (\<forall>C D. B \<noteq> C \<rightarrow>\<^sub>T D) \<Longrightarrow> Vs = Zs \<and> A = B"
proof (induction Vs arbitrary: Zs)
  case Nil
  then show ?case by (cases Zs) auto
next
  case (Cons V Vs)
  then show ?case by (cases Zs) auto
qed

lemma mf_body_type_sound:
  assumes bt: "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> (\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D) \<and>
    (\<exists>Zs. \<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B)"
  using bt
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      with h have "ok (bt env U) B" by simp
      from "1.IH"[OF this refl "1.prems"(2)] obtain Zs where
        "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D" "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> U = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B"
        by blast
      then show ?thesis using T by (intro conjI exI[of _ "T1 # Zs"]) auto
    next
      case False
      with h Type have "B = T" by (auto split: list.splits if_splits)
      with Type False show ?thesis by (intro conjI exI[of _ "[]"]) auto
    qed
  next
    case (TVar v' S')
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v' S') lr"
      and rest: "ok (case lr of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B" by auto
    show ?thesis
    proof (cases lr)
      case None
      with lr have vn: "vt_lookup (tyenv env) v' = None" by (auto simp: ok_type_lookup split: option.splits)
      from None rest TVar have B: "B = TVar v' S'" by simp
      show ?thesis unfolding B using vn TVar by (intro conjI exI[of _ "[]"]) (simp_all add: tnorm_TVar[OF "1.prems"(2)])
    next
      case (Some T')
      with rest have r: "ok (bt env T') B" by simp
      from lr Some have vb: "vt_lookup (tyenv env) v' = Some (S', T')" by (auto simp: ok_type_lookup split: option.splits)
      from "1.IH"[OF r refl "1.prems"(2)] obtain Zs where
        "\<forall>C D. tnorm (tyenv env) B \<noteq> C \<rightarrow>\<^sub>T D" "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> T' = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> B"
        by blast
      then show ?thesis using TVar tsolD[OF _ vb] by (intro conjI exI[of _ Zs]) auto
    qed
  next
    case (TFree a S)
    with h show ?thesis by (intro conjI exI[of _ "[]"]) auto
  qed
qed

lemma pair_base:
  assumes ei: "einv A K env" and p: "upok A env rb X t u" and st: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A"
    and \<rho>: "tsol (tyenv env) \<rho>" and tyt: "e \<turnstile> inst \<rho> t : U"
  shows "U = tsubst \<rho> base" "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
    "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
proof -
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  let ?\<theta> = "tyenv env"
  from mf_binder_types_sound[OF bt[unfolded return_def] refl x(6)] obtain W where
    W: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> W" "\<forall>A B. tnorm ?\<theta> W \<noteq> A \<rightarrow>\<^sub>T B"
      "tvars W \<subseteq> tvars T \<union> tvars_env ?\<theta>"
    by blast
  from mf_body_type_sound[of env T0 "Ok base" base] base x(6) obtain Zs where
    nb: "\<forall>A B. tnorm ?\<theta> base \<noteq> A \<rightarrow>\<^sub>T B" and Zs: "\<And>\<rho>. tsol ?\<theta> \<rho> \<Longrightarrow> tsubst \<rho> T0 = map (tsubst \<rho>) Zs \<Rrightarrow> tsubst \<rho> base"
    by (auto simp: return_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  define uh where "uh = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have u: "u = uh \<degree>\<degree> uargs" by (simp add: uh_def uargs_def strip_comb_apps)
  have tys: "Us = map (tsubst \<rho>') Ts \<and> U' = tsubst \<rho>' W"
    if "e' \<turnstile> inst \<rho>' t : U'" "tsol ?\<theta> \<rho>'" "e' \<tturnstile> map (inst \<rho>') targs : Us" for e' \<rho>' U' Us
  proof -
    from that(1)[unfolded t inst_apps] obtain Us' where tyv: "e' \<turnstile> inst \<rho>' (Var v T) : Us' \<Rrightarrow> U'"
      and tyas: "e' \<tturnstile> map (inst \<rho>') targs : Us'" by (rule list_app_typeE)
    have "Us' = Us" by (rule typings_unique[OF tyas that(3)])
    moreover have "length Us' = length Ts" using typings_nth[OF tyas] len by simp
    moreover from tyv W(1)[OF that(2)] have "Us' \<Rrightarrow> U' = map (tsubst \<rho>') Ts \<Rrightarrow> tsubst \<rho>' W" by auto
    ultimately show ?thesis using funs_eq[of Us' "map (tsubst \<rho>') Ts"] by simp
  qed
  have Wb: "tnorm ?\<theta> W = tnorm ?\<theta> base"
  proof -
    from pd(9)[OF r0] obtain e0 U0 where bs0: "bs_env (rho0 env) e0 rb" and t0: "e0 \<turnstile> inst (rho0 env) t : U0"
      and u0: "e0 \<turnstile> inst (rho0 env) u : U0" by blast
    from t0[unfolded t inst_apps] obtain Us0 where "e0 \<tturnstile> map (inst (rho0 env)) targs : Us0"
      by (rule list_app_typeE)
    from tys[OF t0 r0(1) this] have U0: "U0 = tnorm ?\<theta> W" by simp
    from u0[unfolded u inst_apps] obtain Vs where tyh: "e0 \<turnstile> inst (rho0 env) uh : Vs \<Rrightarrow> U0" by (rule list_app_typeE)
    have "tsubst (rho0 env) T0 = Vs \<Rrightarrow> U0" by (rule fastype_sound[OF T0[folded uh_def] r0(1) bs0 tyh])
    with Zs[OF r0(1)] have "Vs \<Rrightarrow> tnorm ?\<theta> W = map (tsubst (rho0 env)) Zs \<Rrightarrow> tnorm ?\<theta> base" by (simp add: U0)
    from funs_nonarrow_eq[OF this W(2) nb] show ?thesis by simp
  qed
  have tcW: "tcons ?\<theta> W" and tcb: "tcons ?\<theta> base"
    using tinv_tcons[OF x(2)] W(3) head_tvars_strip_comb[OF st] pd(3) tvb by blast+
  have Wb\<rho>: "tsubst \<rho> W = tsubst \<rho> base"
    using tsubst_tnorm[OF x(6,7) \<rho> tcW] tsubst_tnorm[OF x(6,7) \<rho> tcb] Wb by simp
  from tyt[unfolded t inst_apps] obtain Us where tya: "e \<tturnstile> map (inst \<rho>) targs : Us" by (rule list_app_typeE)
  from tys[OF tyt \<rho> tya] Wb\<rho> W(1)[OF \<rho>] tya
  show "U = tsubst \<rho> base" "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
    "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts" by simp_all
qed

subsection \<open>The copies of a single step\<close>

lemma ttvars_types_abs: "ttvars (types_abs Ts u) = (\<Union>T\<in>set Ts. tvars T) \<union> ttvars u"
  by (induction Ts) auto

lemma make_projs_term: "length Ts = length targs \<Longrightarrow> \<exists>ps. okW (make_projs u targs0 Ts targs) ps"
proof (induction Ts arbitrary: targs)
  case (Cons T Ts)
  then obtain targ targs' where "targs = targ # targs'" by (cases targs) auto
  with Cons show ?case by fastforce
qed auto

lemma cuok_okW: "okW m x \<Longrightarrow> P x \<Longrightarrow> cuok m P"
  by (auto simp: xokW_def)

lemma mapM_fastype_term:
  assumes ei: "einv A K env"
    and ty: "\<forall>s\<in>set ss. \<exists>e U. bs_env (rho0 env) e rb \<and> e \<turnstile> inst (rho0 env) s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>Ss. mapM (fastype env rb) ss = return Ss \<and> (\<forall>S\<in>set Ss. tvars S \<subseteq> tvars_env (tyenv env) \<union> A)"
  using ty
proof (induction ss)
  case (Cons s ss)
  from Cons.prems obtain e U where "bs_env (rho0 env) e rb" "e \<turnstile> inst (rho0 env) s : U"
    "\<not> loose_bvar s (ilength rb)" "ttvars s \<union> btvars rb \<subseteq> tvars_env (tyenv env) \<union> A" by auto
  from env_fastype_term[OF einvD(2)[OF ei] refl this(2,1,3,4)] obtain S where
    "env_fastype env (map snd rb) s = return S" "tvars S \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  moreover from Cons obtain Ss where "mapM (fastype env rb) ss = return Ss"
    "\<forall>S\<in>set Ss. tvars S \<subseteq> tvars_env (tyenv env) \<union> A" by auto
  ultimately show ?case by (auto simp: fastype_def[abs_def])
qed simp

lemma mapM_fastype_types:
  assumes "ok (mapM (fastype env rb) ts) Ts'" "tsol (tyenv env) \<rho>" "bs_env \<rho> e rb" "e \<tturnstile> map (inst \<rho>) ts : Us"
  shows "map (tsubst \<rho>) Ts' = Us"
proof -
  from assms(1) have l: "list_all2 (\<lambda>t T. ok (fastype env rb t) T) ts Ts'" by (simp add: ok_mapM)
  from l assms(4) show ?thesis
  proof (induction ts Ts' arbitrary: Us rule: list_all2_induct)
    case (Cons t ts T Ts')
    from Cons.prems obtain U Us' where Us: "Us = U # Us'" and tt: "e \<turnstile> inst \<rho> t : U"
      and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
      by (auto split: list.splits)
    from fastype_sound[OF Cons.hyps(1) assms(2,3) tt] Cons.IH[OF tts] Us show ?case by simp
  qed simp
qed

lemma rtrancl_dep_unbound: "vt_lookup (tenv env) y = None \<Longrightarrow> (x, y) \<in> (dep env)\<^sup>* \<Longrightarrow> x = y"
  by (erule rtranclE) (auto simp: dep_def)

lemma evars_tenv: "tenv env' = tenv env \<Longrightarrow> evars env' = evars env"
  by (simp add: evars_def bnds_def)

text \<open>The new variables applied to the bound variables of the arguments:\<close>

lemma new_args_props:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and len: "length Ts' = length Ts"
    and args: "args = map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs"
  shows "\<forall>a\<in>set args. \<not> loose_bvar a (ilength Ts)" "(\<Union>a\<in>set args. vars a) = lvars Gs"
    "(\<Union>a\<in>set args. ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
  unfolding args
proof -
  have var: "\<exists>x U. G = Var x U" if "G \<in> set Gs" for G
  proof -
    from that obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs i(1)] i(2) show ?thesis by blast
  qed
  have lb: "\<not> loose_bvar b (ilength Ts)" if "b \<in> set (bvs (length Ts'))" for b
    using that len by (auto simp: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq)
  show "\<forall>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). \<not> loose_bvar a (ilength Ts)"
    using var lb by (fastforce simp: loose_bvar_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). vars a) = lvars Gs"
    by (auto simp: vars_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> bvs (length Ts')) Gs). ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
    by (auto simp: ttvars_apps)
qed

lemma ttvars_mlvars_Gs:
  assumes "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U"
  shows "(\<Union>G\<in>set Gs. ttvars G) = vtvars (lvars Gs)"
proof -
  have e: "ttvars G = vtvars (vars G)" if "G \<in> set Gs" for G using assms that by (fastforce simp: vtvars_def)
  have "vtvars (lvars Gs) = (\<Union>G\<in>set Gs. vtvars (vars G))" by (auto simp: vtvars_def)
  then show ?thesis using e by auto
qed

text \<open>The new variables are unbound and do not reach \<open>v\<close>:\<close>

lemma head_var_props:
  assumes p: "upok A env rb X t u" and st: "strip_comb t = (Var v T, targs)" and fr: "fr_shape env (rb, t, u)"
  shows "(v, T) \<in> X \<union> evars env" "vt_lookup (tenv env) v = None" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<forall>s\<in>set targs. vars s \<subseteq> X \<union> evars env \<and> ttvars s \<subseteq> tvars_env (tyenv env) \<union> A \<and> \<not> loose_bvar s (ilength rb)"
proof -
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  note pd = upokD[OF p]
  show "(v, T) \<in> X \<union> evars env" using pd(1) t by (auto simp: vars_apps)
  have "head_of t = Var v T" using st by (simp add: head_of_strip_comb)
  then show "vt_lookup (tenv env) v = None" using fr by (cases v) (auto simp: fr_shape_def hunb_def)
  show "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using head_tvars_strip_comb[OF st] pd(3) by blast
  show "\<forall>s\<in>set targs. vars s \<subseteq> X \<union> evars env \<and> ttvars s \<subseteq> tvars_env (tyenv env) \<union> A \<and> \<not> loose_bvar s (ilength rb)"
    using pd(1,3,7) t by (auto simp: vars_apps ttvars_apps loose_bvar_apps)
qed

lemma below_head:
  assumes "sinv A K X env dps" "(v, T) \<in> X \<union> evars env"
  shows "snd v \<le> maxidx env"
proof -
  have "einv A K env" "winv env X" using assms(1) by (simp_all add: sinv_def)
  from winvD[OF this(2) einv_rho0[OF this(1)]] assms(2) show ?thesis by (auto simp: vinv_def dest: belowD)
qed

end

end
