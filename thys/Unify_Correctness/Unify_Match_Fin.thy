section \<open>Finiteness of \<open>MATCH\<close>\<close>

theory Unify_Match_Fin
  imports Unify_Simpl_Term
begin

text \<open>
  \<^const>\<open>MATCH\<close> on a flex-rigid pair of \<^const>\<open>SIMPL\<close> terminates, raising at most
  \<open>CANTUNIFY\<close>, with a finite enumeration of new problems in the invariant of the termination of
  \<^const>\<open>SIMPL\<close> (theory \<^theory>\<open>Unify_Correctness.Unify_Simpl_Term\<close>). The arity guesses and the
  \<open>\<eta>\<close>-expansion keep the invariant, with new type variables for the guesses.
\<close>

context pure_sig
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
    extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> tnew A env A env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U))"
proof -
  have ei: "einv A K env" using si by (simp add: sinv_def)
  have cT: "cert_typ alg ar (tsubst (rho0 env) T)" and cU: "cert_typ alg ar (tsubst (rho0 env) U)"
    using T(2) U(2) by simp_all
  show ?thesis
    using cunify_types_term[OF ei fin T(1) cert_typ_rev[OF ei cT T(1)] U(1) cert_typ_rev[OF ei cU U(1)]]
  proof (rule cuok_mono)
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
  moreover have "pok (A \<union> ntv Cs) env1 rb X t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from si that have "pok A env rb X t u" by (auto simp: sinv_def)
    then show ?thesis by (rule pok_mono[OF pok_Amono[OF _ Un_upper1] ext]) (simp add: gs(2))
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

lemma mf_funs_prefix:
  "Us \<Rrightarrow> U = Vs \<Rrightarrow> W \<Longrightarrow> length Us \<le> length Vs \<Longrightarrow> U = drop (length Us) Vs \<Rrightarrow> W"
proof (induction Us arbitrary: Vs)
  case (Cons U' Us)
  then obtain V Vs' where "Vs = V # Vs'" by (cases Vs) auto
  with Cons show ?case by simp
qed simp

lemma mf_bs_env_pushes:
  "bs_env \<rho> e rb \<Longrightarrow> \<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow>
    bs_env \<rho> (pushes e (map (tsubst \<rho>) Es)) (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb)"
proof (induction Es arbitrary: e rb)
  case (Cons E Es)
  have "bs_env \<rho> (e\<langle>0:tsubst \<rho> E\<rangle>) ((STR '''', E) # rb)" by (rule bs_env_Cons) (use Cons.prems in simp_all)
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed simp

lemma mf_incr_bv_incr_bv: "0 \<le> m \<Longrightarrow> 0 \<le> n \<Longrightarrow> incr_bv m k (incr_bv n k t) = incr_bv (m + n) k t"
  by (induction n k t arbitrary: m rule: incr_bv.induct) (auto simp: algebra_simps)

lemma mf_typing_incr_pushes: "e \<turnstile> s : S \<Longrightarrow> pushes e Us \<turnstile> incr_bv (ilength Us) 0 s : S"
proof (induction Us arbitrary: e s)
  case (Cons U Us)
  have "e\<langle>0:U\<rangle> \<turnstile> lift s 0 : S" using Cons.prems by (rule lift_type) simp
  from Cons.IH[OF this] show ?case by (simp add: mf_incr_bv_incr_bv add.commute)
qed simp

lemma mf_loose_bvar_incr_bv:
  "0 \<le> n \<Longrightarrow> 0 \<le> lev \<Longrightarrow> lev \<le> k \<Longrightarrow> loose_bvar (incr_bv n lev t) (k + n) = loose_bvar t k"
  by (induction n lev t arbitrary: k rule: incr_bv.induct) (auto simp: algebra_simps)

lemma mf_nat_integer_of_nat [simp]: "nat_of_integer (integer_of_nat m) = m"
  by (simp add: nat_of_integer.rep_eq integer_of_nat.rep_eq)

lemma mf_ttvars_incr_bv [simp]: "ttvars (incr_bv n k t) = ttvars t"
  by (simp add: ttvars_def)

lemma mf_ilength_rb: "ilength (rev (map f Es) @ rb) = ilength rb + ilength Es"
  by (simp add: ilength_eq integer_of_nat_eq_of_nat add.commute)

abbreviation (input) mbvs :: "nat \<Rightarrow> pterm list" where
  "mbvs n \<equiv> map (\<lambda>i. Bound (integer_of_nat i)) (rev [0..<n])"

lemma mf_typings_bvs: "pushes e Ts \<tturnstile> mbvs (length Ts) : Ts"
proof -
  let ?ks = "map integer_of_nat (rev [0..<length Ts])"
  have "pushes e Ts \<tturnstile> map Bound ?ks : map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks"
    by (rule typings_Bounds) (auto simp: pushes_nth ilength_eq integer_of_nat_eq_of_nat)
  moreover have "map (\<lambda>k. rev Ts ! nat_of_integer k) ?ks = Ts"
    by (rule nth_equalityI) (simp_all add: rev_nth)
  ultimately show ?thesis by (simp add: comp_def)
qed

lemma mf_strip_comb_expand:
  "strip_comb t = (Var v T, targs) \<Longrightarrow>
    strip_comb (incr_bv n 0 t \<degree>\<degree> ts) = (Var v T, map (incr_bv n 0) targs @ ts)"
  by (simp add: strip_comb_apps[of t] incr_bv_apps foldl_append[symmetric] strip_comb_atom_apps
      del: foldl_append)

lemma eta_expand_dpair_eq:
  "eta_expand_dpair Es (rb, t, u) =
    (rev (map (\<lambda>T. (STR '''', T)) Es) @ rb, incr_bv (ilength Es) 0 t \<degree>\<degree> mbvs (length Es),
     incr_bv (ilength Es) 0 u \<degree>\<degree> mbvs (length Es))"
  by (simp add: eta_expand_dpair_def Let_def incr_boundvars_def list_comb_apps ilength_eq)

text \<open>The \<open>\<eta>\<close>-expansion of a pair by the missing argument types of its flexible side keeps the
  invariant; the flexible side then has all its arguments.\<close>

lemma sinv_eta_expand:
  assumes si: "sinv A K X env ((rb, t, u) # dps)" and st: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts"
  shows "length targs \<le> length Ts" "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
proof -
  have ei: "einv A K env" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
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
      by (rule mf_funs_prefix[OF Us(2)[symmetric]]) (use n lUs in simp)
    then have "tnorm ?\<theta> W = drop (length Ts) Us \<Rrightarrow> U" by simp
    moreover obtain D Ds where "drop (length Ts) Us = D # Ds" using n lUs by (cases "drop (length Ts) Us") auto
    ultimately show False using W(2) by simp
  qed
  define Es where "Es = drop (length targs) Ts"
  define j where "j = length Es"
  let ?rb = "rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
  let ?x = "\<lambda>x. incr_bv (ilength Es) 0 x \<degree>\<degree> mbvs j"
  have lbx: "\<not> loose_bvar (?x x) (ilength ?rb)" if "\<not> loose_bvar x (ilength rb)" for x
    unfolding mf_ilength_rb
  proof -
    have "\<not> loose_bvar (incr_bv (ilength Es) 0 x) (ilength rb + ilength Es)"
      using mf_loose_bvar_incr_bv[of "ilength Es" 0 "ilength rb" x] that by simp
    moreover have "\<not> loose_bvar b (ilength rb + ilength Es)" if "b \<in> set (mbvs j)" for b
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
    from mf_funs_prefix[OF Us(2)] len lUs have U: "U = map (tsubst \<rho>) Es \<Rrightarrow> tsubst \<rho> W"
      by (simp add: Es_def drop_map)
    have cU: "cert_typ alg ar U" by (rule bs_env_cert[OF bs tyu pd(8)])
    then have cEs: "\<forall>T\<in>set Es. cert_typ alg ar (tsubst \<rho> T)" by (simp add: U cert_typ_funs)
    define e' where "e' = pushes e (map (tsubst \<rho>) Es)"
    have bs': "bs_env \<rho> e' ?rb" unfolding e'_def by (rule mf_bs_env_pushes[OF bs cEs])
    have ty: "e' \<turnstile> inst \<rho> (?x x) : tsubst \<rho> W" if "e \<turnstile> inst \<rho> x : U" for x
      using list_app_typeI[OF mf_typing_incr_pushes[OF that[unfolded U], of "map (tsubst \<rho>) Es", unfolded ilength_map]
          mf_typings_bvs[of e "map (tsubst \<rho>) Es", unfolded length_map]]
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
  have "pok A env ?rb X (?x t) (?x u)"
    unfolding pok_def
    using pd(1-4,6) lbx[OF pd(7)] lbx[OF pd(8)] tyx tvEs
    by (simp add: vars_apps ttvars_apps)
  then show "sinv A K X env (eta_expand_dpair (drop (length targs) Ts) (rb, t, u) # dps)"
    using si unfolding eta_expand_dpair_eq Es_def[symmetric] j_def[symmetric] by (simp add: sinv_def)
qed


lemma cert_tnorm: "einv A K env \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> cert_typ alg ar (tnorm (tyenv env) T)"
  using cert_typ_tsubst[OF _ einv_rho0(2)] by simp

lemma is_Abs_apps: "is_Abs (s \<degree>\<degree> ts) \<longleftrightarrow> ts = [] \<and> is_Abs s"
  by (induction ts arbitrary: s) auto

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
    by (auto simp: is_Abs_apps head_of_apps' head_of_incr_bv ht rigid_def split: pterm.splits)
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

abbreviation (input) mlvars :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "mlvars ts \<equiv> \<Union> (vars ` set ts)"

lemma mf_radix26_append: "radix26 n ds = radix26 n [] @ ds"
proof (induction n arbitrary: ds rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    from less.IH[OF this, of "(n mod 26) # ds"] less.IH[OF this, of "[n mod 26]"] False show ?thesis
      by (subst (1 2) radix26.simps) simp
  qed (subst (1 2) radix26.simps; simp)
qed

lemma mf_radix26_step: "\<not> n < 26 \<Longrightarrow> radix26 n [] = radix26 (n div 26) [] @ [n mod 26]"
  by (subst radix26.simps) (simp add: mf_radix26_append[of "n div 26" "[n mod 26]"])

lemma mf_radix26_small: "n < 26 \<Longrightarrow> radix26 n [] = [n]"
  by (subst radix26.simps) simp

lemma mf_radix26_digits: "d \<in> set (radix26 n []) \<Longrightarrow> d < 26"
proof (induction n arbitrary: d rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have lt: "n div 26 < n" by simp
    have "d \<in> set (radix26 (n div 26) []) \<or> d = n mod 26" using less.prems False by (auto simp: mf_radix26_step)
    then show ?thesis using less.IH[OF lt] by auto
  qed (use less in \<open>simp add: mf_radix26_small\<close>)
qed

lemma mf_radix26_val: "foldl (\<lambda>a d. a * 26 + d) 0 (radix26 n []) = n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 26")
    case False
    then have "n div 26 < n" by simp
    with less False show ?thesis by (simp add: mf_radix26_step)
  qed (simp add: mf_radix26_small)
qed

lemma mf_radix26_inj: "radix26 n [] = radix26 m [] \<Longrightarrow> n = m"
  by (metis mf_radix26_val)

lemma mf_radix26_nonempty: "radix26 n [] \<noteq> []"
  by (cases "n < 26") (simp_all add: mf_radix26_step mf_radix26_small)

lemma mf_radix_char_inj:
  fixes d d' :: nat
  assumes "d < 26" "d' < 26" "String.ascii_of (char_of (97 + d)) = String.ascii_of (char_of (97 + d'))"
  shows "d = d'"
proof -
  have "of_char (String.ascii_of (char_of (97 + x))) = (97 + x :: nat)" if "x < 26" for x :: nat
    using that by (simp add: String.ascii_of_char_of of_char_of take_bit_eq_mod)
  from this[OF assms(1)] this[OF assms(2)] assms(3) show ?thesis by simp
qed

lemma mf_radixstring_inj:
  assumes "0 \<le> n" "0 \<le> m" "radixstring n = radixstring m"
  shows "n = m"
proof -
  let ?f = "\<lambda>d::nat. String.ascii_of (char_of (97 + d))"
  from assms(3) have "String.explode (radixstring n) = String.explode (radixstring m)" by simp
  then have eq: "map ?f (radix26 (nat_of_integer n) []) = map ?f (radix26 (nat_of_integer m) [])"
    unfolding radixstring_def by (simp add: String.explode_implode_eq comp_def)
  have "inj_on ?f {d. d < 26}" by (auto intro!: inj_onI mf_radix_char_inj)
  moreover have "set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []) \<subseteq> {d. d < 26}"
    using mf_radix26_digits by blast
  ultimately have "inj_on ?f (set (radix26 (nat_of_integer n) []) \<union> set (radix26 (nat_of_integer m) []))"
    by (rule inj_on_subset)
  with eq have "radix26 (nat_of_integer n) [] = radix26 (nat_of_integer m) []"
    by (simp add: inj_on_map_eq_map)
  then have "nat_of_integer n = nat_of_integer m" by (rule mf_radix26_inj)
  with assms(1,2) show ?thesis by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq eq_nat_nat_iff)
qed

lemma mf_radixstring_nonempty: "radixstring n \<noteq> STR ''''"
proof
  assume "radixstring n = STR ''''"
  then have "String.explode (radixstring n) = []" by (simp add: String.zero_literal.rep_eq)
  then show False unfolding radixstring_def using mf_radix26_nonempty by (simp add: String.explode_implode_eq)
qed

lemma mf_plus_literal_cancel: "(a :: String.literal) + b = a + c \<longleftrightarrow> b = c"
  by (metis String.plus_literal.rep_eq literal.explode_inject same_append_eq)

lemma mf_plus_literal_neq: "b \<noteq> STR '''' \<Longrightarrow> (a :: String.literal) + b \<noteq> a"
  by (metis String.plus_literal.rep_eq literal.explode_inject append_self_conv zero_literal.rep_eq
      String.zero_literal_def)

fun mf_var_of :: "pterm \<Rightarrow> indexname" where
  "mf_var_of (Var x T) = x"
| "mf_var_of _ = undefined"

lemma mf_genvs_names:
  "0 \<le> n \<Longrightarrow> v \<in> set (genvs name i n Ts) \<Longrightarrow>
    \<exists>T. v = Var (name, i) T \<or> (\<exists>k\<ge>n. v = Var (name + radixstring k, i) T)"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  then show ?case by (fastforce dest: order_trans[of n "n + 1", rotated])
qed auto

lemma mf_genvs_distinct: "0 \<le> n \<Longrightarrow> distinct (map mf_var_of (genvs name i n Ts))"
proof (induction name i n Ts rule: genvs.induct)
  case (3 name i n T v va)
  have "(name + radixstring n, i) \<notin> mf_var_of ` set (genvs name i (n + 1) (v # va))"
  proof
    assume "(name + radixstring n, i) \<in> mf_var_of ` set (genvs name i (n + 1) (v # va))"
    then obtain w where w: "w \<in> set (genvs name i (n + 1) (v # va))" "mf_var_of w = (name + radixstring n, i)"
      by (auto simp: image_iff)
    from mf_genvs_names[OF _ w(1)] "3.prems" obtain U where
      "w = Var (name, i) U \<or> (\<exists>k\<ge>n + 1. w = Var (name + radixstring k, i) U)" by fastforce
    then show False
    proof (elim disjE exE conjE)
      assume "w = Var (name, i) U"
      with w(2) mf_plus_literal_neq[OF mf_radixstring_nonempty, of name n] show False by simp
    next
      fix k assume "n + 1 \<le> k" "w = Var (name + radixstring k, i) U"
      with w(2) "3.prems" mf_radixstring_inj[of k n] show False by (auto simp: mf_plus_literal_cancel)
    qed
  qed
  with "3.IH" "3.prems" show ?case by simp
qed auto

lemma mf_genvs_vars: "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, i) T) (genvs name i n Ts) Ts"
  by (induction name i n Ts rule: genvs.induct) auto

lemma mf_genvars_props:
  assumes "genvars name env Ts = (env', vs)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env' = maxidx env + 1"
    "list_all2 (\<lambda>v T. \<exists>a. v = Var (a, maxidx env + 1) T) vs Ts" "distinct (map mf_var_of vs)"
  using assms mf_genvs_vars mf_genvs_distinct[of 0] by (auto simp: genvars_def split: env.splits)

lemma mf_vinv_genvars:
  assumes g: "genvars name env Ts = (env', vs)" and vi: "vinv \<rho> env X"
  shows "vinv \<rho> env' (mlvars vs \<union> X)"
proof -
  note g' = mf_genvars_props[OF g]
  have ev: "evars env' = evars env" by (simp add: evars_def bnds_def g'(1))
  have b: "below (maxidx env) (X \<union> evars env)" and c: "vcons \<rho> (X \<union> evars env)"
    using vi by (simp_all add: vinv_def)
  have new: "\<exists>k < length vs. vs ! k = Var x W \<and> snd x = maxidx env + 1" if "(x, W) \<in> mlvars vs" for x W
  proof -
    from that obtain v where v: "v \<in> set vs" "(x, W) \<in> vars v" by blast
    then obtain k where k: "k < length vs" "vs ! k = v" by (auto simp: in_set_conv_nth)
    from g'(4) k obtain a where "v = Var (a, maxidx env + 1) (Ts ! k)" by (auto dest: list_all2_nthD)
    with v k show ?thesis by auto
  qed
  have le: "maxidx env \<le> maxidx env'" using g' by (simp add: integer_arith)
  have "below (maxidx env') (mlvars vs \<union> X \<union> evars env')"
    using below_mono[OF b _ le] g'(3) ev new by (fastforce simp: below_def)
  moreover have "vcons \<rho> (mlvars vs \<union> X \<union> evars env')"
    unfolding vcons_def
  proof (intro allI impI)
    fix x U V assume U: "(x, U) \<in> mlvars vs \<union> X \<union> evars env'" and V: "(x, V) \<in> mlvars vs \<union> X \<union> evars env'"
    have old: "snd x \<le> maxidx env" if "(x, W) \<in> X \<union> evars env" for W
      using belowD[OF b that] .
    have clash: False if "(x, W) \<in> mlvars vs" "(x, W') \<in> X \<union> evars env" for W W'
      using new[OF that(1)] old[OF that(2)] by (auto simp: integer_arith)
    have both: "U = V" if "(x, U) \<in> mlvars vs" "(x, V) \<in> mlvars vs"
    proof -
      from new[OF that(1)] new[OF that(2)] obtain k l where
        k: "k < length vs" "vs ! k = Var x U" and l: "l < length vs" "vs ! l = Var x V" by blast
      have "map mf_var_of vs ! k = map mf_var_of vs ! l" using k l by simp
      then have "k = l" using nth_eq_iff_index_eq[OF g'(5), of k l] k(1) l(1) by simp
      with k l show ?thesis by simp
    qed
    have U': "(x, U) \<in> mlvars vs \<or> (x, U) \<in> X \<union> evars env" and V': "(x, V) \<in> mlvars vs \<or> (x, V) \<in> X \<union> evars env"
      using U V ev by blast+
    show "tsubst \<rho> U = tsubst \<rho> V"
    proof (cases "(x, U) \<in> mlvars vs")
      case True
      show ?thesis
      proof (cases "(x, V) \<in> mlvars vs")
        case True
        with \<open>(x, U) \<in> mlvars vs\<close> show ?thesis using both by simp
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from clash[OF True this] show ?thesis ..
      qed
    next
      case False
      with U' have u: "(x, U) \<in> X \<union> evars env" by simp
      show ?thesis
      proof (cases "(x, V) \<in> mlvars vs")
        case True
        from clash[OF True u] show ?thesis ..
      next
        case False
        with V' have "(x, V) \<in> X \<union> evars env" by simp
        from vconsD[OF c u this] show ?thesis .
      qed
    qed
  qed
  ultimately show ?thesis by (simp add: vinv_def ev)
qed

lemma mf_combound_apps: "combound t m k = t \<degree>\<degree> map (\<lambda>i. Bound (m + integer_of_nat i)) (rev [0..<k])"
proof (induction k arbitrary: m)
  case (Suc k)
  have r: "rev [0..<Suc k] = map Suc (rev [0..<k]) @ [0]"
    by (simp add: upt_conv_Cons map_Suc_upt[symmetric] rev_map del: upt_Suc)
  show ?case using Suc.IH[of "m + 1"] by (simp add: r comp_def algebra_simps integer_of_nat_eq_of_nat del: upt_Suc)
qed simp

lemma mf_combound_bvs: "combound t 0 k = t \<degree>\<degree> mbvs k"
  by (simp add: mf_combound_apps)

text \<open>The new arguments of a projection or an imitation:\<close>

lemma mf_make_args_props:
  assumes "make_args name Ts env Us = (env', args)"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (mlvars Gs \<union> X)"
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
  note g' = mf_genvars_props[OF g]
  show ?thesis
  proof (rule that[of vs])
    show "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) vs" by (simp add: e mf_combound_bvs)
    show "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) vs Us"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth)
    show "tenv env' = tenv env" "tyenv env' = tyenv env" using g' e by simp_all
    show "maxidx env \<le> maxidx env'" using g' e by (simp add: integer_arith)
    show "vinv \<rho> env' (mlvars vs \<union> X)" if "vinv \<rho> env X" for \<rho> X
      using mf_vinv_genvars[OF g that] e by simp
    show "\<forall>G\<in>set vs. \<exists>a U. G = Var (a, maxidx env + 1) U"
      using g'(4) by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  qed
qed


subsection \<open>Binding the variable to a copy\<close>

text \<open>
  A copy \<open>u'\<close> for the variable \<open>v :: T\<close> applied to arguments of types \<open>Ts\<close>, with a new problem in
  the invariant: \<open>v\<close> is unbound and not reachable from the copy, and the abstraction of the copy
  over \<open>Ts\<close> is a closed term of the type of \<open>v\<close> for every certified solution of the type
  environment.
\<close>

definition copy_ok :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> indexname \<times> ptyp \<Rightarrow> ptyp list \<Rightarrow> elem \<Rightarrow> bool" where
  "copy_ok A0 env0 vT Ts x \<longleftrightarrow> (\<exists>u' env' dps' A K X. x = El_C u' env' dps' \<and> finite X \<and> finite K \<and>
    A0 \<subseteq> A \<and> tnew A0 env0 A env' \<and> sinv A K X env' dps' \<and> vt_lookup (tenv env') (fst vT) = None \<and> vT \<in> X \<union> evars env' \<and>
    (\<forall>y U. (y, U) \<in> vars u' \<longrightarrow> (fst vT, y) \<notin> (dep env')\<^sup>*) \<and> \<not> loose_bvar u' (ilength Ts) \<and>
    vars u' \<subseteq> X \<union> evars env' \<and> tvars (snd vT) \<union> ttvars (types_abs Ts u') \<subseteq> tvars_env (tyenv env') \<union> A \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<forall>e. e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> (snd vT))))"

lemma mf_vars_types_abs [simp]: "vars (types_abs Ts u) = vars u"
  by (induction Ts) simp_all

lemma mf_loose_bvar_types_abs: "loose_bvar (types_abs Ts u) k \<longleftrightarrow> loose_bvar u (k + ilength Ts)"
  by (induction Ts arbitrary: k) (simp_all add: algebra_simps)

lemma lookup_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> lookup env x T = return None"
  by (simp add: lookup_def)

theorem new_dset_ok:
  assumes c: "copy_ok A0 env0 (v, T) Ts (El_C u' env' dps')"
  shows "\<exists>y. okW (new_dset (v, T) Ts u' env' dps') y \<and> mres A0 env0 y"
proof -
  from c obtain A K X where fin: "finite X" "finite K" and A0: "A0 \<subseteq> A" and tn: "tnew A0 env0 A env'"
    and si: "sinv A K X env' dps'"
    and vn: "vt_lookup (tenv env') v = None" and vX: "(v, T) \<in> X \<union> evars env'"
    and acy: "\<forall>y U. (y, U) \<in> vars u' \<longrightarrow> (v, y) \<notin> (dep env')\<^sup>*" and lb: "\<not> loose_bvar u' (ilength Ts)"
    and vu: "vars u' \<subseteq> X \<union> evars env'"
    and tv: "tvars T \<union> ttvars (types_abs Ts u') \<subseteq> tvars_env (tyenv env') \<union> A"
    and ty: "\<And>\<rho> e. tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T"
    unfolding copy_ok_def by auto
  let ?w = "types_abs Ts u'"
  have ei: "einv A K env'" and wi: "winv env' X" using si by (simp_all add: sinv_def)
  have cl: "closed ?w" using lb by (simp add: closed_def mf_loose_bvar_types_abs)
  from update_ok[OF vn] obtain env'' where upd: "update (v, T) ?w env' = return env''" by blast
  then have upd': "ok (update (v, T) ?w env') env''" by (simp add: return_def)
  have below: "snd v \<le> maxidx env'"
    using winvD[OF wi einv_rho0[OF ei]] vX by (auto simp: vinv_def dest: belowD)
  have ei'': "einv A K env''"
    by (rule einv_update[OF ei upd' _ cl below tv]) (use acy in auto)
  have th: "tyenv env'' = tyenv env'" by (rule ok_update(3)[OF upd'])
  have wi'': "winv env'' X"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume \<rho>: "tsol (tyenv env'') \<rho>" "cert_inst \<rho>"
    then have \<rho>': "tsol (tyenv env') \<rho>" by (simp add: th)
    have w: "wt_env \<rho> env'" "vinv \<rho> env' X" using winvD[OF wi \<rho>' \<rho>(2)] by blast+
    have "wt_env \<rho> env''" by (rule wt_env_update[OF upd' w(1) cl ty[OF \<rho>' \<rho>(2)]])
    moreover have "vinv \<rho> env'' X"
    proof (rule vinv_update[OF upd'])
      have "X \<union> insert (v, T) (vars ?w) \<union> evars env' = X \<union> evars env'" using vX vu by auto
      then show "vinv \<rho> env' (X \<union> insert (v, T) (vars ?w))" using w(2) by (simp add: vinv_def)
    qed
    ultimately show "wt_env \<rho> env'' \<and> vinv \<rho> env'' X" ..
  qed
  have ext: "extends env' env''" by (rule extends_update[OF upd'])
  have "sinv A K X env'' dps'"
    using si ei'' wi'' pok_mono[OF _ ext] th unfolding sinv_def by auto
  moreover have "tnew A0 env0 A env''" using tn th by (simp add: tnew_def)
  ultimately have "mres A0 env0 (El_E env'' dps')" using fin A0 by (auto simp: mres_def)
  moreover have "okW (new_dset (v, T) Ts u' env' dps') (El_E env'' dps')"
    by (simp add: new_dset_def lookup_unbound[OF vn] upd return_def)
  ultimately show ?thesis by blast
qed

lemma fin_MapNewDset_copy:
  "fin cfg s (copy_ok A0 env0 (v, T) Ts) \<Longrightarrow> fin cfg (S_MapNewDset (v, T) Ts s) (mres A0 env0)"
proof (rule fin_MapNewDset, erule fin_mono)
  fix x assume c: "copy_ok A0 env0 (v, T) Ts x"
  then obtain u' env' dps' where x: "x = El_C u' env' dps'" by (auto simp: copy_ok_def)
  with c new_dset_ok[of A0 env0 v T Ts u' env' dps']
  show "\<exists>u env dps y. x = El_C u env dps \<and> okW (new_dset (v, T) Ts u env dps) y \<and> mres A0 env0 y" by blast
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

lemma occurs_terms_term:
  assumes ei: "einv A K env" and wi: "winv env X" and vX: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and vt: "\<forall>t\<in>set ts. vars t \<subseteq> X \<union> evars env"
  shows "\<exists>b. occurs_terms env v ts = return b"
proof -
  note e = einvD[OF ei]
  have vk: "vok env (X \<union> evars env)" by (rule vok_winv[OF ei wi vX])
  have "\<forall>t\<in>set ts. vok env (vars t \<union> evars env)" using vt by (auto intro: vok_mono[OF vk])
  from occurs_list_term[OF e(3,6,7) this, of v "[]"] obtain r where "occurs_list env v [] ts = return r" by blast
  then show ?thesis by (simp add: occurs_terms_def)
qed


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

lemma pok_Xmono:
  "pok A env rb X t u \<Longrightarrow> X \<subseteq> X' \<Longrightarrow> vtvars X' \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> pok A env rb X' t u"
  unfolding pok_def by blast

lemma vtvars_mlvars_Var:
  "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U \<and> tvars U \<subseteq> S \<Longrightarrow> vtvars (mlvars Gs) \<subseteq> S"
  by (fastforce simp: vtvars_def)

text \<open>The new variables of \<^const>\<open>make_args\<close> keep the invariant:\<close>

lemma sinv_make_args:
  assumes si: "sinv A K X env dps" and ma: "make_args name Ts env Us = (env', args)"
    and tv: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
  obtains Gs where "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    "sinv A K (mlvars Gs \<union> X) env' dps"
    "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  obtain Gs where Gs: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts)) Gs"
    "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts \<Rrightarrow> U)) Gs Us"
    "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    "\<And>\<rho> X. vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' (mlvars Gs \<union> X)"
    "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    by (rule mf_make_args_props[OF ma]) blast
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(rb, t, u)\<in>set dps. pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
  proof (rule vtvars_mlvars_Var, intro ballI)
    fix G assume "G \<in> set Gs"
    then obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs(2) i(1)] i obtain x where "G = Var x (Ts \<Rrightarrow> (Us ! i))" by blast
    moreover have "Us ! i \<in> set Us" using i(1) list_all2_lengthD[OF Gs(2)] by simp
    ultimately show "\<exists>x U. G = Var x U \<and> tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
      using tv by (fastforce simp: tvars_funs)
  qed
  have ei': "einv A K env'" by (rule einv_maxidx[OF ei Gs(3-5)])
  have wi': "winv env' (mlvars Gs \<union> X)"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
    then have "wt_env \<rho> env \<and> vinv \<rho> env X" using winvD[OF wi] Gs(4) by simp
    then show "wt_env \<rho> env' \<and> vinv \<rho> env' (mlvars Gs \<union> X)" using Gs(6) wt_env_tenv[OF Gs(3)] by blast
  qed
  have ext: "extends env env'" using Gs(3-5) by (simp add: extends_def)
  have "pok A env' rb (mlvars Gs \<union> X) t u" if "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from ps that have p: "pok A env rb X t u" by auto
    have "pok A env rb (mlvars Gs \<union> X) t u"
      by (rule pok_Xmono[OF p]) (use vG pokD(6)[OF p] in auto)
    then show ?thesis by (rule pok_mono[OF _ ext]) (simp add: Gs(4))
  qed
  then have "sinv A K (mlvars Gs \<union> X) env' dps" using ei' wi' by (auto simp: sinv_def)
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
    by (rule cuok_mono[OF cu]) (simp add: True)
  show ?thesis
  proof (cases "cfg_trace_types cfg")
    case tt: True
    show ?thesis unfolding proj_unify_def using True tt cfg
      by (simp add: test_unify_types_def) (rule cuok_bindW[OF cu'], simp add: cuok_def okW_whenW)
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

lemma typings_unique_mf: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<tturnstile> ts : Us \<Longrightarrow> Ts = Us"
  by (induction ts arbitrary: Ts Us) (auto split: list.splits dest: typing_unique)

lemma pair_base:
  assumes ei: "einv A K env" and p: "pok A env rb X t u" and st: "strip_comb t = (Var v T, targs)"
    and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A"
    and \<rho>: "tsol (tyenv env) \<rho>" and tyt: "e \<turnstile> inst \<rho> t : U"
  shows "U = tsubst \<rho> base" "tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> base"
    "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
proof -
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p]
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
    have "Us' = Us" by (rule typings_unique_mf[OF tyas that(3)])
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

lemma mf_types_abs_abs_list: "types_abs Ts u = abs_list (map (\<lambda>T. (STR '''', T)) Ts) u"
  by (induction Ts) simp_all

lemma mf_inst_types_abs: "inst \<rho> (types_abs Ts u) = types_abs (map (tsubst \<rho>) Ts) (inst \<rho> u)"
  by (induction Ts) simp_all

lemma mf_ttvars_types_abs: "ttvars (types_abs Ts u) = (\<Union>T\<in>set Ts. tvars T) \<union> ttvars u"
  by (induction Ts) auto

lemma mf_typing_types_abs:
  "pushes e Ts \<turnstile> u : U \<Longrightarrow> \<forall>T\<in>set Ts. cert_typ alg ar T \<Longrightarrow> e \<turnstile> types_abs Ts u : Ts \<Rrightarrow> U"
  using typing_abs_list[of e "map (\<lambda>T. (STR '''', T)) Ts" u U]
  by (simp add: mf_types_abs_abs_list comp_def)

lemma mf_typings_iff: "e \<tturnstile> ts : Ts \<longleftrightarrow> list_all2 (typing e) ts Ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits simp: list_all2_Cons1)

lemma mf_cert_targs:
  assumes "bs_env \<rho> e rb" "e \<tturnstile> map (inst \<rho>) targs : map (tsubst \<rho>) Ts"
    "\<forall>t\<in>set targs. \<not> loose_bvar t (ilength rb)"
  shows "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)"
proof
  fix T assume "T \<in> set Ts"
  then obtain i where i: "i < length Ts" "T = Ts ! i" by (auto simp: in_set_conv_nth)
  from typings_nth[OF assms(2)] i have l: "i < length targs" "e \<turnstile> inst \<rho> (targs ! i) : tsubst \<rho> T"
    by auto
  show "cert_typ alg ar (tsubst \<rho> T)"
    by (rule bs_env_cert[OF assms(1) l(2)]) (use assms(3) l(1) in auto)
qed

lemma mf_typings_new_args:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    and cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" and cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)"
    and len: "length Ts' = length Ts"
  shows "pushes e' (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs) : map (tsubst \<rho>) Us"
  unfolding mf_typings_iff
proof (rule list_all2_all_nthI)
  have lGs: "length Gs = length Us" by (rule list_all2_lengthD[OF Gs])
  then show "length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs)) = length (map (tsubst \<rho>) Us)" by simp
  fix k assume "k < length (map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs))"
  then have k: "k < length Gs" by simp
  from list_all2_nthD[OF Gs k] obtain x where "Gs ! k = Var x (Ts' \<Rrightarrow> (Us ! k))" by blast
  moreover have "Us ! k \<in> set Us" using k lGs by simp
  ultimately have "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (Gs ! k) : map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> (Us ! k)"
    using cTs cUs by (auto simp: tsubst_funs ts cert_typ_funs)
  from list_app_typeI[OF this mf_typings_bvs]
  show "pushes e' (map (tsubst \<rho>) Ts) \<turnstile> map (inst \<rho>) (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs) ! k :
      map (tsubst \<rho>) Us ! k"
    using k lGs len by (simp add: inst_apps comp_def)
qed

lemma mf_make_projs_props:
  "okW (make_projs u targs0 Ts targs) ps \<Longrightarrow> length Ts = length targs \<and>
    (\<forall>q\<in>set ps. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k))"
proof (induction u targs0 Ts targs arbitrary: ps rule: make_projs.induct)
  case (1 u targs0 T Ts targ targs)
  from "1.prems" obtain ps' where ps': "okW (make_projs u targs0 Ts targs) ps'"
    and ps: "ps = (Bound (ilength Ts), T, targ) # ps'" by auto
  note IH = "1.IH"[OF ps']
  have "\<exists>k<length (targ # targs). q = (Bound (integer_of_nat (length (targ # targs) - 1 - k)),
      (T # Ts) ! k, (targ # targs) ! k)" if "q \<in> set ps" for q
  proof -
    from that ps consider "q = (Bound (ilength Ts), T, targ)" | "q \<in> set ps'" by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis using IH by (intro exI[of _ 0]) (simp add: ilength_eq)
    next
      case 2
      with IH obtain k where "k < length targs"
        "q = (Bound (integer_of_nat (length targs - 1 - k)), Ts ! k, targs ! k)" by blast
      then show ?thesis by (intro exI[of _ "Suc k"]) simp
    qed
  qed
  with IH show ?case by simp
qed auto

lemma make_projs_term: "length Ts = length targs \<Longrightarrow> \<exists>ps. okW (make_projs u targs0 Ts targs) ps"
proof (induction Ts arbitrary: targs)
  case (Cons T Ts)
  then obtain targ targs' where "targs = targ # targs'" by (cases targs) auto
  with Cons show ?case by fastforce
qed auto

lemma cuok_okW: "okW m x \<Longrightarrow> P x \<Longrightarrow> cuok m P"
  by (auto simp: cuok_def)

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

lemma copy_okI:
  assumes "finite X" "finite K" "A0 \<subseteq> A" "tnew A0 env0 A env'" "sinv A K X env' dps'" "vt_lookup (tenv env') v = None" "(v, T) \<in> X \<union> evars env'"
    "\<And>y U. (y, U) \<in> vars u' \<Longrightarrow> (v, y) \<notin> (dep env')\<^sup>*" "\<not> loose_bvar u' (ilength Ts)"
    "vars u' \<subseteq> X \<union> evars env'" "tvars T \<union> ttvars (types_abs Ts u') \<subseteq> tvars_env (tyenv env') \<union> A"
    "\<And>\<rho> e. tsol (tyenv env') \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> e \<turnstile> inst \<rho> (types_abs Ts u') : tsubst \<rho> T"
  shows "copy_ok A0 env0 (v, T) Ts (El_C u' env' dps')"
  unfolding copy_ok_def using assms by (intro exI[of _ u'] exI[of _ env'] exI[of _ dps'] exI[of _ A] exI[of _ K] exI[of _ X]) auto

text \<open>The new variables applied to the bound variables of the arguments:\<close>

lemma new_args_props:
  assumes Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us" and len: "length Ts' = length Ts"
    and args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs"
  shows "\<forall>a\<in>set args. \<not> loose_bvar a (ilength Ts)" "(\<Union>a\<in>set args. vars a) = mlvars Gs"
    "(\<Union>a\<in>set args. ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
  unfolding args
proof -
  have var: "\<exists>x U. G = Var x U" if "G \<in> set Gs" for G
  proof -
    from that obtain i where i: "i < length Gs" "G = Gs ! i" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF Gs i(1)] i(2) show ?thesis by blast
  qed
  have lb: "\<not> loose_bvar b (ilength Ts)" if "b \<in> set (mbvs (length Ts'))" for b
    using that len by (auto simp: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq)
  show "\<forall>a\<in>set (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs). \<not> loose_bvar a (ilength Ts)"
    using var lb by (fastforce simp: loose_bvar_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs). vars a) = mlvars Gs"
    by (auto simp: vars_apps)
  show "(\<Union>a\<in>set (map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs). ttvars a) = (\<Union>G\<in>set Gs. ttvars G)"
    by (auto simp: ttvars_apps)
qed

lemma ttvars_mlvars_Gs:
  assumes "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U"
  shows "(\<Union>G\<in>set Gs. ttvars G) = vtvars (mlvars Gs)"
proof -
  have e: "ttvars G = vtvars (vars G)" if "G \<in> set Gs" for G using assms that by (fastforce simp: vtvars_def)
  have "vtvars (mlvars Gs) = (\<Union>G\<in>set Gs. vtvars (vars G))" by (auto simp: vtvars_def)
  then show ?thesis using e by auto
qed

text \<open>The new variables are unbound and do not reach \<open>v\<close>:\<close>

lemma new_vars_acyclic:
  assumes ei: "einv A K env1" and te: "tenv env2 = tenv env1"
    and G: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env1 + 1) U" and v: "snd v \<le> maxidx env1"
    and y: "(y, U) \<in> mlvars Gs"
  shows "(v, y) \<notin> (dep env2)\<^sup>*"
proof
  assume r: "(v, y) \<in> (dep env2)\<^sup>*"
  from y G obtain a where ya: "y = (a, maxidx env1 + 1)" by fastforce
  have "vt_lookup (tenv env2) y = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env2) y \<noteq> None"
    then obtain b where "vt_lookup (tenv env1) y = Some b" using te by auto
    from bbelowD[OF einvD(5)[OF ei] this] ya show False by simp
  qed
  from rtrancl_dep_unbound[OF this r] ya v show False by simp
qed

lemma head_var_props:
  assumes p: "pok A env rb X t u" and st: "strip_comb t = (Var v T, targs)" and fr: "fr_shape env (rb, t, u)"
  shows "(v, T) \<in> X \<union> evars env" "vt_lookup (tenv env) v = None" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<forall>s\<in>set targs. vars s \<subseteq> X \<union> evars env \<and> ttvars s \<subseteq> tvars_env (tyenv env) \<union> A \<and> \<not> loose_bvar s (ilength rb)"
proof -
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  note pd = pokD[OF p]
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

text \<open>The copy of a projection with the guess of \<open>Cs\<close> arguments:\<close>

lemma proj_copy_ok:
  assumes finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    and stT: "ok (strip_type env (Ts' ! k)) (Us, bary)" and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and Cs: "\<forall>C\<in>set Cs. \<exists>a. C = TVar a []"
    and si': "sinv (A \<union> ntv Cs) (K \<union> ntv Cs) X env' ((rb, t, u) # dps)" and te: "tenv env' = tenv env"
    and ext: "extends env env'" and tve: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    and tn: "tnew A env (A \<union> ntv Cs) env'"
    and bary: "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base)"
    and ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
  shows "copy_ok A env (v, T) Ts (El_C (list_comb bvar args) env'' ((rb, t, u) # dps))"
proof -
  let ?A = "A \<union> ntv Cs" and ?K = "K \<union> ntv Cs" and ?\<theta> = "tyenv env"
  have ei: "einv A K env" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  have ei': "einv ?A ?K env'" using si' by (simp add: sinv_def)
  note hv = head_var_props[OF p st fr]
  have tvC: "\<forall>C\<in>set Cs. tvars C \<subseteq> ntv Cs" by (auto simp: ntv_def)
  have tvTs'': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env') \<union> ?A" using tvTs' tve by blast
  have tvUC: "\<forall>U\<in>set (Us @ Cs). tvars U \<subseteq> tvars_env (tyenv env') \<union> ?A" using tvUs tvC tve by auto
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs (Us @ Cs)"
    and ma': "tenv env'' = tenv env'" "tyenv env'' = tyenv env'" "maxidx env' \<le> maxidx env''"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env' + 1) U"
    and si'': "sinv ?A ?K (mlvars Gs \<union> X) env'' ((rb, t, u) # dps)"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env') \<union> ?A"
    by (rule sinv_make_args[OF si' ma tvTs'' tvUC])
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD)
  have Gv: "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U" using Gi by blast
  have lTs'': "length Ts' = length Ts" using lTs' len by simp
  note na = new_args_props[OF Gs lTs'' args]
  have j: "0 \<le> integer_of_nat (length targs - 1 - k)" "integer_of_nat (length targs - 1 - k) < ilength Ts"
    using hk len by (simp_all add: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq)
  have vu: "vars (list_comb bvar args) = mlvars Gs" using na(2) hk(2) by (simp add: list_comb_apps vars_apps)
  have vbelow: "snd v \<le> maxidx env'"
    using below_head[OF si hv(1)] extends_def ext by fastforce
  have tn'': "tnew A env ?A env''" using tn ma'(2) by (simp add: tnew_def)
  show ?thesis
  proof (rule copy_okI[OF _ finK[THEN finite_UnI, OF finite_ntv] Un_upper1 tn'' si''])
    show "finite (mlvars Gs \<union> X)" using finX by simp
    show "vt_lookup (tenv env'') v = None" using hv(2) ma'(1) te by simp
    show "(v, T) \<in> mlvars Gs \<union> X \<union> evars env''" using hv(1) evars_tenv[of env'' env] ma'(1) te by auto
    show "(v, y) \<notin> (dep env'')\<^sup>*" if "(y, U) \<in> vars (list_comb bvar args)" for y U
      by (rule new_vars_acyclic[OF ei' _ Gi vbelow]) (use that vu ma'(1) in auto)
    show "\<not> loose_bvar (list_comb bvar args) (ilength Ts)"
      using na(1) j(2) hk(2) by (auto simp: list_comb_apps loose_bvar_apps)
    show "vars (list_comb bvar args) \<subseteq> mlvars Gs \<union> X \<union> evars env''" using vu by auto
    have tvTs: "(\<Union>T\<in>set Ts. tvars T) \<subseteq> tvars_env ?\<theta> \<union> A"
      using mf_binder_types_sound[OF bt[unfolded return_def] refl einvD(6)[OF ei]] hv(3) by blast
    have "ttvars (list_comb bvar args) = vtvars (mlvars Gs)"
      using na(3) hk(2) ttvars_mlvars_Gs[OF Gv] by (simp add: list_comb_apps ttvars_apps)
    then show "tvars T \<union> ttvars (types_abs Ts (list_comb bvar args)) \<subseteq> tvars_env (tyenv env'') \<union> ?A"
      using hv(3) tvTs vG tve ma'(2) by (auto simp: mf_ttvars_types_abs)
    fix \<rho> e assume \<rho>'': "tsol (tyenv env'') \<rho>" and c\<rho>: "cert_inst \<rho>"
    have \<rho>': "tsol (tyenv env') \<rho>" using \<rho>'' ma'(2) by simp
    have \<rho>: "tsol ?\<theta> \<rho>" by (rule extends_tsol[OF \<rho>' ext])
    from pokD(9)[OF p \<rho> c\<rho>] obtain e0 U where bs: "bs_env \<rho> e0 rb" and tyt: "e0 \<turnstile> inst \<rho> t : U"
      and tyu: "e0 \<turnstile> inst \<rho> u : U" by blast
    note pb = pair_base[OF ei p st bt len T0 base tvb \<rho> tyt]
    have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" by (rule mapM_fastype_types[OF Ts' \<rho> bs pb(3)])
    have lba: "\<forall>s\<in>set targs. \<not> loose_bvar s (ilength rb)" using hv(4) by blast
    have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule mf_cert_targs[OF bs pb(3) lba])
    have Tk: "tsubst \<rho> (Ts ! k) = tsubst \<rho> (Ts' ! k)"
      using arg_cong[OF ts, of "\<lambda>xs. xs ! k"] hk(1) len lTs' by simp
    have Tk': "tsubst \<rho> (Ts' ! k) = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> bary" by (rule strip_type_sound[OF stT \<rho>])
    have jT: "tsubst \<rho> (Ts ! k) = map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> tsubst \<rho> base"
      using Tk Tk' bary \<rho>' by (simp add: tsubst_funs)
    have cTk: "cert_typ alg ar (tsubst \<rho> (Ts ! k))" using cTs hk(1) len by simp
    have cUs: "\<forall>U\<in>set (Us @ Cs). cert_typ alg ar (tsubst \<rho> U)" using cTk by (auto simp: jT cert_typ_funs)
    have tyargs: "pushes e (map (tsubst \<rho>) Ts) \<tturnstile> map (inst \<rho>) args : map (tsubst \<rho>) (Us @ Cs)"
      using mf_typings_new_args[OF Gs ts cTs cUs] lTs' len by (simp add: args)
    have "pushes e (map (tsubst \<rho>) Ts) (integer_of_nat (length targs - 1 - k)) = map (tsubst \<rho>) (Us @ Cs) \<Rrightarrow> tsubst \<rho> base"
    proof -
      have "pushes e (map (tsubst \<rho>) Ts) (integer_of_nat (length targs - 1 - k)) =
          rev (map (tsubst \<rho>) Ts) ! (length targs - 1 - k)"
        using j by (simp add: pushes_nth)
      also have "\<dots> = tsubst \<rho> (Ts ! k)" using hk(1) len by (simp add: rev_nth)
      finally show ?thesis using jT by simp
    qed
    from list_app_typeI[OF typing.Bound[where e="pushes e (map (tsubst \<rho>) Ts)", OF j(1) this] tyargs]
    have "pushes e (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb bvar args) : tsubst \<rho> base"
      by (simp add: hk(2) list_comb_apps inst_apps)
    from mf_typing_types_abs[OF this] cTs
    show "e \<turnstile> inst \<rho> (types_abs Ts (list_comb bvar args)) : tsubst \<rho> T"
      using pb(2) by (simp add: mf_inst_types_abs)
  qed
qed

text \<open>The imitation of a single step:\<close>

lemma imit_copy_ok:
  assumes finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and hc: "fst (strip_comb u) = Const c C \<or> fst (strip_comb u) = Free c C"
    and btu: "ok (binder_types env T0) Us" and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and ma: "make_args vname Ts' env Us = (env', args)"
  shows "copy_ok A env (v, T) Ts (El_C (list_comb (fst (strip_comb u)) args) env' ((rb, t, u) # dps))"
proof -
  let ?\<theta> = "tyenv env" and ?h = "fst (strip_comb u)"
  have ei: "einv A K env" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  note hv = head_var_props[OF p st fr]
  obtain Gs where args: "args = map (\<lambda>G. G \<degree>\<degree> mbvs (length Ts')) Gs"
    and Gs: "list_all2 (\<lambda>G U. \<exists>x. G = Var x (Ts' \<Rrightarrow> U)) Gs Us"
    and ma': "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
    and Gi: "\<forall>G\<in>set Gs. \<exists>a U. G = Var (a, maxidx env + 1) U"
    and si'': "sinv A K (mlvars Gs \<union> X) env' ((rb, t, u) # dps)"
    and vG: "vtvars (mlvars Gs) \<subseteq> tvars_env (tyenv env) \<union> A"
    by (rule sinv_make_args[OF si ma tvTs' tvUs])
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD)
  have Gv: "\<forall>G\<in>set Gs. \<exists>x U. G = Var x U" using Gi by blast
  have lTs'': "length Ts' = length Ts" using lTs' len by simp
  note na = new_args_props[OF Gs lTs'' args]
  have hvars: "vars ?h = {}" "\<not> loose_bvar ?h k" "closed ?h" for k using hc by (auto simp: closed_def)
  have vu: "vars (list_comb ?h args) = mlvars Gs" using na(2) hvars(1) by (simp add: list_comb_apps vars_apps)
  have vbelow: "snd v \<le> maxidx env" by (rule below_head[OF si hv(1)])
  have tvh: "ttvars ?h \<subseteq> tvars_env ?\<theta> \<union> A"
    using ttvars_head[of u] pokD(4)[OF p] by (simp add: head_of_strip_comb)
  have tn: "tnew A env A env'" by (rule tnew_tyenv[OF ma'(2) order_refl])
  show ?thesis
  proof (rule copy_okI[OF _ finK order_refl tn si''])
    show "finite (mlvars Gs \<union> X)" using finX by simp
    show "vt_lookup (tenv env') v = None" using hv(2) ma'(1) by simp
    show "(v, T) \<in> mlvars Gs \<union> X \<union> evars env'" using hv(1) evars_tenv[of env' env] ma'(1) by auto
    show "(v, y) \<notin> (dep env')\<^sup>*" if "(y, U) \<in> vars (list_comb ?h args)" for y U
      by (rule new_vars_acyclic[OF ei ma'(1) Gi vbelow]) (use that vu in auto)
    show "\<not> loose_bvar (list_comb ?h args) (ilength Ts)"
      using na(1) hvars(2) by (auto simp: list_comb_apps loose_bvar_apps)
    show "vars (list_comb ?h args) \<subseteq> mlvars Gs \<union> X \<union> evars env'" using vu by auto
    have tvTs: "(\<Union>T\<in>set Ts. tvars T) \<subseteq> tvars_env ?\<theta> \<union> A"
      using mf_binder_types_sound[OF bt[unfolded return_def] refl einvD(6)[OF ei]] hv(3) by blast
    have "ttvars (list_comb ?h args) \<subseteq> ttvars ?h \<union> vtvars (mlvars Gs)"
      using na(3) ttvars_mlvars_Gs[OF Gv] by (simp add: list_comb_apps ttvars_apps)
    then show "tvars T \<union> ttvars (types_abs Ts (list_comb ?h args)) \<subseteq> tvars_env (tyenv env') \<union> A"
      using hv(3) tvTs vG tvh ma'(2) by (auto simp: mf_ttvars_types_abs)
    fix \<rho> e assume \<rho>': "tsol (tyenv env') \<rho>" and c\<rho>: "cert_inst \<rho>"
    have \<rho>: "tsol ?\<theta> \<rho>" using \<rho>' ma'(2) by simp
    from pokD(9)[OF p \<rho> c\<rho>] obtain e0 U where bs: "bs_env \<rho> e0 rb" and tyt: "e0 \<turnstile> inst \<rho> t : U"
      and tyu: "e0 \<turnstile> inst \<rho> u : U" by blast
    note pb = pair_base[OF ei p st bt len T0 base tvb \<rho> tyt]
    have ts: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts" by (rule mapM_fastype_types[OF Ts' \<rho> bs pb(3)])
    have lba: "\<forall>s\<in>set targs. \<not> loose_bvar s (ilength rb)" using hv(4) by blast
    have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst \<rho> T)" by (rule mf_cert_targs[OF bs pb(3) lba])
    have u: "u = ?h \<degree>\<degree> snd (strip_comb u)" by (simp add: strip_comb_apps)
    from tyu[unfolded u[THEN arg_cong[of _ _ "inst \<rho>"]] inst_apps] obtain Vs where
      tyh: "e0 \<turnstile> inst \<rho> ?h : Vs \<Rrightarrow> U" by (rule list_app_typeE)
    have T0': "tsubst \<rho> T0 = Vs \<Rrightarrow> U" by (rule fastype_sound[OF T0 \<rho> bs tyh])
    have T0'': "tsubst \<rho> T0 = map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> base"
      by (rule binder_body_type_sound[OF btu refl base \<rho>])
    have cT0: "cert_typ alg ar (tsubst \<rho> T0)"
      using bs_env_cert[OF bs tyh hvars(2)] by (simp add: T0')
    then have cUs: "\<forall>U\<in>set Us. cert_typ alg ar (tsubst \<rho> U)" by (simp add: T0'' cert_typ_funs)
    have tyh': "e' \<turnstile> inst \<rho> ?h : map (tsubst \<rho>) Us \<Rrightarrow> tsubst \<rho> base" for e'
      using typing_closed[OF tyh] hvars(3) T0' T0'' by (simp add: closed_def)
    have "pushes e (map (tsubst \<rho>) Ts) \<turnstile> inst \<rho> (list_comb ?h args) : tsubst \<rho> base"
      using list_app_typeI[OF tyh' mf_typings_new_args[OF Gs ts cTs cUs]] lTs' len
      by (simp add: args list_comb_apps inst_apps)
    from mf_typing_types_abs[OF this] cTs
    show "e \<turnstile> inst \<rho> (types_abs Ts (list_comb ?h args)) : tsubst \<rho> T"
      using pb(2) by (simp add: mf_inst_types_abs)
  qed
qed

text \<open>The setting of a single step, after the computation of the types:\<close>

lemma match1_types:
  assumes si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
  shows "\<exists>T0 base Ts'. fastype env rb (fst (strip_comb u)) = return T0 \<and> body_type env T0 = return base \<and>
    tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A \<and> tvars base \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    mapM (fastype env rb) targs = return Ts' \<and> (\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A) \<and>
    cert_typ alg ar (tnorm (tyenv env) base) \<and> (\<forall>T\<in>set Ts'. cert_typ alg ar (tnorm (tyenv env) T))"
proof -
  let ?\<theta> = "tyenv env" and ?h = "fst (strip_comb u)" and ?\<rho> = "rho0 env"
  have ei: "einv A K env" and p: "pok A env rb X t u" using si by (auto simp: sinv_def)
  note x = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = pokD[OF p] and hv = head_var_props[OF p st fr]
  from pd(9)[OF r0] obtain e0 U where bs: "bs_env ?\<rho> e0 rb" and tyt: "e0 \<turnstile> inst ?\<rho> t : U"
    and tyu: "e0 \<turnstile> inst ?\<rho> u : U" by blast
  have u: "u = ?h \<degree>\<degree> snd (strip_comb u)" by (simp add: strip_comb_apps)
  from tyu[unfolded u[THEN arg_cong[of _ _ "inst ?\<rho>"]] inst_apps] obtain Vs where
    tyh: "e0 \<turnstile> inst ?\<rho> ?h : Vs \<Rrightarrow> U" by (rule list_app_typeE)
  have lbh: "\<not> loose_bvar ?h (ilength rb)" using pd(8) u by (metis loose_bvar_apps)
  have tvh: "ttvars ?h \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
    using ttvars_head[of u] pd(4,5) by (auto simp: head_of_strip_comb)
  from env_fastype_term[OF x(2) refl tyh bs lbh tvh] obtain T0 where
    T0: "env_fastype env (map snd rb) ?h = return T0" "tvars T0 \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  from body_type_term[OF x(2) refl T0(2)] obtain base where
    base: "body_type env T0 = return base" "tvars base \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  have T0': "ok (fastype env rb ?h) T0" using T0(1) by (simp add: fastype_def return_def)
  have base': "ok (body_type env T0) base" using base(1) by (simp add: return_def)
  note pb = pair_base[OF ei p st bt len T0' base' base(2) r0(1) tyt]
  have cb: "cert_typ alg ar (tnorm ?\<theta> base)" using bs_env_cert[OF bs tyu pd(8)] pb(1) by simp
  have tya: "e0 \<tturnstile> map (inst ?\<rho>) targs : map (tsubst ?\<rho>) Ts" by (rule pb(3))
  have "\<forall>s\<in>set targs. \<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
      ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
  proof
    fix s assume s: "s \<in> set targs"
    then obtain i where i: "i < length targs" "s = targs ! i" by (auto simp: in_set_conv_nth)
    from typings_nth[OF tya] i have "e0 \<turnstile> map (inst ?\<rho>) targs ! i : map (tsubst ?\<rho>) Ts ! i" by auto
    with i have "e0 \<turnstile> inst ?\<rho> s : map (tsubst ?\<rho>) Ts ! i" by simp
    then show "\<exists>e U. bs_env ?\<rho> e rb \<and> e \<turnstile> inst ?\<rho> s : U \<and> \<not> loose_bvar s (ilength rb) \<and>
        ttvars s \<union> btvars rb \<subseteq> tvars_env ?\<theta> \<union> A"
      using bs hv(4) s pd(5) by blast
  qed
  from mapM_fastype_term[OF ei this] obtain Ts' where
    Ts': "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  have ts: "map (tsubst ?\<rho>) Ts' = map (tsubst ?\<rho>) Ts"
    by (rule mapM_fastype_types[OF _ r0(1) bs tya]) (use Ts'(1) in \<open>simp add: return_def\<close>)
  have cTs: "\<forall>T\<in>set Ts. cert_typ alg ar (tsubst ?\<rho> T)"
    by (rule mf_cert_targs[OF bs tya]) (use hv(4) in blast)
  have "\<forall>T\<in>set Ts'. cert_typ alg ar (tnorm ?\<theta> T)"
  proof
    fix T' assume "T' \<in> set Ts'"
    then have "tsubst ?\<rho> T' \<in> set (map (tsubst ?\<rho>) Ts)" using ts by (metis image_eqI list.set_map)
    then show "cert_typ alg ar (tnorm ?\<theta> T')" using cTs by auto
  qed
  with T0 base Ts' cb show ?thesis by (auto simp: fastype_def)
qed

lemma match1_proj_fin:
  assumes cfg: "cfg_alg cfg = alg" and finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar (tnorm (tyenv env) base)"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    and stT: "ok (strip_type env (Ts' ! k)) (Us, bary)" and tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A"
    and tvbary: "tvars bary \<subseteq> tvars_env (tyenv env) \<union> A"
    and cTk: "cert_typ alg ar (tnorm (tyenv env) (Ts' ! k))"
    and tl: "fin cfg tail (copy_ok A env (v, T) Ts)"
  shows "cuok (match1_proj cfg vname env ((rb, t, u) # dps) base Ts' bvar (Us, bary) p tail)
    (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
proof -
  let ?\<theta> = "tyenv env"
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  note gs = gentvars_simps[OF g]
  let ?A = "A \<union> ntv Cs" and ?K = "K \<union> ntv Cs"
  have si0: "sinv ?A ?K X env0 ((rb, t, u) # dps)" by (rule sinv_gentvars[OF si g])
  have ei0: "einv ?A ?K env0" using si0 by (simp add: sinv_def)
  have Cs: "\<forall>C\<in>set Cs. \<exists>a. C = TVar a []" using gs(6) by blast
  have cbary: "cert_typ alg ar (tnorm ?\<theta> bary)"
  proof -
    have "tsubst (rho0 env) (Ts' ! k) = map (tsubst (rho0 env)) Us \<Rrightarrow> tsubst (rho0 env) bary"
      by (rule strip_type_sound[OF stT einv_rho0(1)[of A K]]) (use si in \<open>simp add: sinv_def\<close>)
    with cTk show ?thesis by (simp add: cert_typ_funs)
  qed
  have cC: "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)"
    using Cs cert_tnorm[OF ei0] by (auto simp: cert_typ_def sort_ok_def)
  have inner: "cuok (bindW (proj_unify cfg base bary Cs env0) (\<lambda>env'.
      case make_args vname Ts' env' (Us @ Cs) of (env'', args) \<Rightarrow>
        returnW (S_Append (S_Single (El_C (list_comb bvar args) env'' ((rb, t, u) # dps))) tail)))
      (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
  proof (rule cuok_bindW[OF proj_unify_sinv[OF cfg finite_UnI[OF finK finite_ntv] si0]])
    show "tvars base \<subseteq> tvars_env (tyenv env0) \<union> ?A" "tvars bary \<subseteq> tvars_env (tyenv env0) \<union> ?A"
      using tvb tvbary gs(2) by auto
    show "\<forall>C\<in>set Cs. tvars C \<subseteq> tvars_env (tyenv env0) \<union> ?A" by (auto simp: ntv_def)
    show "cert_typ alg ar (tnorm (tyenv env0) base)" "cert_typ alg ar (tnorm (tyenv env0) bary)"
      using cb cbary gs(2) by simp_all
    show "\<forall>C\<in>set Cs. cert_typ alg ar (tnorm (tyenv env0) C)" by (rule cC)
    fix env' assume post: "sinv ?A ?K X env' ((rb, t, u) # dps) \<and> tenv env' = tenv env0 \<and> extends env0 env' \<and>
      tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env') \<and> tnew ?A env0 ?A env' \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> bary = tsubst \<rho> (Cs \<Rrightarrow> base))"
    obtain env'' args where ma: "make_args vname Ts' env' (Us @ Cs) = (env'', args)"
      by (cases "make_args vname Ts' env' (Us @ Cs)")
    have ext0: "extends env env0" using gs by (simp add: extends_def)
    have tn: "tnew A env ?A env'"
      by (rule tnew_trans[OF tnew_gentvars[OF g]]) (use post gs(3) in auto)
    have "copy_ok A env (v, T) Ts (El_C (list_comb bvar args) env'' ((rb, t, u) # dps))"
      by (rule proj_copy_ok[OF finX finK si fr st bt len T0 base tvb Ts' tvTs' hk stT tvUs Cs _ _ _ _ tn _ ma])
        (use post gs ext0 extends_trans in auto)
    then show "cuok (case make_args vname Ts' env' (Us @ Cs) of (env'', args) \<Rightarrow>
        returnW (S_Append (S_Single (El_C (list_comb bvar args) env'' ((rb, t, u) # dps))) tail))
      (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
      using ma tl by (simp add: fin_Append fin_Single)
  qed
  show ?thesis unfolding match1_proj_def g prod.case
    by (rule cuok_handle_CANTUNIFY_ret[OF inner]) (simp_all add: tl)
qed

lemma match1_projs_fin:
  assumes cfg: "cfg_alg cfg = alg" and finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
    and T0: "ok (fastype env rb (fst (strip_comb u))) T0" and base: "ok (body_type env T0) base"
    and tvb: "tvars base \<subseteq> tvars_env (tyenv env) \<union> A" and cb: "cert_typ alg ar (tnorm (tyenv env) base)"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" and tvTs': "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and cTs': "\<forall>T\<in>set Ts'. cert_typ alg ar (tnorm (tyenv env) T)"
    and tl: "fin cfg tail (copy_ok A env (v, T) Ts)"
  shows "\<forall>q\<in>set projs. \<exists>k<length targs. q = (Bound (integer_of_nat (length targs - 1 - k)), Ts' ! k, targs ! k) \<Longrightarrow>
    cuok (match1_projs cfg vname env ((rb, t, u) # dps) base Ts' projs tail) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
proof (induction projs)
  case Nil
  then show ?case using tl by simp
next
  case (Cons q projs)
  let ?\<theta> = "tyenv env"
  have ei: "einv A K env" using si by (simp add: sinv_def)
  obtain bvar T' targ where q: "q = (bvar, T', targ)" by (cases q)
  from Cons.prems q obtain k where hk: "k < length targs" "bvar = Bound (integer_of_nat (length targs - 1 - k))"
    "T' = Ts' ! k" by auto
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD)
  have T'in: "T' \<in> set Ts'" using hk lTs' by simp
  have tvT': "tvars T' \<subseteq> tvars_env ?\<theta> \<union> A" using tvTs' T'in by blast
  from binder_types_term[OF einvD(2)[OF ei] refl tvT'] obtain Us where bU: "binder_types env T' = return Us" by blast
  from body_type_term[OF einvD(2)[OF ei] refl tvT'] obtain bary where
    bB: "body_type env T' = return bary" "tvars bary \<subseteq> tvars_env ?\<theta> \<union> A" by blast
  have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
    using mf_binder_types_sound[OF bU[unfolded return_def] refl einvD(6)[OF ei]] tvT' by blast
  have sT: "strip_type env T' = return (Us, bary)" using bU bB by (simp add: strip_type_def)
  have IH: "cuok (match1_projs cfg vname env ((rb, t, u) # dps) base Ts' projs tail) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
    by (rule Cons.IH) (use Cons.prems in simp)
  have fo: "fin cfg b0 (copy_ok A env (v, T) Ts) \<Longrightarrow>
      cuok (foldrW (match1_proj cfg vname env ((rb, t, u) # dps) base Ts' bvar (Us, bary)) ps b0)
        (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))" for ps b0
  proof (induction ps)
    case (Cons p ps)
    show ?case
      by (simp, rule cuok_bindW[OF Cons.IH[OF Cons.prems]],
          rule match1_proj_fin[OF cfg finX finK si fr st bt len T0 base tvb cb Ts' tvTs' hk(1,2) _ tvUs bB(2)])
        (use sT hk(3) cTs' T'in in \<open>simp_all add: return_def\<close>)
  qed simp
  show ?case unfolding q match1_projs.simps
    by (rule cuok_liftM_return[OF sT], rule cuok_bindW[OF IH]) (simp add: fo)
qed

theorem match1_fin:
  assumes cfg: "cfg_alg cfg = alg" and finX: "finite X" and finK: "finite K"
    and si: "sinv A K X env ((rb, t, u) # dps)" and fr: "fr_shape env (rb, t, u)"
    and st: "strip_comb t = (Var v T, targs)" and bt: "binder_types env T = return Ts" and len: "length Ts = length targs"
  shows "cuok (match1 cfg vname rb targs u env ((rb, t, u) # dps)) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
proof -
  let ?\<theta> = "tyenv env" and ?h = "fst (strip_comb u)" and ?dps = "(rb, t, u) # dps"
  have ei: "einv A K env" using si by (simp add: sinv_def)
  from match1_types[OF si fr st bt len] obtain T0 base Ts' where
    ty: "fastype env rb ?h = return T0" "body_type env T0 = return base"
      "tvars T0 \<subseteq> tvars_env ?\<theta> \<union> A" "tvars base \<subseteq> tvars_env ?\<theta> \<union> A"
      "mapM (fastype env rb) targs = return Ts'" "\<forall>T\<in>set Ts'. tvars T \<subseteq> tvars_env ?\<theta> \<union> A"
      "cert_typ alg ar (tnorm ?\<theta> base)" "\<forall>T\<in>set Ts'. cert_typ alg ar (tnorm ?\<theta> T)"
    by blast
  have T0: "ok (fastype env rb ?h) T0" and base: "ok (body_type env T0) base"
    and Ts': "ok (mapM (fastype env rb) targs) Ts'" using ty by (simp_all add: return_def)
  have lTs': "length Ts' = length targs" using Ts' by (simp add: ok_mapM list_all2_lengthD)
  from make_projs_term[OF lTs', of u targs] obtain projs where mp: "okW (make_projs u targs Ts' targs) projs" by blast
  note mpp = mf_make_projs_props[OF mp]
  let ?imit = "case ?h of
      Const _ _ \<Rightarrow> do {
        Us \<leftarrow> liftM (binder_types env T0);
        (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
          returnW (S_Single (El_C (list_comb ?h args) env' ?dps)))}
    | Free _ _ \<Rightarrow> do {
        Us \<leftarrow> liftM (binder_types env T0);
        (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
          returnW (S_Single (El_C (list_comb ?h args) env' ?dps)))}
    | _ \<Rightarrow> returnW S_Empty"
  have imit_c: "cuok (do {
        Us \<leftarrow> liftM (binder_types env T0);
        (case make_args vname Ts' env Us of (env', args) \<Rightarrow>
          returnW (S_Single (El_C (list_comb ?h args) env' ?dps)))}) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
    if hc: "?h = Const c C \<or> ?h = Free c C" for c C
  proof -
    from binder_types_term[OF einvD(2)[OF ei] refl ty(3)] obtain Us where bU: "binder_types env T0 = return Us" by blast
    have tvUs: "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
      using mf_binder_types_sound[OF bU[unfolded return_def] refl einvD(6)[OF ei]] ty(3) by blast
    obtain env' args where ma: "make_args vname Ts' env Us = (env', args)" by (cases "make_args vname Ts' env Us")
    have "copy_ok A env (v, T) Ts (El_C (list_comb ?h args) env' ?dps)"
      by (rule imit_copy_ok[OF finX finK si fr st bt len T0 base ty(4) Ts' ty(6) hc _ tvUs ma])
        (use bU in \<open>simp add: return_def\<close>)
    then show ?thesis by (intro cuok_liftM_return[OF bU]) (simp add: ma fin_Single)
  qed
  have imit: "cuok ?imit (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
    using imit_c by (cases ?h) simp_all
  have mpr: "cuok (match1_projs cfg vname env ?dps base Ts' (rev projs) imit) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
    if "fin cfg imit (copy_ok A env (v, T) Ts)" for imit
    by (rule match1_projs_fin[OF cfg finX finK si fr st bt len T0 base ty(4,7) Ts' ty(6,8) that]) (use mpp in auto)
  have "cuok (bindW (make_projs u targs Ts' targs) (\<lambda>projs. bindW ?imit
      (match1_projs cfg vname env ?dps base Ts' (rev projs)))) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
  proof (rule cuok_bindW[OF cuok_okW[OF mp TrueI]])
    fix projs' assume "okW (make_projs u targs Ts' targs) projs'"
    then have "projs' = projs" using mp by auto
    then show "cuok (bindW ?imit (match1_projs cfg vname env ?dps base Ts' (rev projs'))) (\<lambda>s. fin cfg s (copy_ok A env (v, T) Ts))"
      using mpr by (intro cuok_bindW[OF imit]) simp
  qed
  then show ?thesis unfolding match1_def Let_def
    by (intro cuok_liftM_return[OF ty(1)] cuok_liftM_return[OF ty(2)] cuok_liftM_return[OF ty(5)])
qed

end


end
