section \<open>Invariants of \<open>MATCH\<close>\<close>

text \<open>
  New type variables and new variables of \<open>MATCH\<close> in the invariants, and the types of the
  two sides of a flex-rigid pair.
\<close>

theory Unify_Match_Base
  imports Unify_Inv_Base Unify_Match_Sound
begin

subsection \<open>The types of the two sides of a pair\<close>

context pure_sig_gen
begin

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

subsection \<open>New variables\<close>

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

text \<open>The new variables of \<^const>\<open>make_args\<close> keep the invariant:\<close>

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

subsection \<open>Type variables of abstractions over types\<close>

lemma ttvars_types_abs: "ttvars (types_abs Ts u) = (\<Union>T\<in>set Ts. tvars T) \<union> ttvars u"
  by (induction Ts) auto

lemma evars_tenv: "tenv env' = tenv env \<Longrightarrow> evars env' = evars env"
  by (simp add: evars_def bnds_def)

end

end
