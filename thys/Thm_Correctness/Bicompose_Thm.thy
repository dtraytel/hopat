section \<open>The results of \<open>bicompose_aux\<close> are theorems\<close>

theory Bicompose_Thm
  imports Bicompose_Complete
begin

text \<open>
  The results of \<open>bicompose_aux\<close> for a proof state and a rule that satisfy the invariant of
  theorems satisfy it again: they are well-typed, type variables and variables with the same name
  have the same sort and type, and their indices are nonnegative and at most the maximal index of
  the environment of the unifier. The components of a result are normalized by the environment of
  the unifier; a normalized term is a \<open>\<beta>\<close>-reduct of the application of the environment
  (theorem \<open>norm_term_env_apply\<close>), which is an instance by the canonical solution
  (\<open>env_apply_tsol0\<close>).
\<close>


subsection \<open>Normalized terms\<close>

lemma typs_lift: "typs (lift t k) = typs t"
  by (induction t arbitrary: k) auto

lemma typs_subst: "typs (s[t/k]) \<subseteq> typs s \<union> typs t"
proof (induction s arbitrary: t k)
  case (Abs a T s)
  then show ?case using Abs.IH[of "lift t 0" "k + 1"] by (auto simp: typs_lift)
next
  case (App s1 s2)
  have "typs (s1[t/k]) \<subseteq> typs s1 \<union> typs t" "typs (s2[t/k]) \<subseteq> typs s2 \<union> typs t"
    by (rule App.IH)+
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma beta_typs: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> typs t \<subseteq> typs s"
  by (induction rule: beta.induct) (use typs_subst in auto)

lemma beta_reds_typs: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> typs t \<subseteq> typs s"
  by (induction rule: rtranclp_induct) (use beta_typs in auto)

context pure_sig
begin

lemma typing_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_beta)

text \<open>The variables of a theorem after the application of a type environment:\<close>

definition vimg :: "tyenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "vimg \<theta> S = (\<lambda>(x, T). (x, tnorm \<theta> T)) ` S"

lemma vimg_mono: "S \<subseteq> S' \<Longrightarrow> vimg \<theta> S \<subseteq> vimg \<theta> S'"
  by (auto simp: vimg_def)

lemma vtcons_vimg:
  assumes "vcons (tnorm_inst \<theta>) S"
  shows "vtcons (vimg \<theta> S)"
  unfolding vtcons_def
proof (intro allI impI)
  fix x T U assume "(x, T) \<in> vimg \<theta> S" "(x, U) \<in> vimg \<theta> S"
  then obtain T0 U0 where "(x, T0) \<in> S" "T = tnorm \<theta> T0" "(x, U0) \<in> S" "U = tnorm \<theta> U0"
    by (auto simp: vimg_def)
  with vconsD[OF assms, of x T0 U0] show "T = U" by simp
qed

lemma fst_vimg [simp]: "fst ` vimg \<theta> S = fst ` S"
  by (force simp: vimg_def)

text \<open>Unbound variables with unbound types are fixed by the application:\<close>

lemma vimg_unb: "tacyc (tyenv env) \<Longrightarrow> unb env X \<Longrightarrow> vars X \<subseteq> S \<Longrightarrow> vars X \<subseteq> vimg (tyenv env) S"
proof
  fix v assume ac: "tacyc (tyenv env)" and u: "unb env X" and S: "vars X \<subseteq> S" and v: "v \<in> vars X"
  obtain x T where vT: "v = (x, T)" by (cases v)
  have "\<forall>p\<in>tvars T. vt_lookup (tyenv env) (fst p) = None"
    using u v vT vtvars_ttvars[of x T X] by (auto simp: unb_def)
  then have "tnorm (tyenv env) T = T" by (intro tnorm_unbound_id ac) auto
  with S v vT show "v \<in> vimg (tyenv env) S" by (force simp: vimg_def)
qed

lemma tsol0_unb:
  assumes "\<forall>p\<in>tvars T. vt_lookup \<theta> (fst p) = None"
  shows "tsubst (tsol0 \<theta>) T = T"
proof -
  have "tsubst (tsol0 \<theta>) T = tsubst TVar T"
    by (rule tsubst_cong) (use assms in \<open>auto simp: tsol0_def\<close>)
  then show ?thesis by simp
qed

lemma inst_tsol0_unb: "unb env t \<Longrightarrow> inst (tsol0 (tyenv env)) t = t"
proof -
  assume u: "unb env t"
  have "inst (tsol0 (tyenv env)) t = inst TVar t"
  proof (rule inst_cong)
    fix U assume "U \<in> typs t"
    then have "\<forall>p\<in>tvars U. vt_lookup (tyenv env) (fst p) = None" using u by (auto simp: unb_def ttvars_def)
    then show "tsubst (tsol0 (tyenv env)) U = tsubst TVar U" using tsol0_unb by simp
  qed
  then show ?thesis by simp
qed

text \<open>A normalized term:\<close>

lemma norm_term_props:
  assumes ei: "einv A K env" and wi: "winv env Y" and vX: "vars X \<subseteq> Y \<union> evars env"
    and tX: "ttvars X \<subseteq> tvars_env (tyenv env) \<union> A" and ty: "e \<turnstile> X : T"
    and lb: "\<not> loose_bvar X k" "0 \<le> k" and nt: "ok (norm_term env X) X'"
  shows "ienv (tsol0 (tyenv env)) e \<turnstile> X' : tsubst (tsol0 (tyenv env)) T" "\<not> loose_bvar X' k"
    "vars X' \<subseteq> vimg (tyenv env) (vars X \<union> evars env)" "ttvars X' \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  let ?\<theta> = "tyenv env"
  let ?\<rho> = "tsol0 ?\<theta>" and ?\<sigma> = "esol (tsol0 ?\<theta>) env"
  note e = einvD[OF ei] and c = canonical_solution[OF ei wi]
  have nac: "acyc env" "closed_env env" "tacyc ?\<theta>" using e(3,6) wt_env_closed_env[OF c(2)] by blast+
  have red: "env_apply env X \<rightarrow>\<^sub>\<beta>\<^sup>* X'" by (rule norm_term_env_apply(1)[OF nt nac])
  have app: "env_apply env X = ap ?\<rho> ?\<sigma> X"
  proof (rule env_apply_tsol0[OF e(1) e(3) tX])
    have "vcons ?\<rho> (Y \<union> evars env)" using c(3) by (simp add: vinv_def)
    then show "vcons ?\<rho> (vars X \<union> evars env)" by (rule vcons_mono) (use vX in blast)
  qed
  have ws: "wt_subst ?\<sigma>" by (rule solutionD(3)[OF c(1)])
  show "ienv ?\<rho> e \<turnstile> X' : tsubst ?\<rho> T"
    by (rule typing_beta_reds[OF red]) (simp add: app typing_ap_inst[OF ty c(4) ws])
  have "\<not> loose_bvar (ap ?\<rho> ?\<sigma> X) k" using lb ws by (simp add: gsubst_def)
  then show "\<not> loose_bvar X' k" using mcp_loose_reds[OF red lb(2)] app by simp
  have "vars (env_apply env X) \<subseteq> vimg ?\<theta> (vars X \<union> evars env)"
    using vars_unf_sub[OF nac(1), of X] by (auto simp: env_apply_def vars_inst vimg_def)
  then show "vars X' \<subseteq> vimg ?\<theta> (vars X \<union> evars env)" using beta_reds_vars[OF red] by blast
  have "ttvars (env_apply env X) \<subseteq> tvars_env ?\<theta> \<union> A"
  proof
    fix p assume "p \<in> ttvars (env_apply env X)"
    then obtain U where U: "U \<in> typs (unf env X)" "p \<in> tvars (tnorm ?\<theta> U)"
      by (auto simp: env_apply_def ttvars_def typs_inst)
    have "tvars U \<subseteq> tvars_env ?\<theta> \<union> A"
    proof (cases "U \<in> typs X")
      case True
      with tX show ?thesis by (auto simp: ttvars_def)
    next
      case False
      with U(1) typs_unf[OF nac(1), of X] obtain x V u where "vt_lookup (tenv env) x = Some (V, u)" "U \<in> typs u"
        by blast
      with tvinvD(2)[OF e(1) this(1)] show ?thesis by (auto simp: ttvars_def)
    qed
    with U(2) tvars_tnorm[OF nac(3), of U] show "p \<in> tvars_env ?\<theta> \<union> A" by blast
  qed
  then show "ttvars X' \<subseteq> tvars_env ?\<theta> \<union> A"
    using beta_reds_typs[OF red] by (auto simp: ttvars_def)
qed


lemma tvars_tsol0: "tacyc \<theta> \<Longrightarrow> tvars (tsubst (tsol0 \<theta>) T) \<subseteq> tvars T \<union> tvars_env \<theta>"
proof (induction T)
  case (TVar v S)
  show ?case
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S' U where b: "b = (S', U)" by force
    have "tvars (tnorm \<theta> U) \<subseteq> tvars_env \<theta>"
      using tvars_tnorm[OF TVar, of U] tvars_envI2[OF Some[unfolded b]] by blast
    then show ?thesis using Some b by (auto simp: tsol0_def)
  qed (simp add: tsol0_def)
qed auto

text \<open>A term normalized but for the assumptions that \<^const>\<open>norm_term_skip\<close> skips:\<close>

lemma norm_term_skip_props:
  "okT (norm_term_skip env n X) X' \<Longrightarrow> einv A K env \<Longrightarrow> winv env Y \<Longrightarrow> vars X \<subseteq> Y \<union> evars env \<Longrightarrow>
    ttvars X \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> e \<turnstile> X : propT \<Longrightarrow> \<not> loose_bvar X k \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    skip_unb env n X \<Longrightarrow>
    ienv (tsol0 (tyenv env)) e \<turnstile> X' : propT \<and> \<not> loose_bvar X' k \<and>
    vars X' \<subseteq> vimg (tyenv env) (vars X \<union> evars env) \<and> ttvars X' \<subseteq> tvars_env (tyenv env) \<union> A"
proof (induction env n X arbitrary: e k X' rule: norm_term_skip.induct)
  case (1 env n t)
  note ei = "1.prems"(2) and wi = "1.prems"(3)
  let ?\<theta> = "tyenv env" let ?\<rho> = "tsol0 ?\<theta>"
  note e = einvD[OF ei] and c = canonical_solution[OF ei wi]
  have ac: "tacyc ?\<theta>" by (rule e(6))
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems"(1) have "ok (norm_term env t) X'" by (simp add: norm_term_skip.simps)
    from norm_term_props[OF ei wi "1.prems"(4,5,6,7,8) this] show ?thesis by simp
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from "1.prems"(1) n aTb obtain T' b' where T': "ok (norm_type ?\<theta> T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "X' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      note ty = typing_dest_all[OF "1.prems"(6) aTb]
      have sk: "skip_unb env n b" using "1.prems"(9) n aTb by (simp add: skip_unb.simps[of env n t])
      have vb: "vars b \<subseteq> vars t" and tb: "ttvars b \<subseteq> ttvars t" and tT: "tvars T \<subseteq> ttvars t"
        using ty(1) by (auto simp: all_const_def)
      have lb: "\<not> loose_bvar b (k + 1)" using "1.prems"(7) ty(1) by (simp add: all_const_def)
      from T' have T'': "okT (liftMT (norm_type ?\<theta> T)) T'" by simp
      from "1.IH"(2)[OF n aTb refl refl T'' b' ei wi _ _ ty(5) lb _ sk] "1.prems"(4,5,8) vb tb
      have ib: "(ienv ?\<rho> e)\<langle>0:tsubst ?\<rho> T\<rangle> \<turnstile> b' : propT" "\<not> loose_bvar b' (k + 1)"
        "vars b' \<subseteq> vimg ?\<theta> (vars b \<union> evars env)" "ttvars b' \<subseteq> tvars_env ?\<theta> \<union> A"
        by (auto simp: tsubst_shift)
      have "tsubst ?\<rho> T' = T'" by (rule tsol0_unb) (use norm_type_unb[OF T'] in blast)
      moreover have "tsubst ?\<rho> T' = tsubst ?\<rho> T" by (rule norm_type_sound[OF T' c(5)])
      ultimately have TT: "T' = tsubst ?\<rho> T" by simp
      have cT: "cert_typ alg ar (all_type T')" "cert_typ alg ar T'"
        using cert_typ_tsubst[OF ty(3) c(4)] cert_typ_tsubst[OF ty(4) c(4)] TT by (simp_all add: all_type_def propT_def)
      have "tvars T' \<subseteq> tvars_env ?\<theta> \<union> A"
        using TT tvars_tsol0[OF ac, of T] tT "1.prems"(5) by blast
      moreover have "tvars (all_type T') = tvars T'" by (simp add: all_type_def propT_def)
      moreover have "vimg ?\<theta> (vars b \<union> evars env) \<subseteq> vimg ?\<theta> (vars t \<union> evars env)"
        by (rule vimg_mono) (use vb in blast)
      moreover have "vars (all_const T') = {}" "\<not> loose_bvar (all_const T') k"
        "ttvars (all_const T') = tvars (all_type T')"
        by (simp_all add: all_const_all_type)
      ultimately show ?thesis using ib cT TT by (auto simp: t' typing_all_const)
    next
      case None
      with "1.prems"(1) n obtain H B where HB: "dest_imp t = Some (H, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with "1.prems"(1) n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "X' = mk_implies H B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      note ty = typing_dest_imp[OF "1.prems"(6) HB]
      from "1.prems"(9) n None HB have uH: "unb env H" and sk: "skip_unb env (n - 1) B"
        by (simp_all add: skip_unb.simps[of env n t])
      have vHB: "vars H \<subseteq> vars t" "vars B \<subseteq> vars t" and tHB: "ttvars H \<subseteq> ttvars t" "ttvars B \<subseteq> ttvars t"
        and lHB: "\<not> loose_bvar H k" "\<not> loose_bvar B k"
        using ty(1) "1.prems"(7) by (auto simp: implies_def)
      from "1.IH"(1)[OF n None HB refl B' ei wi _ _ ty(5) lHB(2) "1.prems"(8) sk] "1.prems"(4,5) vHB tHB
      have iB: "ienv ?\<rho> e \<turnstile> B' : propT" "\<not> loose_bvar B' k"
        "vars B' \<subseteq> vimg ?\<theta> (vars B \<union> evars env)" "ttvars B' \<subseteq> tvars_env ?\<theta> \<union> A" by auto
      have tH: "ienv ?\<rho> e \<turnstile> H : propT"
        using typing_inst[OF ty(4) cert_inst_inst_ok[OF c(4)]] inst_tsol0_unb[OF uH] by simp
      have "vars H \<subseteq> vimg ?\<theta> (vars t \<union> evars env)" by (rule vimg_unb[OF ac uH]) (use vHB in blast)
      moreover have "ttvars implies = {}" by (simp add: implies_def imp_type_def propT_def)
      moreover have "vimg ?\<theta> (vars B \<union> evars env) \<subseteq> vimg ?\<theta> (vars t \<union> evars env)"
        by (rule vimg_mono) (use vHB in blast)
      moreover have "vars implies = {}" "\<not> loose_bvar implies k" by (simp_all add: implies_def)
      ultimately show ?thesis
        using iB tH ty(3) lHB(1) "1.prems"(5) tHB by (auto simp: t' mk_implies_def typing_implies)
    qed
  qed
qed

end

end
