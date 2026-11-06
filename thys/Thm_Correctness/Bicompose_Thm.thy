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
    and tX: "ttvars X \<subseteq> tvars_env (tyenv env) \<union> A" and ty: "e \<turnstile> inst (tsol0 (tyenv env)) X : T"
    and lb: "\<not> loose_bvar X k" "0 \<le> k" and nt: "ok (norm_term env X) X'"
  shows "e \<turnstile> X' : T" "\<not> loose_bvar X' k"
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
  show "e \<turnstile> X' : T"
    by (rule typing_beta_reds[OF red]) (simp add: app ap_def typing_vsubst[OF ty ws])
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
    have "ienv ?\<rho> e \<turnstile> inst ?\<rho> t : propT"
      using typing_inst[OF "1.prems"(6) cert_inst_inst_ok[OF c(4)]] by simp
    from norm_term_props[OF ei wi "1.prems"(4,5) this "1.prems"(7,8) \<open>ok (norm_term env t) X'\<close>]
    show ?thesis by simp
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



subsection \<open>The new premises of a result\<close>

text \<open>
  The new premises of a closure come from premises \<open>As0\<close> of the rule; an index-preserving map
  \<open>h\<close> undoes their renaming and fixes the variables of the problem, and the lifted assumptions
  that the normalization skips are those of the subgoal.
\<close>

lemma itsok_newAs:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and its: "itsok sp A1o na tus"
    and state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)"
    and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  defines "nlift \<equiv> count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  obtains As0 h where "set As0 \<subseteq> set (rev rAs)"
    "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
    "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" "\<forall>(x, T)\<in>dvars (tdps tus). h x = x"
    "lifted \<Longrightarrow> 0 \<le> nlift \<and>
      (\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?R = "list_implies (rev rAs) B"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have cs: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bi ctx = Bi"
    "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi" "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have spe: "sp_eres sp = eres_flg" "sp_vl sp = vl" "sp_ctx sp = ctx" "sp_rAs sp = rAs" by (simp_all add: sp')
  have wS: "wtp ?S" "ibelow smax ?S" and wR: "wtp ?R" using state rule by (simp_all add: wt_thm_def)
  have wAs: "\<forall>X\<in>set (rev rAs). wtp X" using wtp_list_implies[OF wR] by simp
  have ibBi: "ibelow smax Bi" using wS(2) by simp
  have ibst: "\<forall>(t, u)\<in>set stpairs. ibelow smax t \<and> ibelow smax u" using state by (auto simp: wt_thm_def)
  have cnt0: "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
  have vBBi: "vars (snd BBi) \<subseteq> vars Bi"
  proof (cases lifted)
    case True
    from lr[OF True] obtain p Bi0 As0' B0 where Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" and B: "B = lift_pre p B0" by (rule lifted_rule_lift_pre)
    have "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    then show ?thesis by (simp add: Bi vars_lift_pre)
  qed (simp add: BBi_def)
  text \<open>A map that fixes the variables of the proof state and those of the problem of the rule:\<close>
  have h_tps: "\<forall>(x, T)\<in>dvars (tdps (BBi # rtpairs @ stpairs)). h x = x"
    if h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" and h4: "\<forall>(x, T)\<in>vars (fst BBi). h x = x"
      and h5: "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" for h
  proof (clarify)
    fix x T assume "(x, T) \<in> dvars (tdps (BBi # rtpairs @ stpairs))"
    then consider "(x, T) \<in> vars (fst BBi)" | "(x, T) \<in> vars (snd BBi)"
      | t u where "(t, u) \<in> set rtpairs" "(x, T) \<in> vars t \<union> vars u"
      | t u where "(t, u) \<in> set stpairs" "(x, T) \<in> vars t \<union> vars u"
      by (cases BBi) (auto simp: dvars_def)
    then show "h x = x"
    proof cases
      case 1
      with h4 show ?thesis by blast
    next
      case 2
      with vBBi have "(x, T) \<in> vars Bi" by blast
      with ibBi have "snd x \<le> smax" by (rule ibelow_var)
      with h3 show ?thesis by blast
    next
      case 3
      with h5 show ?thesis by blast
    next
      case 4
      with ibst have "ibelow smax t" "ibelow smax u" by blast+
      with 4(2) have "snd x \<le> smax" by (auto intro: ibelow_var)
      with h3 show ?thesis by blast
    qed
  qed
  text \<open>The generic part, for the premises \<open>As0\<close> of the rule that are kept:\<close>
  note obt = that
  have main: thesis
    if na: "okT (newAs vl ctx As0 n dps tps1) na" and As0: "set As0 \<subseteq> set (rev rAs)"
      and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
      and hid: "\<And>h. \<forall>x. snd x \<le> smax \<longrightarrow> h x = x \<Longrightarrow> \<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x \<Longrightarrow>
        \<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x \<Longrightarrow>
        (\<not> lifted \<Longrightarrow> \<forall>x. h x = x) \<Longrightarrow> \<forall>(x, T)\<in>dvars (tdps tus). h x = x"
      and nl: "lifted \<Longrightarrow> 0 \<le> nlift \<and> nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
    for As0 n dps tps1
  proof -
    obtain h where
      p1: "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)" and
      p2: "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x" and
      p3: "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> h x = x" and
      p4: "\<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x" and
      p5: "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" and
      p7: "\<not> bc_lifted ctx \<Longrightarrow> \<forall>x. h x = x"
    proof (rule newAs_props[OF na])
      show "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" using lr0 by (simp add: cs)
      show "ibelow (bc_smax ctx) (bc_Bi ctx)" using ibBi by (simp add: cs)
      show "\<forall>A\<in>set As0. wtp A" using As0 wAs by blast
    qed (rule vl, blast)
    have sk: "0 \<le> nlift \<and>
        (\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
      if lf: lifted
    proof -
      have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> typs H = typs H0"
        using newAs_skip[OF na _ _ vl, where k = nlift] lf lr0 nl by (simp add: cs)
      then show ?thesis
        using ibelow_spine_hyps[OF ibBi] nl[OF lf] by (fastforce simp: ibelow_def ttvars_def)
    qed
    have dv: "\<forall>(x, T)\<in>dvars (tdps tus). h x = x"
      by (rule hid) (use p3 p4 p5 p7 in \<open>simp_all add: cs\<close>)
    show thesis by (rule obt[OF As0 p1 p2 p3[unfolded cs] dv sk])
  qed
  show thesis
  proof (cases eres_flg)
    case False
    from its False obtain tps1 where res: "tus = BBi # rtpairs @ stpairs"
      "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      unfolding itsok_def spe by (auto simp: cs)
    show thesis
    proof (rule main[OF res(2) _ lr])
      fix h assume h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" and h4: "\<forall>(t, u)\<in>set [BBi]. \<forall>(x, T)\<in>vars t. h x = x"
        and h5: "\<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
      have "\<forall>(x, T)\<in>vars (fst BBi). h x = x" using h4 by (cases BBi) auto
      moreover have "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" using h5 by auto
      ultimately show "\<forall>(x, T)\<in>dvars (tdps tus). h x = x" using h_tps[OF h3] res(1) by blast
    next
      show "0 \<le> nlift \<and> nlift + (if 0 < (0::integer) \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
        using False cnt0 by (simp add: nlift_def)
    qed simp
  next
    case True
    from its True obtain n asm tps1 where eres: "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
      "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
      "okT (newAs vl ctx (er_As (eres_of sp)) n
        [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding itsok_def spe cs[symmetric] by blast
    have n1: "1 \<le> nat_of_integer n" using eres(1) by (simp add: integer_reps)
    obtain A1 As where rA: "rev rAs = A1 # As"
      using eres(2) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
      using rA ap by (simp_all add: eres_of_def asms_of_def sp' cs)
    have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using True by (simp add: nlift_def)
    have "ilength asms \<le> nlift + 1" by (rule assum_problems_length[OF ap]) (use cnt cnt0 in simp)
    moreover have "n \<le> ilength asms" using eres(2) e(2) by (simp add: ilength_eq integer_reps)
    ultimately have nc: "1 \<le> count_prems (strip_all_body Bi)" using cnt eres(1) by simp
    have asm: "asm \<in> set asms"
    proof -
      have "nat_of_integer n - 1 < length asms" using eres(2) n1 e(2) by simp
      then show ?thesis using eres(3) e(2) by simp
    qed
    have tus: "tus = (rlist_abs params asm, rlist_abs params concl) # BBi # rtpairs @ stpairs"
      using eres(4) e by (simp add: eres_prob_def sp' cs)
    have lrA: "lifted_rule smax Bi As B" if "lifted" using lr[OF that] rA by (auto dest: lifted_rule_Cons)
    have na: "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
      using eres(5) e by simp
    show thesis
    proof (rule main[OF na _ lrA])
      show "set As \<subseteq> set (rev rAs)" using rA by auto
      fix h assume h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x"
        and h4: "\<forall>(t, u)\<in>set [BBi, (rlist_abs params concl, rlist_abs params asm)]. \<forall>(x, T)\<in>vars t. h x = x"
        and h5: "\<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
        and h7: "\<not> lifted \<Longrightarrow> \<forall>x. h x = x"
      have a: "\<forall>(x, T)\<in>vars asm. h x = x"
      proof (cases lifted)
        case True
        from lr[OF True] obtain p Bi0 As0' and B0 :: pterm where Bi: "Bi = lift_pre p Bi0"
          and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "rev rAs = map (lift_pre p) As0'"
          by (rule lifted_rule_lift_pre)
        from rA As0 obtain A1' where A1: "A1 = lift_pre p A1'" by (cases As0') auto
        have "set asms \<subseteq> set (phyps p)"
          by (rule assum_problems_lift_pre[OF ok at _ ap[unfolded A1]]) (use cnt cnt0 Bi in simp_all)
        with asm have va: "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        have "\<forall>(x, T)\<in>vars asm. snd x \<le> smax"
        proof (clarify)
          fix x T assume "(x, T) \<in> vars asm"
          with va have "(x, T) \<in> vars Bi" by (auto simp: Bi vars_lift_pre)
          with ibBi show "snd x \<le> smax" by (rule ibelow_var)
        qed
        with h3 show ?thesis by blast
      qed (use h7 in blast)
      have "\<forall>(x, T)\<in>vars (fst BBi). h x = x" using h4 by (cases BBi) auto
      moreover have "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" using h5 by auto
      ultimately have "\<forall>(x, T)\<in>dvars (tdps (BBi # rtpairs @ stpairs)). h x = x" by (rule h_tps[OF h3])
      moreover have "\<forall>(x, T)\<in>vars (rlist_abs params concl). h x = x" using h4 by auto
      ultimately show "\<forall>(x, T)\<in>dvars (tdps tus). h x = x" using a by (auto simp: tus dvars_def)
    next
      show "0 \<le> nlift \<and> nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
        using cnt nc by auto
    qed
  qed
qed

end

end
