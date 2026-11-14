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

text \<open>The type variables and the indices of the variables of the new premises are those of \<open>As0\<close>:\<close>

lemma newAs_idx:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "\<forall>X\<in>set (na_As na @ na_oldAs na). ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
    (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
proof -
  let ?P = "\<lambda>X. ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
    (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
  have old: "?P A1" if A1: "A1 \<in> set (na_oldAs na)" for A1
    using newAs_struct(2)[OF na]
  proof (elim disjE conjE)
    assume "na_oldAs na = As0"
    with A1 show ?thesis by blast
  next
    let ?r = "rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0"
    assume lf: "bc_lifted ctx" and o: "na_oldAs na = map (strip_apply (ren_term ?r) (bc_Bi ctx)) As0"
    from lr[OF lf] obtain p Bi0 As0' B0 where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      by (rule lifted_rule_lift_pre)
    from A1 o obtain X where X: "X \<in> set As0'" "A1 = lift_pre p (ren_term ?r X)"
      by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
    have XA: "lift_pre p X \<in> set As0" using X(1) by (simp add: As0)
    have "ttvars A1 = ttvars (lift_pre p X)" by (simp add: X(2) ttvars_def typs_lift_pre_ren)
    moreover have "(\<lambda>v. snd (fst v)) ` vars A1 = (\<lambda>v. snd (fst v)) ` vars (lift_pre p X)"
      by (simp add: X(2) vars_lift_pre vars_ren_term image_Un image_image)
    ultimately show ?thesis using XA by blast
  qed
  have new: "?P A'" if A': "A' \<in> set (na_As na)" for A'
  proof -
    from list_all2_ex2[OF newAs_struct(1)[OF na] A'] obtain A1 where A1: "A1 \<in> set (na_oldAs na)"
      and f: "if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A'" by blast
    have "vars A' \<subseteq> vars A1 \<and> ttvars A' \<subseteq> ttvars A1"
    proof (cases "bc_flatten ctx")
      case True
      with f have "ok (flatten_params vl n A1) A'" by simp
      from flatten_params_vars[OF this vl] show ?thesis by simp
    next
      case False
      with f show ?thesis by simp
    qed
    with old[OF A1] show ?thesis by blast
  qed
  show ?thesis
  proof
    fix X assume "X \<in> set (na_As na @ na_oldAs na)"
    then consider "X \<in> set (na_As na)" | "X \<in> set (na_oldAs na)" by auto
    then show "?P X"
    proof cases
      case 1
      then show ?thesis by (rule new)
    next
      case 2
      then show ?thesis by (rule old)
    qed
  qed
qed

lemma itsok_newAs:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and its: "itsok sp A1o na tus"
    and state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)"
    and lr0: "lifted \<longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  defines "nlift \<equiv> count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  obtains As0 h where "set As0 \<subseteq> set (rev rAs)"
    "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
    "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" "\<forall>(x, T)\<in>dvars (tdps tus). h x = x"
    "lifted \<Longrightarrow> 0 \<le> nlift \<and>
      (\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
    "\<forall>X\<in>set (na_As na @ na_oldAs na). ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
      (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
    "\<forall>X\<in>set (na_oldAs na). wtp X"
proof -
  have lr: "lifted_rule smax Bi (rev rAs) B" if lifted using lr0 that by blast
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
    have ix: "\<forall>X\<in>set (na_As na @ na_oldAs na). ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
        (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
      by (rule newAs_idx[OF na _ vl]) (use lr0 in \<open>simp add: cs\<close>)
    have ow: "\<forall>X\<in>set (na_oldAs na). wtp X"
      by (rule newAs_oldAs_wtp[OF na, of B]) (use lr0 As0 wAs in \<open>auto simp: cs\<close>)
    show thesis by (rule obt[OF As0 p1 p2 p3[unfolded cs] dv sk ix ow])
  qed
  show thesis
  proof (rule itsok_newAs_data[OF sp its ibBi ibst lr nlift_def[THEN meta_eq_to_obj_eq] BBi_def ctx_def])
    fix As0 n dps tps1
    assume d: "okT (newAs vl ctx As0 n dps tps1) na" "set As0 \<subseteq> set (rev rAs)"
        "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
        "\<And>h. \<forall>x. snd x \<le> smax \<longrightarrow> h x = x \<Longrightarrow> \<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x \<Longrightarrow>
          \<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x \<Longrightarrow>
          (\<not> lifted \<Longrightarrow> \<forall>x. h x = x) \<Longrightarrow> \<forall>(x, T)\<in>dvars (tdps tus). h x = x"
        "0 \<le> nlift" "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
    show thesis by (rule main[OF d(1-4)]) (use d(5,6) in auto)
  qed
qed


subsection \<open>Theorems\<close>

text \<open>
  The invariant of theorems with maximal index \<open>m\<close>: they are well-typed, type variables and
  variables with the same name have the same sort and type, and indices are nonnegative.
\<close>

definition thm_inv :: "integer \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "thm_inv m hs tps P \<longleftrightarrow> wt_thm m hs tps P \<and> -1 \<le> m \<and> scons (tvars_thm tps P) \<and> vtcons (vars_thm tps P) \<and>
    (\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v))"

text \<open>The same without the condition that a name of a variable has one type:\<close>

definition thm_inv0 :: "integer \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "thm_inv0 m hs tps P \<longleftrightarrow> wt_thm m hs tps P \<and> -1 \<le> m \<and> scons (tvars_thm tps P) \<and>
    (\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v))"

lemma thm_inv_iff: "thm_inv m hs tps P \<longleftrightarrow> thm_inv0 m hs tps P \<and> vtcons (vars_thm tps P)"
  by (auto simp: thm_inv_def thm_inv0_def)

lemma thm_inv_inv0: "thm_inv m hs tps P \<Longrightarrow> thm_inv0 m hs tps P"
  by (simp add: thm_inv_iff)

lemma wt_thm_below:
  assumes "wt_thm m hs tps P"
  shows "v \<in> vars_thm tps P \<Longrightarrow> snd (fst v) \<le> m" "w \<in> tvars_thm tps P \<Longrightarrow> snd (fst w) \<le> m"
  using assms by (fastforce simp: wt_thm_def vars_thm_def tvars_thm_def ibelow_def)+

text \<open>
  A variable that occurs neither in the problem nor in the environment and whose index is not
  above the maximal index does not occur in the results (as \<open>unifiers_fresh\<close>):
\<close>

lemma uresult_fresh:
  assumes r: "uresult A env tus (El_R env' tps)" and si: "sinv A K X env (tdps tus)"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "v \<notin> fst ` (evars env' \<union> dvars (tdps tps))"
proof
  assume vin: "v \<in> fst ` (evars env' \<union> dvars (tdps tps))"
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF r])
  from uresultD(3)[OF r] obtain A' K' X' where "ffres A' K' X' env' tps" by blast
  then have ei': "einv A' K' env'" by (simp add: ffres_def)
  let ?\<rho> = "tnorm_inst (tyenv env')"
  note r0 = einv_rho0[OF ei']
  have t: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF r0(1) dstepD(1)[OF ds]])
  from sinv_gtyped[OF si] t r0(2) have w: "wt_env ?\<rho> env" "dtyped ?\<rho> (tdps tus)" "vinv ?\<rho> env (dvars (tdps tus))"
    unfolding gtyped_def by blast+
  have vT: "vinv ?\<rho> env' ({(v, T)} \<union> dvars (tdps tps))" for T
  proof -
    have "vinv ?\<rho> env ({(v, T)} \<union> dvars (tdps tus))" by (rule ur_vinv_fresh[OF w(3)]) (use v in auto)
    from dstepD(2)[OF ds r0(1) extends_refl w(1,2) this] show ?thesis by blast
  qed
  from vin obtain U where U: "(v, U) \<in> evars env' \<union> dvars (tdps tps)" by force
  have "vcons ?\<rho> ({(v, U \<rightarrow>\<^sub>T U)} \<union> dvars (tdps tps) \<union> evars env')"
    using vT[of "U \<rightarrow>\<^sub>T U"] by (simp add: vinv_def)
  from vconsD[OF this, of v "U \<rightarrow>\<^sub>T U" U] U have "tsubst ?\<rho> (U \<rightarrow>\<^sub>T U) = tsubst ?\<rho> U" by blast
  with ur_fun_type_neq[of "tsubst ?\<rho> U"] show False by simp
qed

lemma ibelowI: "(\<forall>v\<in>vars t. snd (fst v) \<le> m) \<Longrightarrow> (\<forall>p\<in>ttvars t. snd (fst p) \<le> m) \<Longrightarrow> ibelow m t"
  by (simp add: ibelow_def)

lemma ttvars_list_implies_sub: "ttvars (list_implies As B) \<subseteq> (\<Union>A\<in>set As. ttvars A) \<union> ttvars B"
  by (induction As) (auto simp: implies_imp_type imp_type_def propT_def)

lemma above_m1: "-1 \<le> smax \<Longrightarrow> max rmax smax \<le> m \<Longrightarrow> \<not> i \<le> m \<Longrightarrow> 0 \<le> (i :: integer)"
  by (simp add: integer_reps)

text \<open>
  The environment of a result is acyclic and closed, and the indices of the variables and type
  variables of the environment and of the new premises of a result are not negative:
\<close>

definition bres_inv :: "bres \<Rightarrow> bool" where
  "bres_inv r \<longleftrightarrow> acyc (br_env r) \<and> closed_env (br_env r) \<and> tacyc (tyenv (br_env r)) \<and>
    tcons_env (tyenv (br_env r)) \<and> (\<forall>(x, T)\<in>evars (br_env r). 0 \<le> snd x) \<and>
    (\<forall>p\<in>tvars_env (tyenv (br_env r)). 0 \<le> snd (fst p)) \<and>
    (\<forall>x U u. vt_lookup (tenv (br_env r)) x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p))) \<and>
    (\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)).
      (\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>p\<in>ttvars A. 0 \<le> snd (fst p))) \<and>
    (\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)). closed A) \<and> tsorted alg (tyenv (br_env r)) \<and>
    scert alg (tyenv (br_env r))"

text \<open>
  The main theorem on typing: the results of \<open>bicompose_aux\<close>, if the proof state and the rule
  are theorems, are theorems (and their indices are not negative). Each name of a variable of
  the results has one type. For the proof state and the rule this is required only if the rule
  is incremented: otherwise \<open>bicompose_aux\<close> unifies the types of the variables of the same name.
\<close>

theorem bicompose_aux_thm_inv_gen:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r" and cfg: "cfg_alg cfg = alg"
    and state: "thm_inv0 smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "thm_inv0 rmax hr rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and tv: "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs rprop)"
    and inc: "incremented \<Longrightarrow> vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "thm_inv (maxidx (br_env r)) (hs @ hr) (br_tpairs r) (br_prop r) \<and> bres_inv r"
  using ok cfg
proof (cases rule: bicompose_aux_binv)
  case empty
  have "bpull (unify_ops cfg vl) BS_Empty = returnW None" by (subst bpull.simps) simp
  with res empty show ?thesis by (cases rule: bresult.cases) auto
next
  case (spec rAs B env)
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  let ?A = "tvars_thm stpairs ?S \<union> tvars_thm rtpairs rprop"
  let ?X = "vars_thm stpairs ?S \<union> vars_thm rtpairs rprop"
  let ?sp = "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have ws: "wt_thm smax hs stpairs ?S" and wr: "wt_thm rmax hr rtpairs rprop"
    and sm: "-1 \<le> smax" and rm: "-1 \<le> rmax"
    using state rule(1) by (simp_all add: thm_inv0_def)
  have nnS: "\<forall>v\<in>vars_thm stpairs ?S. 0 \<le> snd (fst v)" "\<forall>v\<in>tvars_thm stpairs ?S. 0 \<le> snd (fst v)"
    and nnR: "\<forall>v\<in>vars_thm rtpairs rprop. 0 \<le> snd (fst v)" "\<forall>v\<in>tvars_thm rtpairs rprop. 0 \<le> snd (fst v)"
    using state rule(1) by (simp_all add: thm_inv0_def)
  have wS: "wtp ?S" "ibelow smax ?S" and wR: "wtp rprop" "ibelow rmax rprop"
    using ws wr by (simp_all add: wt_thm_def)
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF spec(1) wtpD(2)[OF wR(1), of "\<lambda>_. propT"]])
  have envf: "einv ?A ?A env \<and> vt_is_empty (tenv env) \<and> ?m \<le> maxidx env \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> vcons \<rho> ?X)"
    by (rule call_env[OF ws wr tv inc spec(2,3)])
  then have ei: "einv ?A ?A env" and te: "vt_is_empty (tenv env)" and mx: "?m \<le> maxidx env"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> vcons \<rho> ?X" by blast+
  have tye: "tvars_env (tyenv env) \<subseteq> ?A \<union> {p. ?m < snd (fst p)}"
    by (rule call_env_tvars[OF ws wr tv spec(2,3)])
  have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
    using lifted_over_lifted_rule[OF rule(2)[OF that] spec(1)] by (auto simp: lifted_rule_def)
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    using lifted_over_lifted_rule[OF _ spec(1)] rule(2) by blast
  have fA: "finite ?A" and fX: "finite ?X" by simp_all
  have sa: "sinv_all ?A ?A ?X ?sp"
    using sinv_all_call_spec[OF ws wr[unfolded P] lift ei fA te mx] vc P by simp
  have pa: "pinv_all ?sp" by (rule sinv_all_pinv_all[OF sa fA fX])
  have sel: "sp_cfg ?sp = cfg" "sp_vl ?sp = vl" "sp_env ?sp = env" by (simp_all add: call_spec_def Let_def)
  have "rchar ?sp r"
    by (rule bresult_rchar[of ?sp]) (use res spec(4)[OF pa] cfg pa sel in simp_all)
  then obtain A1o na tus env' tps where its: "itsok ?sp A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth (sp_ctx ?sp) A1o na (env', tps)) r"
    by (auto simp: rchar_def sel)
  have si: "sinv ?A ?A ?X env (tdps tus)" using itsok_sinv[OF its sa] by (simp add: sel)
  have urs: "uresult ?A env tus (El_R env' tps)" by (rule uresD[OF ur fX fA si])
  from uresultD(3)[OF urs] obtain A' K' X' e0 where AA: "?A \<subseteq> A'" and tn: "tnew ?A env A' env'"
    and ff: "ffres A' K' X' env' tps" by blast
  have ei': "einv A' K' env'" and wi': "winv env' X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env' [] X' t u"
    using ff by (simp_all add: ffres_def)
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF urs])
  have ext: "extends env env'" by (rule dstepD(1)[OF ds])
  have mx': "maxidx env \<le> maxidx env'" using ext by (simp add: extends_def)
  let ?\<theta> = "tyenv env'" and ?\<rho> = "tnorm_inst (tyenv env')"
  note e' = einvD[OF ei'] and r0 = einv_rho0[OF ei']
  have ac': "tacyc ?\<theta>" by (rule e'(6))
  text \<open>The new premises.\<close>
  let ?nl = "count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  have lr': "lifted \<longrightarrow> lifted_rule smax Bi (rev rAs) B" using lr by blast
  obtain As0 h where As0: "set As0 \<subseteq> set (rev rAs)"
    and q1: "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    and q2: "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
    and q3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" and q4: "\<forall>(x, T)\<in>dvars (tdps tus). h x = x"
    and q5: "lifted \<longrightarrow> 0 \<le> ?nl \<and>
      (\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer ?nl) (spine_hyps X)). ibelow smax H)"
    and q6: "\<forall>X\<in>set (na_As na @ na_oldAs na). ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
      (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
    and q7: "\<forall>X\<in>set (na_oldAs na). wtp X"
  proof (rule itsok_newAs[OF refl its ws wr[unfolded P] lr' vl])
    fix As0 h assume "set As0 \<subseteq> set (rev rAs)"
      "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
      "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
      "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" "\<forall>(x, T)\<in>dvars (tdps tus). h x = x"
      "lifted \<Longrightarrow> 0 \<le> ?nl \<and>
        (\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer ?nl) (spine_hyps X)). ibelow smax H)"
      "\<forall>X\<in>set (na_As na @ na_oldAs na). ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A) \<and>
        (\<lambda>v. snd (fst v)) ` vars X \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)"
      "\<forall>X\<in>set (na_oldAs na). wtp X"
    then show thesis using that by blast
  qed
  let ?V = "\<Union>X\<in>set (na_As na). vars X" and ?BC = "\<Union>X\<in>insert C (set Bs). vars X"
  have As0X: "(\<Union>A\<in>set As0. vars A) \<subseteq> ?X" using As0 by (auto simp: P vars_thm_def vars_list_implies)
  have As0A: "(\<Union>A\<in>set As0. ttvars A) \<subseteq> ?A"
    using As0 ttvars_list_implies(1)[of _ "rev rAs" B] by (fastforce simp: P tvars_thm_def)
  have BCX: "?BC \<subseteq> ?X" by (auto simp: vars_thm_def vars_list_implies)
  have ibBC: "\<forall>X\<in>insert C (set Bs). ibelow smax X" using wS(2) by simp
  have wBC: "\<forall>X\<in>insert C (set Bs). wtp X" using wtp_list_implies[OF wS(1)] by simp
  have BCA: "ttvars X \<subseteq> ?A" if "X \<in> insert C (set Bs)" for X
    using that ttvars_list_implies(1)[of X "Bs @ [Bi]" C] ttvars_list_implies(2)[of C "Bs @ [Bi]"]
    by (auto simp: tvars_thm_def)
  have ev: "evars env = {}" using te by (simp add: evars_def bnds_def vt_is_empty_lookup)
  have dX: "dvars (tdps tus) \<subseteq> ?X" using sinv_dvars[OF si] ev by simp
  have bX: "below (maxidx env) ?X"
    using wS(2) wR(2) mx ws wr by (fastforce simp: below_def vars_thm_def ibelow_def wt_thm_def)
  text \<open>The variables of the new theorem are consistent:\<close>
  have wZ: "winv env ((?BC \<union> ?V) \<union> dvars (tdps tus))"
  proof (rule winv_reindex[OF te vc bX])
    fix x T assume "(x, T) \<in> (?BC \<union> ?V) \<union> dvars (tdps tus)"
    then consider "(x, T) \<in> ?BC" | "(x, T) \<in> ?V" | "(x, T) \<in> dvars (tdps tus)" by blast
    then show "(h x, T) \<in> ?X \<and> snd (h x) = snd x"
    proof cases
      case 1
      then obtain X where X: "X \<in> insert C (set Bs)" "(x, T) \<in> vars X" by blast
      have "snd x \<le> smax" using ibBC X by (blast intro: ibelow_var)
      with q3 have "h x = x" by blast
      with 1 BCX show ?thesis by auto
    next
      case 2
      with q2 As0X show ?thesis by blast
    next
      case 3
      from 3 q4 have "h x = x" by blast
      with 3 dX show ?thesis by auto
    qed
  qed
  have wY': "winv env' (?BC \<union> ?V)" by (rule uresult_winv[OF urs si wZ])
  have t0: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF r0(1) ext])
  from winvD[OF wZ t0 r0(2)] have w0: "wt_env ?\<rho> env" and v0: "vinv ?\<rho> env ((?BC \<union> ?V) \<union> dvars (tdps tus))"
    by blast+
  have "vinv ?\<rho> env' ((?BC \<union> ?V) \<union> dvars (tdps tps))"
    using dstepD(2)[OF ds r0(1) extends_refl w0 sinv_dtyped[OF si t0 r0(2)] v0] by blast
  define S0 where "S0 = ?BC \<union> ?V \<union> dvars (tdps tps) \<union> evars env'"
  have vS: "vcons ?\<rho> S0" "below (maxidx env') S0"
    using \<open>vinv ?\<rho> env' ((?BC \<union> ?V) \<union> dvars (tdps tps))\<close> by (simp_all add: vinv_def S0_def Un_assoc)
  have vtS: "vtcons (vimg ?\<theta> S0)" by (rule vtcons_vimg[OF vS(1)])
  text \<open>Indices:\<close>
  have nnX: "\<forall>v\<in>?X. 0 \<le> snd (fst v)" using nnS(1) nnR(1) by blast
  have nnS0: "0 \<le> snd x" if xS: "(x, T) \<in> S0" for x T
  proof -
    consider "(x, T) \<in> ?BC" | "(x, T) \<in> ?V" | "(x, T) \<in> dvars (tdps tps) \<union> evars env'"
      using xS unfolding S0_def by (elim UnE; blast)
    then show ?thesis
    proof cases
      case 1
      with BCX have "(x, T) \<in> ?X" by blast
      with nnX show ?thesis by force
    next
      case 2
      then obtain Z where Z: "Z \<in> set (na_As na)" "(x, T) \<in> vars Z" by blast
      from bspec[OF q2 Z(1)] Z(2) have "(h x, T) \<in> (\<Union>A\<in>set As0. vars A)" "snd (h x) = snd x" by auto
      with As0X have "(h x, T) \<in> ?X" "snd (h x) = snd x" by blast+
      with nnX show ?thesis by force
    next
      case 3
      show ?thesis
      proof (cases "snd x \<le> maxidx env")
        case True
        have "x \<in> fst ` (evars env \<union> dvars (tdps tus))"
        proof (rule ccontr)
          assume "x \<notin> fst ` (evars env \<union> dvars (tdps tus))"
          from uresult_fresh[OF urs si this True] 3 show False by force
        qed
        then obtain U where "(x, U) \<in> dvars (tdps tus)" using ev by auto
        with dX have "(x, U) \<in> ?X" by blast
        with nnX show ?thesis by force
      next
        case False
        from above_m1[OF sm mx False] show ?thesis .
      qed
    qed
  qed
  have tA: "tvars_env ?\<theta> \<union> A' \<subseteq> ?A \<union> {p. ?m < snd (fst p)}"
    using tn tye mx unfolding tnew_def by fastforce
  have nnA: "\<forall>p\<in>tvars_env ?\<theta> \<union> A'. 0 \<le> snd (fst p)"
  proof
    fix p assume "p \<in> tvars_env ?\<theta> \<union> A'"
    with tA consider "p \<in> ?A" | "?m < snd (fst p)" by blast
    then show "0 \<le> snd (fst p)"
    proof cases
      case 1
      with nnS(2) nnR(2) show ?thesis by blast
    next
      case 2
      with sm show ?thesis by (simp add: integer_reps)
    qed
  qed
  have ti: "tinv ar (maxidx env') ?\<theta> A'" by (rule e'(2))
  have scA: "scons (tvars_env ?\<theta> \<union> A')" and bA: "\<forall>p\<in>tvars_env ?\<theta> \<union> A'. snd (fst p) \<le> maxidx env'"
    using ti by (simp_all add: tinv_def)
  text \<open>The good components of the new theorem:\<close>
  let ?good = "\<lambda>Z. vars Z \<subseteq> vimg ?\<theta> S0 \<and> ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'"
  have gib: "ibelow (maxidx env') Z" if "?good Z" for Z
  proof (rule ibelowI)
    show "\<forall>v\<in>vars Z. snd (fst v) \<le> maxidx env'"
    proof
      fix v assume "v \<in> vars Z"
      with that have "fst v \<in> fst ` S0" by (metis fst_vimg image_eqI subsetD)
      with vS(2) show "snd (fst v) \<le> maxidx env'" by (auto simp: below_def)
    qed
    show "\<forall>p\<in>ttvars Z. snd (fst p) \<le> maxidx env'" using that bA by blast
  qed
  have c': "solution (tsol0 ?\<theta>) (esol (tsol0 ?\<theta>) env') env'" "cert_inst (tsol0 ?\<theta>)" "tsol ?\<theta> (tsol0 ?\<theta>)"
    using canonical_solution[OF ei' wi'] by blast+
  have SV: "?BC \<union> ?V \<subseteq> S0" "evars env' \<subseteq> S0" "dvars (tdps tps) \<subseteq> S0" by (auto simp: S0_def)
  text \<open>Normalized propositions:\<close>
  have gN: "wtp Z' \<and> ?good Z'"
    if "wtp Z" "vars Z \<subseteq> ?BC \<union> ?V" "ttvars Z \<subseteq> ?A" "ok (norm_term env' Z) Z'" for Z Z'
  proof -
    have ty: "(\<lambda>_. propT) \<turnstile> inst (tsol0 ?\<theta>) Z : propT"
      using typing_inst[OF wtpD(2)[OF that(1), of "\<lambda>_. propT"] cert_inst_inst_ok[OF c'(2)]] by simp
    have "ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'" using that(3) AA by blast
    note n = norm_term_props[OF ei' wY' _ this ty _ _ that(4)]
    have "vars Z \<subseteq> (?BC \<union> ?V) \<union> evars env'" using that(2) by blast
    note n = n[OF this, of 0]
    have cl: "\<not> loose_bvar Z 0" using wtpD(1)[OF that(1)] by (simp add: closed_def)
    have "wtp Z'" by (rule wtpI[OF _ n(1)[OF cl]]) (use n(2)[OF cl] in \<open>simp_all add: closed_def\<close>)
    moreover have "vimg ?\<theta> (vars Z \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      by (rule vimg_mono) (use that(2) SV in blast)
    ultimately show ?thesis using n(3,4)[OF cl] by blast
  qed
  text \<open>Unchanged propositions:\<close>
  have gK: "wtp Z \<and> ?good Z" if "wtp Z" "unb env' Z" "vars Z \<subseteq> ?BC \<union> ?V" "ttvars Z \<subseteq> ?A" for Z
  proof -
    have "vars Z \<subseteq> S0" using that(3) SV by blast
    then have "vars Z \<subseteq> vimg ?\<theta> S0" by (rule vimg_unb[OF ac' that(2)])
    moreover have "ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'" using that(4) AA by blast
    ultimately show ?thesis using that(1) by blast
  qed
  text \<open>Propositions normalized except for skipped assumptions:\<close>
  have gS: "wtp Z' \<and> ?good Z'"
    if lf: lifted and ab: "above env' smax" and Z: "Z \<in> set (na_As na)"
      and nt: "okT (norm_term_skip env' ?nl Z) Z'" for Z Z'
  proof -
    have wZ: "wtp Z" and tZ: "ttvars Z \<subseteq> ?A" using q1 Z As0A by blast+
    have sk: "skip_unb env' ?nl Z"
      by (rule skip_unb_take) (use q5 lf Z above_unb[OF ab] in auto)
    have cl: "\<not> loose_bvar Z 0" using wtpD(1)[OF wZ] by (simp add: closed_def)
    have "ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'" using tZ AA by blast
    from norm_term_skip_props[OF nt ei' wY' _ this wtpD(2)[OF wZ, of "\<lambda>_. propT"] cl _ sk] Z
    have n: "(\<lambda>i. tsubst (tsol0 ?\<theta>) propT) \<turnstile> Z' : propT" "\<not> loose_bvar Z' 0"
      "vars Z' \<subseteq> vimg ?\<theta> (vars Z \<union> evars env')" "ttvars Z' \<subseteq> tvars_env ?\<theta> \<union> A'"
      by auto
    have "wtp Z'" by (rule wtpI[OF _ n(1)]) (use n(2) in \<open>simp add: closed_def\<close>)
    moreover have "vimg ?\<theta> (vars Z \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      by (rule vimg_mono) (use Z SV in blast)
    ultimately show ?thesis using n(3,4) by blast
  qed
  text \<open>The flex-flex pairs:\<close>
  have gT: "closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and> ?good t' \<and> ?good u'"
    if tu: "(t, u) \<in> set tps" and nt: "ok (norm_term env' t) t'" and nu: "ok (norm_term env' u) u'" for t u t' u'
  proof -
    from tpok tu have p: "upok A' env' [] X' t u" by blast
    from upokD(9)[OF p c'(3,2)] obtain e T where tyt: "e \<turnstile> inst (tsol0 ?\<theta>) t : T" and tyu: "e \<turnstile> inst (tsol0 ?\<theta>) u : T"
      by auto
    note nt' = norm_term_props[OF ei' wi' upokD(1)[OF p] upokD(3)[OF p] tyt _ _ nt]
    note nu' = norm_term_props[OF ei' wi' upokD(2)[OF p] upokD(4)[OF p] tyu _ _ nu]
    have l: "\<not> loose_bvar t 0" "\<not> loose_bvar u 0" using upokD(7,8)[OF p] by simp_all
    have cl: "closed t'" "closed u'" using nt'(2)[OF l(1)] nu'(2)[OF l(2)] by (simp_all add: closed_def)
    have "\<forall>e'. e' \<turnstile> t' : T \<and> e' \<turnstile> u' : T"
      using typing_closed[OF nt'(1)[OF l(1)] cl(1)] typing_closed[OF nu'(1)[OF l(2)] cl(2)] by blast
    moreover have "vars t \<union> vars u \<subseteq> dvars (tdps tps)" using tu by (auto simp: dvars_def)
    then have "vimg ?\<theta> (vars t \<union> evars env') \<subseteq> vimg ?\<theta> S0" "vimg ?\<theta> (vars u \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      using SV by (intro vimg_mono; blast)+
    ultimately show ?thesis using cl nt'(3,4)[OF l(1)] nu'(3,4)[OF l(2)] by blast
  qed
  text \<open>The new theorem.\<close>
  have ci: "cert_typ alg ar imp_type"
  proof -
    obtain X Xs where "Bs @ [Bi] = X # Xs" by (cases "Bs @ [Bi]") auto
    with wtpD(2)[OF wS(1), of "\<lambda>_. propT"] show ?thesis by (simp add: typing_implies)
  qed
  have ctx: "bc_Bs (sp_ctx ?sp) = Bs" "bc_C (sp_ctx ?sp) = C" "bc_smax (sp_ctx ?sp) = smax"
    "bc_lifted (sp_ctx ?sp) = lifted" "bc_nlift (sp_ctx ?sp) = ?nl"
    by (simp_all add: call_spec_def Let_def)
  have hyps: "\<forall>h\<in>set (hs @ hr). wtp h \<and> vars h = {} \<and> ttvars h = {}" using ws wr by (auto simp: wt_thm_def)
  have fin: "thm_inv (maxidx env') (hs @ hr) ntps (list_implies Hs C')"
    if Hs: "\<forall>Z\<in>set Hs. wtp Z \<and> ?good Z" and C': "wtp C' \<and> ?good C'"
      and nt: "\<forall>(t, u)\<in>set ntps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
    for Hs C' ntps
  proof -
    have wP: "wtp (list_implies Hs C')" by (rule wtp_list_impliesI) (use Hs C' ci in auto)
    have "vars (list_implies Hs C') \<subseteq> vimg ?\<theta> S0" unfolding vars_list_implies using Hs C' by blast
    moreover have "ttvars (list_implies Hs C') \<subseteq> tvars_env ?\<theta> \<union> A'"
      using ttvars_list_implies_sub[of Hs C'] Hs C' by blast
    ultimately have gP: "?good (list_implies Hs C')" by blast
    have vt: "vars_thm ntps (list_implies Hs C') \<subseteq> vimg ?\<theta> S0"
      using gP nt by (fastforce simp: vars_thm_def)
    have tt: "tvars_thm ntps (list_implies Hs C') \<subseteq> tvars_env ?\<theta> \<union> A'"
      using gP nt by (fastforce simp: tvars_thm_def)
    have "wt_thm (maxidx env') (hs @ hr) ntps (list_implies Hs C')"
      unfolding wt_thm_def using wP gib[OF gP] hyps nt gib by fastforce
    moreover have "-1 \<le> maxidx env'" using sm mx mx' by simp
    moreover have "scons (tvars_thm ntps (list_implies Hs C'))"
      using scA tt unfolding scons_def by blast
    moreover have "vtcons (vars_thm ntps (list_implies Hs C'))"
      using vtS vt unfolding vtcons_def by blast
    moreover have "\<forall>v\<in>vars_thm ntps (list_implies Hs C'). 0 \<le> snd (fst v)"
    proof
      fix v assume "v \<in> vars_thm ntps (list_implies Hs C')"
      with vt have "fst v \<in> fst ` S0" by (metis fst_vimg image_eqI subsetD)
      then obtain U where "(fst v, U) \<in> S0" by force
      then show "0 \<le> snd (fst v)" by (rule nnS0)
    qed
    moreover have "\<forall>v\<in>tvars_thm ntps (list_implies Hs C'). 0 \<le> snd (fst v)"
      using tt nnA by blast
    ultimately show ?thesis by (simp add: thm_inv_def)
  qed
  have rel: "\<forall>Z'\<in>set Zs'. wtp Z' \<and> ?good Z'"
    if "list_all2 R Zs Zs'" "\<And>Z Z'. Z \<in> set Zs \<Longrightarrow> R Z Z' \<Longrightarrow> wtp Z' \<and> ?good Z'" for R Zs Zs'
    using list_all2_ex2[OF that(1)] that(2) by blast
  have vBC: "vars Z \<subseteq> ?BC \<union> ?V" "ttvars Z \<subseteq> ?A" "wtp Z" "ibelow smax Z" if "Z \<in> insert C (set Bs)" for Z
    using that BCA wBC ibBC by blast+
  have vN: "vars Z \<subseteq> ?BC \<union> ?V" "ttvars Z \<subseteq> ?A" "wtp Z" if "Z \<in> set (na_As na)" for Z
    using that q1 As0A by blast+
  have rr: "br_env r = env' \<and> br_newas r = na" using ad by (cases rule: addth_cases) auto
  have nn: "bres_inv r"
    unfolding bres_inv_def
  proof (intro conjI)
    show "acyc (br_env r)" "closed_env (br_env r)" "tacyc (tyenv (br_env r))" "tcons_env (tyenv (br_env r))"
      using rr e'(3,4,6,7) by simp_all
    show "\<forall>(x, T)\<in>evars (br_env r). 0 \<le> snd x" using rr nnS0 by (auto simp: S0_def)
    show "\<forall>p\<in>tvars_env (tyenv (br_env r)). 0 \<le> snd (fst p)" using rr nnA by blast
    show "\<forall>x U u. vt_lookup (tenv (br_env r)) x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p))"
      using rr nnA e'(1) unfolding tvinv_def by blast
    show "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)). closed A"
      using rr q1 q7 by (auto dest: wtpD(1))
    show "tsorted alg (tyenv (br_env r))" using rr e'(12) by simp
    show "scert alg (tyenv (br_env r))" using rr e'(9) by simp
    show "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)).
        (\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>p\<in>ttvars A. 0 \<le> snd (fst p))"
    proof
      fix A assume "A \<in> set (na_As (br_newas r) @ na_oldAs (br_newas r))"
      with q6 rr have tA: "ttvars A \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
        and iA: "(\<lambda>v. snd (fst v)) ` vars A \<subseteq> (\<lambda>v. snd (fst v)) ` (\<Union>A\<in>set As0. vars A)" by auto
      have "\<forall>v\<in>vars A. 0 \<le> snd (fst v)"
      proof
        fix v assume "v \<in> vars A"
        then have "snd (fst v) \<in> (\<lambda>v. snd (fst v)) ` vars A" by (rule imageI)
        with iA obtain w where w: "w \<in> (\<Union>A\<in>set As0. vars A)" "snd (fst v) = snd (fst w)"
          by (blast dest: subsetD)
        have "w \<in> ?X" by (rule subsetD[OF As0X w(1)])
        from bspec[OF nnX this] w(2) show "0 \<le> snd (fst v)" by simp
      qed
      moreover have "\<forall>p\<in>ttvars A. 0 \<le> snd (fst p)"
      proof
        fix p assume "p \<in> ttvars A"
        then have "p \<in> ?A" using subset_trans[OF tA As0A] by (rule rev_subsetD)
        then show "0 \<le> snd (fst p)"
        proof (rule UnE)
          assume "p \<in> tvars_thm stpairs ?S"
          from bspec[OF nnS(2) this] show ?thesis .
        next
          assume "p \<in> tvars_thm rtpairs rprop"
          from bspec[OF nnR(2) this] show ?thesis .
        qed
      qed
      ultimately show "(\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>p\<in>ttvars A. 0 \<le> snd (fst p))" by blast
    qed
  qed
  from ad[unfolded ctx] have "thm_inv (maxidx (br_env r)) (hs @ hr) (br_tpairs r) (br_prop r)"
  proof (cases rule: addth_cases)
    case empty
    have em: "vt_is_empty (tenv env')" "vt_is_empty ?\<theta>" using empty(1) by (simp_all add: env_is_empty_def)
    have unb: "unb env' Z" for Z by (simp add: unb_def em vt_is_empty_lookup)
    have "\<forall>Z\<in>set (Bs @ na_As na). wtp Z \<and> ?good Z"
    proof
      fix Z assume "Z \<in> set (Bs @ na_As na)"
      then consider (s) "Z \<in> insert C (set Bs)" | (n) "Z \<in> set (na_As na)" by auto
      then show "wtp Z \<and> ?good Z"
      proof cases
        case s
        show ?thesis by (rule gK[OF vBC(3)[OF s] unb vBC(1,2)[OF s]])
      next
        case n
        show ?thesis by (rule gK[OF vN(3)[OF n] unb vN(1,2)[OF n]])
      qed
    qed
    moreover have "wtp C \<and> ?good C" by (rule gK[OF vBC(3)[of C] unb vBC(1,2)[of C]]) simp_all
    moreover have "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set tps"
      from tpok tu have p: "upok A' env' [] X' t u" by blast
      from upokD(9)[OF p c'(3,2)] obtain e T where "e \<turnstile> inst (tsol0 ?\<theta>) t : T" "e \<turnstile> inst (tsol0 ?\<theta>) u : T"
        by auto
      then have ty: "e \<turnstile> t : T" "e \<turnstile> u : T" using inst_tsol0_unb[OF unb] by simp_all
      have cl: "closed t" "closed u" using upokD(7,8)[OF p] by (simp_all add: closed_def)
      have "vars t \<union> vars u \<subseteq> S0" using tu SV by (auto simp: dvars_def)
      then have "vars t \<subseteq> vimg ?\<theta> S0" "vars u \<subseteq> vimg ?\<theta> S0" using vimg_unb[OF ac' unb] by blast+
      moreover have "ttvars t \<subseteq> tvars_env ?\<theta> \<union> A'" "ttvars u \<subseteq> tvars_env ?\<theta> \<union> A'"
        using upokD(3,4)[OF p] by simp_all
      moreover have "\<forall>e'. e' \<turnstile> t : T \<and> e' \<turnstile> u : T" using typing_closed ty cl by blast
      ultimately show "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
        using cl by blast
    qed
    ultimately have "thm_inv (maxidx env') (hs @ hr) tps (list_implies (Bs @ na_As na) C)" by (rule fin)
    then show ?thesis using empty(2) by (simp add: ctx)
  next
    case (norm ntps Hs C')
    have nt: "\<forall>(t', u')\<in>set ntps. closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and>
        ?good t' \<and> ?good u'"
    proof (intro ballI, clarify)
      fix t' u' assume "(t', u') \<in> set ntps"
      from list_all2_ex2[OF norm(3) this] obtain t u where "(t, u) \<in> set tps"
        "ok (norm_term env' t) t'" "ok (norm_term env' u) u'" by auto
      from gT[OF this] show "closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and> ?good t' \<and> ?good u'" .
    qed
    have kept: "wtp Z \<and> ?good Z" if ab: "above env' smax" and Z: "Z \<in> insert C (set Bs)" for Z
      using gK[OF vBC(3)[OF Z] above_unb[OF ab vBC(4)[OF Z]] vBC(1,2)[OF Z]] .
    have "(\<forall>Z\<in>set Hs. wtp Z \<and> ?good Z) \<and> wtp C' \<and> ?good C'"
      using norm(4)[unfolded ctx]
    proof (elim disjE conjE exE)
      fix As' assume ab: "above env' smax" and lf: lifted and C': "C' = C" and Hs: "Hs = Bs @ As'"
        and l: "list_all2 (\<lambda>X X'. okT (norm_term_skip env' ?nl X) X') (na_As na) As'"
      have "\<forall>Z'\<in>set As'. wtp Z' \<and> ?good Z'" by (rule rel[OF l]) (rule gS[OF lf ab])
      with kept[OF ab] show ?thesis by (auto simp: Hs C')
    next
      fix As' assume ab: "above env' smax" and lf: "\<not> lifted" and C': "C' = C" and Hs: "Hs = Bs @ As'"
        and l: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (na_As na) As'"
      have "\<forall>Z'\<in>set As'. wtp Z' \<and> ?good Z'" by (rule rel[OF l]) (use gN vN in blast)
      with kept[OF ab] show ?thesis by (auto simp: Hs C')
    next
      assume l: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (Bs @ na_As na) Hs"
        and c: "ok (norm_term env' C) C'"
      have "\<forall>Z'\<in>set Hs. wtp Z' \<and> ?good Z'"
      proof (rule rel[OF l])
        fix Z Z' assume Z: "Z \<in> set (Bs @ na_As na)" and nZ: "ok (norm_term env' Z) Z'"
        from Z consider (s) "Z \<in> insert C (set Bs)" | (n) "Z \<in> set (na_As na)" by auto
        then show "wtp Z' \<and> ?good Z'"
        proof cases
          case s
          show ?thesis by (rule gN[OF vBC(3,1,2)[OF s] nZ])
        next
          case n
          show ?thesis by (rule gN[OF vN(3,1,2)[OF n] nZ])
        qed
      qed
      moreover have "wtp C' \<and> ?good C'" using gN[OF vBC(3,1,2)[of C] c] by simp
      ultimately show ?thesis by blast
    qed
    then show ?thesis using fin[OF _ _ nt] norm(2) by simp
  qed
  with nn show ?thesis by blast
qed

text \<open>For an incremented rule and theorems with one type for each name:\<close>

theorem bicompose_aux_thm_inv:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r" and cfg: "cfg_alg cfg = alg"
    and state: "thm_inv smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "thm_inv rmax hr rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and tv: "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs rprop)"
    and inc: "vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "thm_inv (maxidx (br_env r)) (hs @ hr) (br_tpairs r) (br_prop r) \<and> bres_inv r"
  by (rule bicompose_aux_thm_inv_gen[OF ok res cfg thm_inv_inv0[OF state] thm_inv_inv0[OF rule(1)] _ tv _ vl])
    (use rule(2) inc in auto)

end

end
