section \<open>Problems with Type Variables: Completeness of Copying\<close>

theory Unify_Poly_Copy
  imports Unify_Poly_Simpl_Complete
begin

text \<open>
  The completeness of \<open>matchcopy\<close> for problems with type variables. The solution \<open>(\<rho>, \<sigma>)\<close> and the
  typing \<open>W\<close> are extended by the new variables; the semantic arguments are those of the
  monomorphic case on the ground instance (theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Match_Complete\<close>).
\<close>


subsection \<open>Extending the solution and the typing\<close>

lemma has_type_vars_cong: "has_type V Ts t T \<Longrightarrow> (\<And>x. x \<in> vars t \<Longrightarrow> V' x = V x) \<Longrightarrow> has_type V' Ts t T"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

lemma typed_tctx_cong:
  assumes "typed env W Ts t T" "tyenv env' = tyenv env" "\<And>x. x \<in> vars t \<Longrightarrow> tctx env' W' x = tctx env W x"
  shows "typed env' W' Ts t T"
  using has_type_vars_cong[OF assms(1)[unfolded typed_def], of "tctx env' W'"] assms(2,3)
  by (simp add: typed_def)

abbreviation imap :: "tinst \<Rightarrow> (indexname \<times> ptyp \<times> dB) list \<Rightarrow> (indexname \<times> ptyp \<times> dB) list" where
  "imap \<rho> ys \<equiv> map (\<lambda>(x, G, w). (x, tsubst \<rho> G, w)) ys"

lemma map_of_imap: "map_of (imap \<rho> ys) y = map_option (\<lambda>(G, w). (tsubst \<rho> G, w)) (map_of ys y)"
  by (induction ys) auto

lemma ext_subst_imap: "ext_subst \<sigma> (imap \<rho> ys) = ext_subst \<sigma> ys"
proof
  fix n
  have "map (\<lambda>(x, T, w). (code (AVar x), w)) (imap \<rho> ys) = map (\<lambda>(x, T, w). (code (AVar x), w)) ys"
    by (induction ys) auto
  then show "ext_subst \<sigma> (imap \<rho> ys) n = ext_subst \<sigma> ys n" by (simp only: ext_subst_def)
qed

text \<open>
  New variables \<open>x\<close> of types \<open>G\<close> with values \<open>w\<close>, all newer than the environment, extend the
  solution \<open>\<sigma>\<close> and the typing \<open>W\<close>.
\<close>

lemma pcinv_extend_vars:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and e1: "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1"
    and ys: "\<And>x G w. (x, G, w) \<in> set ys \<Longrightarrow> maxidx env < snd x \<and> tyw ar (tyenv env) A G \<and>
      no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty (tsubst \<rho> G))"
  shows "pcinv alg ar A (ext_typ W ys) \<rho> \<tau>' (ext_subst \<sigma> ys) env1 dps"
    "agree (maxidx env) \<sigma> (ext_subst \<sigma> ys)" "agreeV (maxidx env) W (ext_typ W ys)"
    "ityp \<rho> env1 (ext_typ W ys) = ext_typ (ityp \<rho> env W) (imap \<rho> ys)"
proof -
  let ?\<theta> = "tyenv env" and ?W1 = "ext_typ W ys" and ?\<sigma>1 = "ext_subst \<sigma> ys"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have yi: "maxidx (instE \<rho> env) < snd x \<and> no_loose_bound w 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> w : trty G)"
    if "(x, G, w) \<in> set (imap \<rho> ys)" for x G w
    using that ys by auto
  have frI: "fresh_env (instE \<rho> env)" using ei(6) by simp
  note se = solution_extend[of "ityp \<rho> env W" \<tau>' \<sigma> "instE \<rho> env" "imap \<rho> ys", OF pc0(3) frI yi,
    unfolded ext_subst_imap]
  show ag: "agree (maxidx env) \<sigma> ?\<sigma>1" using se(2) by simp
  have nb: "map_of ys y = None" if "snd y \<le> maxidx env" for y
  proof (rule ccontr)
    assume "map_of ys y \<noteq> None"
    then obtain G w where "map_of ys y = Some (G, w)" by auto
    then have "(y, G, w) \<in> set ys" by (rule map_of_SomeD)
    from ys[OF this] that show False by simp
  qed
  show agV: "agreeV (maxidx env) W ?W1" unfolding agreeV_def using nb by (simp add: ext_typ_simp)
  have bnd: "snd y \<le> maxidx env" if "vt_lookup (tenv env) y = Some (U, u)" for y U u
    using fresh_envD[OF ei(6) that] by simp
  have W1old: "?W1 y = W y" if "snd y \<le> maxidx env" for y using nb[OF that] by (simp add: ext_typ_simp)
  have tw1: "tyw ar ?\<theta> A (?W1 y)" for y
  proof (cases "map_of ys y")
    case (Some p)
    then obtain G w where "map_of ys y = Some (G, w)" by (cases p) auto
    moreover from map_of_SomeD[OF this] have "tyw ar ?\<theta> A G" using ys by blast
    ultimately show ?thesis by (simp add: ext_typ_simp)
  qed (simp add: ext_typ_simp pi(5))
  have wc1: "wcons ?W1 env1"
    using pi(6) e1(1,2) bnd W1old unfolding wcons_def by (metis (no_types, lifting))
  have tctx1: "tctx env1 ?W1 y = tctx env W y" if "snd y \<le> maxidx env" for y
    using wcons_tctx[OF wc1] wcons_tctx[OF pi(6)] W1old[OF that] e1(2) by simp
  have typed1: "typed env1 ?W1 Ts t T" if "typed env W Ts t T" "below (maxidx env) t" for Ts t T
    by (rule typed_tctx_cong[OF that(1) e1(2)]) (use that(2) tctx1 in \<open>auto simp: below_def\<close>)
  show "ityp \<rho> env1 ?W1 = ext_typ (ityp \<rho> env W) (imap \<rho> ys)"
  proof
    fix y
    show "ityp \<rho> env1 ?W1 y = ext_typ (ityp \<rho> env W) (imap \<rho> ys) y"
    proof (cases "map_of ys y")
      case None
      then have "?W1 y = W y" by (simp add: ext_typ_simp)
      moreover have "tctx env1 ?W1 y = tnorm ?\<theta> (?W1 y)" "tctx env W y = tnorm ?\<theta> (W y)"
        using wcons_tctx[OF wc1] wcons_tctx[OF pi(6)] e1(2) by simp_all
      ultimately show ?thesis using None by (simp add: ext_typ_simp map_of_imap)
    next
      case (Some p)
      then obtain G w where m: "map_of ys y = Some (G, w)" by (cases p) auto
      from map_of_SomeD[OF m] ys have tG: "tyw ar ?\<theta> A G" by blast
      have "tctx env1 ?W1 y = tnorm ?\<theta> G" using wcons_tctx[OF wc1] m e1(2) by (simp add: ext_typ_simp)
      then show ?thesis using m tsubst_tnorm[OF ac sol tyw_tcons[OF pi(2) tG]]
        by (simp add: ext_typ_simp map_of_imap)
    qed
  qed
  note it1 = this
  have "penv_inv alg ar ?W1 env1"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env1) (tyenv env1) (etvars env1)"
      using tinv_mono[OF ei(1) e1(3)] e1 etys_same_tenv[OF e1(1)] by (simp add: etvars_def)
    show "tsorted alg (tyenv env1)" using ei(2) e1(2) by simp
    show "nacyc env1" using ei(3) nacyc_same_tenv[OF e1(1)] by simp
    show "pwf_env ar env1" using ei(4) e1(1) by (simp add: pwf_env_def)
    show "wt_env ?W1 env1"
      using pi(1) e1(1) fresh_envD[OF ei(6)] typed1 by (auto simp: penv_inv_def wt_env_def)
    show "fresh_env env1" by (rule fresh_env_same[OF e1(1,3) ei(6)])
  qed
  moreover have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T) \<and> ptyped env1 ?W1 dp \<and>
      dp_below (maxidx env1) dp \<and> dsolved ?\<sigma>1 (instd \<rho> dp)" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" "\<forall>T\<in>dtys dp. tyw ar ?\<theta> A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u" by auto
    have "dsolved ?\<sigma>1 (instd \<rho> dp)"
      using pc0(4)[OF dp] dpe mk_subst_agree[OF _ ag, of "inst \<rho> (rlist_abs rb t)"]
        mk_subst_agree[OF _ ag, of "inst \<rho> (rlist_abs rb u)"] bl
      by (simp add: dsolved_def below_rlist_abs inst_rlist_abs[symmetric])
    then show ?thesis using w e1 typed1[OF ty(1) bl(1)] typed1[OF ty(2) bl(2)] bl below_mono[OF _ e1(3)] dpe
      by auto
  qed
  moreover have "solution (ityp \<rho> env1 ?W1) \<tau>' ?\<sigma>1 (instE \<rho> env1)"
    using se(1) instE_same_tenv[OF e1(1), of \<rho>] it1 by (simp add: solution_def sat_def)
  ultimately show "pcinv alg ar A ?W1 \<rho> \<tau>' ?\<sigma>1 env1 dps"
    using pi(2,3) tw1 wc1 pc0(2) e1 tinv_mono[OF pi(2) e1(3)] etys_same_tenv[OF e1(1)]
    by (auto simp: pcinv_def pinv_def simp del: split_paired_All)
qed


subsection \<open>Types modulo the type environment\<close>

lemma binder_types_ptnorm:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and T: "tcons (tyenv env) T"
  shows "tnorm (tyenv env) T = foldr fun_type Us B \<Longrightarrow> \<not> is_funT B \<Longrightarrow>
    \<exists>Us'. binder_types env T = return Us' \<and> map (tnorm (tyenv env)) Us' = Us \<and>
      (\<forall>U\<in>set Us'. tcons (tyenv env) U)"
  using T
proof (induction arbitrary: Us rule: tnorm_induct[OF ac, consumes 1, case_names TFree Type Unbound Bound])
  case (TFree a S)
  then have "Us = []" by (cases Us) auto
  with TFree show ?case by (subst binder_types.simps) (auto simp: return_def)
next
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>A U. Ts = [A, U])")
    case True
    then obtain A U where a: "a = STR ''fun''" and Ts: "Ts = [A, U]" by blast
    from Type.prems(1,2) a Ts obtain Us' where Us: "Us = tnorm (tyenv env) A # Us'"
      and "tnorm (tyenv env) U = foldr fun_type Us' B"
      by (cases Us) auto
    from Type.IH[of U, OF _ this(2) Type.prems(2)] Ts obtain Ws where
      "binder_types env U = return Ws" "map (tnorm (tyenv env)) Ws = Us'" "\<forall>U\<in>set Ws. tcons (tyenv env) U"
      by auto
    then show ?thesis using binder_types_fun[of env A U] Type.hyps Us
      by (intro exI[of _ "A # Ws"]) (simp add: a Ts bindM_def return_def)
  next
    case False
    have "Us = []"
    proof (rule ccontr)
      assume "Us \<noteq> []"
      then obtain A Us' where "Us = A # Us'" by (cases Us) auto
      with Type.prems(1) False show False by auto
    qed
    with Type.prems(1) Type.hyps False show ?thesis
      by (subst binder_types.simps) (auto simp: return_def split: list.splits)
  qed
next
  case (Unbound v S)
  then have "Us = []" by (cases Us) (auto simp: tnorm_TVar[OF ac(1)])
  with Unbound show ?case
    by (subst binder_types.simps) (auto simp: type_lookup_ok(1) bindM_def return_def)
next
  case (Bound v S U)
  have "tnorm (tyenv env) U = foldr fun_type Us B"
    using Bound.prems(1) Bound(1) by (simp add: tnorm_TVar[OF ac(1)])
  from Bound.IH[OF this Bound.prems(2)] obtain Us' where
    "binder_types env U = return Us'" "map (tnorm (tyenv env)) Us' = Us" "\<forall>U\<in>set Us'. tcons (tyenv env) U"
    by blast
  then show ?case using Bound(1)
    by (subst binder_types.simps) (auto simp: type_lookup_ok(2) bindM_def return_def)
qed

lemma strip_type_ptnorm:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and T: "tcons (tyenv env) T"
    and eq: "tnorm (tyenv env) T = foldr fun_type Us B" and B: "\<not> is_funT B"
  obtains Us' B' where "strip_type env T = return (Us', B')" "map (tnorm (tyenv env)) Us' = Us"
    "tnorm (tyenv env) B' = B" "\<forall>U\<in>set Us'. tcons (tyenv env) U" "tcons (tyenv env) B'"
proof -
  from binder_types_ptnorm[OF ac T eq B] obtain Us' where
    b: "binder_types env T = return Us'" "map (tnorm (tyenv env)) Us' = Us" "\<forall>U\<in>set Us'. tcons (tyenv env) U"
    by blast
  from body_type_ptnorm[OF ac T eq B] obtain B' where
    c: "body_type env T = return B'" "tnorm (tyenv env) B' = B" "tcons (tyenv env) B'"
    by blast
  show ?thesis by (rule that[of Us' B']) (simp_all add: strip_type_def b c bindM_def return_def)
qed

text \<open>The normal form of a type, split into argument types and a result type that is not a function type.\<close>

lemma tnorm_arg_res: "tnorm \<theta> T = foldr fun_type (arg_types (tnorm \<theta> T)) (res_type (tnorm \<theta> T))"
  by (rule arg_res_type[symmetric])

lemma res_type_nonfun: "\<not> is_funT (res_type T)"
  by (rule res_type_base)


subsection \<open>The k-condition\<close>

text \<open>
  The k-condition on the type variables \<open>A\<close> of the problem: the unbound type variables of their
  normal forms are instantiated by types in which every chain of arrows has at most \<open>k\<close>
  argument types. It extends to all types of the problem.
\<close>

definition kokA :: "nat \<Rightarrow> tinst \<Rightarrow> tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "kokA k \<rho> \<theta> A \<longleftrightarrow> (\<forall>(v, S)\<in>A. kok k \<rho> \<theta> (TVar v S))"

lemma kok_tyw:
  assumes inv: "tinv ar n \<theta> A" and T: "tyw ar \<theta> A T" and k: "kokA k \<rho> \<theta> A"
  shows "kok k \<rho> \<theta> T"
  unfolding kok_def
proof (clarify)
  fix w S' assume w: "(w, S') \<in> tvars (tnorm \<theta> T)"
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have "w \<in> uvars \<theta> T" using w by (force simp: uvars_def)
  with T obtain v S where vS: "(v, S) \<in> A" and wv: "w \<in> uvars \<theta> (TVar v S)"
    by (auto simp: tyw_def uvarsA_def)
  from wv obtain S'' where w'': "(w, S'') \<in> tvars (tnorm \<theta> (TVar v S))" by (auto simp: uvars_def)
  have "(w, S') \<in> tvars_env \<theta> \<union> A" using w tvars_tnorm[OF ac, of T] T by (auto simp: tyw_def)
  moreover have "(w, S'') \<in> tvars_env \<theta> \<union> A" using w'' tvars_tnorm[OF ac, of "TVar v S"] vS by auto
  moreover have "scons (tvars_env \<theta> \<union> A)" using inv by (simp add: tinv_def)
  ultimately have "S'' = S'" by (cases w) (simp add: scons_def; blast)
  with w'' k vS show "aok k (\<rho> w S')" by (auto simp: kokA_def kok_def)
qed

lemma aok_arg_types: "aok k T \<Longrightarrow> length (arg_types T) \<le> k"
  by (cases T) auto

lemma aok_fun: "aok k (A \<rightarrow>\<^sub>T B) \<Longrightarrow> aok k A \<and> aok k B"
  by simp

lemma aok_foldr_fun: "aok k (foldr fun_type As B) \<Longrightarrow> (\<forall>A\<in>set As. aok k A) \<and> aok k B"
  by (induction As) auto

text \<open>The k-condition is preserved by extensions with an agreeing solution.\<close>

lemma kokA_textends:
  assumes inv: "tinv ar n \<theta> A" and ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and sol: "tsol \<theta>' \<rho>'"
    and ag: "tagree n \<rho> \<rho>'" and tce: "tcons_env \<theta>'" and inv': "tinv ar n' \<theta>' A"
    and k: "kokA k \<rho> \<theta> A"
  shows "kokA k \<rho>' \<theta>' A"
  unfolding kokA_def
proof (clarify)
  fix v S assume vS: "(v, S) \<in> A"
  have ac0: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have "\<rho>' w S' = \<rho> w S'" if "(w, S') \<in> tvars (tnorm \<theta> (TVar v S))" for w S'
  proof -
    have "(w, S') \<in> tvars_env \<theta> \<union> A" using that tvars_tnorm[OF ac0, of "TVar v S"] vS by auto
    moreover have "\<forall>p\<in>tvars_env \<theta> \<union> A. snd (fst p) \<le> n" using inv by (simp add: tinv_def)
    ultimately have "snd (fst (w, S')) \<le> n" by blast
    then show ?thesis using ag by (cases w) (simp add: tagree_def)
  qed
  moreover have "tcons \<theta>' (tnorm \<theta> (TVar v S))"
  proof -
    have "tvars (tnorm \<theta> (TVar v S)) \<subseteq> tvars_env \<theta>' \<union> A"
      using tvars_tnorm[OF ac0, of "TVar v S"] vS tvars_env_textends[OF ext] by auto
    then show ?thesis by (rule tinv_tcons[OF inv'])
  qed
  ultimately show "kok k \<rho>' \<theta>' (TVar v S)"
    using kok_textends[OF ac ext sol _ tce _] k vS by (auto simp: kokA_def)
qed


subsection \<open>New type variables\<close>

definition gtv :: "integer \<Rightarrow> nat \<Rightarrow> indexname" where
  "gtv i n = (aT + radixstring (integer_of_nat n), i)"

lemma gtv_inj: "gtv i n = gtv i m \<longleftrightarrow> n = m"
proof
  assume "gtv i n = gtv i m"
  then have "radixstring (integer_of_nat n) = radixstring (integer_of_nat m)"
    by (simp add: gtv_def plus_literal_cancel)
  then have "integer_of_nat n = integer_of_nat m"
    by (rule radixstring_inj[rotated 2]) (simp_all add: integer_of_nat_eq_of_nat)
  then show "n = m" by (metis nat_of_integer_integer_of_nat)
qed simp

lemma snd_gtv[simp]: "snd (gtv i n) = i"
  by (simp add: gtv_def)

lemma gentvars_cases:
  assumes "gentvars p env = (env1, Cs)"
  shows "maxidx env \<le> maxidx env1" "p = 0 \<Longrightarrow> env1 = env \<and> Cs = []"
    "0 < p \<Longrightarrow> maxidx env1 = maxidx env + 1 \<and> Cs = map (\<lambda>n. TVar (gtv (maxidx env + 1) n) []) [0..<p]"
  using assms by (auto simp: gentvars_def gtv_def split: if_splits env.splits)

lemma gentvars_tvar:
  assumes "gentvars p env = (env1, Cs)" "C \<in> set Cs"
  obtains n where "n < p" "C = TVar (gtv (maxidx env + 1) n) []" "maxidx env1 = maxidx env + 1"
  using assms gentvars_cases[OF assms(1)] by (cases "p = 0") auto

lemma tyw_mono: "tyw ar \<theta> A T \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> tyw ar \<theta> A' T"
  unfolding tyw_def uvarsA_def by blast

lemma tinv_idx: "tinv ar n \<theta> A \<Longrightarrow> (v, S) \<in> tvars_env \<theta> \<union> A \<Longrightarrow> snd v \<le> n"
  unfolding tinv_def by (drule conjunct2, drule conjunct2, drule conjunct1, drule bspec) auto

lemma tagreeD: "tagree n \<rho> \<rho>' \<Longrightarrow> snd v \<le> n \<Longrightarrow> \<rho>' v S = \<rho> v S"
  by (cases v) (simp add: tagree_def)

abbreviation ctvars :: "ptyp list \<Rightarrow> (indexname \<times> psort) set" where
  "ctvars Cs \<equiv> \<Union> (tvars ` set Cs)"

lemma tinv_gentvars:
  assumes inv: "tinv ar (maxidx env) \<theta> A" and g: "gentvars p env = (env1, Cs)"
  shows "tinv ar (maxidx env1) \<theta> (A \<union> ctvars Cs)"
proof (cases "p = 0")
  case True
  with gentvars_cases(2)[OF g] inv show ?thesis by simp
next
  case False
  note gc = gentvars_cases(3)[OF g] gentvars_cases(1)[OF g]
  have new: "snd v = maxidx env + 1 \<and> S = []" if "(v, S) \<in> ctvars Cs" for v S
    using that False gc by auto
  have old: "snd (fst q) \<le> maxidx env" if "q \<in> tvars_env \<theta> \<union> A" for q
    using tinv_idx[OF inv, of "fst q" "snd q"] that by simp
  show ?thesis
    unfolding tinv_def
  proof (intro conjI)
    show "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
    show "\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> wft ar U" using inv by (simp add: tinv_def)
    show "\<forall>q\<in>tvars_env \<theta> \<union> (A \<union> ctvars Cs). snd (fst q) \<le> maxidx env1"
    proof
      fix q assume "q \<in> tvars_env \<theta> \<union> (A \<union> ctvars Cs)"
      then have "q \<in> tvars_env \<theta> \<union> A \<or> q \<in> ctvars Cs" by blast
      then show "snd (fst q) \<le> maxidx env1"
      proof
        assume "q \<in> tvars_env \<theta> \<union> A"
        from old[OF this] gc(2) show ?thesis by simp
      next
        assume "q \<in> ctvars Cs"
        with new[of "fst q" "snd q"] gc(1) \<open>p \<noteq> 0\<close> show ?thesis by simp
      qed
    qed
    have sc: "scons (tvars_env \<theta> \<union> A)" using inv by (simp add: tinv_def)
    show "scons (tvars_env \<theta> \<union> (A \<union> ctvars Cs))"
      unfolding scons_def
    proof (intro allI impI)
      fix v S S' assume a: "(v, S) \<in> tvars_env \<theta> \<union> (A \<union> ctvars Cs)" "(v, S') \<in> tvars_env \<theta> \<union> (A \<union> ctvars Cs)"
      show "S = S'"
      proof (cases "(v, S) \<in> ctvars Cs \<or> (v, S') \<in> ctvars Cs")
        case True
        then have "snd v = maxidx env + 1" using new by blast
        then have "(v, S) \<in> ctvars Cs" "(v, S') \<in> ctvars Cs" using a old[of "(v, S)"] old[of "(v, S')"] by auto
        then show ?thesis using new by blast
      next
        case False
        with a sc show ?thesis unfolding scons_def by blast
      qed
    qed
  qed
qed

lemma tyw_gentvars:
  assumes inv: "tinv ar (maxidx env) \<theta> A" and g: "gentvars p env = (env1, Cs)" and C: "C \<in> set Cs"
  shows "tyw ar \<theta> (A \<union> ctvars Cs) C"
proof -
  from gentvars_tvar[OF g C] obtain n where C': "C = TVar (gtv (maxidx env + 1) n) []" by blast
  let ?v = "gtv (maxidx env + 1) n"
  have "vt_lookup \<theta> ?v = None"
  proof (rule ccontr)
    assume "vt_lookup \<theta> ?v \<noteq> None"
    then obtain S U where "vt_lookup \<theta> ?v = Some (S, U)" by auto
    then have "(?v, S) \<in> tvars_env \<theta>" by (rule tvars_envI)
    with tinv_idx[OF inv, of ?v S] show False by simp
  qed
  then have "uvars \<theta> C = {?v}" using C' tinv_tacyc[OF inv] by (simp add: uvars_TVar)
  moreover have "(?v, []) \<in> A \<union> ctvars Cs" using C C' by force
  ultimately show ?thesis using C' by (force simp: tyw_def uvarsA_def)
qed

lemma ext_typ_Nil[simp]: "ext_typ W [] = W"
  by (simp add: ext_typ_def fun_eq_iff)

lemma ext_subst_Nil[simp]: "ext_subst \<sigma> [] = \<sigma>"
  by (simp add: ext_subst_def fun_eq_iff)

lemma pcinv_maxidx:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1"
  shows "pcinv alg ar A W \<rho> \<tau>' \<sigma> env1 dps"
  using pcinv_extend_vars(1)[OF assms, of "[]"] by simp

lemma pcinv_gentvars:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow> gentvars p env = (env1, Cs) \<Longrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env1 dps"
  by (erule pcinv_maxidx) (simp_all add: gentvars_simps gentvars_cases(1))

text \<open>The new type variables can be instantiated by arbitrary ground types.\<close>

lemma gentvars_inst:
  assumes g: "gentvars p env = (env1, Cs)" and l: "length Cs' = p" and gr: "\<forall>C\<in>set Cs'. ground ar C"
    and gs: "gsol alg ar \<theta> \<rho>" and inv: "tinv ar (maxidx env) \<theta> A"
  obtains \<rho>1 where "gsol alg ar \<theta> \<rho>1" "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Cs'"
proof (cases "p = 0")
  case True
  with gentvars_cases(2)[OF g] l show ?thesis using that[of \<rho>] gs by simp
next
  case False
  note gc = gentvars_cases(3)[OF g]
  let ?m = "maxidx env + 1"
  define ks where "ks = map (gtv ?m) [0..<p]"
  define \<rho>1 where "\<rho>1 v S = (if S = [] then (case map_of (zip ks Cs') v of Some T \<Rightarrow> T | None \<Rightarrow> \<rho> v S) else \<rho> v S)"
    for v S
  have dk: "distinct ks" by (simp add: ks_def distinct_map gtv_inj inj_on_def)
  have lk: "length ks = length Cs'" using l by (simp add: ks_def)
  have none: "map_of (zip ks Cs') v = None" if "snd v \<le> maxidx env" for v
  proof -
    have "v \<notin> set ks" using that by (auto simp: ks_def)
    then show ?thesis by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
  qed
  have ag: "tagree (maxidx env) \<rho> \<rho>1" by (simp add: tagree_def \<rho>1_def none)
  have hs: "has_sort alg T []" for T by (cases T) auto
  have gr0: "ground ar (\<rho> v S)" for v S using gs unfolding gsol_def by blast
  have "tsol \<theta> \<rho>1"
    unfolding tsol_def
  proof (intro allI impI)
    fix v S U assume b: "vt_lookup \<theta> v = Some (S, U)"
    have vS: "(v, S) \<in> tvars_env \<theta>" by (rule tvars_envI[OF b])
    then have "snd v \<le> maxidx env" using tinv_idx[OF inv] by blast
    then have "\<rho>1 v S = \<rho> v S" by (rule tagreeD[OF ag])
    also have "\<dots> = tsubst \<rho> U" using gs by (simp add: gsol_def tsolD[OF _ b])
    also have "\<dots> = tsubst \<rho>1 U"
    proof (rule tagree_tsubst[OF ag, symmetric])
      show "\<forall>q\<in>tvars U. snd (fst q) \<le> maxidx env"
        using tvars_envI2[OF b] tinv_idx[OF inv] by (metis (no_types) UnI1 prod.collapse subsetD)
    qed
    finally show "\<rho>1 v S = tsubst \<rho>1 U" .
  qed
  moreover have "wsinst alg \<rho>1"
    using gs hs by (auto simp: gsol_def wsinst_def \<rho>1_def split: option.splits)
  moreover have "ground ar (\<rho>1 v S)" for v S
  proof (cases "S = [] \<and> map_of (zip ks Cs') v \<noteq> None")
    case True
    then obtain C where "map_of (zip ks Cs') v = Some C" by auto
    then have "C \<in> set Cs'" by (blast dest: map_of_SomeD set_zip_rightD)
    with True \<open>map_of (zip ks Cs') v = Some C\<close> gr show ?thesis by (simp add: \<rho>1_def)
  qed (auto simp: \<rho>1_def gr0)
  moreover have "map (tsubst \<rho>1) Cs = Cs'"
  proof (rule nth_equalityI)
    show "length (map (tsubst \<rho>1) Cs) = length Cs'" using gc False l by simp
    fix i assume "i < length (map (tsubst \<rho>1) Cs)"
    then have i: "i < p" using gc False by simp
    have "map_of (zip ks Cs') (ks ! i) = Some (Cs' ! i)" using map_of_zip_nth[OF lk dk] i l by simp
    then show "map (tsubst \<rho>1) Cs ! i = Cs' ! i" using gc False i by (simp add: \<rho>1_def ks_def)
  qed
  ultimately have "gsol alg ar \<theta> \<rho>1" unfolding gsol_def by blast
  with that ag \<open>map (tsubst \<rho>1) Cs = Cs'\<close> show ?thesis by blast
qed


subsection \<open>Type unification with new type variables\<close>

lemma cunify_types_unify:
  "unify_types alg T U env = Some (Ok env') \<Longrightarrow> cunify_types alg T U env = returnW env'"
  "unify_types alg T U env = Some (Err (Unif u)) \<Longrightarrow> \<exists>evs. cunify_types alg T U env = Some (evs, UErr CANTUNIFY)"
  by (simp_all add: cunify_types_def emit_def bindW_def raiseW_def)

context wf_algebra
begin

text \<open>
  Type unification of types with new type variables (\<open>A' \<supseteq> A\<close>) does not raise an exception other
  than \<open>CANTUNIFY\<close>, and it is complete.
\<close>

lemma cunify_types_cases':
  assumes "tinv ar (maxidx env) (tyenv env) A'" "tsorted alg (tyenv env)"
    "tyw ar (tyenv env) A' T" "tyw ar (tyenv env) A' U"
  shows "(\<exists>env'. cunify_types alg T U env = returnW env') \<or>
    (\<exists>evs. cunify_types alg T U env = Some (evs, UErr CANTUNIFY))"
  using unify_types_poly[OF assms] cunify_types_unify by blast

lemma cunify_types_pcomplete':
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and A': "A \<subseteq> A'" "tinv ar (maxidx env) (tyenv env) A'"
    and tw: "tyw ar (tyenv env) A' T" "tyw ar (tyenv env) A' U" and eq: "tsubst \<rho> T = tsubst \<rho> U"
  obtains env' \<rho>' where "cunify_types alg T U env = returnW env'" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
    "tenv env' = tenv env" "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X = reach (instE \<rho> env) X" "tnorm (tyenv env') T = tnorm (tyenv env') U"
    "tinv ar (maxidx env') (tyenv env') A'"
proof -
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  note ei = penv_invD[OF pi(1)]
  have g: "gsol alg ar (tyenv env) \<rho>" by (rule pcinvD(2)[OF pc])
  then have ws: "wsinst alg \<rho>" and sol: "tsol (tyenv env) \<rho>" by (simp_all add: gsol_def)
  from unify_types_poly[OF A'(2) ei(2) tw] ws sol eq obtain env' where
    u: "unify_types alg T U env = Some (Ok env')" "tenv env' = tenv env"
      "tstep alg ar A' (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env) (maxidx env) (tyenv env') (maxidx env')"
      "tsorted alg (tyenv env')" "\<And>\<rho>. tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by blast
  from tstep_gsol[OF u(3) g eq] obtain \<rho>' where g': "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    by blast
  note ts = tstepD[OF u(3)]
  have ti: "tinv ar (maxidx env') (tyenv env') A" by (rule tinv_subset[OF ts(3)]) (use A'(1) in blast)
  have pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps" by (rule pcinv_text[OF pc u(2) ts(1,2) ti u(4) g'])
  have cu: "cunify_types alg T U env = returnW env'" using u(1) by (simp add: cunify_types_def)
  have ext: "pextends env' env" using u(2) ts(1) by (simp add: pextends_def extends_def)
  have "reach (instE \<rho>' env') X = reach (instE \<rho> env) X" for X
    by (rule reach_lookup_eq) (rule instE_tagree_lookup[OF pi(2) _ u(2) g'(2)], use pi(3) in blast)
  moreover have "tnorm (tyenv env') T = tnorm (tyenv env') U"
    by (rule tnorm_eq_tsol[OF tinv_tacyc[OF ts(3)] u(5)])
  ultimately show ?thesis using that[OF cu pc' u(2) ext ts(2) g'(2)] ts(3) by blast
qed

end


subsection \<open>Normalizing arguments\<close>

context wf_algebra
begin

text \<open>
  \<open>copycons\<close> normalizes an argument: the result is in head normal form, \<open>\<eta>\<close>-long modulo the
  type environment, and its instance is equivalent to that of the argument.
\<close>

lemma pcopy_norm:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and sb: "sbinders ar rb"
    and twb: "\<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U"
    and w: "swf_tm ar rb t" and twt: "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
    and ty: "typed env W (map snd rb) t T" and bl: "below (maxidx env) t"
  obtains u1 u2 where "ok (head_norm env t) u1" "ok (eta_norm env rb u1) u2"
    "swf_tm ar rb u2" "\<forall>U\<in>tys u2. tyw ar (tyenv env) A U" "hnf u2"
    "hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u2) (tnorm (tyenv env) T)"
    "below (maxidx env) u2"
    "vps (inst \<rho> u2) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "mk_subst \<sigma> (tr (inst \<rho> u2)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))"
proof -
  let ?\<theta> = "tyenv env"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have wte: "wt_env W env" using pi(1) by (simp add: penv_inv_def)
  have swe: "swf_env ar env" by (rule penv_inv_swf_env[OF pi(1)])
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  have twe: "\<forall>U\<in>etys env. tyw ar ?\<theta> A U" using pi(3) by blast
  let ?T = "tnorm ?\<theta> T"
  have tyT: "typed env W (map snd rb) t ?T" using ty by (simp add: typed_tnorm[OF ac(1)])
  from head_norm_pterm[OF pi(1) ty _ pi(2) bl] twt twb obtain t1 where ht: "head_norm env t = Some (Ok t1)"
    by auto
  from head_norm_ptyped[OF ht refl ac wte _ tyT] twt twe tcU
  have ty1: "typed env W (map snd rb) t1 ?T" and st1: "tys t1 \<subseteq> tys t \<union> etys env" by blast+
  have tw1: "\<forall>U\<in>tys t1. tyw ar ?\<theta> A U" using st1 twt twe by blast
  let ?V = "tctx env W" and ?Ts = "map (tnorm ?\<theta>) (map snd rb)"
  have n1: "has_type ?V ?Ts (tnormt ?\<theta> t1) ?T"
    using ty1 by (simp add: typed_def tnorm_idem[OF ac(1)])
  have tc1: "\<forall>U\<in>snd ` set rb \<union> tys t1. tcons ?\<theta> U" using tw1 twb tcU by blast
  from eta_norm_pterm[OF ac tc1 n1] obtain t2 where et: "ok (eta_norm env rb t1) t2" by blast
  have et0: "ok (eta_norm (env0 env) (tnormb ?\<theta> rb) (tnormt ?\<theta> t1)) (tnormt ?\<theta> t2)"
    by (rule eta_norm_tnorm[OF et ac tc1])
  have hl: "hlong ?V ?Ts (tnormt ?\<theta> t2) ?T"
    using eta_norm_hlong[of "env0 env" ?V "tnormb ?\<theta> rb" "tnormt ?\<theta> t1" ?T "tnormt ?\<theta> t2"] n1 et0 by simp
  have tw2: "\<forall>U\<in>tys t2. tyw ar ?\<theta> A U" by (rule eta_norm_tyw[OF et pi(2) twb tw1])
  have ht': "ok (head_norm env t) t1" using ht by simp
  note hw = head_norm_swf_tm[OF ht' swe w]
  note ew = eta_norm_swf_tm[OF et swe sb hw[THEN conjunct1]]
  have hn: "hnf t2" by (rule eta_norm_phnf[OF et head_norm_hnf[OF ht refl]])
  \<comment> \<open>Ground instances\<close>
  have tct: "\<forall>U\<in>tys t. tcons ?\<theta> U" using twt tcU by blast
  have hti: "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok (inst \<rho> t1))"
    using head_norm_pinst[OF pi(1) sol ty tct bl] ht by simp
  note eii = env_invD[OF penv_inv_inst[OF pi(1) pc0(2)]]
  have e: "vt_is_empty (tyenv (instE \<rho> env))" by simp
  have bl1: "below (maxidx env) t1" using below_head_norm[OF hti refl eii(2,4)] bl by simp
  have r1: "vps (inst \<rho> t1) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    using hn_vps[OF head_norm_hn[OF hti e refl]] by simp
  have e0: "vt_is_empty (tyenv (env0 env))" by simp
  have vt: "vps (tnormt ?\<theta> t2) = vps (tnormt ?\<theta> t1)" using eta_norm_shape[OF et0 e0] by simp
  have tc12: "\<forall>U\<in>tys t1. tcons ?\<theta> U" "\<forall>U\<in>tys t2. tcons ?\<theta> U" using tw1 tw2 tcU by blast+
  have vi: "vps (inst \<rho> t2) = vps (inst \<rho> t1)"
    using vt vps_inst_tnormt[OF ac sol tc12(1)] vps_inst_tnormt[OF ac sol tc12(2)] by simp
  have bt: "below (maxidx env) t2"
  proof -
    have "vars t2 = vars t1"
      using arg_cong[OF vt, of "image fst"] by (simp add: vars_vps_eq[symmetric])
    then show ?thesis using bl1 by (simp add: below_def)
  qed
  \<comment> \<open>The solution\<close>
  note \<sigma> = solutionD[OF pc0(3)]
  have cs: "closed_on UNIV (\<sigma> \<circ> cren \<rho>)" "sat (\<sigma> \<circ> cren \<rho>) env"
    using closed_on_cren[OF \<sigma>(1)] \<sigma>(4) by (simp_all add: sat_instE)
  have "mk_subst (\<sigma> \<circ> cren \<rho>) (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma> \<circ> cren \<rho>) (tr t2)"
    using equiv_trans[OF env_equivD[OF hw[THEN conjunct2] cs] env_equivD[OF ew[THEN conjunct2] cs]] .
  then have eq: "mk_subst \<sigma> (tr (inst \<rho> t2)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))"
    by (simp add: mk_subst_inst equiv_sym)
  show ?thesis
    using that[OF ht' et ew[THEN conjunct1] tw2 hn hl bt] r1 vi eq by simp
qed

end

end
