section \<open>Problems with Type Variables: Completeness of Copying\<close>

theory Unify_Poly_Copy
  imports Unify_Poly_Simpl_Complete
begin

context csig
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
    using pi(2,3,7) tw1 wc1 pc0(2) e1 tinv_mono[OF pi(2) e1(3)] etys_same_tenv[OF e1(1)]
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

lemma tinv_index: "tinv ar n \<theta> A \<Longrightarrow> (v, S) \<in> tvars_env \<theta> \<union> A \<Longrightarrow> snd v \<le> n"
  unfolding tinv_def by (drule conjunct2, drule conjunct2, drule conjunct1, drule bspec) auto

lemma tagreeD: "tagree n \<rho> \<rho>' \<Longrightarrow> snd v \<le> n \<Longrightarrow> \<rho>' v S = \<rho> v S"
  by (cases v) (simp add: tagree_def)

abbreviation ctvars :: "ptyp list \<Rightarrow> (indexname \<times> psort) set" where
  "ctvars Cs \<equiv> \<Union> (tvars ` set Cs)"

text \<open>The new type variables have the empty sort, which is certified.\<close>

lemma tcert_gentvars: "gentvars p env = (env1, Cs) \<Longrightarrow> tcert alg (ctvars Cs)"
  by (fastforce simp: tcert_def sort_ok_def elim: gentvars_tvar)

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
    using tinv_index[OF inv, of "fst q" "snd q"] that by simp
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
    with tinv_index[OF inv, of ?v S] show False by simp
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
    then have "snd v \<le> maxidx env" using tinv_index[OF inv] by blast
    then have "\<rho>1 v S = \<rho> v S" by (rule tagreeD[OF ag])
    also have "\<dots> = tsubst \<rho> U" using gs by (simp add: gsol_def tsolD[OF _ b])
    also have "\<dots> = tsubst \<rho>1 U"
    proof (rule tagree_tsubst[OF ag, symmetric])
      show "\<forall>q\<in>tvars U. snd (fst q) \<le> maxidx env"
        using tvars_envI2[OF b] tinv_index[OF inv] by (metis (no_types) UnI1 prod.collapse subsetD)
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

end

context wf_csig
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
    and cA': "tcert alg A \<Longrightarrow> tcert alg A'"
  obtains env' \<rho>' where "cunify_types alg T U env = returnW env'" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
    "tenv env' = tenv env" "pextends env env'" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
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
  have pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
    by (rule pcinv_text[OF pc u(2) ts(1,2) ti u(4) g']) (use ts(6) cA' in auto)
  have cu: "cunify_types alg T U env = returnW env'" using u(1) by (simp add: cunify_types_def)
  have ext: "pextends env env'" using u(2) ts(1) by (simp add: pextends_def extends_def)
  have "reach (instE \<rho>' env') X = reach (instE \<rho> env) X" for X
    by (rule reach_lookup_eq) (rule instE_tagree_lookup[OF pi(2) _ u(2) g'(2)], use pi(3) in blast)
  moreover have "tnorm (tyenv env') T = tnorm (tyenv env') U"
    by (rule tnorm_eq_tsol[OF tinv_tacyc[OF ts(3)] u(5)])
  ultimately show ?thesis using that[OF cu pc' u(2) ext ts(2) g'(2)] ts(3) by blast
qed

end


context wf_csig
begin

subsection \<open>Normalizing arguments\<close>

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


context csig
begin

subsection \<open>New variables\<close>

lemma ext_subst_single: "ext_subst \<sigma> [(x, T, w)] = \<sigma>(code (AVar x) := w)"
  by (simp add: ext_subst_def fun_eq_iff)

lemma ext_typ_single: "ext_typ W [(x, T, w)] = W(x := T)"
  by (simp add: ext_typ_def fun_eq_iff)

lemma genvar_pextend:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and G: "genvar a env T = (env1, G)"
    and tw: "tyw ar (tyenv env) A T"
    and w: "no_loose_bound w 0" "\<And>e. (e, \<tau>') \<turnstile> w : trty (tsubst \<rho> T)"
  defines "\<sigma>1 \<equiv> \<sigma>(code (AVar (a, maxidx env + 1)) := w)" and "W1 \<equiv> W((a, maxidx env + 1) := T)"
  shows "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 dps" "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) W W1"
    "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T" "pextends env env1"
    "tenv env1 = tenv env" "tyenv env1 = tyenv env"
    "\<sigma>1 (code (AVar (a, maxidx env + 1))) = w" "W1 (a, maxidx env + 1) = T"
    "ityp \<rho> env1 W1 = (ityp \<rho> env W)((a, maxidx env + 1) := tsubst \<rho> T)"
proof -
  note g = genvar_simps[OF G]
  let ?ys = "[((a, maxidx env + 1), T, w)]"
  have ys: "maxidx env < snd x \<and> tyw ar (tyenv env) A G' \<and> no_loose_bound w' 0 \<and>
      (\<forall>e. (e, \<tau>') \<turnstile> w' : trty (tsubst \<rho> G'))" if "(x, G', w') \<in> set ?ys" for x G' w'
    using that tw w by auto
  have mx: "maxidx env \<le> maxidx env1" using g(3) by simp
  note ev = pcinv_extend_vars[where ys = ?ys, OF pc g(1,2) mx ys,
      unfolded ext_subst_single ext_typ_single, folded \<sigma>1_def W1_def]
  show "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 dps" "agree (maxidx env) \<sigma> \<sigma>1" "agreeV (maxidx env) W W1"
    using ev by (simp_all add: \<sigma>1_def W1_def)
  show "ityp \<rho> env1 W1 = (ityp \<rho> env W)((a, maxidx env + 1) := tsubst \<rho> T)"
    using ev(4) by (simp add: ext_typ_single)
  show "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T"
    "tenv env1 = tenv env" "tyenv env1 = tyenv env" by (rule g)+
  show "pextends env env1" using g(1,2) by (simp add: pextends_def extends_def)
  show "\<sigma>1 (code (AVar (a, maxidx env + 1))) = w" "W1 (a, maxidx env + 1) = T"
    by (simp_all add: \<sigma>1_def W1_def)
qed

text \<open>The new variables of \<^const>\<open>make_args\<close> extend a solution by given values.\<close>

lemma make_args_pextend:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and ma: "make_args a Ts env Us = (env1, args)"
    and tw: "\<forall>T\<in>set Ts \<union> set Us. tyw ar (tyenv env) A T"
    and lw: "length ws = length Us"
    and ws: "\<And>i. i < length Us \<Longrightarrow>
      no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (tsubst \<rho> (foldr fun_type Ts (Us ! i))))"
  obtains W1 \<sigma>1 xs where "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 dps" "agree (maxidx env) \<sigma> \<sigma>1"
    "agreeV (maxidx env) W W1" "maxidx env \<le> maxidx env1" "pextends env env1"
    "tenv env1 = tenv env" "tyenv env1 = tyenv env"
    "length xs = length Us" "distinct xs" "\<forall>x\<in>set xs. maxidx env < snd x \<and> snd x \<le> maxidx env1"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    "\<forall>i<length Us. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    "\<And>y. snd y \<le> maxidx env \<Longrightarrow> ityp \<rho> env1 W1 y = ityp \<rho> env W y"
    "\<forall>i<length Us. ityp \<rho> env1 W1 (xs ! i) = tsubst \<rho> (foldr fun_type Ts (Us ! i))"
proof (cases "Us = []")
  case True
  with ma have "env1 = env" "args = []" by (simp_all add: make_args_def)
  with True show ?thesis using that[of W \<sigma> "[]"] pc by (simp add: pextends_def extends_def)
next
  case False
  define Gs where "Gs = map (\<lambda>T. foldr fun_type Ts T) Us"
  obtain env' vs where g: "genvars a env Gs = (env', vs)" by (cases "genvars a env Gs")
  with False ma have e: "env1 = env'" "args = map (\<lambda>var. combound var 0 (length Ts)) vs"
    by (simp_all add: make_args_def Gs_def)
  note gm = genvars_maxidx[OF g] and gs = genvars_simps[OF g]
  define xs where "xs = map var_of vs"
  have lvs: "length vs = length Us" using list_all2_lengthD[OF gs(3)] by (simp add: Gs_def)
  have vs: "vs = map2 Var xs Gs" using list_all2_Var[OF gs(3)] by (simp add: xs_def)
  have dxs: "distinct xs" using genvs_distinct[of 0 a "maxidx env + 1" Gs] gm(2) by (simp add: xs_def)
  have ixs: "snd x = maxidx env + 1" if "x \<in> set xs" for x
    using that genvs_index gm(2) by (auto simp: xs_def)
  have lxs: "length xs = length Us" using lvs by (simp add: xs_def)
  define ys where "ys = zip xs (zip Gs ws)"
  have m1: "maxidx env1 = maxidx env + 1" using gm(1) e(1) by simp
  have yv: "maxidx env < snd x \<and> tyw ar (tyenv env) A G \<and> no_loose_bound w 0 \<and>
      (\<forall>e. (e, \<tau>') \<turnstile> w : trty (tsubst \<rho> G))"
    if "(x, G, w) \<in> set ys" for x G w
  proof -
    from that obtain i where i: "i < length Us" "x = xs ! i" "G = Gs ! i" "w = ws ! i"
      using lxs lw by (auto simp: ys_def in_set_conv_nth Gs_def)
    have "x \<in> set xs" using i(1,2) lxs by simp
    moreover have "tyw ar (tyenv env) A G" using i(1,3) tw by (simp add: Gs_def tyw_foldr_fun)
    ultimately show ?thesis using ixs ws[OF i(1)] i by (simp add: Gs_def)
  qed
  have mx: "maxidx env \<le> maxidx env1" using m1 by simp
  note ev = pcinv_extend_vars[where ys = ys, OF pc gs(1,2)[folded e(1)] mx yv]
  define \<sigma>1 where "\<sigma>1 = ext_subst \<sigma> ys"
  define W1 where "W1 = ext_typ W ys"
  have mo: "map_of ys (xs ! i) = Some (Gs ! i, ws ! i)" if i: "i < length Us" for i
    using map_of_zip_nth[of xs "zip Gs ws" i] lxs lw dxs i by (simp add: ys_def Gs_def)
  have "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts U)) 0 (length Ts)) xs Us"
    using lxs by (simp add: e(2) vs Gs_def map_zip_map2 zip_map2 map_map comp_def split_def)
  moreover have "\<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> W1 (xs ! i) = foldr fun_type Ts (Us ! i)"
    if i: "i < length Us" for i
    using mo[OF i] i by (simp add: \<sigma>1_def W1_def ext_subst_AVar ext_typ_simp Gs_def)
  moreover have "ityp \<rho> env1 W1 y = ityp \<rho> env W y" if "snd y \<le> maxidx env" for y
  proof -
    have "map_of ys y = None"
    proof (rule ccontr)
      assume "map_of ys y \<noteq> None"
      then obtain G w where "map_of ys y = Some (G, w)" by auto
      then have "(y, G, w) \<in> set ys" by (rule map_of_SomeD)
      from yv[OF this] that show False by simp
    qed
    then show ?thesis using fun_cong[OF ev(4), of y] by (simp add: W1_def ext_typ_simp map_of_imap)
  qed
  moreover have "ityp \<rho> env1 W1 (xs ! i) = tsubst \<rho> (foldr fun_type Ts (Us ! i))" if i: "i < length Us" for i
    using fun_cong[OF ev(4), of "xs ! i"] mo[OF i] i by (simp add: W1_def ext_typ_simp map_of_imap Gs_def)
  ultimately show ?thesis
    using that[of W1 \<sigma>1 xs] ev(1-3) m1 gs(1,2) e(1) lxs dxs ixs
    by (simp add: \<sigma>1_def W1_def pextends_def extends_def)
qed


subsection \<open>Extensions of states\<close>

text \<open>
  \<open>psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV\<close>: the state \<open>(env', dps')\<close> is in the
  invariant for the extensions \<open>W'\<close>, \<open>\<sigma>'\<close> and \<open>\<rho>'\<close> of \<open>W\<close>, \<open>\<sigma>\<close> and \<open>\<rho>\<close>, and only the variables
  of the instance that are reachable from \<open>D\<close> and the new variables \<open>NV\<close> are reachable from it
  (the analogue of \<^const>\<open>sext\<close>).
\<close>

definition psext :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV \<longleftrightarrow>
    pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env' dps' \<and> agreeV (maxidx env) W W' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> maxidx env \<le> maxidx env' \<and> pextends env env' \<and> finite NV \<and>
    (\<forall>y\<in>NV. maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env') \<and>
    (\<forall>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV) \<and>
    ivps \<rho>' dps' \<subseteq> reach (instE \<rho> env) D \<union> NV"

lemma psextD:
  assumes "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
  shows "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env' dps'" "agreeV (maxidx env) W W'" "agree (maxidx env) \<sigma> \<sigma>'"
    "tagree (maxidx env) \<rho> \<rho>'" "maxidx env \<le> maxidx env'" "pextends env env'" "finite NV"
    "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV"
    "ivps \<rho>' dps' \<subseteq> reach (instE \<rho> env) D \<union> NV"
  using assms by (auto simp: psext_def)

lemma psextI:
  assumes "pcinv alg ar A W' \<rho>' \<tau>' \<sigma>' env' dps'" "agreeV (maxidx env) W W'" "agree (maxidx env) \<sigma> \<sigma>'"
    "tagree (maxidx env) \<rho> \<rho>'" "maxidx env \<le> maxidx env'" "pextends env env'" "finite NV"
    "\<And>y. y \<in> NV \<Longrightarrow> maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV"
    "ivps \<rho>' dps' \<subseteq> reach (instE \<rho> env) D \<union> NV"
  shows "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
  using assms by (auto simp: psext_def)

lemma psext_refl:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow> ivps \<rho> dps \<subseteq> D \<Longrightarrow> psext alg ar A W \<tau>' \<sigma> \<rho> env W \<sigma> \<rho> env dps D {}"
  using reach_incl[of D "instE \<rho> env"]
  by (auto simp: psext_def reach_Un pextends_def extends_def agreeV_def agree_def)

lemma psext_mono:
  assumes s: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV" and D: "D \<subseteq> D'"
  shows "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D' NV"
proof -
  have r: "reach (instE \<rho> env) (X \<union> D) \<subseteq> reach (instE \<rho> env) (X \<union> D')" for X
    using D by (intro reach_subset) blast
  have "reach (instE \<rho> env) D \<subseteq> reach (instE \<rho> env) D'" using D by (rule reach_subset)
  then have "ivps \<rho>' dps' \<subseteq> reach (instE \<rho> env) D' \<union> NV" using s by (auto simp: psext_def)
  moreover have "reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> D') \<union> NV" for X
    using s r[of X] by (auto simp: psext_def)
  ultimately show ?thesis using s by (simp add: psext_def)
qed

lemma psext_trans:
  assumes s1: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>1 env1 dps1 D1 NV1"
    and s2: "psext alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 W2 \<sigma>2 \<rho>2 env2 dps2 D2 NV2"
    and fr: "fresh_env env" and D: "D2 \<subseteq> reach (instE \<rho> env) D1 \<union> NV1"
  shows "psext alg ar A W \<tau>' \<sigma> \<rho> env W2 \<sigma>2 \<rho>2 env2 dps2 D1 (NV1 \<union> NV2)"
proof -
  let ?e = "instE \<rho> env" and ?e1 = "instE \<rho>1 env1" and ?e2 = "instE \<rho>2 env2"
  note c1 = psextD[OF s1] and c2 = psextD[OF s2]
  have fr': "fresh_env ?e" using fr by simp
  have "\<forall>y\<in>NV1. maxidx ?e < snd (fst y)" using c1(8) by simp
  then have nv1: "reach ?e NV1 = NV1" by (rule reach_new[OF fr'])
  have rD2: "reach ?e D2 \<subseteq> reach ?e D1 \<union> NV1"
    using reach_mono[of D2 ?e "D1 \<union> NV1"] D reach_incl[of "D1 \<union> NV1" ?e] nv1
    by (auto simp: reach_Un)
  have r: "reach ?e2 X \<subseteq> reach ?e (X \<union> D1) \<union> (NV1 \<union> NV2)" for X
  proof -
    have "reach ?e2 X \<subseteq> reach ?e1 (X \<union> D2) \<union> NV2" by (rule c2(9))
    also have "\<dots> \<subseteq> reach ?e (X \<union> D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(9)[of "X \<union> D2"] by blast
    also have "\<dots> \<subseteq> reach ?e (X \<union> D1) \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  have v: "ivps \<rho>2 dps2 \<subseteq> reach ?e D1 \<union> (NV1 \<union> NV2)"
  proof -
    have "ivps \<rho>2 dps2 \<subseteq> reach ?e1 D2 \<union> NV2" by (rule c2(10))
    also have "\<dots> \<subseteq> reach ?e (D2 \<union> D1) \<union> NV1 \<union> NV2" using c1(9)[of D2] by blast
    also have "\<dots> \<subseteq> reach ?e D1 \<union> (NV1 \<union> NV2)" using rD2 by (auto simp: reach_Un)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule psextI[OF c2(1) _ _ _ _ _ _ _ r v])
    show "agreeV (maxidx env) W W2" using agreeV_trans[OF c1(2) c2(2) c1(5)] .
    show "agree (maxidx env) \<sigma> \<sigma>2" using agree_trans[OF c1(3) c2(3) c1(5)] .
    show "tagree (maxidx env) \<rho> \<rho>2" using tagree_trans[OF c1(4) c2(4)] c1(5) by simp
    show "maxidx env \<le> maxidx env2" using c1(5) c2(5) by simp
    show "pextends env env2" using c1(6) c2(6) by (rule pextends_trans)
    show "finite (NV1 \<union> NV2)" using c1(7) c2(7) by simp
    show "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env2" if "y \<in> NV1 \<union> NV2" for y
      using that c1(8)[of y] c2(8)[of y] c1(5) c2(5) by auto
  qed
qed


subsection \<open>Copies: types\<close>

lemma tyw_tnorm:
  assumes "tinv ar n \<theta> A" "tyw ar \<theta> A T"
  shows "tyw ar \<theta> A (tnorm \<theta> T)"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF assms(1)])
  have "tvars (tnorm \<theta> T) \<subseteq> tvars_env \<theta> \<union> A" using tvars_tnorm[OF ac, of T] assms(2) by (auto simp: tyw_def)
  moreover have "wft ar (tnorm \<theta> T)"
  proof (rule wft_tnorm[OF ac])
    show "wft ar U" if "vt_lookup \<theta> v = Some (S, U)" for v S U by (rule tinv_wft[OF assms(1) that])
    show "wft ar T" using assms(2) by (simp add: tyw_def)
  qed
  moreover have "uvars \<theta> (tnorm \<theta> T) = uvars \<theta> T" by (simp add: uvars_def tnorm_idem[OF ac])
  ultimately show ?thesis using assms(2) by (simp add: tyw_def)
qed

lemma arg_types_nonfun: "\<not> is_funT T \<Longrightarrow> arg_types T = []"
  by (cases T rule: arg_types.cases) auto

lemma is_funT_arg_types: "is_funT T \<longleftrightarrow> arg_types T \<noteq> []"
  by (cases T rule: arg_types.cases) auto

lemma nonfun_tsubst: "\<not> is_funT T \<Longrightarrow> \<not> is_TVar T \<Longrightarrow> \<not> is_funT (tsubst \<rho> T)"
  by (cases T rule: is_funT.cases) auto

lemma tvars_res_type: "tvars (res_type T) \<subseteq> tvars T"
  by (induction T rule: res_type.induct) auto

text \<open>The k-condition bounds the number of argument types of the instance of a result type.\<close>

lemma kok_res_type:
  assumes "kok k \<rho> \<theta> T"
  shows "length (arg_types (tsubst \<rho> (res_type (tnorm \<theta> T)))) \<le> k"
proof (cases "is_TVar (res_type (tnorm \<theta> T))")
  case True
  then obtain v S where R: "res_type (tnorm \<theta> T) = TVar v S" by (cases "res_type (tnorm \<theta> T)") auto
  have "(v, S) \<in> tvars (tnorm \<theta> T)" using tvars_res_type[of "tnorm \<theta> T"] R by auto
  with assms have "aok k (\<rho> v S)" by (auto simp: kok_def)
  then show ?thesis using R aok_arg_types by simp
next
  case False
  have "\<not> is_funT (tsubst \<rho> (res_type (tnorm \<theta> T)))" by (rule nonfun_tsubst[OF res_type_base False])
  then show ?thesis by (simp add: arg_types_nonfun)
qed

lemma mapM_fastype_ptnorm:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and tc: "\<forall>U\<in>snd ` set rb. tcons (tyenv env) U"
  shows "list_all2 (typed env W (map snd rb)) ts Ts \<Longrightarrow> \<forall>t\<in>set ts. \<forall>U\<in>tys t. tcons (tyenv env) U \<Longrightarrow>
    \<exists>Ts'. mapM (fastype env rb) ts = return Ts' \<and> map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts"
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons t ts T Ts)
  from Cons.hyps(1) have "has_type (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t)
      (tnorm (tyenv env) T)" by (simp add: typed_def)
  from env_fastype_pterm[OF ac _ this] tc Cons.prems obtain T' where
    T': "ok (fastype env rb t) T'" "tnorm (tyenv env) T' = tnorm (tyenv env) T"
    by (auto simp: fastype_def)
  from Cons.IH Cons.prems obtain Ts' where "mapM (fastype env rb) ts = return Ts'"
    "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts" by auto
  with T' show ?case by (intro exI[of _ "T' # Ts'"]) (simp add: bindM_def return_def)
qed

lemma mapM_fastype_tyw:
  "mapM (fastype env rb) ts = return Ts' \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow>
    \<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U \<Longrightarrow> \<forall>t\<in>set ts. \<forall>U\<in>tys t. tyw ar (tyenv env) A U \<Longrightarrow>
    \<forall>T\<in>set Ts'. tyw ar (tyenv env) A T"
proof (induction ts arbitrary: Ts')
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons t ts)
  from Cons.prems(1) obtain T Ts where T: "ok (fastype env rb t) T" and Ts: "mapM (fastype env rb) ts = return Ts"
    and e: "Ts' = T # Ts"
    by (auto simp: bindM_def return_def split: option.splits res.splits)
  have "tyw ar (tyenv env) A T" using fastype_tyw[OF T Cons.prems(2,3)] Cons.prems(4) by simp
  with Cons.IH[OF Ts Cons.prems(2,3)] Cons.prems(4) e show ?case by simp
qed

lemma mc_punfold:
  assumes "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts"
  shows "mc cfg vname rb targs u env dps =
    (case head_of u of
        Abs a T body \<Rightarrow> do {
          s \<leftarrow> mc cfg vname ((a, T) # rb) (map (incr_boundvars 1) targs @ [Bound 0]) body env dps;
          returnW (S_MapAbs a T s)}
      | Var w _ \<Rightarrow>
          (let (env', newhd) = genvar (fst w) env (foldr fun_type Ts base) in
            returnW (S_Single (El_C (combound newhd 0 (length Ts)) env'
              ((rb, list_comb newhd targs, u) # dps))))
      | _ \<Rightarrow> do {
          projs \<leftarrow> make_projs u targs Ts targs;
          matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts (rev projs)})"
  by (subst mc.simps) (simp add: assms fst_strip_comb liftM_return Let_def)


subsection \<open>Copies: the invariants\<close>

abbreviation ibctx :: "tinst \<Rightarrow> ptyp list \<Rightarrow> nat \<Rightarrow> type" where
  "ibctx \<rho> Ts \<equiv> bctx (map (tsubst \<rho>) Ts)"

text \<open>
  \<open>pmc_pre\<close>: the assumptions on a call \<open>mc cfg vname rb targs u env dps\<close> with a target \<open>s\<close>, the
  analogue of \<^const>\<open>mc_pre\<close>: \<open>u\<close> is \<open>\<eta>\<close>-long modulo the type environment, the instance of its
  result type under \<open>\<rho>\<close> is not a function type (so the instance of \<open>u\<close> is \<open>\<eta>\<close>-long), and the
  abstraction \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>n. s\<close> applied to the instances of \<open>targs\<close> is the instance of \<open>u\<close>.
\<close>

definition pmc_pre :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow>
    pterm \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow> bool" where
  "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<longleftrightarrow>
    pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<and> kokA k \<rho> (tyenv env) A \<and>
    sbinders ar rb \<and> (\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T) \<and>
    (\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)) \<and>
    list_all2 (typed env W (map snd rb)) targs Ts \<and> (\<forall>T\<in>set Ts. tyw ar (tyenv env) A T) \<and>
    swf_tm ar rb u \<and> (\<forall>T\<in>tys u. tyw ar (tyenv env) A T) \<and> hnf u \<and> below (maxidx env) u \<and>
    hlong (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) (tnorm (tyenv env) U) \<and>
    tyw ar (tyenv env) A U \<and> \<not> is_funT (tsubst \<rho> (res_type (tnorm (tyenv env) U))) \<and>
    (ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U) \<and> no_redex s \<and> no_loose_bound s (length Ts) \<and>
    Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"

text \<open>
  \<open>pcopy_res\<close>: a copy \<open>u'\<close> with the extensions of the solution and the typing: its instance is
  the target, and the values of the new variables are smaller than the target, strictly by \<open>m\<close>.
\<close>

definition pcopy_res :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow>
    nat \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s m u' env' dps' W' \<sigma>' \<rho>' NV \<longleftrightarrow>
    psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV \<and> typed env' W' (rev Ts) u' U \<and>
    swf_cp ar (length Ts) u' \<and> (\<forall>T\<in>tys u'. tyw ar (tyenv env') A T) \<and> below (maxidx env') u' \<and>
    vps (inst \<rho>' u') \<subseteq> NV \<and> mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s \<and>
    (\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + m \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"

abbreviation pmc_dom :: "tinst \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set" where
  "pmc_dom \<rho> u targs dps \<equiv> vps (inst \<rho> u) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps"

definition pmc_post :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> cfg \<Rightarrow> name \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> binders \<Rightarrow>
    pterm list \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> dB \<Rightarrow> bool" where
  "pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<longleftrightarrow>
    (\<exists>sq. okW (mc cfg vname rb targs u env dps) sq \<and>
      (\<exists>u' env' dps' W' \<sigma>' \<rho>' NV. ev cfg sq (El_C u' env' dps') \<and>
        pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs dps) Ts U s
          (if is_Var (head_of (strip_abs_body u)) then 0 else 1) u' env' dps' W' \<sigma>' \<rho>' NV))"


subsection \<open>Copies: auxiliary lemmas\<close>

lemma body_type_tyw:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> tyw ar (tyenv env) A T \<Longrightarrow> tyw ar (tyenv env) A B"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> length Ts = 2")
      case True
      then have "length Ts = Suc (Suc 0)" by simp
      then obtain X Y where Ts: "Ts = [X, Y]" by (auto simp: length_Suc_conv)
      have "tyw ar (tyenv env) A Y" using "1.prems"(3) Type Ts tyw_Type by simp
      with "1.hyps" "1.prems"(1,2) Type Ts True show ?thesis by (auto intro: "1.IH")
    next
      case False
      with "1.hyps" "1.prems" Type show ?thesis
        by (auto simp: return_def split: list.splits if_splits)
    qed
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) v S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest "1.prems" show ?thesis by (simp add: return_def)
    next
      fix U assume U: "r' = Some U" "vt_lookup (tyenv env) v = Some (S, U)"
      have "tyw ar (tyenv env) A U" by (rule tyw_lookup[OF "1.prems"(2) _ U(2)]) (use "1.prems"(3) TVar in simp)
      with rest U(1) "1.IH"[of env U "Ok B" B] "1.prems"(2) show ?thesis by simp
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma tsubst_tnorm_eq:
  "tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tcons \<theta> X \<Longrightarrow> tcons \<theta> Y \<Longrightarrow> tnorm \<theta> X = tnorm \<theta> Y \<Longrightarrow>
    tsubst \<rho> X = tsubst \<rho> Y"
  by (metis tsubst_tnorm)

lemma tnorm_foldr_fun: "tnorm \<theta> (foldr fun_type Us B) = foldr fun_type (map (tnorm \<theta>) Us) (tnorm \<theta> B)"
  by (induction Us) auto

lemma tsubst_foldr_fun: "tsubst \<rho> (foldr fun_type Us B) = foldr fun_type (map (tsubst \<rho>) Us) (tsubst \<rho> B)"
  by (induction Us) auto

lemma tys_combound[simp]: "tys (combound t n k) = tys t"
  by (induction k arbitrary: n) auto

lemma vars_combound[simp]: "vars (combound t n k) = vars t"
  by (induction k arbitrary: n) auto

lemma tnormt_combound[simp]: "tnormt \<theta> (combound t n k) = combound (tnormt \<theta> t) n k"
  by (induction k arbitrary: n) auto

lemma inst_combound[simp]: "inst \<rho> (combound t n k) = combound (inst \<rho> t) n k"
  by (induction k arbitrary: n) auto

lemma typed_Var_list_comb:
  assumes "tctx env W x = tnorm (tyenv env) (foldr fun_type Us B)" "list_all2 (typed env W Bs) ts Us"
  shows "typed env W Bs (list_comb (Var x (foldr fun_type Us B)) ts) B"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  have hv: "has_type ?V (map (tnorm ?\<theta>) Bs) (Var x (tnorm ?\<theta> (foldr fun_type Us B)))
      (foldr fun_type (map (tnorm ?\<theta>) Us) (tnorm ?\<theta> B))"
    using assms(1) by (simp add: has_type.Var tnorm_foldr_fun)
  have "list_all2 (has_type ?V (map (tnorm ?\<theta>) Bs)) (map (tnormt ?\<theta>) ts) (map (tnorm ?\<theta>) Us)"
    unfolding list_all2_map1 list_all2_map2 using assms(2) by (rule list_all2_mono) (simp add: typed_def)
  with hv show ?thesis by (auto simp: typed_def has_type_list_comb)
qed

lemma typed_combound_Var:
  assumes "tctx env W x = tnorm (tyenv env) (foldr fun_type Ts B)"
  shows "typed env W (rev Ts) (combound (Var x (foldr fun_type Ts B)) 0 (length Ts)) B"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  have "has_type ?V (rev (map (tnorm ?\<theta>) Ts) @ []) (Var x (tnorm ?\<theta> (foldr fun_type Ts B)))
      (foldr fun_type (map (tnorm ?\<theta>) Ts) (tnorm ?\<theta> B))"
    using assms by (simp add: has_type.Var tnorm_foldr_fun)
  from has_type_combound0[OF this] show ?thesis by (simp add: typed_def rev_map)
qed

lemma typed_pext:
  assumes "typed env W Ts t T" "tyenv env1 = tyenv env" "wcons W env" "wcons W1 env1"
    "agreeV (maxidx env) W W1" "below (maxidx env) t"
  shows "typed env1 W1 Ts t T"
proof (rule typed_tctx_cong[OF assms(1,2)])
  fix x assume "x \<in> vars t"
  then have "snd x \<le> maxidx env" using assms(6) by (simp add: below_def)
  then have "W1 x = W x" using assms(5) unfolding agreeV_def by blast
  then show "tctx env1 W1 x = tctx env W x"
    using wcons_tctx[OF assms(3)] wcons_tctx[OF assms(4)] assms(2) by simp
qed

lemma pcinv_Cons:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow> swf_dp ar dp \<Longrightarrow> \<forall>T\<in>dtys dp. tyw ar (tyenv env) A T \<Longrightarrow>
    ptyped env W dp \<Longrightarrow> dp_below (maxidx env) dp \<Longrightarrow> dsolved \<sigma> (instd \<rho> dp) \<Longrightarrow>
    pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dp # dps)"
  by (simp add: pcinv_def pinv_def)

text \<open>The types computed by \<^const>\<open>mc\<close>.\<close>

lemma pmc_types:
  assumes pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
  obtains T0 base Ts' where "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts"
    "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T" "tyw ar (tyenv env) A T0" "tyw ar (tyenv env) A base"
    "has_type (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) (head_of u))
      (tnorm (tyenv env) T0)"
    "tnorm (tyenv env) base = res_type (tnorm (tyenv env) U)"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    and hl: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    unfolding pmc_pre_def by blast+
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)" by (rule hlong_typed[OF hl])
  from has_type_head_of[OF tyu] obtain Th where tyh: "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) Th" by auto
  have tch: "\<forall>X\<in>set (map snd rb) \<union> tys (head_of u). tcons ?\<theta> X"
    using twb twu tys_head_of[of u] tcU by auto
  from env_fastype_pterm[OF ac tch tyh] obtain T0 where
    f: "ok (fastype env rb (head_of u)) T0" "tnorm ?\<theta> T0 = Th" by (auto simp: fastype_def)
  have twT0: "tyw ar ?\<theta> A T0" using fastype_tyw[OF f(1) pi(2) twb] twu tys_head_of[of u] by blast
  have rTh: "res_type Th = res_type (tnorm ?\<theta> U)"
  proof (cases "is_Abs u")
    case True
    then have "head_of u = u" by (cases u) auto
    with tyh tyu has_type_unique show ?thesis by metis
  next
    case False
    then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
    from hlong_nonAbs[OF hl this] have nf: "\<not> is_funT (tnorm ?\<theta> U)" by simp
    have "res_type Th = tnorm ?\<theta> U" using res_type_head(1)[OF tyu nf] tyh by simp
    with nf show ?thesis by (simp add: arg_types_nonfun arg_res_type_base)
  qed
  have "tnorm ?\<theta> T0 = foldr fun_type (arg_types Th) (res_type Th)" using f(2) by (simp add: arg_res_type)
  from body_type_ptnorm[OF ac tcU[OF twT0] this res_type_base] obtain base where
    b: "body_type env T0 = return base" "tnorm ?\<theta> base = res_type Th" by blast
  have twb0: "tyw ar ?\<theta> A base" using body_type_tyw[OF b(1)[unfolded return_def] refl pi(2) twT0] .
  have tct: "\<forall>t\<in>set targs. \<forall>X\<in>tys t. tcons ?\<theta> X" using tg tcU by blast
  from mapM_fastype_ptnorm[OF ac _ tgty tct] twb tcU obtain Ts' where
    m: "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts" by blast
  have twTs: "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" by (rule mapM_fastype_tyw[OF m(1) pi(2) twb]) (use tg in blast)
  show ?thesis using that[OF _ b(1) m twTs twT0 twb0] f tyh b(2) rTh by (simp add: return_def)
qed


lemma typed_tnorm_cong:
  "typed env W Ts t T \<Longrightarrow> map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts \<Longrightarrow>
    tnorm (tyenv env) T' = tnorm (tyenv env) T \<Longrightarrow> typed env W Ts' t T'"
  by (simp add: typed_def)

lemma list_all2_typed_tnorm:
  "list_all2 (typed env W Bs) ts Ts \<Longrightarrow> map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts \<Longrightarrow>
    list_all2 (typed env W Bs) ts Ts'"
proof -
  assume a: "list_all2 (typed env W Bs) ts Ts" "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts"
  have l: "length Ts' = length Ts" using arg_cong[OF a(2), of length] by simp
  show ?thesis unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length ts = length Ts'" using list_all2_lengthD[OF a(1)] l by simp
    fix i assume i: "i < length ts"
    have "tnorm (tyenv env) (Ts' ! i) = tnorm (tyenv env) (Ts ! i)"
      using arg_cong[OF a(2), of "\<lambda>xs. xs ! i"] i l list_all2_lengthD[OF a(1)] by simp
    with a(1) i show "typed env W Bs (ts ! i) (Ts' ! i)" by (auto simp: list_all2_conv_all_nth typed_def)
  qed
qed

lemma map_tsubst_tnorm:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>" "\<forall>X\<in>set Ts. tcons \<theta> X" "\<forall>X\<in>set Ts'. tcons \<theta> X"
    "map (tnorm \<theta>) Ts' = map (tnorm \<theta>) Ts"
  shows "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
proof -
  have "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) (map (tnorm \<theta>) Ts')"
    using tsubst_tnorm[OF assms(1-3)] assms(5) by simp
  also have "\<dots> = map (tsubst \<rho>) (map (tnorm \<theta>) Ts)" using assms(6) by simp
  also have "\<dots> = map (tsubst \<rho>) Ts" using tsubst_tnorm[OF assms(1-3)] assms(4) by simp
  finally show ?thesis .
qed

lemma list_all2_typed_pext:
  assumes "list_all2 (typed env W Bs) ts Ts" "\<forall>t\<in>set ts. below (maxidx env) t"
    "tyenv env1 = tyenv env" "wcons W env" "wcons W1 env1" "agreeV (maxidx env) W W1"
  shows "list_all2 (typed env1 W1 Bs) ts Ts"
  using assms(1,2) by (induction rule: list_all2_induct) (auto intro: typed_pext[OF _ assms(3-6)])


subsection \<open>Copies: flexible heads\<close>

text \<open>A flexible head: a new variable for the copy, with a new pair.\<close>

text \<open>
  A new variable \<open>?G\<close> of type \<open>Ts' \<Rightarrow> Y\<close> for \<open>u\<close>: the copy is \<open>?G\<close> applied to the bound
  variables, with the new pair \<open>?G targs =?= u\<close>.
\<close>

lemma pflex_copy:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar (tyenv env) A T"
    and wu: "swf_tm ar rb u" and twu: "\<forall>T\<in>tys u. tyw ar (tyenv env) A T" and bu: "below (maxidx env) u"
    and tyu: "typed env W (map snd rb) u U" and twU: "tyw ar (tyenv env) A U"
    and Ts': "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts" "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T"
    and Y: "tyw ar (tyenv env) A Y" "tnorm (tyenv env) Y = tnorm (tyenv env) U"
    and g: "genvar a env (foldr fun_type Ts' Y) = (env1, newhd)"
    and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
    and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
  shows "\<exists>W1 \<sigma>1 NV. pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs dps) Ts U s 0
    (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps) W1 \<sigma>1 \<rho> NV"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF Ts'(1), of length] by simp
  have iTs: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    by (rule map_tsubst_tnorm[OF ac sol _ _ Ts'(1)]) (use twTs Ts'(2) tcU in blast)+
  have ib: "tsubst \<rho> Y = tsubst \<rho> U" by (rule tsubst_tnorm_eq[OF ac sol tcU[OF Y(1)] tcU[OF twU] Y(2)])
  define GT where "GT = foldr fun_type Ts' Y"
  have twGT: "tyw ar ?\<theta> A GT" using Ts'(2) Y(1) by (simp add: GT_def tyw_foldr_fun)
  have iGT: "tsubst \<rho> GT = foldr fun_type (map (tsubst \<rho>) Ts) (tsubst \<rho> U)"
    using iTs ib by (simp add: GT_def tsubst_foldr_fun)
  define G where "G = (a, maxidx env + 1)"
  define \<sigma>1 where "\<sigma>1 = \<sigma>(code (AVar G) := Abs_m (length Ts) s)"
  define W1 where "W1 = W(G := GT)"
  have w0: "no_loose_bound (Abs_m (length Ts) s) 0" using nls by (simp add: loose_bound_Abs_m)
  have wty: "(e, \<tau>') \<turnstile> Abs_m (length Ts) s : trty (tsubst \<rho> GT)" for e
  proof -
    have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m (length (map trty (map (tsubst \<rho>) Ts))) s :
        map trty (map (tsubst \<rho>) Ts) \<Rrightarrow> trty (tsubst \<rho> U)"
      by (rule typing_Abs_m) (use tys in simp)
    from typing_closed[OF this] w0 show ?thesis by (simp add: iGT trty_foldr)
  qed
  note ge = genvar_pextend[OF pc g[folded GT_def] twGT w0 wty, folded G_def \<sigma>1_def W1_def]
  note pi1 = pinvD[OF pcinvD(1)[OF ge(1)]]
  define dp where "dp = (rb, list_comb newhd targs, u)"
  have tctxG: "tctx env1 W1 G = tnorm (tyenv env1) GT" using wcons_tctx[OF pi1(6)] ge(10) by simp
  have tg1: "list_all2 (typed env1 W1 (map snd rb)) targs Ts'"
    using list_all2_typed_tnorm[OF list_all2_typed_pext[OF tgty _ ge(8) pi(6) pi1(6) ge(3)] Ts'(1)[folded ge(8)]] tg
    by blast
  have tyl: "typed env1 W1 (map snd rb) (list_comb newhd targs) Y"
    using typed_Var_list_comb[OF tctxG[unfolded GT_def] tg1] ge(5) by (simp add: GT_def)
  have tyu0: "typed env W (map snd rb) u Y" using tyu Y(2) by (simp add: typed_def)
  have tyu1: "typed env1 W1 (map snd rb) u Y" by (rule typed_pext[OF tyu0 ge(8) pi(6) pi1(6) ge(3) bu])
  have bGT: "below (maxidx env1) (list_comb newhd targs)"
  proof -
    have "below (maxidx env1) newhd" using ge(4,5) by (simp add: below_def G_def)
    moreover have "\<forall>t\<in>set targs. below (maxidx env1) t" using tg ge(4) by (auto intro: below_mono)
    ultimately show ?thesis by (simp add: below_list_comb)
  qed
  have ds: "dsolved \<sigma>1 (instd \<rho> dp)"
  proof -
    have ta1: "map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho> t))) targs = map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
      using tg mk_subst_agree[OF _ ge(2)] by (auto simp: below_def)
    have "mk_subst \<sigma>1 (tr (inst \<rho> (list_comb newhd targs))) =
        Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
      using ge(5,9) ta1 by (simp add: inst_list_comb tr_list_comb comp_def G_def del: map_eq_conv)
    moreover have "mk_subst \<sigma>1 (tr (inst \<rho> u)) = mk_subst \<sigma> (tr (inst \<rho> u))"
      using mk_subst_agree[OF _ ge(2)] bu by (simp add: below_def)
    ultimately show ?thesis unfolding dp_def instd_simp dsolved_dsolvedB dsolvedB_unabs using eqs by simp
  qed
  have pc1: "pcinv alg ar A W1 \<rho> \<tau>' \<sigma>1 env1 (dp # dps)"
  proof (rule pcinv_Cons[OF ge(1) _ _ _ _ ds])
    have "swf_tm ar rb newhd" using ge(5) twGT by (simp add: swf_tm_def tyw_def)
    then show "swf_dp ar dp" using sb wu tg by (simp add: dp_def swf_dp_def swf_tm_list_comb)
    show "\<forall>T\<in>dtys dp. tyw ar (tyenv env1) A T"
      using twb twu tg twGT ge(5,8) by (auto simp: dp_def tys_list_comb)
    show "ptyped env1 W1 dp" using tyl tyu1 by (auto simp: dp_def)
    show "dp_below (maxidx env1) dp" using bGT bu ge(4) by (auto simp: dp_def dp_below_def intro: below_mono)
  qed
  define NV where "NV = {(G, tsubst \<rho> GT)}"
  define D where "D = pmc_dom \<rho> u targs dps"
  have rr: "reach (instE \<rho> env1) X = reach (instE \<rho> env) X" for X
    by (rule reach_lookup_eq) (simp add: ge(7))
  have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho> env1 (dp # dps) D NV"
  proof (rule psextI[OF pc1 ge(3,2)])
    show "maxidx env \<le> maxidx env1" using ge(4) by simp
    show "pextends env env1" by (rule ge(6))
    show "finite NV" by (simp add: NV_def)
    show "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env1" if "y \<in> NV" for y
      using that ge(4) by (simp add: NV_def G_def)
    show "reach (instE \<rho> env1) X \<subseteq> reach (instE \<rho> env) (X \<union> D) \<union> NV" for X
      using reach_subset[of X "X \<union> D" "instE \<rho> env"] rr by auto
    have "ivps \<rho> (dp # dps) \<subseteq> D \<union> NV"
      using ge(5) by (auto simp: dp_def vps_dp_def vps_list_comb inst_list_comb D_def NV_def)
    then show "ivps \<rho> (dp # dps) \<subseteq> reach (instE \<rho> env) D \<union> NV" using reach_incl[of D "instE \<rho> env"] by blast
  qed (simp_all add: tagree_def)
  define u' where "u' = combound newhd 0 (length Ts')"
  have "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s 0 u' env1 (dp # dps) W1 \<sigma>1 \<rho> NV"
    unfolding pcopy_res_def
  proof (intro conjI sx)
    have "typed env1 W1 (rev Ts') u' Y"
      using typed_combound_Var[OF tctxG[unfolded GT_def]] ge(5) by (simp add: u'_def GT_def)
    then show "typed env1 W1 (rev Ts) u' U"
      by (rule typed_tnorm_cong) (use Ts'(1) Y(2) ge(8) in \<open>simp_all add: rev_map[symmetric]\<close>)
    show "swf_cp ar (length Ts) u'"
      using ge(5) twGT lTs' by (auto simp: u'_def tyw_def intro!: swf_cp_combound)
    show "\<forall>T\<in>tys u'. tyw ar (tyenv env1) A T" using ge(5,8) twGT by (simp add: u'_def)
    show "below (maxidx env1) u'" using ge(4,5) by (simp add: u'_def below_def G_def)
    show "vps (inst \<rho> u') \<subseteq> NV" using ge(5) by (simp add: u'_def NV_def)
    show "mk_subst \<sigma>1 (tr (inst \<rho> u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
      using Abs_m_apps_downs[OF nls] ge(5,9) lTs' by (simp add: u'_def tr_combound0 G_def)
    have "vsz \<tau>' \<sigma>1 (G, foldr fun_type (map (tsubst \<rho>) Ts) (tsubst \<rho> U)) =
        lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"
      by (rule vsz_Abs_m) (use ge(9) tys nrs nls in \<open>simp_all add: G_def\<close>)
    then show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) + 0 \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"
      by (simp add: NV_def iGT)
  qed
  then show ?thesis unfolding D_def u'_def dp_def by blast
qed

text \<open>A flexible head: a new variable for the copy, with a new pair.\<close>

lemma pmc_var:
  assumes pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s" and hV: "head_of u = Var w Wt"
  shows "pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  from pre have hl: "hlong ?V (map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    unfolding pmc_pre_def by blast
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts"
    "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" "tyw ar ?\<theta> A base" "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    by (rule pmc_types[OF pre]) blast
  have nA: "\<not> is_Abs u" using hV by (cases u) auto
  then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
  from hlong_nonAbs[OF hl this] have tyu: "typed env W (map snd rb) u U"
    and nfU: "\<not> is_funT (tnorm ?\<theta> U)" by (auto simp: typed_def)
  have bU: "tnorm ?\<theta> base = tnorm ?\<theta> U" using ty0(7) arg_res_type_base[OF nfU] by simp
  obtain env1 newhd where g: "genvar (fst w) env (foldr fun_type Ts' base) = (env1, newhd)"
    by (cases "genvar (fst w) env (foldr fun_type Ts' base)")
  from pre have "\<exists>W1 \<sigma>1 NV. pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs dps) Ts U s 0
      (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps) W1 \<sigma>1 \<rho> NV"
    unfolding pmc_pre_def by (intro pflex_copy[OF _ _ _ _ _ _ _ _ _ tyu _ ty0(4,5,6) bU g]) blast+
  moreover have "is_Var (head_of (strip_abs_body u))" using hV nA by (simp add: strip_abs_body_nonAbs)
  moreover have "okW (mc cfg vname rb targs u env dps)
      (S_Single (El_C (combound newhd 0 (length Ts')) env1 ((rb, list_comb newhd targs, u) # dps)))"
    using mc_punfold[OF ty0(1-3), of cfg vname dps] hV g by simp
  ultimately show ?thesis unfolding pmc_post_def using ev.single by fastforce
qed


subsection \<open>Copies: abstractions\<close>

lemma tys_incr_bv[simp]: "tys (incr_bv i lev t) = tys t"
  by (induction t arbitrary: lev) auto

lemma tys_incr_boundvars[simp]: "tys (incr_boundvars i t) = tys t"
  by (simp add: incr_boundvars_def)

lemma vars_incr_boundvars[simp]: "vars (incr_boundvars i t) = vars t"
  by (simp add: incr_boundvars_def vars_incr_bv)

text \<open>An abstraction is copied by copying its body, with one more argument.\<close>

lemma pmc_abs:
  assumes IH: "\<And>rb' targs' Ts' u' U' s'. size u' < size u \<Longrightarrow>
      lsize (ibctx \<rho> Ts') \<tau>' s' (trty (tsubst \<rho> U')) = N \<Longrightarrow>
      pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb' targs' Ts' u' U' s' \<Longrightarrow>
      pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb' targs' Ts' u' U' s'"
    and pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and lsz: "lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U)) = N"
    and hA: "head_of u = Abs a T body"
  shows "pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> ?\<theta> A" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar ?\<theta> A T"
    and wu: "swf_tm ar rb u" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T" and hu: "hnf u"
    and bu: "below (maxidx env) u" and hl: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and twU: "tyw ar ?\<theta> A U" and fU: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U)))"
    and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
    and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    unfolding pmc_pre_def by blast+
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  note \<sigma> = solutionD[OF pc0(3)]
  have u: "u = Abs a T body" using hnf_Abs_head[OF hu] hA by (simp add: fst_strip_comb)
  from hl u obtain U' where U: "tnorm ?\<theta> U = tnorm ?\<theta> T \<rightarrow>\<^sub>T U'"
    and hlb: "hlong ?V (tnorm ?\<theta> T # ?Bs) (tnormt ?\<theta> body) U'"
    by (auto elim: hlong.cases)
  have twT: "tyw ar ?\<theta> A T" using twu u by simp
  have twUn: "tyw ar ?\<theta> A (tnorm ?\<theta> U)" by (rule tyw_tnorm[OF pi(2) twU])
  then have twU': "tyw ar ?\<theta> A U'" using U by (simp add: tyw_fun)
  have nU': "tnorm ?\<theta> U' = U'"
  proof -
    have "tnorm ?\<theta> (tnorm ?\<theta> U) = tnorm ?\<theta> U" by (rule tnorm_idem[OF ac(1)])
    with U show ?thesis by simp
  qed
  have iU: "tsubst \<rho> U = tsubst \<rho> T \<rightarrow>\<^sub>T tsubst \<rho> U'"
  proof -
    have "tsubst \<rho> U = tsubst \<rho> (tnorm ?\<theta> U)" by (rule tsubst_tnorm[OF ac sol tcU[OF twU], symmetric])
    also have "\<dots> = tsubst \<rho> (tnorm ?\<theta> T) \<rightarrow>\<^sub>T tsubst \<rho> U'" using U by simp
    also have "tsubst \<rho> (tnorm ?\<theta> T) = tsubst \<rho> T" by (rule tsubst_tnorm[OF ac sol tcU[OF twT]])
    finally show ?thesis .
  qed
  have wb: "swf_tm ar ((a, T) # rb) body" and wT: "wft ar T" using wu u by (simp_all add: swf_tm_def)
  have sb': "sbinders ar ((a, T) # rb)" using sb wT by (simp add: sbinders_def)
  have hb: "hnf body" using hu u by simp
  have bb: "below (maxidx env) body" using bu u by (simp add: below_def)
  define targs' where "targs' = map (incr_boundvars 1) targs @ [Bound 0]"
  have tg': "\<forall>t\<in>set targs'. swf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t \<and> (\<forall>X\<in>tys t. tyw ar ?\<theta> A X)"
    using tg by (auto simp: targs'_def below_def intro: swf_tm_incr swf_tm_Bound0)
  have tgty': "list_all2 (typed env W (map snd ((a, T) # rb))) targs' (Ts @ [T])"
    unfolding targs'_def
  proof (rule list_all2_appendI)
    show "list_all2 (typed env W (map snd ((a, T) # rb))) (map (incr_boundvars 1) targs) Ts"
      unfolding list_all2_map1 using tgty
      by (rule list_all2_mono) (simp add: typed_def has_type_incr_boundvars1)
  qed (simp add: typed_def has_type_Bound_iff)
  have tys0: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> T) \<Rightarrow> trty (tsubst \<rho> U')" using tys iU by simp
  obtain s' where s': "((ibctx \<rho> Ts)\<langle>0:trty (tsubst \<rho> T)\<rangle>, \<tau>') \<turnstile> s' : trty (tsubst \<rho> U')" "no_redex s'"
    "no_loose_bound s' (Suc (length Ts))" "dB.Abs s' \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
    "lsize ((ibctx \<rho> Ts)\<langle>0:trty (tsubst \<rho> T)\<rangle>) \<tau>' s' (trty (tsubst \<rho> U')) =
      lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> T) \<Rightarrow> trty (tsubst \<rho> U'))"
    by (rule eta_body[OF tys0 nrs nls])
  have bctx': "ibctx \<rho> (Ts @ [T]) = (ibctx \<rho> Ts)\<langle>0:trty (tsubst \<rho> T)\<rangle>" by (simp add: env_ext_snoc)
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
  have st': "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs' = map (\<lambda>t. lift t 0) ?st @ [BVar 0]"
  proof -
    have "mk_subst \<sigma> (tr (inst \<rho> (incr_boundvars 1 t))) = lift (mk_subst \<sigma> (tr (inst \<rho> t))) 0"
      if "t \<in> set targs" for t
    proof -
      have "proper (inst \<rho> t)" using tg that by (simp add: swf_tm_def)
      then have "tr (incr_boundvars 1 (inst \<rho> t)) = lift (tr (inst \<rho> t)) 0" by (rule tr_incr_boundvars1)
      moreover have "closed_on (FV (tr (inst \<rho> t))) \<sigma>" using \<sigma>(1) by (simp add: closed_on_def)
      ultimately show ?thesis by (simp add: mk_subst_lift_on inst_incr_boundvars)
    qed
    then show ?thesis by (simp add: targs'_def)
  qed
  define F where "F = Abs_m (Suc (length Ts)) s'"
  have F0: "no_loose_bound F 0" using s'(3) by (simp add: F_def loose_bound_Abs_m)
  have "F \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ts) s" unfolding F_def Abs_m_Suc' by (rule equiv_Abs_m[OF s'(4)])
  then have "F \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    using equiv_trans[OF equiv_list_app[OF _ list_all2_refl] eqs] by (simp add: equiv_refl)
  then have Fe: "F \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr (inst \<rho> body)))" using u by simp
  have "dB.Abs ((F \<degree>\<degree> map (\<lambda>t. lift t 0) ?st) \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr (inst \<rho> body)))"
    by (rule equiv_trans[OF Abs_apps_lift_eta[OF F0] Fe])
  then have eqb: "Abs_m (length (Ts @ [T])) s' \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs' \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst \<sigma> (tr (inst \<rho> body))"
    using equiv_Abs_reflect st' by (simp add: F_def)
  have pre': "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps ((a, T) # rb) targs' (Ts @ [T]) body U' s'"
    unfolding pmc_pre_def bctx'
  proof (intro conjI pc kk sb' tgty' wb hb bb twU' s'(1-3) eqb)
    show "\<forall>X\<in>snd ` set ((a, T) # rb). tyw ar ?\<theta> A X" using twb twT by simp
    show "\<forall>t\<in>set targs'. swf_tm ar ((a, T) # rb) t \<and> below (maxidx env) t \<and> (\<forall>X\<in>tys t. tyw ar ?\<theta> A X)"
      by (rule tg')
    show "\<forall>X\<in>set (Ts @ [T]). tyw ar ?\<theta> A X" using twTs twT by simp
    show "\<forall>X\<in>tys body. tyw ar ?\<theta> A X" using twu u by simp
    show "hlong ?V (map (tnorm ?\<theta>) (map snd ((a, T) # rb))) (tnormt ?\<theta> body) (tnorm ?\<theta> U')"
      using hlb nU' by simp
    show "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U')))" using fU U nU' by simp
    show "no_loose_bound s' (length (Ts @ [T]))" using s'(3) by simp
  qed
  have lsz': "lsize (ibctx \<rho> (Ts @ [T])) \<tau>' s' (trty (tsubst \<rho> U')) = N"
    unfolding bctx' using s'(5) lsz iU by simp
  have "size body < size u" using u by simp
  from IH[OF this lsz' pre'] obtain sq u' env' dps' W' \<sigma>' \<rho>' NV where
    mcb: "okW (mc cfg vname ((a, T) # rb) targs' body env dps) sq" and evb: "ev cfg sq (El_C u' env' dps')"
    and cr: "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> body targs' dps) (Ts @ [T]) U' s'
        (if is_Var (head_of (strip_abs_body body)) then 0 else 1) u' env' dps' W' \<sigma>' \<rho>' NV"
    unfolding pmc_post_def by blast
  have D: "pmc_dom \<rho> body targs' dps = pmc_dom \<rho> u targs dps"
    using u by (auto simp: targs'_def inst_incr_boundvars)
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'"
    by (rule pmc_types[OF pre]) blast
  have mc: "okW (mc cfg vname rb targs u env dps) (S_MapAbs a T sq)"
    using mc_punfold[OF ty0, of cfg vname dps] hA mcb by (simp add: targs'_def)
  have ev: "ev cfg (S_MapAbs a T sq) (El_C (Abs a T u') env' dps')" by (rule ev.map_abs[OF evb])
  from cr have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' (pmc_dom \<rho> u targs dps) NV"
    and ty': "typed env' W' (rev (Ts @ [T])) u' U'" and w': "swf_cp ar (length (Ts @ [T])) u'"
    and tw': "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X" and b': "below (maxidx env') u'"
    and v': "vps (inst \<rho>' u') \<subseteq> NV" and e': "mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s'"
    and sz: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + (if is_Var (head_of (strip_abs_body body)) then 0 else 1)
      \<le> lsize (ibctx \<rho> (Ts @ [T])) \<tau>' s' (trty (tsubst \<rho> U'))"
    unfolding pcopy_res_def D by blast+
  note sd = psextD[OF sx]
  note pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
  have ext: "textends ?\<theta> (tyenv env')" using sd(6) by (simp add: pextends_def)
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have cr': "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env (pmc_dom \<rho> u targs dps) Ts U s
      (if is_Var (head_of (strip_abs_body u)) then 0 else 1) (Abs a T u') env' dps' W' \<sigma>' \<rho>' NV"
    unfolding pcopy_res_def
  proof (intro conjI sx)
    have "tnorm (tyenv env') U = tnorm (tyenv env') T \<rightarrow>\<^sub>T tnorm (tyenv env') U'"
      using arg_cong[OF U, of "tnorm (tyenv env')"] tnorm_textends[OF ac' ext] by simp
    then show "typed env' W' (rev Ts) (Abs a T u') U"
      using ty' by (simp add: typed_def has_type.Abs)
    show "swf_cp ar (length Ts) (Abs a T u')" using w' wT by (simp add: swf_cp_def)
    show "\<forall>X\<in>tys (Abs a T u'). tyw ar (tyenv env') A X"
      using tw' tyw_textends[OF ac' ext twT] by simp
    show "below (maxidx env') (Abs a T u')" using b' by (simp add: below_def)
    show "vps (inst \<rho>' (Abs a T u')) \<subseteq> NV" using v' by simp
    show "mk_subst \<sigma>' (tr (inst \<rho>' (Abs a T u'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s" using equiv_trans[OF equiv_Abs[OF e'] s'(4)] by simp
    show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
        \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"
      using sz s'(5) iU u unfolding bctx' by simp
  qed
  show ?thesis unfolding pmc_post_def using mc ev cr' by blast
qed


subsection \<open>Copies: projections\<close>

lemma okW_det: "okW m x \<Longrightarrow> okW m y \<Longrightarrow> x = y"
  by auto

lemma ev_foldrW:
  assumes "\<And>x t. x \<in> set xs \<Longrightarrow>
    \<exists>r. okW (f x t) r \<and> (\<forall>y. ev cfg t y \<longrightarrow> ev cfg r y) \<and> (\<forall>y. Q x y \<longrightarrow> ev cfg r y)"
  shows "\<exists>r. okW (foldrW f xs b) r \<and> (\<forall>y. ev cfg b y \<longrightarrow> ev cfg r y) \<and>
    (\<forall>x\<in>set xs. \<forall>y. Q x y \<longrightarrow> ev cfg r y)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "\<exists>r. okW (f x' t) r \<and> (\<forall>y. ev cfg t y \<longrightarrow> ev cfg r y) \<and> (\<forall>y. Q x' y \<longrightarrow> ev cfg r y)"
    if "x' \<in> set xs" for x' t using Cons.prems[of x' t] that by simp
  from Cons.IH[OF this] obtain t where t: "okW (foldrW f xs b) t" "\<forall>y. ev cfg b y \<longrightarrow> ev cfg t y"
    "\<forall>x\<in>set xs. \<forall>y. Q x y \<longrightarrow> ev cfg t y"
    by blast
  from Cons.prems[of x t] obtain r where r: "okW (f x t) r" "\<forall>y. ev cfg t y \<longrightarrow> ev cfg r y"
    "\<forall>y. Q x y \<longrightarrow> ev cfg r y" by auto
  have "okW (foldrW f (x # xs) b) r" using t(1) r(1) by auto
  with t r show ?case by (intro exI[of _ r]) auto
qed

lemma proj_unify_ok:
  "Cs = [] \<Longrightarrow> cunify_types (cfg_alg cfg) base bary env = returnW env' \<Longrightarrow> okW (proj_unify cfg base bary Cs env) env'"
  "Cs \<noteq> [] \<Longrightarrow> cunify_types (cfg_alg cfg) bary (foldr fun_type Cs base) env = returnW env' \<Longrightarrow>
    okW (proj_unify cfg base bary Cs env) env'"
  by (auto simp: proj_unify_def test_unify_types_def okW_whenW)

lemma proj_unify_cantunify:
  "Cs = [] \<Longrightarrow> cunify_types (cfg_alg cfg) base bary env = Some (evs, UErr CANTUNIFY) \<Longrightarrow>
    \<exists>evs'. proj_unify cfg base bary Cs env = Some (evs', UErr CANTUNIFY)"
  "Cs \<noteq> [] \<Longrightarrow> cunify_types (cfg_alg cfg) bary (foldr fun_type Cs base) env = Some (evs, UErr CANTUNIFY) \<Longrightarrow>
    \<exists>evs'. proj_unify cfg base bary Cs env = Some (evs', UErr CANTUNIFY)"
  by (auto simp: proj_unify_def test_unify_types_def bindW_def)

text \<open>The elements of a projection with the guess \<open>p\<close>:\<close>

definition proj_elem :: "cfg \<Rightarrow> name \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> ptyp \<Rightarrow>
    ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp list \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> nat \<Rightarrow> elem \<Rightarrow> bool" where
  "proj_elem cfg vname rb targs u env dps base Ts head Us bary targ p y \<longleftrightarrow>
    (\<exists>env0 Cs env' env'' args env2 fr ff. gentvars p env = (env0, Cs) \<and>
      okW (proj_unify cfg base bary Cs env0) env' \<and> make_args vname Ts env' (Us @ Cs) = (env'', args) \<and>
      okW (SIMPL (cfg_alg cfg) env''
        ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff) \<and>
      y = El_C (list_comb head args) env2 (fr @ ff))"

definition proj_total :: "cfg \<Rightarrow> env \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> nat \<Rightarrow> bool" where
  "proj_total cfg env base bary p \<longleftrightarrow> (\<forall>env0 Cs. gentvars p env = (env0, Cs) \<longrightarrow>
    (\<exists>env'. okW (proj_unify cfg base bary Cs env0) env') \<or>
    (\<exists>evs. proj_unify cfg base bary Cs env0 = Some (evs, UErr CANTUNIFY)))"

lemma projenv_presult:
  assumes "proj_total cfg env base bary p"
  shows "\<exists>r. okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) r \<and>
    (\<forall>y. ev cfg tail y \<longrightarrow> ev cfg r y) \<and>
    (\<forall>y. proj_elem cfg vname rb targs u env dps base Ts head Us bary targ p y \<longrightarrow> ev cfg r y)"
proof -
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  let ?m = "proj_unify cfg base bary Cs env0"
  let ?r = "do {env' \<leftarrow> ?m; returnW (S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ tail)}"
  have pe: "projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail =
      handleW ?r (\<lambda>e. case e of CANTUNIFY \<Rightarrow> returnW tail | _ \<Rightarrow> raiseW e)"
    by (simp add: projenv_def g)
  from assms g have "(\<exists>env'. okW ?m env') \<or> (\<exists>evs. ?m = Some (evs, UErr CANTUNIFY))"
    by (simp add: proj_total_def)
  then show ?thesis
  proof
    assume "\<exists>env'. okW ?m env'"
    then obtain env' where e': "okW ?m env'" by blast
    let ?R = "S_Proj vname env' Ts (Us @ Cs) targs rb u dps head targ tail"
    have "okW ?r ?R" using e' by auto
    then have ok: "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) ?R"
      unfolding pe by (rule okW_handleW[THEN iffD2, OF disjI1])
    have "ev cfg ?R y" if "proj_elem cfg vname rb targs u env dps base Ts head Us bary targ p y" for y
    proof -
      from that g obtain env1 env'' args env2 fr ff where
        a: "okW ?m env1" "make_args vname Ts env1 (Us @ Cs) = (env'', args)"
        "okW (SIMPL (cfg_alg cfg) env''
          ((rb, list_comb targ (map (\<lambda>arg. list_comb (head_of arg) targs) args), u) # dps)) (env2, fr, ff)"
        "y = El_C (list_comb head args) env2 (fr @ ff)"
        unfolding proj_elem_def by auto
      have "env1 = env'" using okW_det[OF a(1) e'] .
      with a show ?thesis by (auto intro: ev.proj)
    qed
    with ok show ?thesis by (blast intro: ev.proj_tail)
  next
    assume "\<exists>evs. ?m = Some (evs, UErr CANTUNIFY)"
    then obtain evs where c: "?m = Some (evs, UErr CANTUNIFY)" by blast
    then have "?r = Some (evs, UErr CANTUNIFY)" by (simp add: bindW_def)
    then have ok: "okW (projenv cfg vname rb targs u env dps base Ts head (Us, bary) targ p tail) tail"
      unfolding pe by (auto simp: okW_handleW)
    have "\<not> proj_elem cfg vname rb targs u env dps base Ts head Us bary targ p y" for y
      using c g by (auto simp: proj_elem_def)
    with ok show ?thesis by blast
  qed
qed

text \<open>The sequence of \<^const>\<open>matchfun\<close> contains the elements of all projections, with all guesses, and of the imitation.\<close>

lemma matchfun_presult:
  assumes "\<forall>(bv, T, targ)\<in>set projs. \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
  shows "\<exists>sq. okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) sq \<and>
    (\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg sq x) \<and>
    (\<forall>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<longrightarrow> ok (strip_type env T) (Us, bary) \<longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<longrightarrow> proj_elem cfg vname rb targs u env dps base Ts bv Us bary targ p y \<longrightarrow>
      ev cfg sq y)"
  using assms
proof (induction projs)
  case Nil
  show ?case by (intro exI[of _ "case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty"]) simp
next
  case (Cons pr projs)
  obtain bv T targ where pr: "pr = (bv, T, targ)" by (cases pr)
  from Cons.prems pr obtain Us bary where st: "ok (strip_type env T) (Us, bary)"
    and gs: "\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p" by auto
  from Cons.IH Cons.prems obtain tail where tl: "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts projs) tail"
    and imit: "\<forall>x. ev cfg (case uhead of
        Const _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | Free _ _ \<Rightarrow> S_MapJoin uhead (copyargs vname rb targs env dps uargs)
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg tail x"
    and prj: "\<forall>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<longrightarrow> ok (strip_type env T) (Us, bary) \<longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<longrightarrow> proj_elem cfg vname rb targs u env dps base Ts bv Us bary targ p y \<longrightarrow>
      ev cfg tail y"
    by auto
  have "\<exists>r. okW (foldrW (projenv cfg vname rb targs u env dps base Ts bv (Us, bary) targ) (arity_guesses cfg bary) tail) r \<and>
      (\<forall>y. ev cfg tail y \<longrightarrow> ev cfg r y) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). \<forall>y. proj_elem cfg vname rb targs u env dps base Ts bv Us bary targ p y \<longrightarrow> ev cfg r y)"
    by (rule ev_foldrW) (use gs projenv_presult in blast)
  then obtain r where r: "okW (foldrW (projenv cfg vname rb targs u env dps base Ts bv (Us, bary) targ) (arity_guesses cfg bary) tail) r"
    "\<forall>y. ev cfg tail y \<longrightarrow> ev cfg r y"
    "\<forall>p\<in>set (arity_guesses cfg bary). \<forall>y. proj_elem cfg vname rb targs u env dps base Ts bv Us bary targ p y \<longrightarrow> ev cfg r y"
    by blast
  have "okW (matchfun cfg vname rb targs u env dps uhead uargs base Ts (pr # projs)) r"
    using tl r(1) st by (auto simp: pr)
  moreover have "ev cfg r y" if "(bv', T', targ') \<in> set (pr # projs)" "ok (strip_type env T') (Us', bary')"
    "p \<in> set (arity_guesses cfg bary')" "proj_elem cfg vname rb targs u env dps base Ts bv' Us' bary' targ' p y"
    for bv' T' targ' Us' bary' p y
  proof (cases "(bv', T', targ') = pr")
    case True
    with that(2) st pr have "Us' = Us" "bary' = bary" by auto
    with True that(3,4) r(3) pr show ?thesis by auto
  next
    case False
    with that have "(bv', T', targ') \<in> set projs" by simp
    with that(2-4) prj r(2) show ?thesis by blast
  qed
  ultimately show ?case using imit r(2) by blast
qed


subsection \<open>Copies: rigid heads, auxiliary lemmas\<close>

lemma binder_types_tyw:
  assumes "binder_types env T = Some r"
  shows "r = Ok Us \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> tyw ar (tyenv env) A T \<Longrightarrow>
    \<forall>U\<in>set Us. tyw ar (tyenv env) A U"
  using assms
proof (induction env T r arbitrary: Us rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by auto
      from "1.hyps" "1.prems"(1) Type Ts a obtain Us' where r: "bt env U = Some (Ok Us')" and Us: "Us = T1 # Us'"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      have "tyw ar (tyenv env) A T1" "tyw ar (tyenv env) A U" using "1.prems"(3) Type Ts a by (simp_all add: tyw_fun)
      with "1.IH"[OF r refl "1.prems"(2)] Us show ?thesis by simp
    next
      case False
      with "1.hyps" "1.prems"(1) Type show ?thesis
        by (auto simp: return_def split: list.splits if_splits)
    qed
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) v S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Us"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest show ?thesis by (simp add: return_def)
    next
      fix U assume U: "r' = Some U" "vt_lookup (tyenv env) v = Some (S, U)"
      have "tyw ar (tyenv env) A U" by (rule tyw_lookup[OF "1.prems"(2) _ U(2)]) (use "1.prems"(3) TVar in simp)
      with rest U(1) "1.IH"[of env U "Ok Us" Us] "1.prems"(2) show ?thesis by simp
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma strip_type_tyw:
  "ok (strip_type env T) (Us, B) \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> tyw ar (tyenv env) A T \<Longrightarrow>
    (\<forall>U\<in>set Us. tyw ar (tyenv env) A U) \<and> tyw ar (tyenv env) A B"
  by (auto simp: strip_type_def bind_def return_def split: option.splits res.splits
      dest: body_type_tyw binder_types_tyw)

lemma arrows_split:
  "Xs \<Rrightarrow> Y = Ws \<Rrightarrow> Atom a \<Longrightarrow> \<exists>Zs. Ws = Xs @ Zs \<and> Y = Zs \<Rrightarrow> Atom a"
proof (induction Xs arbitrary: Ws)
  case (Cons X Xs)
  then show ?case by (cases Ws) auto
qed simp

lemma ground_arg_types: "ground ar T \<Longrightarrow> \<forall>X\<in>set (arg_types T). ground ar X"
  by (induction T rule: arg_types.induct) auto

lemma ground_res_type: "ground ar T \<Longrightarrow> ground ar (res_type T)"
  by (induction T rule: res_type.induct) auto

text \<open>The instance of a type under \<open>\<rho>\<close> splits into argument types and a result type.\<close>

lemma arrows_inst_split:
  assumes "trty (foldr fun_type Xs Y) = Ws \<Rrightarrow> trty B" "\<not> is_funT B"
  shows "Ws = map trty Xs @ map trty (arg_types Y) \<and> res_type Y = B"
proof -
  from trty_base[OF assms(2)] obtain a where a: "trty B = Atom a" by blast
  have "map trty Xs \<Rrightarrow> trty Y = Ws \<Rrightarrow> Atom a" using assms(1) a by (simp add: trty_foldr)
  from arrows_split[OF this] obtain Zs where Z: "Ws = map trty Xs @ Zs" "trty Y = Zs \<Rrightarrow> Atom a" by blast
  have "map trty (arg_types Y) \<Rrightarrow> trty (res_type Y) = Zs \<Rrightarrow> trty B"
    using Z(2) a arg_res_type[of Y] by (metis trty_foldr)
  from arrows_base_inj[OF this res_type_base assms(2)] Z(1) show ?thesis by blast
qed

lemma tvars_tnorm_unbound:
  assumes "tacyc \<theta>" "(c, S) \<in> tvars T" "vt_lookup \<theta> c = None"
  shows "(c, S) \<in> tvars (tnorm \<theta> T)"
  using assms(2)
proof (induction T)
  case (TVar v S')
  then show ?case using assms(3) by (simp add: tnorm_TVar[OF assms(1)])
qed auto

text \<open>A type of a larger problem whose unbound type variables come from the smaller one belongs to the smaller one.\<close>

lemma tyw_shrink:
  assumes inv: "tinv ar n \<theta> (A \<union> X)" and tw: "tyw ar \<theta> (A \<union> X) T" and uv: "uvars \<theta> T \<subseteq> uvarsA \<theta> A"
  shows "tyw ar \<theta> A T"
proof -
  have ac: "tacyc \<theta>" by (rule tinv_tacyc[OF inv])
  have sc: "scons (tvars_env \<theta> \<union> (A \<union> X))" using inv by (simp add: tinv_def)
  have "(c, S) \<in> tvars_env \<theta> \<union> A" if cS: "(c, S) \<in> tvars T" for c S
  proof (cases "vt_lookup \<theta> c")
    case (Some p)
    then obtain S0 U where b: "vt_lookup \<theta> c = Some (S0, U)" by (cases p) auto
    then have "(c, S0) \<in> tvars_env \<theta>" by (rule tvars_envI)
    moreover have "(c, S) \<in> tvars_env \<theta> \<union> (A \<union> X)" using cS tw by (auto simp: tyw_def)
    ultimately have "S0 = S" using sc unfolding scons_def by blast
    with \<open>(c, S0) \<in> tvars_env \<theta>\<close> show ?thesis by simp
  next
    case None
    have "(c, S) \<in> tvars (tnorm \<theta> T)" by (rule tvars_tnorm_unbound[OF ac cS None])
    then have "c \<in> uvars \<theta> T" by (force simp: uvars_def)
    with uv obtain v S1 where vS: "(v, S1) \<in> A" and cv: "c \<in> uvars \<theta> (TVar v S1)"
      by (auto simp: uvarsA_def)
    from cv obtain S2 where c2: "(c, S2) \<in> tvars (tnorm \<theta> (TVar v S1))" by (auto simp: uvars_def)
    have "(c, S2) \<in> tvars_env \<theta> \<union> A" using tvars_tnorm[OF ac, of "TVar v S1"] c2 vS by auto
    moreover have "(c, S) \<in> tvars_env \<theta> \<union> (A \<union> X)" using cS tw by (auto simp: tyw_def)
    ultimately have "S2 = S" using sc unfolding scons_def by blast
    with \<open>(c, S2) \<in> tvars_env \<theta> \<union> A\<close> show ?thesis by simp
  qed
  then show ?thesis using tw uv by (auto simp: tyw_def)
qed

lemma uvars_tnorm_eq: "tnorm \<theta> T = tnorm \<theta> U \<Longrightarrow> uvars \<theta> T = uvars \<theta> U"
  by (simp add: uvars_def)

lemma uvars_fun: "uvars \<theta> (T \<rightarrow>\<^sub>T U) = uvars \<theta> T \<union> uvars \<theta> U"
  by simp

lemma uvars_foldr_fun: "uvars \<theta> (foldr fun_type Ts U) = (\<Union>T\<in>set Ts. uvars \<theta> T) \<union> uvars \<theta> U"
  by (induction Ts) auto

text \<open>Typing modulo the type environment is stable under extensions of the environment and of the typing.\<close>

lemma typed_ext:
  assumes ac: "tacyc (tyenv env2)" and ext: "textends (tyenv env) (tyenv env2)"
    and wc: "wcons W env" "wcons W2 env2"
    and ag: "\<And>x. x \<in> vars t \<Longrightarrow> tnorm (tyenv env2) (W2 x) = tnorm (tyenv env2) (W x)"
    and ty: "typed env W Ts t T"
  shows "typed env2 W2 Ts t T"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>2 = "tyenv env2"
  have "has_type (\<lambda>x. tnorm ?\<theta>2 (tctx env W x)) (map (tnorm ?\<theta>2) (map (tnorm ?\<theta>) Ts))
      (tnormt ?\<theta>2 (tnormt ?\<theta> t)) (tnorm ?\<theta>2 (tnorm ?\<theta> T))"
    using has_type_tnormt[OF ty[unfolded typed_def]] .
  then have "has_type (\<lambda>x. tnorm ?\<theta>2 (tctx env W x)) (map (tnorm ?\<theta>2) Ts) (tnormt ?\<theta>2 t) (tnorm ?\<theta>2 T)"
    using ac ext by (simp add: comp_def tnorm_textends tnormt_textends)
  moreover have "tctx env2 W2 x = tnorm ?\<theta>2 (tctx env W x)" if "x \<in> vars (tnormt ?\<theta>2 t)" for x
    using that ag wcons_tctx[OF wc(1)] wcons_tctx[OF wc(2)] tnorm_textends[OF ac ext] by simp
  ultimately show ?thesis unfolding typed_def by (rule has_type_vars_cong) simp
qed

lemma typed_psext:
  assumes "tacyc (tyenv env2)" "pextends env env2" "wcons W env" "wcons W2 env2" "agreeV (maxidx env) W W2"
    "below (maxidx env) t" "typed env W Ts t T"
  shows "typed env2 W2 Ts t T"
proof (rule typed_ext[OF assms(1) _ assms(3,4) _ assms(7)])
  show "textends (tyenv env) (tyenv env2)" using assms(2) by (simp add: pextends_def)
  fix x assume "x \<in> vars t"
  with assms(6) have "snd x \<le> maxidx env" by (simp add: below_def)
  with assms(5) have "W2 x = W x" unfolding agreeV_def by blast
  then show "tnorm (tyenv env2) (W2 x) = tnorm (tyenv env2) (W x)" by simp
qed

lemma list_all2_typed_psext:
  assumes "tacyc (tyenv env2)" "pextends env env2" "wcons W env" "wcons W2 env2" "agreeV (maxidx env) W W2"
    "\<forall>t\<in>set ts. below (maxidx env) t" "list_all2 (typed env W Ts) ts Us"
  shows "list_all2 (typed env2 W2 Ts) ts Us"
  using assms(7,6) by (induction rule: list_all2_induct) (auto intro: typed_psext[OF assms(1-5)])

lemma typed_list_comb:
  assumes "typed env W Bs h (foldr fun_type Us B)" "list_all2 (typed env W Bs) ts Us"
  shows "typed env W Bs (list_comb h ts) B"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  have "list_all2 (has_type ?V (map (tnorm ?\<theta>) Bs)) (map (tnormt ?\<theta>) ts) (map (tnorm ?\<theta>) Us)"
    unfolding list_all2_map1 list_all2_map2 using assms(2) by (rule list_all2_mono) (simp add: typed_def)
  with assms(1) show ?thesis by (auto simp: typed_def has_type_list_comb tnorm_foldr_fun)
qed


lemma agree_mono: "agree m \<sigma> \<sigma>' \<Longrightarrow> m' \<le> m \<Longrightarrow> agree m' \<sigma> \<sigma>'"
  unfolding agree_def by force

lemma agreeV_mono: "agreeV m V V' \<Longrightarrow> m' \<le> m \<Longrightarrow> agreeV m' V V'"
  unfolding agreeV_def by force

lemma tagree_mono: "tagree m \<rho> \<rho>' \<Longrightarrow> m' \<le> m \<Longrightarrow> tagree m' \<rho> \<rho>'"
  unfolding tagree_def by force

lemma textends_refl: "textends \<theta> \<theta>"
  by (simp add: textends_def)

end

context wf_csig
begin

text \<open>The type unification of a projection with \<open>p\<close> more arguments raises no exception other than \<open>CANTUNIFY\<close>.\<close>

lemma proj_total_tyw:
  assumes cfg: "cfg_alg cfg = alg" and inv: "tinv ar (maxidx env) (tyenv env) A" and srt: "tsorted alg (tyenv env)"
    and tw: "tyw ar (tyenv env) A base" "tyw ar (tyenv env) A bary"
  shows "proj_total cfg env base bary p"
  unfolding proj_total_def
proof (intro allI impI)
  fix env0 Cs assume g: "gentvars p env = (env0, Cs)"
  note gs = gentvars_simps[OF g]
  let ?A' = "A \<union> ctvars Cs"
  have inv': "tinv ar (maxidx env0) (tyenv env0) ?A'" using tinv_gentvars[OF inv g] gs(2) by simp
  have srt': "tsorted alg (tyenv env0)" using srt gs(2) by simp
  have tw': "tyw ar (tyenv env0) ?A' base" "tyw ar (tyenv env0) ?A' bary" using tw gs(2) by (auto intro: tyw_mono)
  have twC: "\<forall>C\<in>set Cs. tyw ar (tyenv env0) ?A' C" using tyw_gentvars[OF inv g] gs(2) by simp
  have twF: "tyw ar (tyenv env0) ?A' (foldr fun_type Cs base)" using tw'(1) twC by (simp add: tyw_foldr_fun)
  show "(\<exists>env'. okW (proj_unify cfg base bary Cs env0) env') \<or>
      (\<exists>evs. proj_unify cfg base bary Cs env0 = Some (evs, UErr CANTUNIFY))"
  proof (cases "Cs = []")
    case True
    from cunify_types_cases'[OF inv' srt' tw'] show ?thesis
      using proj_unify_ok(1)[OF True] proj_unify_cantunify(1)[OF True] cfg by metis
  next
    case False
    from cunify_types_cases'[OF inv' srt' tw'(2) twF] show ?thesis
      using proj_unify_ok(2)[OF False] proj_unify_cantunify(2)[OF False] cfg by metis
  qed
qed

text \<open>The sequence of \<^const>\<open>mc\<close> on a term with a rigid head.\<close>

lemma pmc_rigid_seq:
  assumes cfg: "cfg_alg cfg = alg" and pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
  obtains T0 base Ts' projs sq where "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "map (tnorm (tyenv env)) Ts' = map (tnorm (tyenv env)) Ts" "\<forall>T\<in>set Ts'. tyw ar (tyenv env) A T"
    "tyw ar (tyenv env) A T0" "tyw ar (tyenv env) A base"
    "has_type (tctx env W) (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) (head_of u))
      (tnorm (tyenv env) T0)"
    "tnorm (tyenv env) base = res_type (tnorm (tyenv env) U)"
    "\<forall>j<length targs. (Bound (integer_of_nat j), Ts' ! (length targs - Suc j), targs ! (length targs - Suc j))
      \<in> set projs"
    "okW (mc cfg vname rb targs u env dps) sq"
    "\<And>x. ev cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | _ \<Rightarrow> S_Empty) x \<Longrightarrow> ev cfg sq x"
    "\<And>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<Longrightarrow> ok (strip_type env T) (Us, bary) \<Longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<Longrightarrow>
      proj_elem cfg vname rb targs u env dps base Ts' bv Us bary targ p y \<Longrightarrow> ev cfg sq y"
proof -
  let ?\<theta> = "tyenv env"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts"
    unfolding pmc_pre_def by blast+
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain T0 base Ts' where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "mapM (fastype env rb) targs = return Ts'" "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts"
    "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T" "tyw ar ?\<theta> A T0" "tyw ar ?\<theta> A base"
    "has_type (tctx env W) (map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    by (rule pmc_types[OF pre])
  have lTs: "length Ts' = length targs"
    using arg_cong[OF ty0(4), of length] list_all2_lengthD[OF tgty] by simp
  from make_projs_exact[OF lTs, of u targs] obtain projs where pr: "make_projs u targs Ts' targs = returnW projs"
    and prs: "\<forall>j<length targs. (Bound (integer_of_nat j), Ts' ! (length targs - Suc j),
      targs ! (length targs - Suc j)) \<in> set projs"
    by blast
  have pT: "T \<in> set Ts'" if "(bv, T, targ) \<in> set (rev projs)" for bv T targ
    using make_projs_ok[of u targs Ts' targs projs] pr that by fastforce
  have "\<forall>(bv, T, targ)\<in>set (rev projs). \<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
      (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
  proof (clarify)
    fix bv T targ assume "(bv, T, targ) \<in> set (rev projs)"
    then have twT: "tyw ar ?\<theta> A T" using pT ty0(5) by blast
    have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
      by (simp add: arg_res_type)
    from strip_type_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Us bary where
      st: "strip_type env T = return (Us, bary)" by blast
    have twb: "tyw ar ?\<theta> A bary" using strip_type_tyw[OF st[unfolded return_def] pi(2) twT] by simp
    have "proj_total cfg env base bary p" for p
      by (rule proj_total_tyw[OF cfg pi(2) ei(2) ty0(7) twb])
    with st show "\<exists>Us bary. ok (strip_type env T) (Us, bary) \<and>
        (\<forall>p\<in>set (arity_guesses cfg bary). proj_total cfg env base bary p)"
      by (auto simp: return_def)
  qed
  from matchfun_presult[OF this, where vname = vname and rb = rb and targs = targs and u = u and dps = dps
      and uhead = "head_of u" and uargs = "snd (strip_comb u)" and Ts = Ts'] obtain sq where
    mf: "okW (matchfun cfg vname rb targs u env dps (head_of u) (snd (strip_comb u)) base Ts' (rev projs)) sq"
    and imit: "\<forall>x. ev cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | _ \<Rightarrow> S_Empty) x \<longrightarrow> ev cfg sq x"
    and prj: "\<forall>bv T targ Us bary p y. (bv, T, targ) \<in> set (rev projs) \<longrightarrow> ok (strip_type env T) (Us, bary) \<longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<longrightarrow> proj_elem cfg vname rb targs u env dps base Ts' bv Us bary targ p y \<longrightarrow>
      ev cfg sq y"
    by blast
  have mc: "okW (mc cfg vname rb targs u env dps) sq"
    using mc_punfold[OF ty0(1-3), of cfg vname dps] pr mf hA hV by (cases "head_of u") simp_all
  show ?thesis
    by (rule that[OF ty0(1,2,4-9) prs mc]) (use imit prj in auto)
qed

end


context wf_csig
begin

subsection \<open>Copies: projections, the guess of the number of arguments\<close>

text \<open>
  The guess of a projection on a bound variable of type \<open>T\<close>, if the instance of \<open>T\<close> is
  \<open>Ws \<Rightarrow> \<rho>U\<close>: \<open>T\<close> splits into \<open>Us \<Rightarrow> bary\<close>, and the instance of \<open>bary\<close> takes \<open>p \<le> k\<close> more
  arguments; the type unification of the projection succeeds with an extension of \<open>\<rho>\<close>.
\<close>

lemma proj_guess:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> (tyenv env) A"
    and twT: "tyw ar (tyenv env) A T" and twb0: "tyw ar (tyenv env) A base"
    and ib: "tsubst \<rho> base = \<rho>U" and nf\<rho>U: "\<not> is_funT \<rho>U"
    and tT: "trty (tsubst \<rho> T) = Ws \<Rrightarrow> trty \<rho>U"
  obtains Us bary p env0 Cs env' \<rho>' where
    "strip_type env T = return (Us, bary)" "p \<in> set (arity_guesses cfg bary)" "gentvars p env = (env0, Cs)"
    "okW (proj_unify cfg base bary Cs env0) env'" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
    "tenv env' = tenv env" "pextends env env'" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>Z. reach (instE \<rho>' env') Z = reach (instE \<rho> env) Z"
    "\<forall>X\<in>set (Us @ Cs). tyw ar (tyenv env') A X"
    "Ws = map trty (map (tsubst \<rho>') (Us @ Cs))"
    "tnorm (tyenv env') T = tnorm (tyenv env') (foldr fun_type (Us @ Cs) base)"
proof -
  let ?\<theta> = "tyenv env" and ?\<rho>U = "\<rho>U"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  \<comment> \<open>The type of the bound variable\<close>
  have "tnorm ?\<theta> T = foldr fun_type (arg_types (tnorm ?\<theta> T)) (res_type (tnorm ?\<theta> T))"
    by (simp add: arg_res_type)
  from strip_type_ptnorm[OF ac tcU[OF twT] this res_type_base] obtain Us bary where
    st: "strip_type env T = return (Us, bary)" "map (tnorm ?\<theta>) Us = arg_types (tnorm ?\<theta> T)"
      "tnorm ?\<theta> bary = res_type (tnorm ?\<theta> T)" "\<forall>X\<in>set Us. tcons ?\<theta> X" "tcons ?\<theta> bary"
    by blast
  have twUs: "\<forall>X\<in>set Us. tyw ar ?\<theta> A X" and twbary: "tyw ar ?\<theta> A bary"
    using strip_type_tyw[OF st(1)[unfolded return_def] pi(2) twT] by simp_all
  have iTT: "tsubst \<rho> T = foldr fun_type (map (tsubst \<rho>) Us) (tsubst \<rho> bary)"
  proof -
    have "tsubst \<rho> T = tsubst \<rho> (tnorm ?\<theta> T)" by (rule tsubst_tnorm[OF ac sol tcU[OF twT], symmetric])
    also have "tnorm ?\<theta> T = foldr fun_type (map (tnorm ?\<theta>) Us) (tnorm ?\<theta> bary)"
      using st(2,3) arg_res_type[of "tnorm ?\<theta> T"] by simp
    also have "tsubst \<rho> \<dots> = foldr fun_type (map (tsubst \<rho>) (map (tnorm ?\<theta>) Us)) (tsubst \<rho> (tnorm ?\<theta> bary))"
      by (simp add: tsubst_foldr_fun)
    also have "map (tsubst \<rho>) (map (tnorm ?\<theta>) Us) = map (tsubst \<rho>) Us"
      using st(4) tsubst_tnorm[OF ac sol] by simp
    also have "tsubst \<rho> (tnorm ?\<theta> bary) = tsubst \<rho> bary" by (rule tsubst_tnorm[OF ac sol st(5)])
    finally show ?thesis .
  qed
  have "trty (foldr fun_type (map (tsubst \<rho>) Us) (tsubst \<rho> bary)) = Ws \<Rrightarrow> trty ?\<rho>U" using tT iTT by simp
  from arrows_inst_split[OF this nf\<rho>U] have Ws: "Ws = map trty (map (tsubst \<rho>) Us) @ map trty (arg_types (tsubst \<rho> bary))"
    and rb: "res_type (tsubst \<rho> bary) = ?\<rho>U" by blast+
  define Cs' where "Cs' = arg_types (tsubst \<rho> bary)"
  define p where "p = length Cs'"
  have \<rho>bary: "tsubst \<rho> bary = foldr fun_type Cs' ?\<rho>U" using rb arg_res_type[of "tsubst \<rho> bary"] by (simp add: Cs'_def)
  have pk: "p \<le> k"
  proof -
    have "kok k \<rho> ?\<theta> T" by (rule kok_tyw[OF pi(2) twT kk])
    from kok_res_type[OF this] st(3) tsubst_tnorm[OF ac sol st(5)] show ?thesis by (simp add: p_def Cs'_def)
  qed
  have pg: "p \<in> set (arity_guesses cfg bary)"
  proof (cases "is_TVar bary")
    case True
    with pk cfg(2) show ?thesis by (auto simp: arity_guesses_def)
  next
    case False
    have "\<not> is_funT bary"
    proof
      assume "is_funT bary"
      then obtain X Y where "bary = X \<rightarrow>\<^sub>T Y" by (auto simp: is_funT_fun)
      then have "is_funT (tnorm ?\<theta> bary)" by simp
      with st(3) res_type_base[of "tnorm ?\<theta> T"] show False by simp
    qed
    from nonfun_tsubst[OF this False] have "Cs' = []" by (simp add: Cs'_def arg_types_nonfun)
    with False show ?thesis by (simp add: arity_guesses_def p_def)
  qed
  \<comment> \<open>New type variables for the guess\<close>
  obtain env0 Cs where g: "gentvars p env = (env0, Cs)" by (cases "gentvars p env")
  note gs = gentvars_simps[OF g] and gm = gentvars_cases(1)[OF g]
  have grb: "ground ar (tsubst \<rho> bary)" using twbary pc0(2) by (auto simp: tyw_def gsol_def intro: ground_tsubst)
  have gC: "\<forall>C\<in>set Cs'. ground ar C" using ground_arg_types[OF grb] by (simp add: Cs'_def)
  from gentvars_inst[OF g _ gC pc0(2) pi(2)] obtain \<rho>1 where
    r1: "gsol alg ar ?\<theta> \<rho>1" "tagree (maxidx env) \<rho> \<rho>1" "map (tsubst \<rho>1) Cs = Cs'"
    by (auto simp: p_def)
  have ti0: "tinv ar (maxidx env0) ?\<theta> A" by (rule tinv_mono[OF pi(2) gm])
  have pc1: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env0 dps"
    by (rule pcinv_text[OF pc gs(1)]) (simp_all add: gs(2) textends_refl gm ti0 ei(2) r1(1,2))
  let ?A' = "A \<union> ctvars Cs"
  have ti0': "tinv ar (maxidx env0) (tyenv env0) ?A'" using tinv_gentvars[OF pi(2) g] gs(2) by simp
  have twC: "\<forall>C\<in>set Cs. tyw ar (tyenv env0) ?A' C" using tyw_gentvars[OF pi(2) g] gs(2) by simp
  have tw0: "tyw ar (tyenv env0) ?A' base" "tyw ar (tyenv env0) ?A' bary"
    using twb0 twbary gs(2) by (auto intro: tyw_mono)
  have i1bary: "tsubst \<rho>1 bary = tsubst \<rho> bary" by (rule tyw_tagree[OF pi(2) twbary r1(2)])
  have i1base: "tsubst \<rho>1 base = ?\<rho>U" using tyw_tagree[OF pi(2) twb0 r1(2)] ib by simp
  define X where "X = (if Cs = [] then base else bary)"
  define Y where "Y = (if Cs = [] then bary else foldr fun_type Cs base)"
  have twXY: "tyw ar (tyenv env0) ?A' X" "tyw ar (tyenv env0) ?A' Y"
    using tw0 twC by (auto simp: X_def Y_def tyw_foldr_fun)
  have eqXY: "tsubst \<rho>1 X = tsubst \<rho>1 Y"
  proof (cases "Cs = []")
    case True
    then have "Cs' = []" using r1(3) by simp
    with True show ?thesis using i1bary i1base \<rho>bary by (simp add: X_def Y_def)
  next
    case False
    then show ?thesis using i1bary i1base \<rho>bary r1(3) by (simp add: X_def Y_def tsubst_foldr_fun)
  qed
  have cA': "tcert alg A \<Longrightarrow> tcert alg ?A'" using tcert_gentvars[OF g] by simp
  from cunify_types_pcomplete'[OF pc1 Un_upper1 ti0' twXY eqXY cA'] obtain env' \<rho>' where
    cu: "cunify_types alg X Y env0 = returnW env'" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
      "tenv env' = tenv env0" "pextends env0 env'" "maxidx env0 \<le> maxidx env'" "tagree (maxidx env0) \<rho>1 \<rho>'"
      "\<And>Z. reach (instE \<rho>' env') Z = reach (instE \<rho>1 env0) Z" "tnorm (tyenv env') X = tnorm (tyenv env') Y"
      "tinv ar (maxidx env') (tyenv env') ?A'"
    by blast
  have pu: "okW (proj_unify cfg base bary Cs env0) env'"
    using cu(1) cfg(1) proj_unify_ok by (cases "Cs = []") (simp_all add: X_def Y_def)
  let ?\<theta>' = "tyenv env'"
  note pi' = pinvD[OF pcinvD(1)[OF cu(2)]]
  have ac': "tacyc ?\<theta>'" by (rule tinv_tacyc[OF pi'(2)])
  have ext0: "textends ?\<theta> ?\<theta>'" using cu(4) gs(2) by (simp add: pextends_def)
  have tb': "tnorm ?\<theta>' bary = tnorm ?\<theta>' (foldr fun_type Cs base)"
    using cu(8) by (cases "Cs = []") (simp_all add: X_def Y_def)
  have twC': "\<forall>C\<in>set Cs. tyw ar ?\<theta>' A C"
  proof
    fix C assume C: "C \<in> set Cs"
    have t1: "tyw ar ?\<theta>' ?A' C" using twC C tyw_textends[OF ac' ext0] gs(2) by simp
    have "uvars ?\<theta>' C \<subseteq> uvars ?\<theta>' (foldr fun_type Cs base)" using C by (auto simp: uvars_foldr_fun)
    also have "\<dots> = uvars ?\<theta>' bary" using uvars_tnorm_eq[OF tb'] by simp
    also have "\<dots> \<subseteq> uvarsA ?\<theta>' A" using tyw_textends[OF ac' ext0 twbary] by (simp add: tyw_def)
    finally show "tyw ar ?\<theta>' A C" by (rule tyw_shrink[OF cu(9) t1])
  qed
  have pe': "pextends env env'" using gentvars_pextends[OF g] cu(4) by (rule pextends_trans)
  have mx: "maxidx env \<le> maxidx env'" using gm cu(5) by simp
  have ag': "tagree (maxidx env) \<rho> \<rho>'" using tagree_trans[OF r1(2) cu(6)] gm by simp
  have iUs: "map (tsubst \<rho>') Us = map (tsubst \<rho>) Us"
    using tyw_tagree[OF pi(2) _ ag'] twUs by simp
  have iCs: "map (tsubst \<rho>') Cs = Cs'"
  proof -
    have "tsubst \<rho>' C = tsubst \<rho>1 C" if "C \<in> set Cs" for C
    proof -
      from gentvars_tvar[OF g that] obtain n where "C = TVar (gtv (maxidx env + 1) n) []"
        "maxidx env0 = maxidx env + 1" by blast
      then show ?thesis using tagreeD[OF cu(6), of "gtv (maxidx env + 1) n" "[]"] by simp
    qed
    then show ?thesis using r1(3) by (metis (no_types, lifting) map_eq_conv)
  qed
  have rr: "reach (instE \<rho>' env') Z = reach (instE \<rho> env) Z" for Z
  proof -
    have "reach (instE \<rho>' env') Z = reach (instE \<rho>1 env0) Z" by (rule cu(7))
    also have "\<dots> = reach (instE \<rho> env) Z"
      by (rule reach_lookup_eq, rule instE_tagree_lookup[OF pi(2) _ gs(1) r1(2)]) (use pi(3) in blast)
    finally show ?thesis .
  qed
  have tw': "\<forall>X\<in>set (Us @ Cs). tyw ar ?\<theta>' A X" using twUs twC' tyw_textends[OF ac' ext0] by auto
  have "Ws = map trty (map (tsubst \<rho>') (Us @ Cs))" using Ws iUs iCs by (simp add: Cs'_def)
  moreover have "tnorm ?\<theta>' T = tnorm ?\<theta>' (foldr fun_type (Us @ Cs) base)"
  proof -
    have "tnorm ?\<theta>' T = tnorm ?\<theta>' (tnorm ?\<theta> T)" by (simp add: tnorm_textends[OF ac' ext0])
    also have "tnorm ?\<theta> T = foldr fun_type (map (tnorm ?\<theta>) Us) (tnorm ?\<theta> bary)"
      using st(2,3) arg_res_type[of "tnorm ?\<theta> T"] by simp
    also have "tnorm ?\<theta>' \<dots> = foldr fun_type (map (tnorm ?\<theta>') Us) (tnorm ?\<theta>' bary)"
      by (simp add: tnorm_foldr_fun tnorm_textends[OF ac' ext0] comp_def)
    also have "tnorm ?\<theta>' bary = tnorm ?\<theta>' (foldr fun_type Cs base)" by (rule tb')
    finally show ?thesis by (simp add: tnorm_foldr_fun)
  qed
  ultimately show ?thesis
    using that[OF st(1) pg g pu cu(2) _ pe' mx ag' rr tw'] cu(3) gs(1) by simp
qed

text \<open>
  A projection on a bound variable of type \<open>Us \<Rightarrow> bary\<close>: the instance of \<open>bary\<close> takes \<open>p\<close>
  arguments; the guess \<open>p\<close> is at most \<open>k\<close> by the k-condition.
\<close>

lemma pmc_proj:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
    and sj: "s = BVar j \<degree>\<degree> ss"
  shows "pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> ?\<theta> A" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar ?\<theta> A T"
    and wu: "swf_tm ar rb u" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    and bu: "below (maxidx env) u" and hl: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and twU: "tyw ar ?\<theta> A U" and fU: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U)))"
    and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
    and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    unfolding pmc_pre_def by blast+
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain T0 base Ts' projs sq where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts" "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T"
    "tyw ar ?\<theta> A T0" "tyw ar ?\<theta> A base"
    "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    "\<forall>j<length targs. (Bound (integer_of_nat j), Ts' ! (length targs - Suc j), targs ! (length targs - Suc j))
      \<in> set projs"
    "okW (mc cfg vname rb targs u env dps) sq"
    and prj: "\<And>bv T targ Us bary p y. (bv, T, targ) \<in> set projs \<Longrightarrow> ok (strip_type env T) (Us, bary) \<Longrightarrow>
      p \<in> set (arity_guesses cfg bary) \<Longrightarrow>
      proj_elem cfg vname rb targs u env dps base Ts' bv Us bary targ p y \<Longrightarrow> ev cfg sq y"
    by (rule pmc_rigid_seq[OF cfg(1) pre hA hV]) blast
  have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
  then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
  from hlong_nonAbs[OF hl this] have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and nfU: "\<not> is_funT (tnorm ?\<theta> U)" by auto
  have bU: "tnorm ?\<theta> base = tnorm ?\<theta> U" using ty0(8) arg_res_type_base[OF nfU] by simp
  let ?\<rho>U = "tsubst \<rho> U"
  have iU: "tsubst \<rho> (tnorm ?\<theta> U) = ?\<rho>U" by (rule tsubst_tnorm[OF ac sol tcU[OF twU]])
  have nf\<rho>U: "\<not> is_funT ?\<rho>U" using fU arg_res_type_base[OF nfU] iU by simp
  have ib: "tsubst \<rho> base = ?\<rho>U" by (rule tsubst_tnorm_eq[OF ac sol tcU[OF ty0(6)] tcU[OF twU] bU])
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  have lTs': "length Ts' = length Ts" using arg_cong[OF ty0(3), of length] by simp
  have iTs: "map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
    by (rule map_tsubst_tnorm[OF ac sol _ _ ty0(3)]) (use twTs ty0(4) tcU in blast)+
  \<comment> \<open>The target\<close>
  from tys sj obtain Ws where tyh': "(ibctx \<rho> Ts, \<tau>') \<turnstile> BVar j : Ws \<Rrightarrow> trty ?\<rho>U"
    and tyss: "(ibctx \<rho> Ts, \<tau>') \<tturnstile> ss : Ws"
    by (auto elim: list_app_typeE)
  have atj: "is_atom (BVar j)" by (simp add: is_atom_def)
  have nrss: "\<forall>w\<in>set ss. no_redex w" using nrs sj no_redex_atom_apps[OF atj] by simp
  have nlh: "no_loose_bound (BVar j) (length Ts)" and nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)"
    using nls sj by (simp_all add: no_loose_bound_list_app)
  have lWs: "length Ws = length ss" by (rule typings_length[OF tyss])
  have lsz_s: "lsize (ibctx \<rho> Ts) \<tau>' s (trty ?\<rho>U) =
      Suc (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i)) + (tsize (trty ?\<rho>U) - 1)"
    using lsize_atom_apps[OF atj tyh' tyss nrss] sj by simp
  have jn: "j < length Ts" using nlh by simp
  define i0 where "i0 = length targs - Suc j"
  have i0: "i0 < length targs" using jn lTs by (simp add: i0_def)
  define T where "T = Ts' ! i0"
  define targ where "targ = targs ! i0"
  have inp: "(Bound (integer_of_nat j), T, targ) \<in> set projs"
    using ty0(9) jn lTs by (simp add: T_def targ_def i0_def)
  have tgm: "targ \<in> set targs" using i0 by (simp add: targ_def)
  have twT: "tyw ar ?\<theta> A T" using ty0(4) i0 lTs lTs' by (simp add: T_def)
  have tnT: "tnorm ?\<theta> T = tnorm ?\<theta> (Ts ! i0)"
    using arg_cong[OF ty0(3), of "\<lambda>xs. xs ! i0"] i0 lTs lTs' by (simp add: T_def)
  have iT: "tsubst \<rho> T = tsubst \<rho> (Ts ! i0)"
    using arg_cong[OF iTs, of "\<lambda>xs. xs ! i0"] i0 lTs lTs' by (simp add: T_def)
  have bT: "ibctx \<rho> Ts j = trty (tsubst \<rho> T)" using jn lTs iT by (simp add: env_ext_map i0_def)
  from tyh' bT have tT: "trty (tsubst \<rho> T) = Ws \<Rrightarrow> trty ?\<rho>U" by auto
  from proj_guess[OF cfg pc kk twT ty0(6) ib nf\<rho>U tT] obtain Us bary p env0 Cs env' \<rho>' where
    st1: "strip_type env T = return (Us, bary)" and pg: "p \<in> set (arity_guesses cfg bary)"
    and g: "gentvars p env = (env0, Cs)" and pu: "okW (proj_unify cfg base bary Cs env0) env'"
    and pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps" and te': "tenv env' = tenv env"
    and pe': "pextends env env'" and mx: "maxidx env \<le> maxidx env'" and ag': "tagree (maxidx env) \<rho> \<rho>'"
    and rr': "\<And>Z. reach (instE \<rho>' env') Z = reach (instE \<rho> env) Z"
    and twUC0: "\<forall>X\<in>set (Us @ Cs). tyw ar (tyenv env') A X"
    and WsUC0: "Ws = map trty (map (tsubst \<rho>') (Us @ Cs))"
    and tT': "tnorm (tyenv env') T = tnorm (tyenv env') (foldr fun_type (Us @ Cs) base)"
    by blast
  let ?\<theta>' = "tyenv env'"
  note pi' = pinvD[OF pcinvD(1)[OF pc']]
  have ac': "tacyc ?\<theta>'" by (rule tinv_tacyc[OF pi'(2)])
  have ext0: "textends ?\<theta> ?\<theta>'" using pe' by (simp add: pextends_def)
  define UC where "UC = Us @ Cs"
  have twUC: "\<forall>X\<in>set Ts' \<union> set UC. tyw ar ?\<theta>' A X"
    using ty0(4) twUC0 tyw_textends[OF ac' ext0] by (auto simp: UC_def)
  have iTs'': "map (tsubst \<rho>') Ts' = map (tsubst \<rho>) Ts"
    using iTs tyw_tagree[OF pi(2) _ ag'] ty0(4) by (metis (no_types, lifting) map_eq_conv)
  have WsUC: "Ws = map trty (map (tsubst \<rho>') UC)" using WsUC0 by (simp add: UC_def)
  have lUC: "length UC = length ss" using lWs WsUC by simp
  \<comment> \<open>The arguments of the projection\<close>
  obtain env'' args where ma: "make_args vname Ts' env' UC = (env'', args)"
    by (cases "make_args vname Ts' env' UC")
  define ws where "ws = map (Abs_m (length Ts)) ss"
  have lw: "length ws = length UC" using lUC by (simp add: ws_def)
  have tyssi: "(ibctx \<rho> Ts, \<tau>') \<turnstile> ss ! i : trty (tsubst \<rho>' (UC ! i))" if "i < length UC" for i
    using typings_nth[OF tyss, of i] that lUC WsUC by simp
  have wsi: "no_loose_bound (ws ! i) 0 \<and> (\<forall>e. (e, \<tau>') \<turnstile> ws ! i : trty (tsubst \<rho>' (foldr fun_type Ts' (UC ! i))))"
    if i: "i < length UC" for i
  proof -
    have nl: "no_loose_bound (ws ! i) 0" using nlss i lUC by (simp add: ws_def loose_bound_Abs_m)
    have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m (length (map trty (map (tsubst \<rho>) Ts))) (ss ! i) :
        map trty (map (tsubst \<rho>) Ts) \<Rrightarrow> trty (tsubst \<rho>' (UC ! i))"
      by (rule typing_Abs_m) (use tyssi[OF i] in simp)
    then have "(e, \<tau>') \<turnstile> ws ! i : trty (tsubst \<rho>' (foldr fun_type Ts' (UC ! i)))" for e
      using typing_closed[OF _ nl] iTs'' i lUC by (simp add: ws_def tsubst_foldr_fun trty_foldr)
    with nl show ?thesis by blast
  qed
  obtain W1 \<sigma>1 xs where me: "pcinv alg ar A W1 \<rho>' \<tau>' \<sigma>1 env'' dps" "agree (maxidx env') \<sigma> \<sigma>1"
    "agreeV (maxidx env') W W1" "maxidx env' \<le> maxidx env''" "pextends env' env''"
    "tenv env'' = tenv env'" "tyenv env'' = tyenv env'"
    "length xs = length UC" "distinct xs" "\<forall>x\<in>set xs. maxidx env' < snd x \<and> snd x \<le> maxidx env''"
    "args = map2 (\<lambda>x U. combound (Var x (foldr fun_type Ts' U)) 0 (length Ts')) xs UC"
    "\<forall>i<length UC. \<sigma>1 (code (AVar (xs ! i))) = ws ! i \<and> W1 (xs ! i) = foldr fun_type Ts' (UC ! i)"
    by (rule make_args_pextend[OF pc' ma _ lw wsi]) (use twUC in auto)
  have me12: "\<sigma>1 (code (AVar (xs ! i))) = ws ! i" "W1 (xs ! i) = foldr fun_type Ts' (UC ! i)"
    if "i < length UC" for i using me(12) that by blast+
  have la: "length args = length UC" using me(8,11) by simp
  have ai: "args ! i = combound (Var (xs ! i) (foldr fun_type Ts' (UC ! i))) 0 (length Ts')"
    if "i < length UC" for i using me(8,11) that by simp
  have hai: "head_of (args ! i) = Var (xs ! i) (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using ai[OF that] by (simp add: head_of_combound)
  define Ls where "Ls = map (\<lambda>arg. list_comb (head_of arg) targs) args"
  have lLs: "length Ls = length UC" using la by (simp add: Ls_def)
  have Lsi: "Ls ! i = list_comb (Var (xs ! i) (foldr fun_type Ts' (UC ! i))) targs" if "i < length UC" for i
    using hai[OF that] la that by (simp add: Ls_def)
  define dp where "dp = (rb, list_comb targ Ls, u)"
  \<comment> \<open>The new pair is in the invariant\<close>
  note pi'' = pinvD[OF pcinvD(1)[OF me(1)]]
  let ?\<theta>'' = "tyenv env''"
  have ac'': "tacyc ?\<theta>''" by (rule tinv_tacyc[OF pi''(2)])
  have pe'': "pextends env env''" using pe' me(5) by (rule pextends_trans)
  have ext'': "textends ?\<theta> ?\<theta>''" using pe'' by (simp add: pextends_def)
  have agV: "agreeV (maxidx env) W W1" using agreeV_mono[OF me(3) mx] .
  have agS: "agree (maxidx env) \<sigma> \<sigma>1" using agree_mono[OF me(2) mx] .
  have tn'': "tnorm ?\<theta>'' (tnorm ?\<theta> X) = tnorm ?\<theta>'' X" for X by (rule tnorm_textends[OF ac'' ext''])
  have tg'': "list_all2 (typed env'' W1 (map snd rb)) targs Ts'"
  proof -
    have "list_all2 (typed env'' W1 (map snd rb)) targs Ts"
      by (rule list_all2_typed_psext[OF ac'' pe'' pi(6) pi''(6) agV _ tgty]) (use tg in blast)
    moreover have "map (tnorm ?\<theta>'') Ts' = map (tnorm ?\<theta>'') Ts"
      using arg_cong[OF ty0(3), of "map (tnorm ?\<theta>'')"] by (simp add: comp_def tn'')
    ultimately show ?thesis by (rule list_all2_typed_tnorm)
  qed
  have tctxi: "tctx env'' W1 (xs ! i) = tnorm ?\<theta>'' (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using wcons_tctx[OF pi''(6)] me12(2)[OF that] by simp
  have tyLs: "list_all2 (typed env'' W1 (map snd rb)) Ls UC"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length Ls = length UC" by (rule lLs)
    fix i assume "i < length Ls"
    then have i: "i < length UC" using lLs by simp
    show "typed env'' W1 (map snd rb) (Ls ! i) (UC ! i)"
      using typed_Var_list_comb[OF tctxi[OF i] tg''] Lsi[OF i] by simp
  qed
  have tUC: "tnorm ?\<theta>'' (foldr fun_type UC base) = tnorm ?\<theta>'' (Ts ! i0)"
  proof -
    have "tnorm ?\<theta>'' (Ts ! i0) = tnorm ?\<theta>'' T" using tnT tn'' by metis
    then show ?thesis using tT' me(7) by (simp add: UC_def)
  qed
  have btarg: "below (maxidx env) targ" using tg tgm by blast
  have tytarg: "typed env'' W1 (map snd rb) targ (foldr fun_type UC base)"
  proof -
    have "typed env W (map snd rb) targ (Ts ! i0)" using tgty i0 by (simp add: list_all2_conv_all_nth targ_def)
    then have "typed env'' W1 (map snd rb) targ (Ts ! i0)" by (rule typed_psext[OF ac'' pe'' pi(6) pi''(6) agV btarg])
    then show ?thesis by (rule typed_tnorm_cong[OF _ refl tUC])
  qed
  have tyl: "typed env'' W1 (map snd rb) (list_comb targ Ls) base" by (rule typed_list_comb[OF tytarg tyLs])
  have tyu'': "typed env'' W1 (map snd rb) u base"
  proof -
    have "typed env W (map snd rb) u base" using tyu bU by (simp add: typed_def)
    then show ?thesis by (rule typed_psext[OF ac'' pe'' pi(6) pi''(6) agV bu])
  qed
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
  have itg: "inst \<rho>' t = inst \<rho> t" if "t \<in> set targs" for t
    using inst_tyw_tagree[OF pi(2) _ ag'] tg that by blast
  have ta1: "mk_subst \<sigma>1 (tr (inst \<rho>' t)) = mk_subst \<sigma> (tr (inst \<rho> t))" if "t \<in> set targs" for t
    using itg[OF that] mk_subst_agree[OF _ agS, of "inst \<rho> t"] tg that by simp
  have Lsem: "map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>' t))) Ls = map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
  proof (rule nth_equalityI)
    show "length (map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>' t))) Ls) = length (map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss)"
      using lLs lUC by simp
    fix i assume "i < length (map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>' t))) Ls)"
    then have i: "i < length UC" using lLs by simp
    have "map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>' t))) targs = ?st" using ta1 by simp
    then show "map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>' t))) Ls ! i = map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss ! i"
      using Lsi[OF i] me12(1)[OF i] i lUC lLs
      by (simp add: inst_list_comb tr_list_comb ws_def comp_def del: map_eq_conv)
  qed
  have stj: "rev ?st ! j = mk_subst \<sigma> (tr (inst \<rho> targ))" using jn lTs by (simp add: rev_nth targ_def i0_def)
  have e1: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> targ)) \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
    using Abs_m_apps_BVar_head[of ?st "length Ts" j ss] lTs jn stj sj by simp
  have "mk_subst \<sigma>1 (tr (inst \<rho>' (list_comb targ Ls))) =
      mk_subst \<sigma> (tr (inst \<rho> targ)) \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
    using Lsem ta1[OF tgm] by (simp add: inst_list_comb tr_list_comb comp_def del: map_eq_conv)
  moreover have "mk_subst \<sigma>1 (tr (inst \<rho>' u)) = mk_subst \<sigma> (tr (inst \<rho> u))"
    using inst_tyw_tagree[OF pi(2) twu ag'] mk_subst_agree[OF _ agS, of "inst \<rho> u"] bu by simp
  ultimately have dsol: "dsolved \<sigma>1 (instd \<rho>' dp)"
    unfolding dp_def instd_simp dsolved_dsolvedB dsolvedB_unabs using equiv_trans[OF equiv_sym[OF e1] eqs] by simp
  have twG: "tyw ar ?\<theta>'' A (foldr fun_type Ts' (UC ! i))" if "i < length UC" for i
    using twUC that me(7) by (simp add: tyw_foldr_fun)
  have bxs: "maxidx env < snd (xs ! i) \<and> snd (xs ! i) \<le> maxidx env''" if "i < length UC" for i
  proof -
    have "xs ! i \<in> set xs" using me(8) that by simp
    with me(10) mx show ?thesis by force
  qed
  have pcd: "pcinv alg ar A W1 \<rho>' \<tau>' \<sigma>1 env'' (dp # dps)"
  proof (rule pcinv_Cons[OF me(1) _ _ _ _ dsol])
    have wLs: "swf_tm ar rb t" if "t \<in> set Ls" for t
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "swf_tm ar rb (Var (xs ! i) (foldr fun_type Ts' (UC ! i)))" using twG[OF i(1)] by (simp add: swf_tm_def tyw_def)
      then show ?thesis using Lsi[OF i(1)] i(2) tg by (simp add: swf_tm_list_comb)
    qed
    show "swf_dp ar dp" using sb wu tg tgm wLs by (simp add: dp_def swf_dp_def swf_tm_list_comb)
    have tLs: "tyw ar ?\<theta>'' A X" if "t \<in> set Ls" "X \<in> tys t" for t X
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      then show ?thesis using that(2) Lsi[OF i(1)] twG[OF i(1)] tg tyw_textends[OF ac'' ext'']
        by (auto simp: tys_list_comb)
    qed
    show "\<forall>X\<in>dtys dp. tyw ar ?\<theta>'' A X"
      using twb twu tg tgm tLs tyw_textends[OF ac'' ext''] by (auto simp: dp_def tys_list_comb)
    show "ptyped env'' W1 dp" using tyl tyu'' by (auto simp: dp_def)
    have "below (maxidx env'') t" if "t \<in> set Ls" for t
    proof -
      from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
      have "maxidx env \<le> maxidx env''" using mx me(4) by simp
      then have "\<forall>t\<in>set targs. below (maxidx env'') t" using tg by (auto intro: below_mono)
      moreover have "below (maxidx env'') (Var (xs ! i) (foldr fun_type Ts' (UC ! i)))"
        using bxs[OF i(1)] by (simp add: below_def)
      ultimately show ?thesis using Lsi[OF i(1)] i(2) by (simp add: below_list_comb)
    qed
    moreover have "maxidx env \<le> maxidx env''" using mx me(4) by simp
    ultimately show "dp_below (maxidx env'') dp"
      using btarg bu by (auto simp: dp_def dp_below_def below_list_comb intro: below_mono)
  qed
  \<comment> \<open>Simplification of the new pair\<close>
  from SIMPL_pcomplete[OF pcd] obtain st' \<rho>2 where sp: "okW (SIMPL alg env'' (dp # dps)) st'"
    and sr: "psimpl_res alg ar A W1 \<tau>' \<sigma>1 \<rho>' (dp # dps) env'' \<rho>2 st'" by blast
  obtain env2 fr ff where st'e: "st' = (env2, fr, ff)" by (cases st')
  from sr have sr': "pcinv alg ar A W1 \<rho>2 \<tau>' \<sigma>1 env2 (fr @ ff)" "pextends env'' env2" "maxidx env'' \<le> maxidx env2"
    "tagree (maxidx env'') \<rho>' \<rho>2"
    "\<And>Z. reach (instE \<rho>2 env2) Z \<subseteq> reach (instE \<rho>' env'') (Z \<union> ivps \<rho>' (dp # dps))"
    "ivps \<rho>2 (fr @ ff) \<subseteq> reach (instE \<rho>' env'') (ivps \<rho>' (dp # dps))"
    unfolding st'e psimpl_res_def by auto
  have pel: "proj_elem cfg vname rb targs u env dps base Ts' (Bound (integer_of_nat j)) Us bary targ p
      (El_C (list_comb (Bound (integer_of_nat j)) args) env2 (fr @ ff))"
    unfolding proj_elem_def using g pu ma sp st'e cfg(1) by (auto simp: dp_def Ls_def UC_def)
  have evp: "ev cfg sq (El_C (list_comb (Bound (integer_of_nat j)) args) env2 (fr @ ff))"
    by (rule prj[OF inp _ pg pel]) (simp add: st1 return_def)
  \<comment> \<open>The new variables\<close>
  define NV where "NV = set (map2 (\<lambda>x X. (x, tsubst \<rho>' (foldr fun_type Ts' X))) xs UC)"
  have "map2 (\<lambda>x X. (x, tsubst \<rho>' (foldr fun_type Ts' X))) xs UC =
      map (\<lambda>i. (xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i)))) [0..<length UC]"
    using me(8) by (intro nth_equalityI) auto
  then have NVi: "y \<in> NV \<longleftrightarrow> (\<exists>i<length UC. y = (xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i))))" for y
    by (auto simp: NV_def)
  have NVb: "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env''" if "y \<in> NV" for y
    using that NVi bxs by auto
  have vai: "vps (inst \<rho>' (args ! i)) = {(xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i)))}" if "i < length UC" for i
    using ai[OF that] by simp
  have vargs: "\<Union> (vps ` inst \<rho>' ` set args) = NV"
  proof
    show "\<Union> (vps ` inst \<rho>' ` set args) \<subseteq> NV" using vai la NVi by (force simp: in_set_conv_nth)
    show "NV \<subseteq> \<Union> (vps ` inst \<rho>' ` set args)"
    proof
      fix y assume "y \<in> NV"
      then obtain i where i: "i < length UC" "y = (xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i)))" using NVi by blast
      then have "y \<in> vps (inst \<rho>' (args ! i))" using vai by simp
      with i(1) la show "y \<in> \<Union> (vps ` inst \<rho>' ` set args)" by (auto dest: nth_mem[of i args])
    qed
  qed
  have iargs: "inst \<rho>2 a = inst \<rho>' a" if "a \<in> set args" for a
  proof -
    from that obtain i where i: "i < length UC" "a = args ! i" using la by (auto simp: in_set_conv_nth)
    have "\<forall>X\<in>tys a. tyw ar ?\<theta>'' A X" using ai[OF i(1)] i(2) twG[OF i(1)] by simp
    from inst_tyw_tagree[OF pi''(2) this sr'(4)] show ?thesis .
  qed
  define D where "D = pmc_dom \<rho> u targs dps"
  have vLs: "vps (inst \<rho>' t) \<subseteq> NV \<union> D" if "t \<in> set Ls" for t
  proof -
    from that obtain i where i: "i < length UC" "t = Ls ! i" using lLs by (auto simp: in_set_conv_nth)
    have "(xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i))) \<in> NV" using NVi i(1) by blast
    then show ?thesis using Lsi[OF i(1)] i(2) itg by (auto simp: inst_list_comb vps_list_comb D_def)
  qed
  have idps: "ivps \<rho>' dps = ivps \<rho> dps" using ivps_tagree[OF pc ag'] by simp
  have vdp: "ivps \<rho>' (dp # dps) \<subseteq> D \<union> NV"
  proof -
    have "vps (inst \<rho>' targ) \<subseteq> D" using itg[OF tgm] tgm by (auto simp: D_def)
    moreover have "vps (inst \<rho>' u) \<subseteq> D" using inst_tyw_tagree[OF pi(2) twu ag'] by (auto simp: D_def)
    ultimately show ?thesis using vLs idps
      by (auto simp: dp_def vps_dp_def inst_list_comb vps_list_comb D_def)
  qed
  have rr: "reach (instE \<rho>' env'') Z = reach (instE \<rho> env) Z" for Z
  proof -
    have "reach (instE \<rho>' env'') Z = reach (instE \<rho>' env') Z" by (rule reach_lookup_eq) (simp add: me(6))
    also have "\<dots> = reach (instE \<rho> env) Z" by (rule rr')
    finally show ?thesis .
  qed
  have nvr: "reach (instE \<rho> env) NV = NV" using reach_new[of "instE \<rho> env" NV] ei(6) NVb by simp
  have rDNV: "reach (instE \<rho> env) (Z \<union> D \<union> NV) = reach (instE \<rho> env) (Z \<union> D) \<union> NV" for Z
    using nvr by (simp add: reach_Un)
  have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>2 env2 (fr @ ff) D NV"
  proof (rule psextI[OF sr'(1) agV agS])
    show "tagree (maxidx env) \<rho> \<rho>2" using tagree_trans[OF ag' sr'(4)] mx me(4) by simp
    show "maxidx env \<le> maxidx env2" using mx me(4) sr'(3) by simp
    show "pextends env env2" using pe'' sr'(2) by (rule pextends_trans)
    show "finite NV" by (simp add: NV_def)
    show "maxidx env < snd (fst y) \<and> snd (fst y) \<le> maxidx env2" if "y \<in> NV" for y
      using NVb[OF that] sr'(3) by simp
    show "reach (instE \<rho>2 env2) Z \<subseteq> reach (instE \<rho> env) (Z \<union> D) \<union> NV" for Z
    proof -
      have "reach (instE \<rho>2 env2) Z \<subseteq> reach (instE \<rho> env) (Z \<union> ivps \<rho>' (dp # dps))" using sr'(5)[of Z] rr by simp
      also have "\<dots> \<subseteq> reach (instE \<rho> env) (Z \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
      finally show ?thesis using rDNV by simp
    qed
    show "ivps \<rho>2 (fr @ ff) \<subseteq> reach (instE \<rho> env) D \<union> NV"
    proof -
      have "ivps \<rho>2 (fr @ ff) \<subseteq> reach (instE \<rho> env) (ivps \<rho>' (dp # dps))" using sr'(6) rr by simp
      also have "\<dots> \<subseteq> reach (instE \<rho> env) ({} \<union> D \<union> NV)" using vdp by (intro reach_subset) blast
      finally show ?thesis using rDNV[of "{}"] by simp
    qed
  qed
  \<comment> \<open>The copy\<close>
  define u' where "u' = list_comb (Bound (integer_of_nat j)) args"
  note pi2 = pinvD[OF pcinvD(1)[OF sr'(1)]]
  have ac2: "tacyc (tyenv env2)" by (rule tinv_tacyc[OF pi2(2)])
  have ext2: "textends ?\<theta>'' (tyenv env2)" using sr'(2) by (simp add: pextends_def)
  have nri: "no_redex (ss ! i)" "no_loose_bound (ss ! i) (length Ts)" if "i < length ss" for i
    using nrss nlss that by auto
  have cr: "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s 1 u' env2 (fr @ ff) W1 \<sigma>1 \<rho>2 NV"
    unfolding pcopy_res_def
  proof (intro conjI sx)
    have tyai: "list_all2 (typed env'' W1 (rev Ts)) args UC"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length args = length UC" by (rule la)
      fix i assume "i < length args"
      then have i: "i < length UC" using la by simp
      have "typed env'' W1 (rev Ts') (args ! i) (UC ! i)"
        using typed_combound_Var[OF tctxi[OF i]] ai[OF i] by simp
      moreover have "map (tnorm ?\<theta>'') (rev Ts) = map (tnorm ?\<theta>'') (rev Ts')"
        using arg_cong[OF ty0(3), of "\<lambda>xs. rev (map (tnorm ?\<theta>'') xs)"] by (simp add: rev_map comp_def tn'')
      ultimately show "typed env'' W1 (rev Ts) (args ! i) (UC ! i)" by (rule typed_tnorm_cong) simp
    qed
    have tyBj: "typed env'' W1 (rev Ts) (Bound (integer_of_nat j)) (foldr fun_type UC base)"
      using tUC jn lTs by (simp add: typed_def has_type_Bound_iff rev_nth i0_def rev_map[symmetric] integer_reps)
    have "typed env'' W1 (rev Ts) u' base" using typed_list_comb[OF tyBj tyai] by (simp add: u'_def)
    moreover have "tnorm ?\<theta>'' U = tnorm ?\<theta>'' base" using arg_cong[OF bU, of "tnorm ?\<theta>''"] tn'' by simp
    ultimately have tyu'2: "typed env'' W1 (rev Ts) u' U" by (rule typed_tnorm_cong[OF _ refl])
    show "typed env2 W1 (rev Ts) u' U" by (rule typed_ext[OF ac2 ext2 pi''(6) pi2(6) _ tyu'2]) simp
    have "\<forall>a\<in>set args. swf_cp ar (length Ts') a"
      by (rule make_args_swf_cp[OF ma]) (use twUC in \<open>auto simp: tyw_def\<close>)
    moreover have "swf_cp ar (length Ts) (Bound (integer_of_nat j))"
      using jn by (simp add: swf_cp_def integer_reps)
    ultimately show "swf_cp ar (length Ts) u'" using lTs' by (simp add: u'_def swf_cp_list_comb)
    show "\<forall>X\<in>tys u'. tyw ar (tyenv env2) A X"
      using twG ai la tyw_textends[OF ac2 ext2] by (auto simp: u'_def tys_list_comb in_set_conv_nth)
    have "below (maxidx env2) a" if "a \<in> set args" for a
    proof -
      from that obtain i where i: "i < length UC" "a = args ! i" using la by (auto simp: in_set_conv_nth)
      then show ?thesis using ai[OF i(1)] bxs[OF i(1)] sr'(3) by (simp add: below_def)
    qed
    moreover have "below (maxidx env2) (Bound (integer_of_nat j))" by (simp add: below_def)
    ultimately show "below (maxidx env2) u'" by (simp add: u'_def below_list_comb)
    show "vps (inst \<rho>2 u') \<subseteq> NV" using vargs iargs by (auto simp: u'_def inst_list_comb vps_list_comb)
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho>2 a))) args) ss"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho>2 a))) args) = length ss" using la lUC by simp
      fix i assume "i < length (map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho>2 a))) args)"
      then have i: "i < length UC" using la by simp
      have "inst \<rho>2 (args ! i) = inst \<rho>' (args ! i)" using iargs i la by simp
      then have "mk_subst \<sigma>1 (tr (inst \<rho>2 (args ! i))) = Abs_m (length Ts) (ss ! i) \<degree>\<degree> map BVar (downs (length Ts))"
        using ai[OF i] me12(1)[OF i] i lUC lTs' by (simp add: tr_combound0 ws_def)
      then show "map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho>2 a))) args ! i \<equiv>\<^sub>\<beta>\<^sub>\<eta> ss ! i"
        using Abs_m_apps_downs[OF nri(2)] i lUC la by simp
    qed
    then have "BVar j \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma>1 (tr (inst \<rho>2 a))) args \<equiv>\<^sub>\<beta>\<^sub>\<eta> BVar j \<degree>\<degree> ss"
      by (rule equiv_list_app[OF equiv_refl])
    then show "mk_subst \<sigma>1 (tr (inst \<rho>2 u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
      using sj by (simp add: u'_def inst_list_comb tr_list_comb comp_def integer_reps)
    let ?L = "map2 (\<lambda>x X. (x, tsubst \<rho>' (foldr fun_type Ts' X))) xs UC"
    have "map fst ?L = xs" using me(8) by (simp add: map_zip_map2 zip_map2 map_map comp_def split_def)
    then have dL: "distinct ?L" using me(9) by (metis distinct_map)
    have "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) = sum_list (map (vsz \<tau>' \<sigma>1) ?L)"
      using sum.distinct_set_conv_list[OF dL] by (simp add: NV_def)
    also have "\<dots> = (\<Sum>i<length UC. vsz \<tau>' \<sigma>1 (xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i))))"
      using me(8) by (simp add: sum_list_sum_nth atLeast0LessThan)
    also have "\<dots> = (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i))"
    proof (rule sum.cong)
      show "{..<length UC} = {..<length ss}" using lUC by simp
      fix i assume "i \<in> {..<length ss}"
      then have i: "i < length UC" using lUC by simp
      have i': "i < length ss" using i lUC by simp
      have "vsz \<tau>' \<sigma>1 (xs ! i, foldr fun_type (map (tsubst \<rho>) Ts) (tsubst \<rho>' (UC ! i))) =
          lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (trty (tsubst \<rho>' (UC ! i)))"
        by (rule vsz_Abs_m) (use me12(1)[OF i] tyssi[OF i] nri[OF i'] i' in \<open>simp_all add: ws_def\<close>)
      then show "vsz \<tau>' \<sigma>1 (xs ! i, tsubst \<rho>' (foldr fun_type Ts' (UC ! i))) = lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i)"
        using WsUC iTs'' i lUC by (simp add: tsubst_foldr_fun)
    qed
    finally show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>1 y) + 1 \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))" using lsz_s by simp
  qed
  have "\<not> is_Var (head_of (strip_abs_body u))" using hV nA by (simp add: strip_abs_body_nonAbs)
  with cr have "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
      u' env2 (fr @ ff) W1 \<sigma>1 \<rho>2 NV" by simp
  then show ?thesis unfolding pmc_post_def D_def using ty0(10) evp[folded u'_def] by blast
qed

end


context csig
begin

subsection \<open>Copies: arguments of an imitation\<close>

lemma psext_kokA:
  assumes "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    "kokA k \<rho> (tyenv env) A"
  shows "kokA k \<rho>' (tyenv env') A"
proof -
  note sd = psextD[OF assms(1)]
  note pi = pinvD[OF pcinvD(1)[OF assms(2)]]
  note pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
  have sol: "tsol (tyenv env') \<rho>'" using pcinvD(2)[OF sd(1)] by (simp add: gsol_def)
  have ext: "textends (tyenv env) (tyenv env')" using sd(6) by (simp add: pextends_def)
  show ?thesis
    by (rule kokA_textends[OF pi(2) tinv_tacyc[OF pi'(2)] ext sol sd(4) tinv_tcons_env[OF pi'(2)] pi'(2) assms(3)])
qed

lemma copycons_mc:
  assumes "ok (head_norm env uarg) u1" "ok (eta_norm env rb u1) u2"
    "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg env rb u2) else returnW False) False"
    "okW (mc cfg vname rb targs u2 env dps) sq"
  shows "okW (copycons cfg vname rb targs uarg uargs env dps) (S_MapCons uargs sq)"
proof -
  have h: "okW (liftM (head_norm env uarg)) u1" "okW (liftM (eta_norm env rb u1)) u2" using assms(1,2) by simp_all
  have m: "okW (if False then liftM (fastype env rb u2) \<bind> (\<lambda>A. liftM (mapM (fastype env rb) targs) \<bind>
      (\<lambda>Ts. let (env', newhd) = genvar vname env (foldr fun_type Ts A) in
        returnW (S_Single (El_C (combound newhd 0 (length Ts)) env' ((rb, list_comb newhd targs, u2) # dps)))))
      else mc cfg vname rb targs u2 env dps) sq"
    using assms(4) by simp
  have r: "okW (returnW (S_MapCons uargs sq)) (S_MapCons uargs sq)" by simp
  show ?thesis unfolding copycons_def okW_bindW using h assms(3) m r by blast
qed

lemma copycons_defer:
  "ok (head_norm env uarg) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> 0 < cfg_arity_bound cfg \<Longrightarrow>
    ok (defer_arg env rb u2) True \<Longrightarrow> ok (fastype env rb u2) A \<Longrightarrow> ok (mapM (fastype env rb) targs) Ts \<Longrightarrow>
    genvar vname env (foldr fun_type Ts A) = (env', newhd) \<Longrightarrow>
    okW (copycons cfg vname rb targs uarg uargs env dps)
      (S_MapCons uargs (S_Single (El_C (combound newhd 0 (length Ts)) env' ((rb, list_comb newhd targs, u2) # dps))))"
  by (simp add: copycons_def)

lemma sum_vsz_agree': "agree m \<sigma> \<sigma>' \<Longrightarrow> \<forall>y\<in>NV. snd (fst y) \<le> m \<Longrightarrow> sum (vsz \<tau>' \<sigma>') NV = sum (vsz \<tau>' \<sigma>) NV"
  by (rule sum_vsz_agree)

end

context wf_csig
begin

text \<open>
  Copying the arguments of an imitation, given copies of each argument. An argument whose
  type ends in an unbound type variable is deferred if the arity bound is positive; otherwise
  the instance of its result type is not a function type, and it is copied by \<^const>\<open>mc\<close>.
\<close>

lemma pcopyargs_complete:
  assumes MC: "\<And>W0 \<sigma>0 \<rho>0 env0 dps0 u0 X0 s0. (X0, s0) \<in> set (zip As ss) \<Longrightarrow>
      tsubst \<rho>0 X0 = tsubst \<rho> X0 \<Longrightarrow> map (tsubst \<rho>0) Ts = map (tsubst \<rho>) Ts \<Longrightarrow>
      pmc_pre alg ar k A W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s0 \<Longrightarrow>
      pmc_post alg ar A cfg vname W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s0"
    and cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> (tyenv env) A" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar (tyenv env) A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar (tyenv env) A T"
    and ua: "\<forall>t\<in>set uargs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar (tyenv env) A T)"
    and uaty: "list_all2 (typed env W (map snd rb)) uargs As" and twAs: "\<forall>X\<in>set As. tyw ar (tyenv env) A X"
    and ss: "list_all2 (\<lambda>s X. (ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> X) \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss As"
    and eq: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst \<sigma> (tr (inst \<rho> t))) ss uargs"
  shows "\<exists>uargs' env' dps' W' \<sigma>' \<rho>' NV. ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs' env' dps') \<and>
    psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps'
      (\<Union> (vps ` inst \<rho> ` set uargs) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps) NV \<and>
    list_all2 (typed env' W' (rev Ts)) uargs' As \<and>
    (\<forall>u'\<in>set uargs'. swf_cp ar (length Ts) u' \<and> (\<forall>X\<in>tys u'. tyw ar (tyenv env') A X) \<and>
      below (maxidx env') u' \<and> vps (inst \<rho>' u') \<subseteq> NV) \<and>
    list_all2 (\<lambda>u' s. mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs' ss \<and>
    (\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) \<le> sum_list (map2 (\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))) ss As)"
  using MC ua uaty twAs ss eq
proof (induction uargs arbitrary: As ss)
  case Nil
  then have "As = []" "ss = []" by (simp_all add: list_all2_Nil list_all2_Nil2)
  with Nil show ?case
    using psext_refl[OF pc, of "\<Union> (vps ` inst \<rho> ` set []) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps"]
    by (intro exI[of _ "[]"] exI[of _ env] exI[of _ dps] exI[of _ W] exI[of _ \<sigma>] exI[of _ \<rho>] exI[of _ "{}"])
      (auto intro: ev.single)
next
  case (Cons uarg uargs)
  let ?\<theta> = "tyenv env"
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  from Cons.prems(3) obtain A0 As' where As: "As = A0 # As'" "typed env W (map snd rb) uarg A0"
    "list_all2 (typed env W (map snd rb)) uargs As'"
    by (auto simp: list_all2_Cons1)
  from Cons.prems(5) As obtain s0 ss' where ss: "ss = s0 # ss'"
    "(ibctx \<rho> Ts, \<tau>') \<turnstile> s0 : trty (tsubst \<rho> A0)" "no_redex s0" "no_loose_bound s0 (length Ts)"
    "list_all2 (\<lambda>s X. (ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> X) \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss' As'"
    by (auto simp: list_all2_Cons2)
  from Cons.prems(6) ss(1) have "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs
      \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))) (s0 # ss') (uarg # uargs)" by (simp only:)
  then have eq0: "Abs_m (length Ts) s0 \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst \<sigma> (tr (inst \<rho> uarg))"
    and eqs: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      mk_subst \<sigma> (tr (inst \<rho> t))) ss' uargs"
    unfolding list_all2_Cons by blast+
  have twA0: "tyw ar ?\<theta> A A0" and twAs': "\<forall>X\<in>set As'. tyw ar ?\<theta> A X" using Cons.prems(4) As(1) by auto
  have MC': "pmc_post alg ar A cfg vname W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s1"
    if "(X0, s1) \<in> set (zip As' ss')" "tsubst \<rho>0 X0 = tsubst \<rho> X0" "map (tsubst \<rho>0) Ts = map (tsubst \<rho>) Ts"
      "pmc_pre alg ar k A W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s1"
    for W0 \<sigma>0 \<rho>0 env0 dps0 u0 X0 s1
    using Cons.prems(1)[OF _ that(2,3,4)] that(1) As ss by simp
  have ua': "\<forall>t\<in>set uargs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    using Cons.prems(2) by simp
  from Cons.IH[OF MC' ua' As(3) twAs' ss(5) eqs] obtain uargs1 env1 dps1 W1 \<sigma>1 \<rho>1 NV1 where
    ev1: "ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs1 env1 dps1)"
    and s1: "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>1 env1 dps1
      (\<Union> (vps ` inst \<rho> ` set uargs) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps) NV1"
    and ty1: "list_all2 (typed env1 W1 (rev Ts)) uargs1 As'"
    and w1: "\<forall>u'\<in>set uargs1. swf_cp ar (length Ts) u' \<and> (\<forall>X\<in>tys u'. tyw ar (tyenv env1) A X) \<and>
      below (maxidx env1) u' \<and> vps (inst \<rho>1 u') \<subseteq> NV1"
    and e1: "list_all2 (\<lambda>u' s. mk_subst \<sigma>1 (tr (inst \<rho>1 u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs1 ss'"
    and sz1: "(\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>1 y) \<le> sum_list (map2 (\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))) ss' As')"
    by blast
  define D where "D = \<Union> (vps ` inst \<rho> ` set (uarg # uargs)) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps"
  have s1': "psext alg ar A W \<tau>' \<sigma> \<rho> env W1 \<sigma>1 \<rho>1 env1 dps1 D NV1" by (rule psext_mono[OF s1]) (auto simp: D_def)
  note sd1 = psextD[OF s1']
  note pi1 = pinvD[OF pcinvD(1)[OF sd1(1)]]
  let ?\<theta>1 = "tyenv env1"
  have ac1: "tacyc ?\<theta>1" "tcons_env ?\<theta>1" using tinv_tacyc[OF pi1(2)] tinv_tcons_env[OF pi1(2)] by simp_all
  have sol1: "tsol ?\<theta>1 \<rho>1" using pcinvD(2)[OF sd1(1)] by (simp add: gsol_def)
  have ext1: "textends ?\<theta> ?\<theta>1" using sd1(6) by (simp add: pextends_def)
  have tw1: "tyw ar ?\<theta>1 A X" if "tyw ar ?\<theta> A X" for X by (rule tyw_textends[OF ac1(1) ext1 that])
  have tcU1: "tcons ?\<theta>1 X" if "tyw ar ?\<theta>1 A X" for X by (rule tyw_tcons[OF pi1(2) that])
  have kk1: "kokA k \<rho>1 ?\<theta>1 A" by (rule psext_kokA[OF s1' pc kk])
  have wu: "swf_tm ar rb uarg" "below (maxidx env) uarg" "\<forall>T\<in>tys uarg. tyw ar ?\<theta> A T" using Cons.prems(2) by auto
  have bu1: "below (maxidx env1) uarg" using below_mono[OF wu(2) sd1(5)] .
  have twu1: "\<forall>T\<in>tys uarg. tyw ar ?\<theta>1 A T" using wu(3) tw1 by blast
  have twb1: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta>1 A T" using twb tw1 by blast
  have tyu1: "typed env1 W1 (map snd rb) uarg A0" by (rule typed_psext[OF ac1(1) sd1(6) pi(6) pi1(6) sd1(2) wu(2) As(2)])
  obtain u1 u2 where cn: "ok (head_norm env1 uarg) u1" "ok (eta_norm env1 rb u1) u2"
    "swf_tm ar rb u2" "\<forall>U\<in>tys u2. tyw ar ?\<theta>1 A U" "hnf u2"
    "hlong (tctx env1 W1) (map (tnorm ?\<theta>1) (map snd rb)) (tnormt ?\<theta>1 u2) (tnorm ?\<theta>1 A0)"
    "below (maxidx env1) u2" "vps (inst \<rho>1 u2) \<subseteq> reach (instE \<rho>1 env1) (vps (inst \<rho>1 uarg))"
    "mk_subst \<sigma>1 (tr (inst \<rho>1 u2)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr (inst \<rho>1 uarg))"
    by (rule pcopy_norm[OF sd1(1) sb twb1 wu(1) twu1 tyu1 bu1])
  have tyu2: "typed env1 W1 (map snd rb) u2 A0" using hlong_typed[OF cn(6)] by (simp add: typed_def tnorm_idem[OF ac1(1)])
  have tg1: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env1) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta>1 A T)"
    using tg below_mono[OF _ sd1(5)] tw1 by blast
  have tgty1: "list_all2 (typed env1 W1 (map snd rb)) targs Ts"
    by (rule list_all2_typed_psext[OF ac1(1) sd1(6) pi(6) pi1(6) sd1(2) _ tgty]) (use tg in blast)
  have twTs1: "\<forall>T\<in>set Ts. tyw ar ?\<theta>1 A T" using twTs tw1 by blast
  have twA01: "tyw ar ?\<theta>1 A A0" by (rule tw1[OF twA0])
  \<comment> \<open>The instances under \<open>\<rho>1\<close> agree with those under \<open>\<rho>\<close>\<close>
  have iA0: "tsubst \<rho>1 A0 = tsubst \<rho> A0" by (rule tyw_tagree[OF pi(2) twA0 sd1(4)])
  have iTs: "map (tsubst \<rho>1) Ts = map (tsubst \<rho>) Ts" using tyw_tagree[OF pi(2) _ sd1(4)] twTs by simp
  have itg: "inst \<rho>1 t = inst \<rho> t" if "t \<in> set targs" for t using inst_tyw_tagree[OF pi(2) _ sd1(4)] tg that by blast
  have iu: "inst \<rho>1 uarg = inst \<rho> uarg" using inst_tyw_tagree[OF pi(2) wu(3) sd1(4)] .
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
  have ta: "map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>1 t))) targs = ?st"
    using itg tg mk_subst_agree[OF _ sd1(3)] by simp
  have "mk_subst \<sigma>1 (tr (inst \<rho>1 uarg)) = mk_subst \<sigma> (tr (inst \<rho> uarg))"
    using iu mk_subst_agree[OF _ sd1(3), of "inst \<rho> uarg"] wu(2) by simp
  with cn(9) have e12: "mk_subst \<sigma>1 (tr (inst \<rho>1 u2)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> uarg))" by simp
  have eq1: "Abs_m (length Ts) s0 \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma>1 (tr (inst \<rho>1 t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr (inst \<rho>1 u2))"
    unfolding ta by (rule equiv_trans[OF eq0 equiv_sym[OF e12]])
  have tys1: "(ibctx \<rho>1 Ts, \<tau>') \<turnstile> s0 : trty (tsubst \<rho>1 A0)" unfolding iTs iA0 by (rule ss(2))
  \<comment> \<open>The types computed by \<open>copycons\<close>\<close>
  have nt2: "has_type (tctx env1 W1) (map (tnorm ?\<theta>1) (map snd rb)) (tnormt ?\<theta>1 u2) (tnorm ?\<theta>1 A0)"
    by (rule hlong_typed[OF cn(6)])
  have tcu2: "\<forall>U\<in>set (map snd rb) \<union> tys u2. tcons ?\<theta>1 U" using twb1 cn(4) tcU1 by auto
  from env_fastype_pterm[OF ac1 tcu2 nt2] obtain A' where
    fA: "ok (fastype env1 rb u2) A'" "tnorm ?\<theta>1 A' = tnorm ?\<theta>1 A0" by (auto simp: fastype_def)
  have twA': "tyw ar ?\<theta>1 A A'" using fastype_tyw[OF fA(1) pi1(2) twb1 cn(4)] .
  have "tnorm ?\<theta>1 A' = foldr fun_type (arg_types (tnorm ?\<theta>1 A0)) (res_type (tnorm ?\<theta>1 A0))"
    using fA(2) by (simp add: arg_res_type)
  from body_type_ptnorm[OF ac1 tcU1[OF twA'] this res_type_base] obtain B where
    bB: "body_type env1 A' = return B" "tnorm ?\<theta>1 B = res_type (tnorm ?\<theta>1 A0)" "tcons ?\<theta>1 B" by blast
  have da: "ok (defer_arg env1 rb u2) (is_TVar B)" using fA(1) bB(1) by (simp add: defer_arg_def bindM_def return_def)
  from mapM_fastype_ptnorm[OF ac1 _ tgty1] twb1 tg1 tcU1 obtain Ts1 where
    mT: "mapM (fastype env1 rb) targs = return Ts1" "map (tnorm ?\<theta>1) Ts1 = map (tnorm ?\<theta>1) Ts" by blast
  have twTs1': "\<forall>T\<in>set Ts1. tyw ar ?\<theta>1 A T" by (rule mapM_fastype_tyw[OF mT(1) pi1(2) twb1]) (use tg1 in blast)
  \<comment> \<open>The copy of the argument\<close>
  have "\<exists>sq u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2 m. okW (copycons cfg vname rb targs uarg uargs1 env1 dps1) (S_MapCons uargs1 sq) \<and>
      ev cfg sq (El_C u' env2 dps2) \<and>
      pcopy_res alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 (pmc_dom \<rho>1 u2 targs dps1) Ts A0 s0 m u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2"
  proof (cases "0 < cfg_arity_bound cfg \<and> is_TVar B")
    case True
    obtain env2 newhd where g: "genvar vname env1 (foldr fun_type Ts1 A') = (env2, newhd)"
      by (cases "genvar vname env1 (foldr fun_type Ts1 A')")
    from pflex_copy[OF sd1(1) sb twb1 tg1 tgty1 twTs1 cn(3,4,7) tyu2 twA01 mT(2) twTs1' twA' fA(2) g tys1 ss(3)]
      ss(4) eq1 obtain W2 \<sigma>2 NV2 where
      cr0: "pcopy_res alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 (pmc_dom \<rho>1 u2 targs dps1) Ts A0 s0 0
        (combound newhd 0 (length Ts1)) env2 ((rb, list_comb newhd targs, u2) # dps1) W2 \<sigma>2 \<rho>1 NV2"
      by blast
    let ?x = "El_C (combound newhd 0 (length Ts1)) env2 ((rb, list_comb newhd targs, u2) # dps1)"
    have cc0: "okW (copycons cfg vname rb targs uarg uargs1 env1 dps1) (S_MapCons uargs1 (S_Single ?x))"
      using copycons_defer[OF cn(1,2) _ _ fA(1) _ g] True da mT(1) by (simp add: return_def)
    have "ev cfg (S_Single ?x) ?x" by (rule ev.single)
    with cc0 cr0 show ?thesis
      by (intro exI[of _ "S_Single ?x"] exI[of _ "combound newhd 0 (length Ts1)"] exI[of _ env2]
          exI[of _ "(rb, list_comb newhd targs, u2) # dps1"] exI[of _ W2] exI[of _ \<sigma>2] exI[of _ \<rho>1]
          exI[of _ NV2] exI[of _ 0]) simp
  next
    case False
    have "\<not> is_funT (tsubst \<rho>1 (res_type (tnorm ?\<theta>1 A0)))"
    proof (cases "0 < cfg_arity_bound cfg")
      case True
      with False have nB: "\<not> is_TVar B" by simp
      have "\<not> is_funT B"
      proof
        assume "is_funT B"
        then obtain X Y where "B = X \<rightarrow>\<^sub>T Y" by (auto simp: is_funT_fun)
        then have "is_funT (tnorm ?\<theta>1 B)" by simp
        with bB(2) res_type_base[of "tnorm ?\<theta>1 A0"] show False by simp
      qed
      from nonfun_tsubst[OF this nB] bB(2) tsubst_tnorm[OF ac1 sol1 bB(3)] show ?thesis by metis
    next
      case nb: False
      then have "k = 0" using cfg(2) by (simp add: less_integer_def nat_of_integer.rep_eq)
      have "kok k \<rho>1 ?\<theta>1 A0" by (rule kok_tyw[OF pi1(2) twA01 kk1])
      from kok_res_type[OF this] \<open>k = 0\<close> show ?thesis by (simp add: is_funT_arg_types)
    qed
    then have pre: "pmc_pre alg ar k A W1 \<tau>' \<sigma>1 \<rho>1 env1 dps1 rb targs Ts u2 A0 s0"
      unfolding pmc_pre_def using sd1(1) kk1 sb twb1 tg1 tgty1 twTs1 cn(3-7) twA01 tys1 ss(3,4) eq1 by blast
    have "(A0, s0) \<in> set (zip As ss)" using As(1) ss(1) by simp
    from Cons.prems(1)[OF this iA0 iTs pre] obtain sq u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2 where
      mc: "okW (mc cfg vname rb targs u2 env1 dps1) sq" and ev2: "ev cfg sq (El_C u' env2 dps2)"
      and cr: "pcopy_res alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 (pmc_dom \<rho>1 u2 targs dps1) Ts A0 s0
        (if is_Var (head_of (strip_abs_body u2)) then 0 else 1) u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2"
      unfolding pmc_post_def by blast
    have "okW (if 0 < cfg_arity_bound cfg then liftM (defer_arg env1 rb u2) else returnW False) False"
      using False da by auto
    from copycons_mc[OF cn(1,2) this mc, where uargs = uargs1] ev2 cr show ?thesis by blast
  qed
  then obtain sq u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2 m where
    cc: "okW (copycons cfg vname rb targs uarg uargs1 env1 dps1) (S_MapCons uargs1 sq)"
    and ev2: "ev cfg sq (El_C u' env2 dps2)"
    and cr: "pcopy_res alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 (pmc_dom \<rho>1 u2 targs dps1) Ts A0 s0 m u' env2 dps2 W2 \<sigma>2 \<rho>2 NV2"
    by blast
  from cr have s2: "psext alg ar A W1 \<tau>' \<sigma>1 \<rho>1 env1 W2 \<sigma>2 \<rho>2 env2 dps2 (pmc_dom \<rho>1 u2 targs dps1) NV2"
    and ty2: "typed env2 W2 (rev Ts) u' A0" and w2: "swf_cp ar (length Ts) u'"
    "\<forall>X\<in>tys u'. tyw ar (tyenv env2) A X" "below (maxidx env2) u'" "vps (inst \<rho>2 u') \<subseteq> NV2"
    and e2: "mk_subst \<sigma>2 (tr (inst \<rho>2 u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s0"
    and sz2: "(\<Sum>y\<in>NV2. vsz \<tau>' \<sigma>2 y) + m \<le> lsize (ibctx \<rho>1 Ts) \<tau>' s0 (trty (tsubst \<rho>1 A0))"
    unfolding pcopy_res_def by blast+
  note sd2 = psextD[OF s2]
  note pi2 = pinvD[OF pcinvD(1)[OF sd2(1)]]
  have DD: "pmc_dom \<rho>1 u2 targs dps1 \<subseteq> reach (instE \<rho> env) D \<union> NV1"
  proof -
    have "vps (inst \<rho>1 u2) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho>1 uarg) \<union> D) \<union> NV1"
      using cn(8) sd1(9)[of "vps (inst \<rho>1 uarg)"] by blast
    moreover have "vps (inst \<rho>1 uarg) \<union> D = D" using iu by (auto simp: D_def)
    moreover have "\<Union> (vps ` inst \<rho>1 ` set targs) \<subseteq> reach (instE \<rho> env) D"
      using reach_incl[of D "instE \<rho> env"] itg by (auto simp: D_def)
    ultimately show ?thesis using sd1(10) by auto
  qed
  have s12: "psext alg ar A W \<tau>' \<sigma> \<rho> env W2 \<sigma>2 \<rho>2 env2 dps2 D (NV1 \<union> NV2)"
    by (rule psext_trans[OF s1' s2 ei(6) DD])
  have ev: "ev cfg (copyargs vname rb targs env dps (uarg # uargs)) (El_D (u' # uargs1) env2 dps2)"
    using ev.maps[OF ev1 cc ev.map_cons[OF ev2]] by simp
  have b1: "\<forall>t\<in>set uargs1. below (maxidx env1) t" using w1 by blast
  have ac2: "tacyc (tyenv env2)" by (rule tinv_tacyc[OF pi2(2)])
  have ty: "list_all2 (typed env2 W2 (rev Ts)) (u' # uargs1) As"
    using ty2 list_all2_typed_psext[OF ac2 sd2(6) pi1(6) pi2(6) sd2(2) b1 ty1] As(1) by simp
  have iu1: "inst \<rho>2 a = inst \<rho>1 a" if "a \<in> set uargs1" for a
    using inst_tyw_tagree[OF pi1(2) _ sd2(4)] w1 that by blast
  have ext2: "textends ?\<theta>1 (tyenv env2)" using sd2(6) by (simp add: pextends_def)
  have w: "\<forall>u''\<in>set (u' # uargs1). swf_cp ar (length Ts) u'' \<and> (\<forall>X\<in>tys u''. tyw ar (tyenv env2) A X) \<and>
      below (maxidx env2) u'' \<and> vps (inst \<rho>2 u'') \<subseteq> NV1 \<union> NV2"
    using w1 w2 below_mono[OF _ sd2(5)] iu1 tyw_textends[OF ac2 ext2] by auto
  have "list_all2 (\<lambda>u' s. mk_subst \<sigma>2 (tr (inst \<rho>2 u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs1 ss'"
    using e1 b1 iu1 by (induction rule: list_all2_induct) (auto simp: mk_subst_agree[OF _ sd2(3)])
  with e2 have e: "list_all2 (\<lambda>u' s. mk_subst \<sigma>2 (tr (inst \<rho>2 u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) (u' # uargs1) ss" using ss(1) by simp
  have "(\<Sum>y\<in>NV1 \<union> NV2. vsz \<tau>' \<sigma>2 y) \<le> (\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>2 y) + (\<Sum>y\<in>NV2. vsz \<tau>' \<sigma>2 y)"
    by (rule sum_Un_le[OF sd1(7) sd2(7)])
  also have "(\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>2 y) = (\<Sum>y\<in>NV1. vsz \<tau>' \<sigma>1 y)"
    using sum_vsz_agree[OF sd2(3)] sd1(8) by blast
  finally have "(\<Sum>y\<in>NV1 \<union> NV2. vsz \<tau>' \<sigma>2 y) \<le> sum_list (map2 (\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))) ss As)"
    using sz1 sz2 ss(1) As(1) iTs iA0 by simp
  with ev s12[unfolded D_def] ty w e show ?case
    by (intro exI[of _ "u' # uargs1"] exI[of _ env2] exI[of _ dps2] exI[of _ W2] exI[of _ \<sigma>2] exI[of _ \<rho>2]
        exI[of _ "NV1 \<union> NV2"] conjI)
qed

end


context csig
begin

subsection \<open>Copies: imitation\<close>

lemma tnorm_foldr_normal:
  "tnorm \<theta> (foldr fun_type As B) = foldr fun_type As B \<Longrightarrow> map (tnorm \<theta>) As = As"
  by (induction As) auto

end

context wf_csig
begin

lemma pmc_imit:
  assumes IH: "\<And>W \<sigma> \<rho> env dps rb targs Ts u U s. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U)) < N \<Longrightarrow>
      pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<Longrightarrow>
      pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and pre: "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and lsz: "lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U)) = N"
    and hA: "\<not> is_Abs (head_of u)" and hV: "\<not> is_Var (head_of u)"
    and sc: "s = dB.Var c \<degree>\<degree> ss"
  shows "pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof -
  let ?\<theta> = "tyenv env" and ?V = "tctx env W" and ?Bs = "map (tnorm (tyenv env)) (map snd rb)"
  from pre have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and kk: "kokA k \<rho> ?\<theta> A" and sb: "sbinders ar rb"
    and twb: "\<forall>T\<in>snd ` set rb. tyw ar ?\<theta> A T"
    and tg: "\<forall>t\<in>set targs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    and tgty: "list_all2 (typed env W (map snd rb)) targs Ts" and twTs: "\<forall>T\<in>set Ts. tyw ar ?\<theta> A T"
    and wu: "swf_tm ar rb u" and twu: "\<forall>T\<in>tys u. tyw ar ?\<theta> A T"
    and bu: "below (maxidx env) u" and hl: "hlong ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and twU: "tyw ar ?\<theta> A U" and fU: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U)))"
    and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
    and nls: "no_loose_bound s (length Ts)"
    and eqs: "Abs_m (length Ts) s \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
    unfolding pmc_pre_def by blast+
  note pc0 = pcinvD[OF pc]
  note pi = pinvD[OF pc0(1)]
  note ei = penv_invD[OF pi(1)]
  note \<sigma> = solutionD[OF pc0(3)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pc0(2) by (simp add: gsol_def)
  have tcU: "tcons ?\<theta> X" if "tyw ar ?\<theta> A X" for X by (rule tyw_tcons[OF pi(2) that])
  obtain T0 base Ts' projs sq where ty0: "fastype env rb (head_of u) = return T0" "body_type env T0 = return base"
    "map (tnorm ?\<theta>) Ts' = map (tnorm ?\<theta>) Ts" "\<forall>T\<in>set Ts'. tyw ar ?\<theta> A T"
    "tyw ar ?\<theta> A T0" "tyw ar ?\<theta> A base"
    "has_type ?V ?Bs (tnormt ?\<theta> (head_of u)) (tnorm ?\<theta> T0)"
    "tnorm ?\<theta> base = res_type (tnorm ?\<theta> U)"
    "\<forall>j<length targs. (Bound (integer_of_nat j), Ts' ! (length targs - Suc j), targs ! (length targs - Suc j))
      \<in> set projs"
    "okW (mc cfg vname rb targs u env dps) sq"
    and imit: "\<And>x. ev cfg (case head_of u of
        Const _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | Free _ _ \<Rightarrow> S_MapJoin (head_of u) (copyargs vname rb targs env dps (snd (strip_comb u)))
      | _ \<Rightarrow> S_Empty) x \<Longrightarrow> ev cfg sq x"
    by (rule pmc_rigid_seq[OF cfg(1) pre hA hV]) blast
  have nA: "\<not> is_Abs u" by (rule head_of_nonAbs[OF hA])
  then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
  from hlong_nonAbs[OF hl this] have tyu: "has_type ?V ?Bs (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
    and nfU: "\<not> is_funT (tnorm ?\<theta> U)" by auto
  let ?\<rho>U = "tsubst \<rho> U"
  have iU: "tsubst \<rho> (tnorm ?\<theta> U) = ?\<rho>U" by (rule tsubst_tnorm[OF ac sol tcU[OF twU]])
  have nf\<rho>U: "\<not> is_funT ?\<rho>U" using fU arg_res_type_base[OF nfU] iU by simp
  have lTs: "length Ts = length targs" using list_all2_lengthD[OF tgty] by simp
  define uargs where "uargs = snd (strip_comb u)"
  have u_eq: "u = list_comb (head_of u) uargs" unfolding uargs_def by (rule head_of_list_comb)
  from res_type_head(2)[OF tyu nfU ty0(7)[folded head_of_tnormt]] obtain As where
    T0: "tnorm ?\<theta> T0 = foldr fun_type As (tnorm ?\<theta> U)"
    and tyas: "list_all2 (has_type ?V ?Bs) (snd (strip_comb (tnormt ?\<theta> u))) As"
    by blast
  have nAs: "map (tnorm ?\<theta>) As = As"
  proof -
    have "tnorm ?\<theta> (tnorm ?\<theta> T0) = tnorm ?\<theta> T0" by (rule tnorm_idem[OF ac(1)])
    with T0 have "tnorm ?\<theta> (foldr fun_type As (tnorm ?\<theta> U)) = foldr fun_type As (tnorm ?\<theta> U)" by simp
    then show ?thesis by (rule tnorm_foldr_normal)
  qed
  have ha: "list_all2 (has_type ?V ?Bs) (map (tnormt ?\<theta>) uargs) As"
    using tyas by (simp add: strip_comb_tnormt uargs_def)
  have lAs: "length As = length uargs" using list_all2_lengthD[OF ha] by simp
  have uaty: "list_all2 (typed env W (map snd rb)) uargs As"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length uargs = length As" using lAs by simp
    fix i assume i: "i < length uargs"
    have "has_type ?V ?Bs (tnormt ?\<theta> (uargs ! i)) (As ! i)" using ha i by (simp add: list_all2_conv_all_nth)
    moreover have "tnorm ?\<theta> (As ! i) = As ! i" using arg_cong[OF nAs, of "\<lambda>xs. xs ! i"] i lAs by simp
    ultimately show "typed env W (map snd rb) (uargs ! i) (As ! i)" by (simp add: typed_def)
  qed
  have twAs: "\<forall>X\<in>set As. tyw ar ?\<theta> A X" using tyw_tnorm[OF pi(2) ty0(5)] T0 by (simp add: tyw_foldr_fun)
  have ua: "\<forall>t\<in>set uargs. swf_tm ar rb t \<and> below (maxidx env) t \<and> (\<forall>T\<in>tys t. tyw ar ?\<theta> A T)"
    using wu bu twu u_eq by (metis UnCI UN_I swf_tm_list_comb below_list_comb tys_list_comb)
  \<comment> \<open>The target\<close>
  from tys sc obtain Ws where tyh': "(ibctx \<rho> Ts, \<tau>') \<turnstile> dB.Var c : Ws \<Rrightarrow> trty ?\<rho>U"
    and tyss: "(ibctx \<rho> Ts, \<tau>') \<tturnstile> ss : Ws"
    by (auto elim: list_app_typeE)
  have atc: "is_atom (dB.Var c)" by (simp add: is_atom_def)
  have nrss: "\<forall>w\<in>set ss. no_redex w" using nrs sc no_redex_atom_apps[OF atc] by simp
  have nlss: "\<forall>w\<in>set ss. no_loose_bound w (length Ts)" using nls sc by (simp add: no_loose_bound_list_app)
  have lWs: "length Ws = length ss" by (rule typings_length[OF tyss])
  have lsz_s: "lsize (ibctx \<rho> Ts) \<tau>' s (trty ?\<rho>U) =
      Suc (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i)) + (tsize (trty ?\<rho>U) - 1)"
    using lsize_atom_apps[OF atc tyh' tyss nrss] sc by simp
  let ?H = "inst \<rho> (head_of u)"
  have hd: "(\<exists>a T. head_of u = Const a T) \<or> (\<exists>a T. head_of u = Free a T) \<or> (\<exists>i. head_of u = Bound i)"
    using hA hV head_of_not_App[of u] by (cases "head_of u") auto
  have trh: "mk_subst \<sigma> (tr ?H) = tr ?H" and ath: "is_atom (tr ?H)"
    using hd rigid_substD[OF \<sigma>(3)] by auto
  have equ: "mk_subst \<sigma> (tr (inst \<rho> u)) = tr ?H \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) uargs"
    using arg_cong[OF u_eq, of "\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))"] trh
    by (simp add: inst_list_comb tr_list_comb comp_def)
  let ?st = "map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) targs"
  have e2: "Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss"
    using Abs_m_apps_closed_head[of "dB.Var c" ?st "length Ts" ss] sc lTs by simp
  have "dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      tr ?H \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) uargs"
    using equiv_trans[OF equiv_sym[OF e2] eqs] equ by simp
  from atom_apps_equiv[OF atc ath this] have hh: "dB.Var c = tr ?H"
    and la2: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. Abs_m (length Ts) a \<degree>\<degree> ?st) ss)
      (map (\<lambda>t. mk_subst \<sigma> (tr (inst \<rho> t))) uargs)"
    by auto
  from hd hh obtain a Tc where hu': "head_of u = Const a Tc \<or> head_of u = Free a Tc" by auto
  have tTc: "tnorm ?\<theta> Tc = tnorm ?\<theta> T0"
    using ty0(7) hu' by (auto elim: has_type.cases)
  have cTc: "const_typ_ok a (tnorm ?\<theta> Tc)" if "head_of u = Const a Tc"
    using ty0(7) that by (auto elim: has_type.cases)
  have twTc: "tyw ar ?\<theta> A Tc" using twu tys_head_of[of u] hu' by auto
  have iTc: "tsubst \<rho> Tc = foldr fun_type (map (tsubst \<rho>) As) ?\<rho>U"
  proof -
    have "tsubst \<rho> Tc = tsubst \<rho> (tnorm ?\<theta> Tc)" by (rule tsubst_tnorm[OF ac sol tcU[OF twTc], symmetric])
    also have "\<dots> = foldr fun_type (map (tsubst \<rho>) As) (tsubst \<rho> (tnorm ?\<theta> U))"
      using tTc T0 by (simp add: tsubst_foldr_fun)
    finally show ?thesis using iU by simp
  qed
  have tyhc: "(ibctx \<rho> Ts, \<tau>') \<turnstile> tr ?H : trty (tsubst \<rho> Tc)"
    by (rule solution_rigid_type[OF pc0(3)]) (use hu' in auto)
  from tyhc[folded hh] tyh' have "Ws \<Rrightarrow> trty ?\<rho>U = map trty (map (tsubst \<rho>) As) \<Rrightarrow> trty ?\<rho>U"
    by (auto simp: iTc trty_foldr)
  with arrows_base_inj[OF _ nf\<rho>U nf\<rho>U] have Ws: "Ws = map trty (map (tsubst \<rho>) As)" by blast
  have lss: "length ss = length uargs" using lWs Ws lAs by simp
  have MC: "pmc_post alg ar A cfg vname W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s0"
    if "(X0, s0) \<in> set (zip As ss)" "tsubst \<rho>0 X0 = tsubst \<rho> X0" "map (tsubst \<rho>0) Ts = map (tsubst \<rho>) Ts"
      "pmc_pre alg ar k A W0 \<tau>' \<sigma>0 \<rho>0 env0 dps0 rb targs Ts u0 X0 s0"
    for W0 \<sigma>0 \<rho>0 env0 dps0 u0 X0 s0
  proof (rule IH[OF _ that(4)])
    from that(1) obtain i where i: "i < length ss" "X0 = As ! i" "s0 = ss ! i"
      using lAs lss by (auto simp: in_set_zip)
    have "lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i) \<le> (\<Sum>k<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! k) (Ws ! k))"
      by (rule member_le_sum) (use i in auto)
    moreover have "lsize (ibctx \<rho>0 Ts) \<tau>' s0 (trty (tsubst \<rho>0 X0)) = lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i)"
    proof -
      have "tsubst \<rho>0 (As ! i) = tsubst \<rho> (As ! i)" using that(2) i(2) by simp
      then show ?thesis using i Ws lAs lss by (simp only: that(3)) simp
    qed
    ultimately show "lsize (ibctx \<rho>0 Ts) \<tau>' s0 (trty (tsubst \<rho>0 X0)) < N"
      using lsz_s lsz by simp
  qed
  have ssc: "list_all2 (\<lambda>s X. (ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> X) \<and> no_redex s \<and> no_loose_bound s (length Ts)) ss As"
    unfolding list_all2_conv_all_nth using lss lAs typings_nth[OF tyss] Ws nrss nlss by auto
  have eqa: "list_all2 (\<lambda>s t. Abs_m (length Ts) s \<degree>\<degree> ?st \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> t))) ss uargs"
    using la2 by (simp add: list_all2_map1 list_all2_map2)
  from pcopyargs_complete[OF MC cfg pc kk sb twb tg tgty twTs ua uaty twAs ssc eqa] obtain uargs' env' dps' W' \<sigma>' \<rho>' NV where
    evc: "ev cfg (copyargs vname rb targs env dps uargs) (El_D uargs' env' dps')"
    and sxc: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps'
      (\<Union> (vps ` inst \<rho> ` set uargs) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps) NV"
    and tyc: "list_all2 (typed env' W' (rev Ts)) uargs' As"
    and wc: "\<forall>u'\<in>set uargs'. swf_cp ar (length Ts) u' \<and> (\<forall>X\<in>tys u'. tyw ar (tyenv env') A X) \<and>
      below (maxidx env') u' \<and> vps (inst \<rho>' u') \<subseteq> NV"
    and ec: "list_all2 (\<lambda>u' s. mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s) uargs' ss"
    and szc: "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) \<le> sum_list (map2 (\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))) ss As)"
    by blast
  have "ev cfg (S_MapJoin (head_of u) (copyargs vname rb targs env dps uargs))
      (El_C (list_comb (head_of u) uargs') env' dps')" by (rule ev.map_join[OF evc])
  then have evj: "ev cfg sq (El_C (list_comb (head_of u) uargs') env' dps')"
    using hu' imit by (auto simp: uargs_def)
  define D where "D = pmc_dom \<rho> u targs dps"
  have sx: "psext alg ar A W \<tau>' \<sigma> \<rho> env W' \<sigma>' \<rho>' env' dps' D NV"
  proof (rule psext_mono[OF sxc])
    have "vps (inst \<rho> u) = vps ?H \<union> \<Union> (vps ` inst \<rho> ` set uargs)"
      by (subst u_eq) (simp add: inst_list_comb vps_list_comb)
    then show "\<Union> (vps ` inst \<rho> ` set uargs) \<union> \<Union> (vps ` inst \<rho> ` set targs) \<union> ivps \<rho> dps \<subseteq> D"
      by (auto simp: D_def)
  qed
  note sd = psextD[OF sx]
  note pi' = pinvD[OF pcinvD(1)[OF sd(1)]]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have ext': "textends ?\<theta> (tyenv env')" using sd(6) by (simp add: pextends_def)
  define u' where "u' = list_comb (head_of u) uargs'"
  have cr: "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s 1 u' env' dps' W' \<sigma>' \<rho>' NV"
    unfolding pcopy_res_def
  proof (intro conjI sx)
    have "tnorm (tyenv env') Tc = tnorm (tyenv env') (foldr fun_type As U)"
    proof -
      have "tnorm (tyenv env') Tc = tnorm (tyenv env') (tnorm ?\<theta> Tc)" by (simp add: tnorm_textends[OF ac' ext'])
      also have "\<dots> = tnorm (tyenv env') (foldr fun_type As (tnorm ?\<theta> U))" using tTc T0 by simp
      finally show ?thesis by (simp add: tnorm_foldr_fun tnorm_textends[OF ac' ext'])
    qed
    moreover have "const_typ_ok a (tnorm (tyenv env') Tc)" if "head_of u = Const a Tc"
      using const_typ_ok_tnorm[OF cTc[OF that], of "tyenv env'"] by (simp add: tnorm_textends[OF ac' ext'])
    ultimately have "typed env' W' (rev Ts) (head_of u) (foldr fun_type As U)"
      using hu' by (auto simp: typed_def intro: has_type.Const has_type.Free)
    from typed_list_comb[OF this tyc] show "typed env' W' (rev Ts) u' U" by (simp add: u'_def)
    have "swf_tm ar rb (head_of u)" using wu u_eq by (metis swf_tm_list_comb)
    then have "swf_cp ar (length Ts) (head_of u)" using hu' by (auto simp: swf_tm_def swf_cp_def)
    then show "swf_cp ar (length Ts) u'" using wc by (simp add: u'_def swf_cp_list_comb)
    show "\<forall>X\<in>tys u'. tyw ar (tyenv env') A X"
      using wc tyw_textends[OF ac' ext' twTc] hu' by (auto simp: u'_def tys_list_comb)
    have "below (maxidx env') (head_of u)" using hu' by (auto simp: below_def)
    then show "below (maxidx env') u'" using wc by (simp add: u'_def below_list_comb)
    show "vps (inst \<rho>' u') \<subseteq> NV" using wc hu' by (auto simp: u'_def inst_list_comb vps_list_comb)
    have iH: "inst \<rho>' (head_of u) = ?H"
      using inst_tyw_tagree[OF pi(2) _ sd(4), of "head_of u"] twTc hu' by auto
    have rs': "rigid_subst \<sigma>'" using solutionD(3)[OF pcinvD(3)[OF sd(1)]] .
    have trh': "mk_subst \<sigma>' (tr ?H) = tr ?H" using hu' rigid_substD[OF rs'] by auto
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma>' (tr (inst \<rho>' a))) uargs') ss"
      using ec by (simp add: list_all2_map1)
    from equiv_list_app[OF equiv_refl this]
    show "mk_subst \<sigma>' (tr (inst \<rho>' u')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
      using trh' hh sc iH by (simp add: u'_def inst_list_comb tr_list_comb comp_def)
    have "sum_list (map2 (\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))) ss As) =
        (\<Sum>i<length ss. lsize (ibctx \<rho> Ts) \<tau>' (ss ! i) (Ws ! i))"
      using sum_list_map2_nth[of ss As "\<lambda>s X. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> X))"] lss lAs Ws by simp
    with szc show "(\<Sum>y\<in>NV. vsz \<tau>' \<sigma>' y) + 1 \<le> lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))"
      using lsz_s by simp
  qed
  have "\<not> is_Var (head_of (strip_abs_body u))" using hV nA by (simp add: strip_abs_body_nonAbs)
  with cr have "pcopy_res alg ar A W \<tau>' \<sigma> \<rho> env D Ts U s (if is_Var (head_of (strip_abs_body u)) then 0 else 1)
      u' env' dps' W' \<sigma>' \<rho>' NV" by simp
  then show ?thesis unfolding pmc_post_def D_def using ty0(10) evj[folded u'_def] by blast
qed

end

context wf_csig
begin

subsection \<open>Completeness of copying\<close>

lemma pmc_complete_step:
  assumes IH: "\<And>W \<sigma> \<rho> env dps rb targs Ts u U s. lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U)) < N \<Longrightarrow>
      pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<Longrightarrow>
      pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
    and cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
  shows "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<Longrightarrow>
    lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U)) = N \<Longrightarrow>
    pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof (induction "size u" arbitrary: rb targs Ts u U s rule: less_induct)
  case less
  show ?case
  proof (cases "is_Abs (head_of u)")
    case True
    then obtain a T body where h: "head_of u = Abs a T body" by (cases "head_of u") auto
    show ?thesis by (rule pmc_abs[OF _ less.prems h]) (rule less.hyps; assumption)
  next
    case nA: False
    show ?thesis
    proof (cases "is_Var (head_of u)")
      case True
      then obtain w Wt where "head_of u = Var w Wt" by (cases "head_of u") auto
      then show ?thesis by (rule pmc_var[OF less.prems(1)])
    next
      case nV: False
      let ?\<theta> = "tyenv env"
      from less.prems(1) have pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
        and hl: "hlong (tctx env W) (map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> u) (tnorm ?\<theta> U)"
        and twU: "tyw ar ?\<theta> A U" and fU: "\<not> is_funT (tsubst \<rho> (res_type (tnorm ?\<theta> U)))"
        and tys: "(ibctx \<rho> Ts, \<tau>') \<turnstile> s : trty (tsubst \<rho> U)" and nrs: "no_redex s"
        unfolding pmc_pre_def by blast+
      note pi = pinvD[OF pcinvD(1)[OF pc]]
      have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
      have sol: "tsol ?\<theta> \<rho>" using pcinvD(2)[OF pc] by (simp add: gsol_def)
      have "\<not> is_Abs u" by (rule head_of_nonAbs[OF nA])
      then have "\<not> is_Abs (tnormt ?\<theta> u)" by (cases u) auto
      from hlong_nonAbs[OF hl this] have nfU: "\<not> is_funT (tnorm ?\<theta> U)" by auto
      have "tsubst \<rho> (tnorm ?\<theta> U) = tsubst \<rho> U" by (rule tsubst_tnorm[OF ac sol tyw_tcons[OF pi(2) twU]])
      with fU arg_res_type_base[OF nfU] have nf: "\<not> is_funT (tsubst \<rho> U)" by simp
      have sA: "\<not> Unif_Occurs.is_Abs s"
      proof
        assume "Unif_Occurs.is_Abs s"
        then obtain s1 where "s = dB.Abs s1" by (cases s) auto
        with tys have "\<exists>X Y. trty (tsubst \<rho> U) = X \<Rightarrow> Y" by auto
        with trty_base[OF nf] show False by auto
      qed
      obtain h ss where h: "is_atom h" "s = h \<degree>\<degree> ss" by (rule no_redex_atom_head[OF nrs sA])
      from h(1) show ?thesis
        unfolding is_atom_def
      proof (elim disjE exE)
        fix j assume "h = BVar j"
        with h(2) show ?thesis by (intro pmc_proj[OF cfg less.prems(1) nA nV]) simp
      next
        fix c assume "h = dB.Var c"
        with h(2) show ?thesis by (intro pmc_imit[OF IH cfg less.prems nA nV]) simp_all
      qed
    qed
  qed
qed

theorem pmc_complete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
  shows "pmc_pre alg ar k A W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s \<Longrightarrow>
    pmc_post alg ar A cfg vname W \<tau>' \<sigma> \<rho> env dps rb targs Ts u U s"
proof (induction "lsize (ibctx \<rho> Ts) \<tau>' s (trty (tsubst \<rho> U))" arbitrary: W \<sigma> \<rho> env dps rb targs Ts u U s
    rule: less_induct)
  case less
  show ?case by (rule pmc_complete_step[OF less.hyps cfg less.prems refl])
qed

end

end
