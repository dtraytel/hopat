section \<open>Problems with Type Variables: Typing\<close>

theory Unify_Poly_Typing
  imports Unify_Poly_Pull Unify_Match_Complete "Pure_Pattern_Correctness.Poly_Typing"
begin

text \<open>
  The completeness of the search for problems with type variables is relative to a solution
  \<open>(\<rho>, \<sigma>)\<close>: a ground well-sorted type instantiation \<open>\<rho>\<close> that solves the type environment, and a
  solution \<open>\<sigma>\<close> of the ground instance of the problem under \<open>\<rho>\<close>. The invariant has two views of a
  state of the search:
  \<^item> the terms are typed modulo the type environment \<open>\<theta>\<close> (\<^const>\<open>typed\<close>): their types,
    normalized by \<open>\<theta>\<close>, are those of a simply typed term in which the unbound type variables are
    base types. The type computations of \<open>unify.ML\<close> follow this typing.
  \<^item> the ground instance under \<open>\<rho>\<close> satisfies the invariant \<^const>\<open>cinv\<close> of the monomorphic case,
    for the solution \<open>\<sigma>\<close>. The semantic arguments of the monomorphic case apply to it.
\<close>


subsection \<open>Types of pairs\<close>

context csig
begin

definition dtys :: "dpair \<Rightarrow> ptyp set" where
  "dtys dp = (case dp of (rb, t, u) \<Rightarrow> snd ` set rb \<union> tys t \<union> tys u)"

definition ptyped :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "ptyped env W dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<exists>T. typed env W (map snd rb) t T \<and> typed env W (map snd rb) u T)"

lemma dtys_simp[simp]: "dtys (rb, t, u) = snd ` set rb \<union> tys t \<union> tys u"
  by (simp add: dtys_def)

lemma ptyped_simp[simp]:
  "ptyped env W (rb, t, u) \<longleftrightarrow> (\<exists>T. typed env W (map snd rb) t T \<and> typed env W (map snd rb) u T)"
  by (simp add: ptyped_def)

lemma twft_tys: "twft ar t \<longleftrightarrow> (\<forall>T\<in>tys t. wft ar T)"
  by (induction t) auto


subsection \<open>The invariants\<close>

text \<open>
  \<open>pinv alg ar A W env dps\<close>: the environment satisfies the invariant of polymorphic
  environments, the type variables of the problem are known to the type invariant (\<open>A\<close>), and
  the pairs are well-formed, typed modulo the type environment, and not newer than the
  environment. The typing \<open>W\<close> has well-formed types, and it agrees with the types of the bound
  variables modulo the type environment (\<open>wcons\<close>): then the typing modulo the type
  environment is \<open>tnorm (tyenv env) \<circ> W\<close>, which is stable under extensions of the environment.
\<close>

definition wcons :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "wcons W env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
    tnorm (tyenv env) U = tnorm (tyenv env) (W x))"

definition pinv :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pinv alg ar A W env dps \<longleftrightarrow> penv_inv alg ar W env \<and> tinv ar (maxidx env) (tyenv env) A \<and>
    (\<forall>T\<in>etys env. tyw ar (tyenv env) A T) \<and> (\<forall>x. tyw ar (tyenv env) A (W x)) \<and> wcons W env \<and>
    (\<forall>dp\<in>set dps. swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env) A T) \<and> ptyped env W dp \<and>
      dp_below (maxidx env) dp)"

text \<open>The typing of the ground instance under \<open>\<rho>\<close>:\<close>

abbreviation ityp :: "tinst \<Rightarrow> env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "ityp \<rho> env W \<equiv> \<lambda>x. tsubst \<rho> (tctx env W x)"

text \<open>
  \<open>pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps\<close>: the state satisfies \<^const>\<open>pinv\<close>, \<open>\<rho>\<close> is a ground
  well-sorted solution of its type environment, and \<open>\<sigma>\<close> is a solution of the ground instance.
\<close>

definition pcinv :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    tinst \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<longleftrightarrow> pinv alg ar A W env dps \<and> gsol alg ar (tyenv env) \<rho> \<and>
    solution (ityp \<rho> env W) \<tau>' \<sigma> (instE \<rho> env) \<and> (\<forall>dp\<in>set dps. dsolved \<sigma> (instd \<rho> dp))"

lemma pinvD:
  assumes "pinv alg ar A W env dps"
  shows "penv_inv alg ar W env" "tinv ar (maxidx env) (tyenv env) A"
    "T \<in> etys env \<Longrightarrow> tyw ar (tyenv env) A T"
    "dp \<in> set dps \<Longrightarrow> swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env) A T) \<and> ptyped env W dp \<and>
      dp_below (maxidx env) dp"
    "tyw ar (tyenv env) A (W x)" "wcons W env"
  using assms by (simp_all add: pinv_def del: split_paired_All)

lemma pcinvD:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
  shows "pinv alg ar A W env dps" "gsol alg ar (tyenv env) \<rho>"
    "solution (ityp \<rho> env W) \<tau>' \<sigma> (instE \<rho> env)" "dp \<in> set dps \<Longrightarrow> dsolved \<sigma> (instd \<rho> dp)"
  using assms by (simp_all add: pcinv_def)

lemma pinv_append: "pinv alg ar A W env (dps @ dps') \<longleftrightarrow> pinv alg ar A W env dps \<and> pinv alg ar A W env dps'"
  by (auto simp: pinv_def)

lemma pcinv_append:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dps @ dps') \<longleftrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<and> pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps'"
  by (auto simp: pcinv_def pinv_def)


subsection \<open>Ground instances\<close>

lemma tyok_tinv: "tinv ar n (tyenv env) A \<Longrightarrow> tyok env"
  by (simp add: tyok_def tinv_tacyc tinv_tcons_env)

lemma binders_ok_instb: "sbinders ar rb \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> binders_ok ar (instb \<rho> rb)"
  by (auto simp: binders_ok_def sbinders_def instb_def intro: ground_tsubst)

lemma wf_tm_inst:
  "swf_tm ar rb t \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> wf_tm ar (instb \<rho> rb) (inst \<rho> t)"
  using typs_ok_inst[of t ar \<rho>]
  by (auto simp: swf_tm_def wf_tm_def twft_tys)

lemma wf_dp_instd:
  "swf_dp ar dp \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> wf_dp ar (instd \<rho> dp)"
  by (cases dp) (simp add: binders_ok_instb wf_tm_inst)

lemma map_snd_instb: "map snd (instb \<rho> rb) = map (tsubst \<rho>) (map snd rb)"
  by (induction rb) (auto simp: instb_def)

lemma length_instb[simp]: "length (instb \<rho> rb) = length rb"
  by (simp add: instb_def)

lemma typed_inst:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)" "tsol (tyenv env) \<rho>"
    "\<forall>U\<in>set Ts \<union> tys t. tcons (tyenv env) U" "tcons (tyenv env) T" "typed env W Ts t T"
  shows "has_type (ityp \<rho> env W) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> T)"
proof -
  let ?\<theta> = "tyenv env"
  from has_type_inst[OF assms(6)[unfolded typed_def], of \<rho>]
  have "has_type (ityp \<rho> env W) (map (tsubst \<rho> \<circ> tnorm ?\<theta>) Ts) (inst \<rho> (tnormt ?\<theta> t))
      (tsubst \<rho> (tnorm ?\<theta> T))"
    by (simp add: comp_def)
  moreover have "map (tsubst \<rho> \<circ> tnorm ?\<theta>) Ts = map (tsubst \<rho>) Ts"
    using assms(4) tsubst_tnorm[OF assms(1-3)] by auto
  moreover have "inst \<rho> (tnormt ?\<theta> t) = inst \<rho> t"
    using inst_tnormt[OF assms(1-3)] assms(4) by blast
  moreover have "tsubst \<rho> (tnorm ?\<theta> T) = tsubst \<rho> T" by (rule tsubst_tnorm[OF assms(1-3,5)])
  ultimately show ?thesis by simp
qed

lemma typed_tnorm: "tacyc (tyenv env) \<Longrightarrow> typed env W Ts t (tnorm (tyenv env) T) \<longleftrightarrow> typed env W Ts t T"
  by (simp add: typed_def tnorm_idem)

text \<open>The ground instance of a state in the invariant is in the invariant of the monomorphic case:\<close>

lemma pcinv_cinv:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
  shows "cinv ar (ityp \<rho> env W) \<tau>' \<sigma> (instE \<rho> env) (map (instd \<rho>) dps)"
proof -
  note pi = pinvD[OF pcinvD(1)[OF assms]]
  have g: "gsol alg ar (tyenv env) \<rho>" by (rule pcinvD(2)[OF assms])
  then have sol: "tsol (tyenv env) \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)" by (simp_all add: gsol_def)
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have "env_inv ar (ityp \<rho> env W) (instE \<rho> env)" by (rule penv_inv_inst[OF pi(1) g])
  moreover have "wf_dp ar dp' \<and> dp_typed (ityp \<rho> env W) dp' \<and> dp_below (maxidx (instE \<rho> env)) dp' \<and>
      dsolved \<sigma> dp'" if "dp' \<in> set (map (instd \<rho>) dps)" for dp'
  proof -
    from that obtain dp where dp: "dp \<in> set dps" and dp': "dp' = instd \<rho> dp" by auto
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar (rb, t, u)"
      and ty: "\<forall>U\<in>dtys (rb, t, u). tyw ar (tyenv env) A U"
      and tt: "typed env W (map snd rb) t T" and tu: "typed env W (map snd rb) u T"
      and bl: "dp_below (maxidx env) (rb, t, u)"
      by auto
    let ?T = "tnorm (tyenv env) T"
    have tc: "tcons (tyenv env) U" if "U \<in> dtys (rb, t, u)" for U
      using tyw_tcons[OF pi(2)] ty that by blast
    have tcT: "tcons (tyenv env) ?T" by (rule tcons_tnorm[OF ac(1)])
    have "has_type (ityp \<rho> env W) (map (tsubst \<rho>) (map snd rb)) (inst \<rho> t) (tsubst \<rho> ?T)"
      by (rule typed_inst[OF ac sol _ tcT]) (use tc tt in \<open>auto simp: typed_tnorm[OF ac(1)]\<close>)
    moreover have "has_type (ityp \<rho> env W) (map (tsubst \<rho>) (map snd rb)) (inst \<rho> u) (tsubst \<rho> ?T)"
      by (rule typed_inst[OF ac sol _ tcT]) (use tc tu in \<open>auto simp: typed_tnorm[OF ac(1)]\<close>)
    moreover have "dsolved \<sigma> dp'" using pcinvD(4)[OF assms dp] dp' by simp
    ultimately show ?thesis
      using wf_dp_instd[OF w gr] bl dp' dpe by (auto simp: map_snd_instb)
  qed
  ultimately show ?thesis using pcinvD(3)[OF assms] by (simp add: cinv_def)
qed



subsection \<open>Type unification of equal types\<close>

text \<open>Type unification of types that are equal modulo the type environment does not change it.\<close>

lemma foldM_same: "(\<And>x. x \<in> set xs \<Longrightarrow> f x b = return b) \<Longrightarrow> foldM f xs b = return b"
  by (induction xs) (simp_all add: bindM_def return_def)

lemma devar_unbound:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tcons \<theta> T"
  obtains T' where "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "tcons \<theta> T'" "\<not> tbound \<theta> T'"
  using devar_ok[OF assms] by blast

lemma tnorm_nbound_cases:
  assumes "tacyc \<theta>" "\<not> tbound \<theta> T"
  shows "(\<exists>v S. T = TVar v S \<and> tnorm \<theta> T = TVar v S \<and> vt_lookup \<theta> v = None) \<or>
    (\<exists>a S. T = TFree a S \<and> tnorm \<theta> T = T) \<or>
    (\<exists>a Ts. T = Type a Ts \<and> tnorm \<theta> T = Type a (map (tnorm \<theta>) Ts))"
  using assms by (cases T) (auto simp: tbound_def split: option.splits)

lemma unify_aux_same:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
  shows "tcons \<theta> T \<Longrightarrow> tcons \<theta> U \<Longrightarrow> tnorm \<theta> T = tnorm \<theta> U \<Longrightarrow> unify_aux alg T U (\<theta>, n) = return (\<theta>, n)"
proof (induction "size (tnorm \<theta> T)" arbitrary: T U rule: less_induct)
  case less
  obtain T' where dT: "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "tcons \<theta> T'" "\<not> tbound \<theta> T'"
    by (rule devar_unbound[OF ac tc less.prems(1)])
  obtain U' where dU: "devar \<theta> U = return U'" "tnorm \<theta> U' = tnorm \<theta> U" "tcons \<theta> U'" "\<not> tbound \<theta> U'"
    by (rule devar_unbound[OF ac tc less.prems(2)])
  have eq: "tnorm \<theta> T' = tnorm \<theta> U'" using dT(2) dU(2) less.prems(3) by simp
  have body: "unify_aux alg T U (\<theta>, n) = (case (T', U') of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return (\<theta>, n) else tvar_clash v S1 S2)
          else if sort_le alg S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T')) \<theta>; return (tye', n)}
          else if sort_le alg S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U')) \<theta>; return (tye', n)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg S1 S2) n;
            tye' \<leftarrow> update_new (w, (S2, S)) \<theta>;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> U';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg U' S (tye', n)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> T';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T')) \<theta>; meet alg T' S (tye', n)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) (\<theta>, n)
      | _ \<Rightarrow> if T' = U' then return (\<theta>, n) else raise TUnify)"
    by (subst unify_aux.simps) (simp add: dT(1) dU(1) bindM_def return_def)
  from tnorm_nbound_cases[OF ac dT(4)] tnorm_nbound_cases[OF ac dU(4)] eq
  consider (V) v S where "T' = TVar v S" "U' = TVar v S"
    | (F) a S where "T' = TFree a S" "U' = TFree a S"
    | (Ty) a Ts Us where "T' = Type a Ts" "U' = Type a Us" "map (tnorm \<theta>) Ts = map (tnorm \<theta>) Us"
    by auto
  then show ?case
  proof cases
    case V
    then show ?thesis by (simp add: body)
  next
    case F
    then show ?thesis by (simp add: body)
  next
    case (Ty a Ts Us)
    have l: "length Ts = length Us" using Ty(3) by (metis length_map)
    have "foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) (\<theta>, n) = return (\<theta>, n)"
    proof (rule foldM_same)
      fix p assume p: "p \<in> set (zip Ts Us)"
      obtain X Y where pXY: "p = (X, Y)" by force
      with p obtain i where i: "i < length Ts" "X = Ts ! i" "Y = Us ! i"
        using l by (auto simp: set_zip)
      have tT: "tnorm \<theta> T = Type a (map (tnorm \<theta>) Ts)"
        using dT(2) Ty(1) tnorm_nbound_cases[OF ac dT(4)] by auto
      have "tnorm \<theta> X \<in> set (map (tnorm \<theta>) Ts)" using i by auto
      then have lt: "size (tnorm \<theta> X) < size (tnorm \<theta> T)"
        unfolding tT by (auto simp: size_list_estimation' less_Suc_eq_le)
      have tX: "tcons \<theta> X" "tcons \<theta> Y" using dT(3) dU(3) Ty i l by auto
      have "tnorm \<theta> X = tnorm \<theta> Y" using Ty(3) i l by (metis nth_map)
      from less.hyps[OF lt tX this] show "(\<lambda>(T, U) st. unify_aux alg T U st) p (\<theta>, n) = return (\<theta>, n)"
        by (simp add: pXY)
    qed
    with Ty show ?thesis by (simp add: body)
  qed
qed

lemma unify_types_same_mod:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)" "tcons (tyenv env) T" "tcons (tyenv env) U"
    "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "unify_types alg T U env = return env"
proof (cases "T = U")
  case False
  have "type_unify alg U T (tyenv env, maxidx env) = return (tyenv env, maxidx env)"
    unfolding type_unify_def by (rule unify_aux_same[OF assms(1,2,4,3) assms(5)[symmetric]])
  with False show ?thesis by (simp add: unify_types_def handle_def bindM_def return_def)
qed (simp add: unify_types_def)

lemma cunify_types_same_mod:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)" "tcons (tyenv env) T" "tcons (tyenv env) U"
    "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "cunify_types alg T U env = returnW env"
  by (simp add: cunify_types_def unify_types_same_mod[OF assms] return_def)



subsection \<open>Normalizing the types of terms\<close>

lemma tnormt_incr_bv[simp]: "tnormt \<theta> (incr_bv inc lev t) = incr_bv inc lev (tnormt \<theta> t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma tnormt_incr_boundvars[simp]: "tnormt \<theta> (incr_boundvars inc t) = incr_boundvars inc (tnormt \<theta> t)"
  by (simp add: incr_boundvars_def)

lemma tnormt_subst_bound_aux:
  "tnormt \<theta> (subst_bound_aux arg lev t) = subst_bound_aux (tnormt \<theta> arg) lev (tnormt \<theta> t)"
  by (induction arg lev t rule: subst_bound_aux.induct) auto

lemma tnormt_subst_bound[simp]: "tnormt \<theta> (subst_bound arg t) = subst_bound (tnormt \<theta> arg) (tnormt \<theta> t)"
  by (simp add: subst_bound_def tnormt_subst_bound_aux)

lemma tnormt_list_comb[simp]: "tnormt \<theta> (list_comb h ts) = list_comb (tnormt \<theta> h) (map (tnormt \<theta>) ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma head_of_tnormt[simp]: "head_of (tnormt \<theta> t) = tnormt \<theta> (head_of t)"
  by (induction t rule: head_of.induct) auto

lemma strip_comb_tnormt:
  "strip_comb (tnormt \<theta> t) = (tnormt \<theta> (fst (strip_comb t)), map (tnormt \<theta>) (snd (strip_comb t)))"
proof -
  have "strip_comb_acc (tnormt \<theta> t) (map (tnormt \<theta>) ts) =
      (tnormt \<theta> (fst (strip_comb_acc t ts)), map (tnormt \<theta>) (snd (strip_comb_acc t ts)))" for ts
    by (induction t ts rule: strip_comb_acc.induct) auto
  from this[of "[]"] show ?thesis by (simp add: strip_comb_def)
qed

lemma tnormt_simps2[simp]:
  "is_Abs (tnormt \<theta> t) \<longleftrightarrow> is_Abs t" "is_Var (tnormt \<theta> t) \<longleftrightarrow> is_Var t" "proper (tnormt \<theta> t) \<longleftrightarrow> proper t"
  "strip_abs_body (tnormt \<theta> t) = tnormt \<theta> (strip_abs_body t)"
  by (induction t) auto

lemma tnormt_nlb[simp]: "no_loose_bound (tr (tnormt \<theta> t)) n \<longleftrightarrow> no_loose_bound (tr t) n"
  by (induction t arbitrary: n) auto

lemma vps_tnormt': "(x, T) \<in> vps t \<Longrightarrow> (x, tnorm \<theta> T) \<in> vps (tnormt \<theta> t)"
  using vps_tnormt[of \<theta> t] by auto


subsection \<open>Typing modulo the type environment\<close>

text \<open>The variables of a typed term have the types of the typing, modulo the type environment:\<close>

lemma typed_vps:
  "typed env W Ts t T \<Longrightarrow> (x, U) \<in> vps t \<Longrightarrow> tnorm (tyenv env) U = tctx env W x"
  unfolding typed_def by (auto dest: has_type_vps vps_tnormt')

lemma wt_envD:
  "wt_env W env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> typed env W [] u U"
  unfolding wt_env_def by blast

lemma tctx_bound:
  "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tctx env W x = tnorm (tyenv env) U"
  by (simp add: vtyp_def)

lemma typed_weaken: "typed env W [] u U \<Longrightarrow> typed env W Ts u U"
  unfolding typed_def using has_type_weaken[of _ "[]"] by fastforce

text \<open>Types of terms whose types are normalized are normalized:\<close>

lemma has_type_normal:
  "has_type V Ts s Z \<Longrightarrow> tacyc \<theta> \<Longrightarrow> (\<forall>x. tnorm \<theta> (V x) = V x) \<Longrightarrow> (\<forall>T\<in>set Ts. tnorm \<theta> T = T) \<Longrightarrow>
    (\<forall>T\<in>tys s. tnorm \<theta> T = T) \<Longrightarrow> tnorm \<theta> Z = Z"
  by (induction rule: has_type.induct) auto

lemma tctx_normal: "tacyc (tyenv env) \<Longrightarrow> tnorm (tyenv env) (tctx env W x) = tctx env W x"
  by (simp add: tnorm_idem)

lemma typed_type_normal:
  "has_type (tctx env W) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) t) Z \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow>
    tnorm (tyenv env) Z = Z"
  by (erule has_type_normal) (auto simp: tnorm_idem tys_tnormt)

lemma typed_App:
  assumes "tacyc (tyenv env)" "typed env W Ts (f $ u) T"
  obtains Y where "typed env W Ts f (Y \<rightarrow>\<^sub>T T)" "typed env W Ts u Y"
proof -
  from assms(2) obtain Y where f: "has_type (tctx env W) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) f)
      (Y \<rightarrow>\<^sub>T tnorm (tyenv env) T)"
    and u: "has_type (tctx env W) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) u) Y"
    by (auto simp: typed_def elim: has_type_elims)
  have "tnorm (tyenv env) Y = Y" by (rule typed_type_normal[OF u assms(1)])
  with f u show ?thesis by (intro that[of Y]) (simp_all add: typed_def)
qed

lemma typed_AppI: "typed env W Ts f (Y \<rightarrow>\<^sub>T T) \<Longrightarrow> typed env W Ts u Y \<Longrightarrow> typed env W Ts (f $ u) T"
  by (auto simp: typed_def intro: has_type.App)

lemma typed_beta:
  assumes "tacyc (tyenv env)" "typed env W Ts (pterm.Abs a X body) (Y \<rightarrow>\<^sub>T T)" "typed env W Ts u Y"
  shows "typed env W Ts (subst_bound u body) T"
  using assms(2,3) by (auto simp: typed_def elim!: has_type_elims intro: has_type_subst_bound)

text \<open>\<open>head_norm\<close> keeps the typing modulo the type environment.\<close>

lemma head_norm_ptyped:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> wt_env W env \<Longrightarrow>
    (\<forall>U\<in>tys t \<union> etys env. tcons (tyenv env) U) \<Longrightarrow> typed env W Ts t T \<Longrightarrow>
    typed env W Ts t' T \<and> tys t' \<subseteq> tys t \<union> etys env"
  using assms
proof (induction env t r arbitrary: t' Ts T rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  let ?\<theta> = "tyenv env" and ?V = "tctx env W"
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" and wt: "wt_env W env"
    and tc: "\<forall>U\<in>tys t \<union> etys env. tcons ?\<theta> U" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  have IH: "typed env W Ts' t2 T' \<and> tys t2 \<subseteq> tys t1 \<union> etys env"
    if "hn env t1 = Some (Ok t2)" "\<forall>U\<in>tys t1 \<union> etys env. tcons ?\<theta> U" "typed env W Ts' t1 T'" for t1 t2 Ts' T'
    by (rule "1.IH"[OF that(1) refl ac wt that(2,3)])
  have ty: "has_type ?V (map (tnorm ?\<theta>) Ts) (tnormt ?\<theta> t) (tnorm ?\<theta> T)"
    using "1.prems"(6) by (simp add: typed_def)
  show ?case
  proof (cases t)
    case (Var xi U)
    with t' obtain r' where lk: "ok (lookup env xi U) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    show ?thesis
    proof (cases "vt_lookup (tenv env) xi")
      case None
      with lk have "r' = None" by (simp add: lookup_def return_def)
      with rest "1.prems" show ?thesis by auto
    next
      case (Some b)
      obtain U' u where b: "b = (U', u)" by force
      have lku: "vt_lookup (tenv env) xi = Some (U', u)" using Some b by simp
      have tcU: "tcons ?\<theta> U" using tc Var by simp
      have tcU': "tcons ?\<theta> U'" using tc etysI[OF lku] by auto
      from lk lku have "ok (do {b \<leftarrow> unified ?\<theta> U U'; if b then return (Some u) else var_clash xi U U'}) r'"
        by (simp add: lookup_def)
      moreover have vx: "?V xi = tnorm ?\<theta> U" and tT: "tnorm ?\<theta> T = tnorm ?\<theta> U"
        using ty Var by (auto elim: has_type_elims)
      moreover have eqU: "tnorm ?\<theta> U' = tnorm ?\<theta> U"
        using tctx_bound[OF lku, of W] vx by simp
      ultimately have "r' = Some u"
        by (auto simp: unified_ok[OF ac tcU tcU'] bindM_def return_def)
      with rest have hu: "hn env u = Some (Ok t')" by simp
      have "typed env W [] u U'" by (rule wt_envD[OF wt lku])
      then have tyu: "typed env W Ts u T"
        using tT eqU has_type_weaken[of _ "[]"] by (fastforce simp: typed_def)
      have tcu: "\<forall>V\<in>tys u \<union> etys env. tcons ?\<theta> V" using tc etysI[OF lku] by auto
      from IH[OF hu tcu tyu] etysI[OF lku] show ?thesis by auto
    qed
  next
    case (Abs a U body)
    with t' obtain b' where hb: "hn env body = Some (Ok b')" and tb: "t' = pterm.Abs a U b'" by auto
    from ty Abs obtain X where tT: "tnorm ?\<theta> T = tnorm ?\<theta> U \<rightarrow>\<^sub>T X"
      and tbody: "has_type ?V (tnorm ?\<theta> U # map (tnorm ?\<theta>) Ts) (tnormt ?\<theta> body) X"
      by (auto elim: has_type_elims)
    have X: "tnorm ?\<theta> X = X"
    proof -
      have "tnorm ?\<theta> (tnorm ?\<theta> T) = tnorm ?\<theta> T" by (rule tnorm_idem[OF ac(1)])
      with tT show ?thesis by simp
    qed
    have tyb: "typed env W (U # Ts) body X" using tbody X by (simp add: typed_def)
    have tcb: "\<forall>V\<in>tys body \<union> etys env. tcons ?\<theta> V" using tc Abs by auto
    from IH[OF hb tcb tyb] show ?thesis using tb tT X Abs by (auto simp: typed_def intro: has_type.Abs)
  next
    case (App f u)
    from typed_App[OF ac(1) "1.prems"(6)[unfolded App]] obtain Y
      where tf: "typed env W Ts f (Y \<rightarrow>\<^sub>T T)" and tu: "typed env W Ts u Y" .
    have tcf: "\<forall>V\<in>tys f \<union> etys env. tcons ?\<theta> V" and tcu: "\<forall>V\<in>tys u \<union> etys env. tcons ?\<theta> V"
      using tc App by auto
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a X body where f: "f = pterm.Abs a X body" by (cases f) auto
      with t' App have hs: "hn env (subst_bound u body) = Some (Ok t')" by simp
      have tcs: "\<forall>V\<in>tys (subst_bound u body) \<union> etys env. tcons ?\<theta> V"
        using tys_subst_bound[of u body] tcf tcu f by auto
      from IH[OF hs tcs typed_beta[OF ac(1) tf[unfolded f] tu]] tys_subst_bound[of u body] f App
      show ?thesis by auto
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF nf tcf tf] have tnf: "typed env W Ts nf (Y \<rightarrow>\<^sub>T T)"
        and tysnf: "tys nf \<subseteq> tys f \<union> etys env" by simp_all
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a X body where nfa: "nf = pterm.Abs a X body" by (cases nf) auto
        with rest have hs: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have "\<forall>V\<in>tys (subst_bound u body) \<union> etys env. tcons ?\<theta> V"
          using tys_subst_bound[of u body] tysnf nfa tcf tcu by auto
        from IH[OF hs this typed_beta[OF ac(1) tnf[unfolded nfa] tu]] tys_subst_bound[of u body] tysnf nfa App
        show ?thesis by auto
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with tnf tu tysnf App show ?thesis by (auto simp: typed_AppI)
      qed
    qed
  qed (use t' "1.prems" in auto)
qed



subsection \<open>Ground instances of head normalization\<close>

text \<open>The variables of a typed term and of the environment have consistent types modulo \<open>\<theta>\<close>:\<close>

lemma penv_inv_hyp:
  assumes inv: "penv_inv alg ar W env" and sol: "tsol (tyenv env) \<rho>"
    and X: "\<forall>p\<in>X. tcons (tyenv env) (snd p) \<and> tnorm (tyenv env) (snd p) = tctx env W (fst p) \<and>
      snd (fst p) \<le> maxidx env"
  shows "hyp \<rho> env X"
proof -
  note i = penv_invD[OF inv]
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF i(1)] tinv_tcons_env[OF i(1)] by simp_all
  have tce: "tcons (tyenv env) T" if "T \<in> etys env" for T
    using that by (intro tinv_tcons[OF i(1)]) (auto simp: etvars_def)
  have "tnorm (tyenv env) (snd p) = tnorm (tyenv env) (tctx env W (fst p)) \<and> tcons (tyenv env) (snd p) \<and>
      snd (fst p) \<le> maxidx env"
    if p: "p \<in> X \<union> bvps env \<union> bpairs env" for p
  proof -
    have "tnorm (tyenv env) (snd p) = tctx env W (fst p) \<and> tcons (tyenv env) (snd p) \<and>
        snd (fst p) \<le> maxidx env"
    proof (cases "p \<in> X")
      case True
      with X show ?thesis by blast
    next
      case False
      with p have pb: "p \<in> bvps env \<union> bpairs env" by blast
      then have tc: "tcons (tyenv env) (snd p)" using tce bvps_bpairs_etys by blast
      from pb obtain x U u where b: "vt_lookup (tenv env) x = Some (U, u)"
        and pc: "p \<in> vps u \<or> p = (x, U)"
        unfolding bvps_def bpairs_def by (cases p) auto
      have fr: "snd x \<le> maxidx env" "below (maxidx env) u" using fresh_envD[OF i(6) b] by simp_all
      show ?thesis
      proof (cases "p = (x, U)")
        case True
        with tctx_bound[OF b, of W] tc fr show ?thesis by simp
      next
        case False
        with pc have "p \<in> vps u" by simp
        have wt: "wt_env W env" using inv by (simp add: penv_inv_def)
        from \<open>p \<in> vps u\<close> typed_vps[OF wt_envD[OF wt b]] tc fr below_vps[OF fr(2)]
        show ?thesis by (cases p) auto
      qed
    qed
    then show ?thesis using tctx_normal[OF ac(1)] by simp
  qed
  then show ?thesis unfolding hyp_def using ac sol by (auto simp: tyok_def intro!: exI[of _ "tctx env W"])
qed

lemma typed_hyp:
  assumes inv: "penv_inv alg ar W env" and sol: "tsol (tyenv env) \<rho>"
    and ty: "typed env W Ts t T" and tc: "\<forall>U\<in>tys t. tcons (tyenv env) U" and bl: "below (maxidx env) t"
  shows "hyp \<rho> env (vps t)"
  by (rule penv_inv_hyp[OF inv sol]) (auto dest: typed_vps[OF ty] vps_tys below_vps[OF bl] intro: tc[rule_format])

lemma head_norm_pinst:
  assumes "penv_inv alg ar W env" "tsol (tyenv env) \<rho>" "typed env W Ts t T" "\<forall>U\<in>tys t. tcons (tyenv env) U"
    "below (maxidx env) t"
  shows "head_norm (instE \<rho> env) (inst \<rho> t) = instM \<rho> (inst \<rho>) (head_norm env t)"
proof -
  have h: "hyp \<rho> env (vps t)" by (rule typed_hyp[OF assms])
  show ?thesis by (rule head_norm_inst[OF hypD(1)[OF h] hyp_lkdec[OF h]])
qed

end

context wf_csig
begin

text \<open>Head normalization terminates on typed terms, without an exception:\<close>

lemma head_norm_pterm:
  assumes inv: "penv_inv alg ar W env" and ty: "typed env W Ts t T"
    and tw: "\<forall>U\<in>tys t \<union> set Ts. tyw ar (tyenv env) A U" and A: "tinv ar (maxidx env) (tyenv env) A"
    and bl: "below (maxidx env) t"
  obtains t' where "head_norm env t = Some (Ok t')"
proof -
  note i = penv_invD[OF inv]
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" using gsol_exists[OF A i(2)] .
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF A] tinv_tcons_env[OF A] by simp_all
  have tc: "\<forall>U\<in>tys t \<union> set Ts. tcons (tyenv env) U" using tw tyw_tcons[OF A] by blast
  have ty': "typed env W Ts t (tnorm (tyenv env) T)" using ty by (simp add: typed_tnorm[OF ac(1)])
  note ei = env_invD[OF penv_inv_inst[OF inv g]]
  have "has_type (ityp \<rho> env W) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> (tnorm (tyenv env) T))"
    by (rule typed_inst[OF ac sol _ tcons_tnorm[OF ac(1)] ty']) (use tc in auto)
  from head_norm_term[OF ei(1-3) this] obtain t0 where "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok t0)" by blast
  with head_norm_pinst[OF inv sol ty _ bl] tc have "instM \<rho> (inst \<rho>) (head_norm env t) = Some (Ok t0)" by simp
  then obtain r where r: "head_norm env t = Some r" "instr \<rho> (inst \<rho>) r = Ok t0" by (auto simp: instM_def)
  then obtain t' where "r = Ok t'" by (cases r) auto
  with r(1) show ?thesis by (intro that) simp
qed

end



subsection \<open>Type computations modulo the type environment\<close>

text \<open>
  The type computations of \<open>unify.ML\<close> depend only on the type environment. On terms with
  normalized types, they agree with those in the empty type environment: the environment
  \<open>env0 env\<close> has the bindings of \<open>env\<close> and an empty type environment.
\<close>

context csig
begin

definition env0 :: "env \<Rightarrow> env" where
  "env0 env = Envir (maxidx env) (tenv env) vt_empty"

lemma env0_simps[simp]: "tyenv (env0 env) = vt_empty" "tenv (env0 env) = tenv env" "maxidx (env0 env) = maxidx env"
  by (simp_all add: env0_def)

definition tnormb :: "tyenv \<Rightarrow> binders \<Rightarrow> binders" where
  "tnormb \<theta> rb = map (\<lambda>(a, T). (a, tnorm \<theta> T)) rb"

lemma map_snd_tnormb[simp]: "map snd (tnormb \<theta> rb) = map (tnorm \<theta>) (map snd rb)"
  by (induction rb) (auto simp: tnormb_def)

lemma tnormb_simps[simp]: "tnormb \<theta> [] = []" "tnormb \<theta> ((a, T) # rb) = (a, tnorm \<theta> T) # tnormb \<theta> rb"
  "length (tnormb \<theta> rb) = length rb" "tnormb \<theta> (rb @ rb') = tnormb \<theta> rb @ tnormb \<theta> rb'"
  by (simp_all add: tnormb_def)

lemma devar_tnorm_fun:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tcons \<theta> T" "ok (devar \<theta> T) (Type a [A, U])"
  shows "tnorm \<theta> T = Type a [tnorm \<theta> A, tnorm \<theta> U]" "tcons \<theta> A" "tcons \<theta> U"
proof -
  from devar_ok[OF assms(1-3)] obtain T' where "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "tcons \<theta> T'"
    by blast
  with assms(4) show "tnorm \<theta> T = Type a [tnorm \<theta> A, tnorm \<theta> U]" "tcons \<theta> A" "tcons \<theta> U"
    by (auto simp: return_def)
qed


lemma ok_nth_map: "ok (nth xs i) x \<Longrightarrow> ok (nth (map f xs) i) (f x)"
  by (simp add: ok_nth)

lemma env_fastype_tnorm:
  "tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> ok (env_fastype env Ts t) T \<Longrightarrow>
    \<forall>U\<in>set Ts \<union> tys t. tcons (tyenv env) U \<Longrightarrow>
    ok (env_fastype (env0 env) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) t)) (tnorm (tyenv env) T) \<and>
    tcons (tyenv env) T"
proof (induction env Ts t arbitrary: T rule: env_fastype.induct)
  case (1 env Ts f u)
  let ?\<theta> = "tyenv env"
  from "1.prems"(3) obtain T0 T' where f: "ok (env_fastype env Ts f) T0" and d: "ok (devar ?\<theta> T0) T'"
    and r: "ok (case T' of
        Type a Us \<Rightarrow>
          (case Us of
            [_, U] \<Rightarrow> if a = STR ''fun'' then return U else raise (Term_Error funerr [f $ u])
          | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by (auto simp: bindM_def split: option.splits res.splits)
  from r obtain A where T': "T' = Type STR ''fun'' [A, T]"
    by (auto simp: return_def raise_def split: ptyp.splits list.splits if_splits)
  have IH: "ok (env_fastype (env0 env) (map (tnorm ?\<theta>) Ts) (tnormt ?\<theta> f)) (tnorm ?\<theta> T0) \<and> tcons ?\<theta> T0"
    using "1.IH"[OF "1.prems"(1,2) f] "1.prems"(4) by auto
  note dt = devar_tnorm_fun[OF "1.prems"(1,2) conjunct2[OF IH] d[unfolded T']]
  show ?case
    using IH dt by (simp add: bindM_def devar_empty return_def)
next
  case (4 env Ts i)
  then have "ok (nth Ts i) T" by (auto simp: handle_def return_def split: option.splits res.splits exn.splits)
  with "4.prems"(4) show ?case
    by (auto simp: handle_def ok_nth_map ok_nth return_def)
next
  case (6 env Ts a A u)
  then obtain U where u: "ok (env_fastype env (A # Ts) u) U" and T: "T = A \<rightarrow>\<^sub>T U"
    by (auto simp: bindM_def return_def split: option.splits res.splits)
  from "6.IH"[OF "6.prems"(1,2) u] "6.prems"(4) T show ?case by (auto simp: bindM_def return_def)
qed (auto simp: return_def)

lemma fastype_tnorm:
  "tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> ok (fastype env rb t) T \<Longrightarrow>
    \<forall>U\<in>snd ` set rb \<union> tys t. tcons (tyenv env) U \<Longrightarrow>
    ok (fastype (env0 env) (tnormb (tyenv env) rb) (tnormt (tyenv env) t)) (tnorm (tyenv env) T) \<and>
    tcons (tyenv env) T"
  unfolding fastype_def using env_fastype_tnorm[of env "map snd rb" t T] by auto

lemma etif_tnorm:
  assumes "etif \<theta> T t = Some r"
  shows "r = Ok t' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tcons \<theta> T \<Longrightarrow>
    etif vt_empty (tnorm \<theta> T) (tnormt \<theta> t) = Some (Ok (tnormt \<theta> t'))"
  using assms
proof (induction \<theta> T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et \<theta> T t r)
  have e: "type_lookup vt_empty v S = return None" for v S by (simp add: type_lookup_def return_def)
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where a: "a = STR ''fun''" and Ts: "Ts = [T1, U]" by blast
      from "1.hyps" "1.prems"(1) Type a Ts obtain u where u: "et \<theta> U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
        and t': "t' = Abs STR '''' T1 u"
        by (auto simp: bindM_def return_def split: option.splits res.splits)
      have "tcons \<theta> U" using "1.prems"(4) Type Ts by simp
      from "1.IH"[OF u refl "1.prems"(2,3) this] show ?thesis
        by (subst etif.simps) (simp add: Type a Ts t' bindM_def return_def)
    next
      case False
      with "1.hyps" "1.prems"(1) Type have "t' = t"
        by (auto simp: return_def split: list.splits if_splits)
      with False Type show ?thesis
        by (subst etif.simps) (auto simp: return_def split: list.splits)
    qed
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> v S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et \<theta> T' t) t'"
      by (auto simp: bindM_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume r': "r' = None"
      with lk have "vt_lookup \<theta> v = None"
        by (auto simp: type_lookup_def tvar_clash_def return_def raise_def split: option.splits if_splits)
      with rest r' TVar show ?thesis
        by (subst etif.simps) (simp add: e return_def bindM_def tnorm_TVar[OF "1.prems"(2)])
    next
      fix U assume r': "r' = Some U" and l: "vt_lookup \<theta> v = Some (S, U)"
      with rest have "et \<theta> U t = Some (Ok t')" by simp
      moreover have "tcons \<theta> U" using "1.prems"(3) l unfolding tcons_env_def by blast
      ultimately have "etif vt_empty (tnorm \<theta> U) (tnormt \<theta> t) = Some (Ok (tnormt \<theta> t'))"
        using "1.IH" "1.prems"(2,3) by blast
      then show ?thesis using TVar l by (simp add: tnorm_TVar[OF "1.prems"(2)])
    qed
  qed (use "1.hyps" "1.prems" in \<open>subst etif.simps, simp add: return_def\<close>)+
qed

lemma eta_norm_nonAbs_tnorm:
  assumes "\<not> is_Abs t" "ok (eta_norm env rb t) t'" "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "\<forall>U\<in>snd ` set rb \<union> tys t. tcons (tyenv env) U"
  shows "ok (eta_norm (env0 env) (tnormb (tyenv env) rb) (tnormt (tyenv env) t)) (tnormt (tyenv env) t')"
proof -
  let ?\<theta> = "tyenv env"
  from assms(2) obtain T where T: "ok (fastype env rb t) T" and e: "ok (etif ?\<theta> T t) t'"
    by (auto simp: eta_norm_nonAbs[OF assms(1)] bindM_def split: option.splits res.splits)
  note ft = fastype_tnorm[OF assms(3,4) T assms(5)]
  from etif_tnorm[OF e refl assms(3,4) conjunct2[OF ft]] conjunct1[OF ft] assms(1)
  show ?thesis by (simp add: eta_norm_nonAbs bindM_def)
qed

lemma eta_norm_tnorm:
  "ok (eta_norm env rb t) t' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow>
    \<forall>U\<in>snd ` set rb \<union> tys t. tcons (tyenv env) U \<Longrightarrow>
    ok (eta_norm (env0 env) (tnormb (tyenv env) rb) (tnormt (tyenv env) t)) (tnormt (tyenv env) t')"
proof (induction t arbitrary: rb t')
  case (Abs a A body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, A) # rb) body) b'" and t': "t' = Abs a A b'"
    by (auto simp: bindM_def return_def split: option.splits res.splits)
  from Abs.IH[OF b' Abs.prems(2,3)] Abs.prems(4) t' show ?case by (simp add: bindM_def return_def)
qed (rule eta_norm_nonAbs_tnorm; simp)+



subsection \<open>Termination of the type computations\<close>

lemma env_fastype_pterm:
  "tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> \<forall>U\<in>set Ts \<union> tys t. tcons (tyenv env) U \<Longrightarrow>
    has_type V (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) t) T \<Longrightarrow>
    \<exists>T'. ok (env_fastype env Ts t) T' \<and> tnorm (tyenv env) T' = T"
proof (induction env Ts t arbitrary: T rule: env_fastype.induct)
  case (1 env Ts f u)
  let ?\<theta> = "tyenv env"
  from "1.prems"(4) obtain Y where tf: "has_type V (map (tnorm ?\<theta>) Ts) (tnormt ?\<theta> f) (Y \<rightarrow>\<^sub>T T)"
    by (auto elim: has_type_elims)
  from "1.IH"[OF "1.prems"(1,2) _ tf] "1.prems"(3) obtain T0 where f: "ok (env_fastype env Ts f) T0"
    and T0: "tnorm ?\<theta> T0 = Y \<rightarrow>\<^sub>T T" by auto
  have tc0: "tcons ?\<theta> T0" using env_fastype_tnorm[OF "1.prems"(1,2) f] "1.prems"(3) by auto
  from devar_ok[OF "1.prems"(1,2) tc0] obtain D where d: "devar ?\<theta> T0 = return D"
    "tnorm ?\<theta> D = tnorm ?\<theta> T0" "\<not> tbound ?\<theta> D" by blast
  from tnorm_nbound_cases[OF "1.prems"(1) d(3)] d(2) T0 obtain A U where D: "D = A \<rightarrow>\<^sub>T U"
    "tnorm ?\<theta> U = T" by auto
  show ?case using f d(1) D by (auto simp: bindM_def return_def)
next
  case (4 env Ts i)
  then have "0 \<le> i" "nat_of_integer i < length Ts" "T = tnorm (tyenv env) (Ts ! nat_of_integer i)"
    by (auto elim!: has_type_elims simp: has_type_Bound_iff)
  then show ?case by (auto simp: handle_def nth_return return_def)
next
  case (6 env Ts a A u)
  from "6.prems"(4) obtain U where tu: "has_type V (map (tnorm (tyenv env)) (A # Ts)) (tnormt (tyenv env) u) U"
    and T: "T = tnorm (tyenv env) A \<rightarrow>\<^sub>T U"
    by (auto elim: has_type_elims)
  from "6.IH"[OF "6.prems"(1,2) _ tu] "6.prems"(3) obtain U' where "ok (env_fastype env (A # Ts) u) U'"
    "tnorm (tyenv env) U' = U" by auto
  with T show ?case by (auto simp: bindM_def return_def)
qed (auto elim!: has_type_elims simp: return_def)

lemma etif_pterm:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and T: "tcons \<theta> T"
  shows "\<exists>t'. ok (etif \<theta> T t) t'"
proof -
  have "\<forall>t. \<exists>t'. ok (etif \<theta> T t) t'"
    using T
  proof (induction rule: tnorm_induct[OF ac tc, consumes 1, case_names TFree Type Unbound Bound])
    case (TFree a S)
    then show ?case by (subst etif.simps) (simp add: return_def)
  next
    case (Type a Ts)
    show ?case
    proof
      fix t
      show "\<exists>t'. ok (etif \<theta> (Type a Ts) t) t'"
      proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
        case True
        then obtain T1 U where a: "a = STR ''fun''" and Ts: "Ts = [T1, U]" by blast
        from Type.IH[of U] Ts obtain u where "ok (etif \<theta> U (incr_boundvars 1 t $ Bound 0)) u" by auto
        then show ?thesis by (subst etif.simps) (auto simp: a Ts bindM_def return_def)
      next
        case False
        then show ?thesis by (subst etif.simps) (auto simp: return_def split: list.splits)
      qed
    qed
  next
    case (Unbound v S)
    then have "type_lookup \<theta> v S = return None" by (simp add: type_lookup_def return_def)
    then show ?case by (subst etif.simps) (simp add: bindM_def return_def)
  next
    case (Bound v S U)
    have lk: "type_lookup \<theta> v S = return (Some U)"
      using Bound(1) by (simp add: type_lookup_def return_def)
    show ?case
    proof
      fix t
      from Bound(3) obtain t' where "ok (etif \<theta> U t) t'" by blast
      then show "\<exists>t'. ok (etif \<theta> (TVar v S) t) t'" by (subst etif.simps) (auto simp: lk bindM_def return_def)
    qed
  qed
  then show ?thesis by blast
qed

lemma eta_norm_nonAbs_pterm:
  assumes "\<not> is_Abs t" "tacyc (tyenv env)" "tcons_env (tyenv env)" "\<forall>U\<in>snd ` set rb \<union> tys t. tcons (tyenv env) U"
    "has_type V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t) T"
  shows "\<exists>t'. ok (eta_norm env rb t) t'"
proof -
  from env_fastype_pterm[OF assms(2,3) _ assms(5)] assms(4) obtain T' where
    T': "ok (fastype env rb t) T'" by (auto simp: fastype_def)
  have "tcons (tyenv env) T'" using fastype_tnorm[OF assms(2,3) T' assms(4)] by simp
  from etif_pterm[OF assms(2,3) this] obtain t' where "ok (etif (tyenv env) T' t) t'" by blast
  with T' assms(1) show ?thesis by (auto simp: eta_norm_nonAbs bindM_def)
qed

lemma eta_norm_pterm:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)"
  shows "\<forall>U\<in>snd ` set rb \<union> tys t. tcons (tyenv env) U \<Longrightarrow>
    has_type V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t) T \<Longrightarrow>
    \<exists>t'. ok (eta_norm env rb t) t'"
proof (induction t arbitrary: rb T)
  case (Abs a A body)
  from Abs.prems(2) obtain U where tb: "has_type V (tnorm (tyenv env) A # map (tnorm (tyenv env)) (map snd rb))
      (tnormt (tyenv env) body) U"
    by (auto elim: has_type_elims)
  have "\<forall>U\<in>snd ` set ((a, A) # rb) \<union> tys body. tcons (tyenv env) U" using Abs.prems(1) by auto
  from Abs.IH[OF this] tb obtain b' where "ok (eta_norm env ((a, A) # rb) body) b'" by auto
  then show ?case by (auto simp: bindM_def return_def)
qed (rule eta_norm_nonAbs_pterm[OF _ assms]; simp)+



subsection \<open>Extending the type environment\<close>

lemma tctx_textends:
  assumes "tacyc (tyenv env')" "textends (tyenv env) (tyenv env')" "tenv env' = tenv env"
  shows "tctx env' W x = tnorm (tyenv env') (tctx env W x)"
  using assms by (simp add: vtyp_def tnorm_textends)

lemma typed_textends:
  assumes "tacyc (tyenv env')" "textends (tyenv env) (tyenv env')" "tenv env' = tenv env"
    "typed env W Ts t T"
  shows "typed env' W Ts t T"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  from has_type_tnormt[OF assms(4)[unfolded typed_def], of ?\<theta>']
  show ?thesis
    unfolding typed_def using assms(1-3)
    by (simp add: comp_def tnorm_textends tnormt_textends tctx_textends)
qed

lemma wt_env_textends:
  assumes "tacyc (tyenv env')" "textends (tyenv env) (tyenv env')" "tenv env' = tenv env" "wt_env W env"
  shows "wt_env W env'"
  using assms typed_textends[OF assms(1-3)] by (auto simp: wt_env_def)

lemma etys_same_tenv: "tenv env' = tenv env \<Longrightarrow> etys env' = etys env"
  by (simp add: etys_def)


subsection \<open>Well-formed types\<close>

lemma tyw_Type: "tyw ar \<theta> A (Type a Ts) \<Longrightarrow> T \<in> set Ts \<Longrightarrow> tyw ar \<theta> A T"
proof -
  assume a: "tyw ar \<theta> A (Type a Ts)" "T \<in> set Ts"
  have "uvars \<theta> T \<subseteq> uvars \<theta> (Type a Ts)" using a(2) by (auto simp: uvars_def)
  with a show ?thesis by (auto simp: tyw_def)
qed

lemma tyw_fun: "tyw ar \<theta> A (T \<rightarrow>\<^sub>T U) \<longleftrightarrow> tyw ar \<theta> A T \<and> tyw ar \<theta> A U"
  by (auto simp: tyw_def uvars_def tarity_def)

lemma tyw_foldr_fun: "tyw ar \<theta> A (foldr fun_type Ts U) \<longleftrightarrow> (\<forall>T\<in>set Ts. tyw ar \<theta> A T) \<and> tyw ar \<theta> A U"
  by (induction Ts) (auto simp: tyw_fun)

lemma tyw_devar:
  assumes "tinv ar n \<theta> A" "tyw ar \<theta> A T" "ok (devar \<theta> T) T'"
  shows "tyw ar \<theta> A T'"
proof -
  have T: "tvars T \<subseteq> tvars_env \<theta> \<union> A" "wft ar T" using assms(2) by (simp_all add: tyw_def)
  obtain U where U: "devar \<theta> T = return U" "tnorm \<theta> U = tnorm \<theta> T"
    "tvars U \<subseteq> tvars_env \<theta> \<union> A" "wft ar U"
    by (rule tinv_devar[OF assms(1) T])
  with assms(3) have "U = T'" by (simp add: return_def)
  with U assms(2) show ?thesis by (auto simp: tyw_def uvars_def)
qed

text \<open>
  The k-condition: the unbound type variables of the normal form of a type are instantiated by
  types in which every chain of arrows has at most \<open>k\<close> argument types. It is preserved by every
  extension of the type environment with an agreeing solution.
\<close>

fun aok :: "nat \<Rightarrow> ptyp \<Rightarrow> bool" where
  "aok k (Type a Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. aok k T) \<and> length (arg_types (Type a Ts)) \<le> k"
| "aok k T \<longleftrightarrow> True"

definition kok :: "nat \<Rightarrow> tinst \<Rightarrow> tyenv \<Rightarrow> ptyp \<Rightarrow> bool" where
  "kok k \<rho> \<theta> T \<longleftrightarrow> (\<forall>(v, S)\<in>tvars (tnorm \<theta> T). aok k (\<rho> v S))"

lemma aok_tsubst_sub:
  "aok k (tsubst \<rho> T) \<Longrightarrow> (v, S) \<in> tvars T \<Longrightarrow> aok k (\<rho> v S)"
  by (induction T) (auto simp: split: if_splits)

lemma kok_textends:
  assumes ac: "tacyc \<theta>'" and ext: "textends \<theta> \<theta>'" and sol: "tsol \<theta>' \<rho>'"
    and ag: "\<And>v S. (v, S) \<in> tvars (tnorm \<theta> T) \<Longrightarrow> \<rho>' v S = \<rho> v S"
    and tce: "tcons_env \<theta>'" and tc: "tcons \<theta>' (tnorm \<theta> T)"
    and k: "kok k \<rho> \<theta> T"
  shows "kok k \<rho>' \<theta>' T"
  unfolding kok_def
proof (clarify)
  fix w S' assume w: "(w, S') \<in> tvars (tnorm \<theta>' T)"
  have "tnorm \<theta>' T = tnorm \<theta>' (tnorm \<theta> T)" by (rule tnorm_textends[OF ac ext, symmetric])
  also have "\<dots> = tsubst (\<lambda>v S. tnorm \<theta>' (TVar v S)) (tnorm \<theta> T)" by (rule tnorm_tsubst)
  finally obtain v S where vS: "(v, S) \<in> tvars (tnorm \<theta> T)" and wv: "(w, S') \<in> tvars (tnorm \<theta>' (TVar v S))"
    using w by (auto simp: tvars_tsubst)
  have "tcons \<theta>' (TVar v S)" using tc vS by (cases v) (simp add: tcons_def; blast)
  then have "tsubst \<rho>' (tnorm \<theta>' (TVar v S)) = \<rho>' v S" using tsubst_tnorm[OF ac tce sol] by simp
  also have "\<dots> = \<rho> v S" by (rule ag[OF vS])
  finally have "aok k (tsubst \<rho>' (tnorm \<theta>' (TVar v S)))" using k vS by (auto simp: kok_def)
  from aok_tsubst_sub[OF this wv] show "aok k (\<rho>' w S')" .
qed

lemma kok_fun: "kok k \<rho> \<theta> (T \<rightarrow>\<^sub>T U) \<longleftrightarrow> kok k \<rho> \<theta> T \<and> kok k \<rho> \<theta> U"
  by (auto simp: kok_def)

lemma kok_foldr_fun: "kok k \<rho> \<theta> (foldr fun_type Ts U) \<longleftrightarrow> (\<forall>T\<in>set Ts. kok k \<rho> \<theta> T) \<and> kok k \<rho> \<theta> U"
  by (induction Ts) (auto simp: kok_fun)

lemma kok_tnorm: "tacyc \<theta> \<Longrightarrow> kok k \<rho> \<theta> (tnorm \<theta> T) \<longleftrightarrow> kok k \<rho> \<theta> T"
  by (simp add: kok_def tnorm_idem)



subsection \<open>Stripping common abstractions\<close>

lemma new_dpair_nonAbs: "\<not> is_Abs t \<Longrightarrow> \<not> is_Abs u \<Longrightarrow> new_dpair alg rb t u env = returnW ((rb, t, u), env)"
  by (cases t; cases u) auto

lemma arg_res_type_base: "\<not> is_funT T \<Longrightarrow> arg_types T = [] \<and> res_type T = T"
  by (cases T rule: arg_types.cases) auto

lemma hlong_funT_Abs: "hlong V Ts t T \<Longrightarrow> is_funT T \<Longrightarrow> is_Abs t"
  by (cases rule: hlong.cases) auto

lemma hlong_nonAbs: "hlong V Ts t T \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> has_type V Ts t T \<and> \<not> is_funT T"
  by (cases rule: hlong.cases) auto

lemma hlong_Abs_funT: "hlong V Ts t T \<Longrightarrow> is_Abs t \<Longrightarrow> is_funT T"
  by (cases rule: hlong.cases) auto

lemma new_dpair_phlong_base:
  assumes "\<not> is_Abs t"
    and "hlong V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t) T"
    and "hlong V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) T"
  shows "\<exists>rb'. new_dpair alg rb t u env = returnW ((rb', strip_abs_body t, strip_abs_body u), env) \<and>
      map (tnorm (tyenv env)) (map snd rb') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb) \<and>
      length rb' = length (arg_types T) + length rb \<and>
      has_type V (map (tnorm (tyenv env)) (map snd rb')) (tnormt (tyenv env) (strip_abs_body t)) (res_type T) \<and>
      has_type V (map (tnorm (tyenv env)) (map snd rb')) (tnormt (tyenv env) (strip_abs_body u)) (res_type T) \<and>
      \<not> is_Abs (strip_abs_body t) \<and> \<not> is_Abs (strip_abs_body u) \<and>
      snd ` set rb' \<subseteq> snd ` set rb \<union> tys t"
proof -
  have nA: "\<not> is_Abs (tnormt (tyenv env) t)" using assms(1) by simp
  from hlong_nonAbs[OF assms(2) nA] have T: "\<not> is_funT T"
    and ht: "has_type V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t) T" by auto
  have "\<not> is_Abs (tnormt (tyenv env) u)" using hlong_Abs_funT[OF assms(3)] T by blast
  with hlong_nonAbs[OF assms(3)] have u: "\<not> is_Abs u"
    and hu: "has_type V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) T" by auto
  have "strip_abs_body t = t" "strip_abs_body u = u" using assms(1) u by (cases t; simp; cases u; simp)+
  with new_dpair_nonAbs[OF assms(1) u] arg_res_type_base[OF T] ht hu assms(1) u show ?thesis
    by (intro exI[of _ rb]) auto
qed

lemma new_dpair_phlong:
  assumes ac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
  shows "hlong V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) t) T \<Longrightarrow>
    hlong V (map (tnorm (tyenv env)) (map snd rb)) (tnormt (tyenv env) u) T \<Longrightarrow>
    \<forall>X\<in>tys t \<union> tys u. tcons (tyenv env) X \<Longrightarrow>
    \<exists>rb'. new_dpair alg rb t u env = returnW ((rb', strip_abs_body t, strip_abs_body u), env) \<and>
      map (tnorm (tyenv env)) (map snd rb') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb) \<and>
      length rb' = length (arg_types T) + length rb \<and>
      has_type V (map (tnorm (tyenv env)) (map snd rb')) (tnormt (tyenv env) (strip_abs_body t)) (res_type T) \<and>
      has_type V (map (tnorm (tyenv env)) (map snd rb')) (tnormt (tyenv env) (strip_abs_body u)) (res_type T) \<and>
      \<not> is_Abs (strip_abs_body t) \<and> \<not> is_Abs (strip_abs_body u) \<and>
      snd ` set rb' \<subseteq> snd ` set rb \<union> tys t"
proof (induction t arbitrary: rb u T)
  case (Abs a A b)
  let ?\<theta> = "tyenv env"
  from Abs.prems(1) obtain U where T: "T = tnorm ?\<theta> A \<rightarrow>\<^sub>T U"
    and hb: "hlong V (tnorm ?\<theta> A # map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> b) U"
    by (auto elim: hlong.cases)
  have "is_Abs (tnormt ?\<theta> u)" by (rule hlong_funT_Abs[OF Abs.prems(2)]) (simp add: T)
  then obtain c A' b' where u: "u = Abs c A' b'" by (cases u) auto
  from Abs.prems(2) u T have AA: "tnorm ?\<theta> A' = tnorm ?\<theta> A"
    and hb': "hlong V (tnorm ?\<theta> A # map (tnorm ?\<theta>) (map snd rb)) (tnormt ?\<theta> b') U"
    by (auto elim: hlong.cases)
  define n where "n = (if a = STR '''' then c else a)"
  have tcA: "tcons ?\<theta> A" "tcons ?\<theta> A'" using Abs.prems(3) u by auto
  have cu: "cunify_types alg A A' env = returnW env"
    by (rule cunify_types_same_mod[OF ac tcA AA[symmetric]])
  have m: "tnorm ?\<theta> A # map (tnorm ?\<theta>) (map snd rb) = map (tnorm ?\<theta>) (map snd ((n, A) # rb))" by simp
  have "\<forall>X\<in>tys b \<union> tys b'. tcons ?\<theta> X" using Abs.prems(3) u by auto
  from Abs.IH[OF hb[unfolded m] hb'[unfolded m] this] obtain rb' where
    r: "new_dpair alg ((n, A) # rb) b b' env = returnW ((rb', strip_abs_body b, strip_abs_body b'), env)"
      "map (tnorm ?\<theta>) (map snd rb') = rev (arg_types U) @ map (tnorm ?\<theta>) (map snd ((n, A) # rb))"
      "length rb' = length (arg_types U) + length ((n, A) # rb)"
      "has_type V (map (tnorm ?\<theta>) (map snd rb')) (tnormt ?\<theta> (strip_abs_body b)) (res_type U)"
      "has_type V (map (tnorm ?\<theta>) (map snd rb')) (tnormt ?\<theta> (strip_abs_body b')) (res_type U)"
      "\<not> is_Abs (strip_abs_body b)" "\<not> is_Abs (strip_abs_body b')"
      "snd ` set rb' \<subseteq> snd ` set ((n, A) # rb) \<union> tys b"
    by blast
  have "new_dpair alg rb (Abs a A b) u env = returnW ((rb', strip_abs_body b, strip_abs_body b'), env)"
    using r(1) cu by (simp add: u n_def Let_def bindW_def returnW_def)
  with r T u show ?case by (intro exI[of _ rb']) auto
qed (rule new_dpair_phlong_base; simp)+



subsection \<open>Well-formed types of the type computations\<close>

lemma tyw_lookup:
  assumes "tinv ar n \<theta> A" "tyw ar \<theta> A (TVar v S)" "vt_lookup \<theta> v = Some (S', U)"
  shows "tyw ar \<theta> A U"
proof -
  have "uvars \<theta> U = uvars \<theta> (TVar v S)" using tinv_tacyc[OF assms(1)] assms(3) by (simp add: uvars_TVar)
  moreover have "tvars U \<subseteq> tvars_env \<theta>" by (rule tvars_envI2[OF assms(3)])
  moreover have "wft ar U" using assms(1,3) by (cases v) (auto simp: tinv_def)
  ultimately show ?thesis using assms(2) by (auto simp: tyw_def)
qed

lemma env_fastype_tyw:
  "ok (env_fastype env Ts t) T \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> \<forall>U\<in>set Ts. tyw ar (tyenv env) A U \<Longrightarrow>
    \<forall>U\<in>tys t. tyw ar (tyenv env) A U \<Longrightarrow> tyw ar (tyenv env) A T"
proof (induction env Ts t arbitrary: T rule: env_fastype.induct)
  case (1 env Ts f u)
  from "1.prems"(1) obtain T0 T' where f: "ok (env_fastype env Ts f) T0"
    and dv: "ok (devar (tyenv env) T0) T'"
    and rest: "ok (case T' of
      Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
        else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by (auto simp: bind_def split: option.splits res.splits)
  have "tyw ar (tyenv env) A T0" using "1.IH"[OF f "1.prems"(2,3)] "1.prems"(4) by simp
  then have "tyw ar (tyenv env) A T'" by (rule tyw_devar[OF "1.prems"(2) _ dv])
  with rest show ?case
    by (auto simp: return_def raise_def split: ptyp.splits list.splits if_splits intro: tyw_Type)
next
  case (4 env Ts i)
  then have "ok (nth Ts i) T" by (auto simp: ok_handle not_ok_reraise)
  with "4.prems"(3) show ?case by (auto simp: ok_nth dest!: nth_mem)
next
  case (6 env Ts uu T u)
  then show ?case by (auto simp: bind_def return_def tyw_fun split: option.splits res.splits)
qed (simp_all add: return_def)

lemma fastype_tyw:
  "ok (fastype env rb t) T \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> \<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U \<Longrightarrow>
    \<forall>U\<in>tys t. tyw ar (tyenv env) A U \<Longrightarrow> tyw ar (tyenv env) A T"
  unfolding fastype_def by (erule env_fastype_tyw) auto

lemma etif_tyw:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> tinv ar n tye A \<Longrightarrow> tyw ar tye A T \<Longrightarrow> \<forall>U\<in>tys t. tyw ar tye A U \<Longrightarrow>
    \<forall>U\<in>tys t'. tyw ar tye A U"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  show ?case
  proof (cases "\<exists>T1 U. T = Type STR ''fun'' [T1, U]")
    case True
    then obtain T1 U where T: "T = Type STR ''fun'' [T1, U]" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have wU: "tyw ar tye A T1" "tyw ar tye A U" using "1.prems"(3) T by (simp_all add: tyw_fun)
    have "\<forall>U\<in>tys (incr_boundvars 1 t $ Bound 0). tyw ar tye A U"
      using "1.prems"(4) by (simp add: incr_boundvars_def)
    from "1.IH"[OF u refl "1.prems"(2) wU(2) this] wU(1) t' show ?thesis by simp
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup tye v S) r'"
        and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by (auto simp: bind_def split: option.splits res.splits)
      from ok_type_lookup[OF lk] show ?thesis
      proof (elim disjE exE conjE)
        assume "r' = None"
        with rest "1.prems" show ?thesis by (simp add: return_def)
      next
        fix U assume U: "r' = Some U" "vt_lookup tye v = Some (S, U)"
        have e: "ef tye U t = Some (Ok t')" using rest U(1) by simp
        have "tyw ar tye A U" by (rule tyw_lookup[OF "1.prems"(2) _ U(2)]) (use "1.prems"(3) TVar in simp)
        from "1.IH"[OF e refl "1.prems"(2) this "1.prems"(4)] show ?thesis .
      qed
    next
      case (Type a Ts)
      with nf "1.hyps" "1.prems" have "t' = t"
        by (auto simp: return_def split: list.splits if_splits)
      with "1.prems" show ?thesis by simp
    qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
  qed
qed

lemma eta_norm_nonAbs_tyw:
  assumes "ok (eta_norm env rb t) t'" "\<not> is_Abs t" "tinv ar n (tyenv env) A"
    "\<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U" "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
  shows "\<forall>U\<in>tys t'. tyw ar (tyenv env) A U"
proof -
  from assms(1,2) obtain T where T: "ok (fastype env rb t) T" and e: "ok (etif (tyenv env) T t) t'"
    by (auto simp: eta_norm_nonAbs)
  have "tyw ar (tyenv env) A T" by (rule fastype_tyw[OF T assms(3-5)])
  from etif_tyw[OF e refl assms(3) this assms(5)] show ?thesis .
qed

lemma eta_norm_tyw:
  "ok (eta_norm env rb t) t' \<Longrightarrow> tinv ar n (tyenv env) A \<Longrightarrow> \<forall>U\<in>snd ` set rb. tyw ar (tyenv env) A U \<Longrightarrow>
    \<forall>U\<in>tys t. tyw ar (tyenv env) A U \<Longrightarrow> \<forall>U\<in>tys t'. tyw ar (tyenv env) A U"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rb) body) b'"
    and t': "t' = Abs a T b'" by auto
  from Abs.IH[OF b' Abs.prems(2)] Abs.prems(3,4) t' show ?case by simp
qed (erule eta_norm_nonAbs_tyw; simp)+



subsection \<open>Head normalization of disagreement pairs\<close>

lemma penv_inv_swf_env: "penv_inv alg ar W env \<Longrightarrow> swf_env ar env"
  using penv_invD(1,4)[of alg ar W env]
  by (fastforce simp: swf_env_def twf_def tinv_def pwf_env_def pwf_term_def twft_tys)

lemma inst_head_of[simp]: "head_of (inst \<rho> t) = inst \<rho> (head_of t)"
  by (induction t) auto

lemma inst_strip_abs_body[simp]: "strip_abs_body (inst \<rho> t) = inst \<rho> (strip_abs_body t)"
  by (induction t) auto

lemma vars_tnormt[simp]: "vars (tnormt \<theta> t) = vars t"
  by (induction t) auto

lemma below_tnormt[simp]: "below m (tnormt \<theta> t) \<longleftrightarrow> below m t"
  by (simp add: below_def)

lemma tnormt_VarD: "tnormt \<theta> s = Var F V \<Longrightarrow> \<exists>V'. s = Var F V' \<and> V = tnorm \<theta> V'"
  by (cases s) auto

lemma tys_strip_abs_body: "tys (strip_abs_body t) \<subseteq> tys t"
  by (induction t) auto

lemma vars_strip_abs_body[simp]: "vars (strip_abs_body t) = vars t"
  by (induction t) auto

lemma tnorm_res_type: "tnorm \<theta> T = T \<Longrightarrow> tnorm \<theta> (res_type T) = res_type T"
  by (induction T rule: res_type.induct) auto

lemma vps_inst_tnormt:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>" "\<forall>T\<in>tys t. tcons \<theta> T"
  shows "vps (inst \<rho> t) = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vps (tnormt \<theta> t)"
  using inst_tnormt[OF assms] by (metis vps_inst)

end

context wf_csig
begin

lemma head_norm_dpair_pgen:
  assumes inv: "pinv alg ar A W env [(rb, t, u)]" and g: "gsol alg ar (tyenv env) \<rho>"
  obtains rb' t' u' T where
    "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    "pinv alg ar A W env [(rb', t', u')]"
    "tnorm (tyenv env) T = T" "typed env W (map snd rb) t T"
    "map (tnorm (tyenv env)) (map snd rb') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb)"
    "typed env W (map snd rb') t' (res_type T)" "typed env W (map snd rb') u' (res_type T)"
    "\<not> is_Abs t'" "\<not> is_Abs u'" "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "vps (inst \<rho> t') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "vps (inst \<rho> u') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'" "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
proof -
  let ?\<theta> = "tyenv env"
  note pi = pinvD[OF inv]
  have sol: "tsol ?\<theta> \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  note ei = penv_invD[OF pi(1)]
  have wte: "wt_env W env" using pi(1) by (simp add: penv_inv_def)
  have swe: "swf_env ar env" by (rule penv_inv_swf_env[OF pi(1)])
  from pi(4)[of "(rb, t, u)"] obtain T0 where swd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U"
    and tyt0: "typed env W (map snd rb) t T0" and tyu0: "typed env W (map snd rb) u T0"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  define T where "T = tnorm ?\<theta> T0"
  have Tn: "tnorm ?\<theta> T = T" by (simp add: T_def tnorm_idem[OF ac(1)])
  have tyt: "typed env W (map snd rb) t T" and tyu: "typed env W (map snd rb) u T"
    using tyt0 tyu0 by (simp_all add: T_def typed_tnorm[OF ac(1)])
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  have twe: "\<forall>U\<in>etys env. tyw ar ?\<theta> A U" using pi(3) by blast
  \<comment> \<open>Head normalization\<close>
  from head_norm_pterm[OF pi(1) tyt _ pi(2) bl(1)] twd obtain t1 where ht: "head_norm env t = Some (Ok t1)"
    by auto
  from head_norm_pterm[OF pi(1) tyu _ pi(2) bl(2)] twd obtain u1 where hu: "head_norm env u = Some (Ok u1)"
    by auto
  from head_norm_ptyped[OF ht refl ac wte _ tyt] twd twe tcU
  have tyt1: "typed env W (map snd rb) t1 T" and st1: "tys t1 \<subseteq> tys t \<union> etys env" by blast+
  from head_norm_ptyped[OF hu refl ac wte _ tyu] twd twe tcU
  have tyu1: "typed env W (map snd rb) u1 T" and su1: "tys u1 \<subseteq> tys u \<union> etys env" by blast+
  have tw1: "\<forall>U\<in>tys t1. tyw ar ?\<theta> A U" "\<forall>U\<in>tys u1. tyw ar ?\<theta> A U" using st1 su1 twd twe by blast+
  have twb: "\<forall>U\<in>snd ` set rb. tyw ar ?\<theta> A U" using twd by blast
  \<comment> \<open>\<open>\<eta>\<close>-normalization, in the view with normalized types\<close>
  let ?V = "tctx env W" and ?Ts = "map (tnorm ?\<theta>) (map snd rb)"
  have nt1: "has_type ?V ?Ts (tnormt ?\<theta> t1) T" and nu1: "has_type ?V ?Ts (tnormt ?\<theta> u1) T"
    using tyt1 tyu1 Tn by (simp_all add: typed_def)
  have tc1: "\<forall>U\<in>snd ` set rb \<union> tys t1. tcons ?\<theta> U" "\<forall>U\<in>snd ` set rb \<union> tys u1. tcons ?\<theta> U"
    using tw1 twb tcU by blast+
  from eta_norm_pterm[OF ac tc1(1) nt1] obtain t2 where et: "ok (eta_norm env rb t1) t2" by blast
  from eta_norm_pterm[OF ac tc1(2) nu1] obtain u2 where eu: "ok (eta_norm env rb u1) u2" by blast
  have et0: "ok (eta_norm (env0 env) (tnormb ?\<theta> rb) (tnormt ?\<theta> t1)) (tnormt ?\<theta> t2)"
    by (rule eta_norm_tnorm[OF et ac tc1(1)])
  have eu0: "ok (eta_norm (env0 env) (tnormb ?\<theta> rb) (tnormt ?\<theta> u1)) (tnormt ?\<theta> u2)"
    by (rule eta_norm_tnorm[OF eu ac tc1(2)])
  have hlt: "hlong ?V ?Ts (tnormt ?\<theta> t2) T"
    using eta_norm_hlong[of "env0 env" ?V "tnormb ?\<theta> rb" "tnormt ?\<theta> t1" T "tnormt ?\<theta> t2"] nt1 et0 by simp
  have hlu: "hlong ?V ?Ts (tnormt ?\<theta> u2) T"
    using eta_norm_hlong[of "env0 env" ?V "tnormb ?\<theta> rb" "tnormt ?\<theta> u1" T "tnormt ?\<theta> u2"] nu1 eu0 by simp
  have tw2: "\<forall>U\<in>tys t2. tyw ar ?\<theta> A U" "\<forall>U\<in>tys u2. tyw ar ?\<theta> A U"
    using eta_norm_tyw[OF et pi(2) twb tw1(1)] eta_norm_tyw[OF eu pi(2) twb tw1(2)] by blast+
  from new_dpair_phlong[OF ac hlt hlu, of alg] tw2 tcU obtain rb' where
    nd: "new_dpair alg rb t2 u2 env = returnW ((rb', strip_abs_body t2, strip_abs_body u2), env)"
    and rb': "map (tnorm ?\<theta>) (map snd rb') = rev (arg_types T) @ ?Ts"
    and ty': "has_type ?V (map (tnorm ?\<theta>) (map snd rb')) (tnormt ?\<theta> (strip_abs_body t2)) (res_type T)"
      "has_type ?V (map (tnorm ?\<theta>) (map snd rb')) (tnormt ?\<theta> (strip_abs_body u2)) (res_type T)"
    and nA: "\<not> is_Abs (strip_abs_body t2)" "\<not> is_Abs (strip_abs_body u2)"
    and srb: "snd ` set rb' \<subseteq> snd ` set rb \<union> tys t2"
    by blast
  define t' where "t' = strip_abs_body t2"
  define u' where "u' = strip_abs_body u2"
  have hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    by (simp add: head_norm_dpair_def ht hu et eu nd t'_def u'_def)
  note snd = head_norm_dpair_ssound[OF hd swe swd]
  note shp = head_norm_dpair_pshape[OF hd swe swd]
  \<comment> \<open>Typing of the result\<close>
  have tyt': "typed env W (map snd rb') t' (res_type T)" and tyu': "typed env W (map snd rb') u' (res_type T)"
    using ty' by (simp_all add: typed_def tnorm_res_type[OF Tn] t'_def u'_def)
  have tw': "\<forall>U\<in>snd ` set rb' \<union> tys t' \<union> tys u'. tyw ar ?\<theta> A U"
  proof -
    have "\<forall>U\<in>snd ` set rb'. tyw ar ?\<theta> A U" using srb twb tw2 by blast
    then show ?thesis
      using tw2 tys_strip_abs_body[of t2] tys_strip_abs_body[of u2] by (auto simp: t'_def u'_def)
  qed
  \<comment> \<open>Ground instances of head normalization\<close>
  have tct: "\<forall>U\<in>tys t. tcons ?\<theta> U" "\<forall>U\<in>tys u. tcons ?\<theta> U" using twd tcU by blast+
  have hti: "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok (inst \<rho> t1))"
    using head_norm_pinst[OF pi(1) sol tyt tct(1) bl(1)] ht by simp
  have hui: "head_norm (instE \<rho> env) (inst \<rho> u) = Some (Ok (inst \<rho> u1))"
    using head_norm_pinst[OF pi(1) sol tyu tct(2) bl(2)] hu by simp
  note eii = env_invD[OF penv_inv_inst[OF pi(1) g]]
  have e: "vt_is_empty (tyenv (instE \<rho> env))" by simp
  have bl1: "below (maxidx env) t1" "below (maxidx env) u1"
    using below_head_norm[OF hti refl eii(2,4)] below_head_norm[OF hui refl eii(2,4)] bl by simp_all
  have r1: "vps (inst \<rho> t1) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "vps (inst \<rho> u1) \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    using hn_vps[OF head_norm_hn[OF hti e refl]] hn_vps[OF head_norm_hn[OF hui e refl]] by simp_all
  have e0: "vt_is_empty (tyenv (env0 env))" by simp
  note est = eta_norm_shape[OF et0 e0] eta_norm_shape[OF eu0 e0]
  have vt: "vps (tnormt ?\<theta> t2) = vps (tnormt ?\<theta> t1)" "vps (tnormt ?\<theta> u2) = vps (tnormt ?\<theta> u1)"
    using est by simp_all
  have tc12: "\<forall>U\<in>tys t1. tcons ?\<theta> U" "\<forall>U\<in>tys t2. tcons ?\<theta> U"
    "\<forall>U\<in>tys u1. tcons ?\<theta> U" "\<forall>U\<in>tys u2. tcons ?\<theta> U"
    using tw1 tw2 tcU by blast+
  have vi: "vps (inst \<rho> t') = vps (inst \<rho> t1)" "vps (inst \<rho> u') = vps (inst \<rho> u1)"
    using vt vps_inst_tnormt[OF ac sol tc12(1)] vps_inst_tnormt[OF ac sol tc12(2)]
      vps_inst_tnormt[OF ac sol tc12(3)] vps_inst_tnormt[OF ac sol tc12(4)]
    by (simp_all add: t'_def u'_def vps_inst)
  have bt: "below (maxidx env) t'" "below (maxidx env) u'"
  proof -
    have "vars t2 = vars t1" "vars u2 = vars u1"
      using arg_cong[OF vt(1), of "image fst"] arg_cong[OF vt(2), of "image fst"]
      by (simp_all add: vars_vps_eq[symmetric])
    then show "below (maxidx env) t'" "below (maxidx env) u'"
      using bl1 by (simp_all add: t'_def u'_def below_def)
  qed
  have "pinv alg ar A W env [(rb', t', u')]"
    using pi(1-3,5,6) snd(4) tw' tyt' tyu' bt by (auto simp: pinv_def)
  moreover have "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    using shp(3,4) nA by (simp_all add: hnf_nonAbs t'_def u'_def)
  moreover have "vt_lookup (tenv env) F = None" if "head_of t' = Var F U" for F U
  proof -
    have "head_of (strip_abs_body (tnormt ?\<theta> t2)) = Var F (tnorm ?\<theta> U)" using that by (simp add: t'_def)
    with est(1) have "head_of (strip_abs_body (tnormt ?\<theta> t1)) = Var F (tnorm ?\<theta> U)"
      unfolding head_rel_def by blast
    then have "tnormt ?\<theta> (head_of (strip_abs_body t1)) = Var F (tnorm ?\<theta> U)" by simp
    then obtain V' where "head_of (strip_abs_body t1) = Var F V'" by (blast dest: tnormt_VarD)
    then have "head_of (strip_abs_body (inst \<rho> t1)) = Var F (tsubst \<rho> V')" by simp
    from head_norm_body_head_unbound[OF hti refl e this] show ?thesis by simp
  qed
  moreover have "vt_lookup (tenv env) F = None" if "head_of u' = Var F U" for F U
  proof -
    have "head_of (strip_abs_body (tnormt ?\<theta> u2)) = Var F (tnorm ?\<theta> U)" using that by (simp add: u'_def)
    with est(2) have "head_of (strip_abs_body (tnormt ?\<theta> u1)) = Var F (tnorm ?\<theta> U)"
      unfolding head_rel_def by blast
    then have "tnormt ?\<theta> (head_of (strip_abs_body u1)) = Var F (tnorm ?\<theta> U)" by simp
    then obtain V' where "head_of (strip_abs_body u1) = Var F V'" by (blast dest: tnormt_VarD)
    then have "head_of (strip_abs_body (inst \<rho> u1)) = Var F (tsubst \<rho> V')" by simp
    from head_norm_body_head_unbound[OF hui refl e this] show ?thesis by simp
  qed
  ultimately show ?thesis
    using that[OF hd _ Tn tyt rb' tyt' tyu' nA[folded t'_def u'_def]] r1 vi snd(5,6) by simp
qed

lemma head_norm_dpair_pcomplete:
  assumes inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t, u)]"
  obtains rb' t' u' T where
    "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb', t', u')]"
    "tnorm (tyenv env) T = T" "typed env W (map snd rb) t T"
    "map (tnorm (tyenv env)) (map snd rb') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb)"
    "typed env W (map snd rb') t' (res_type T)" "typed env W (map snd rb') u' (res_type T)"
    "\<not> is_Abs t'" "\<not> is_Abs u'" "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "vps (inst \<rho> t') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "vps (inst \<rho> u') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb' t'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t)))"
proof -
  note pc = pcinvD[OF inv]
  show thesis
  proof (rule head_norm_dpair_pgen[OF pc(1) pc(2)])
  fix rb' t' u' T
  assume h: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    "pinv alg ar A W env [(rb', t', u')]"
    "tnorm (tyenv env) T = T" "typed env W (map snd rb) t T"
    "map (tnorm (tyenv env)) (map snd rb') = rev (arg_types T) @ map (tnorm (tyenv env)) (map snd rb)"
    "typed env W (map snd rb') t' (res_type T)" "typed env W (map snd rb') u' (res_type T)"
    "\<not> is_Abs t'" "\<not> is_Abs u'" "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "vps (inst \<rho> t') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
    "vps (inst \<rho> u') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'" "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
  note \<sigma> = solutionD[OF pc(3)]
  have cs: "closed_on UNIV (\<sigma> \<circ> cren \<rho>)" "sat (\<sigma> \<circ> cren \<rho>) env"
    using closed_on_cren[OF \<sigma>(1)] \<sigma>(4) by (simp_all add: sat_instE)
  have ds: "dsolved (\<sigma> \<circ> cren \<rho>) (rb, t, u)"
    using pc(4)[of "(rb, t, u)"] dsolved_instd[of \<sigma> \<rho> "(rb, t, u)"] by simp
  have eqt: "mk_subst (\<sigma> \<circ> cren \<rho>) (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma> \<circ> cren \<rho>) (tr (rlist_abs rb' t'))"
    by (rule env_equivD[OF h(16) cs])
  have equ: "mk_subst (\<sigma> \<circ> cren \<rho>) (tr (rlist_abs rb u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma> \<circ> cren \<rho>) (tr (rlist_abs rb' u'))"
    by (rule env_equivD[OF h(17) cs])
  have ds': "dsolved \<sigma> (instd \<rho> (rb', t', u'))"
    using dsolvedI[OF equiv_trans[OF equiv_trans[OF equiv_sym[OF eqt] dsolvedD[OF ds]] equ]]
      dsolved_instd[of \<sigma> \<rho> "(rb', t', u')"] by simp
  have pcf: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb', t', u')]"
    using h(2) pc(2,3) ds' by (auto simp: pcinv_def)
  have eqf: "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb' t'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t)))"
    using equiv_sym[OF eqt] by (simp add: mk_subst_inst)
  show thesis
    by (rule that[of rb' t' u' T, OF h(1) pcf h(3) h(4) h(5) h(6) h(7) h(8) h(9) h(10) h(11) h(12) h(13)
        h(14) h(15) eqf])
  qed
qed

end

end
