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
  environment.
\<close>

definition pinv :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "pinv alg ar A W env dps \<longleftrightarrow> penv_inv alg ar W env \<and> tinv ar (maxidx env) (tyenv env) A \<and>
    (\<forall>T\<in>etys env. tyw ar (tyenv env) A T) \<and>
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
  using assms by (simp_all add: pinv_def)

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

context wf_algebra
begin

text \<open>Head normalization terminates on typed terms, without an exception:\<close>

lemma head_norm_pterm:
  assumes inv: "penv_inv alg ar W env" and ty: "typed env W Ts t T"
    and tw: "\<forall>U\<in>tys t \<union> set Ts \<union> {T}. tyw ar (tyenv env) A U" and A: "tinv ar (maxidx env) (tyenv env) A"
    and bl: "below (maxidx env) t"
  obtains t' where "head_norm env t = Some (Ok t')"
proof -
  note i = penv_invD[OF inv]
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" using gsol_exists[OF A i(2)] .
  have sol: "tsol (tyenv env) \<rho>" using g by (simp add: gsol_def)
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF A] tinv_tcons_env[OF A] by simp_all
  have tc: "\<forall>U\<in>tys t \<union> set Ts \<union> {T}. tcons (tyenv env) U" using tw tyw_tcons[OF A] by blast
  note ei = env_invD[OF penv_inv_inst[OF inv g]]
  have "has_type (ityp \<rho> env W) (map (tsubst \<rho>) Ts) (inst \<rho> t) (tsubst \<rho> T)"
    by (rule typed_inst[OF ac sol _ _ ty]) (use tc in auto)
  from head_norm_term[OF ei(1-3) this] obtain t0 where "head_norm (instE \<rho> env) (inst \<rho> t) = Some (Ok t0)" by blast
  with head_norm_pinst[OF inv sol ty _ bl] tc have "instM \<rho> (inst \<rho>) (head_norm env t) = Some (Ok t0)" by simp
  then obtain r where r: "head_norm env t = Some r" "instr \<rho> (inst \<rho>) r = Ok t0" by (auto simp: instM_def)
  then obtain t' where "r = Ok t'" by (cases r) auto
  with r(1) show ?thesis by (intro that) simp
qed

end

end
