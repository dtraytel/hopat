section \<open>Problems with Type Variables: Completeness of Simplification\<close>

theory Unify_Poly_Simpl_Complete
  imports Unify_Poly_Occurs
begin

text \<open>
  The completeness of \<^const>\<open>SIMPL\<close> for problems with type variables, relative to a solution
  \<open>(\<rho>, \<sigma>)\<close> (theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Poly_Typing\<close>). The type environment
  grows only at rigid-rigid pairs whose heads are constants or free variables of different
  types; the solution \<open>\<rho>\<close> is then extended by the completeness of type unification.
\<close>


subsection \<open>Transfer of the invariant\<close>

lemma wcons_tctx: "wcons W env \<Longrightarrow> tctx env W x = tnorm (tyenv env) (W x)"
  unfolding wcons_def vtyp_def by (auto split: option.splits simp del: split_paired_All)

lemma typed_wcons:
  assumes "tacyc (tyenv env')" "textends (tyenv env) (tyenv env')" "wcons W env" "wcons W env'"
    "typed env W Ts t T"
  shows "typed env' W Ts t T"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  have "tctx env' W x = tnorm ?\<theta>' (tctx env W x)" for x
    using assms(1-4) by (simp add: wcons_tctx tnorm_textends)
  with has_type_tnormt[OF assms(5)[unfolded typed_def], of ?\<theta>'] show ?thesis
    unfolding typed_def using assms(1,2) by (simp add: comp_def tnorm_textends tnormt_textends)
qed

lemma inst_tyw_tagree:
  "tinv ar n \<theta> A \<Longrightarrow> \<forall>T\<in>tys t. tyw ar \<theta> A T \<Longrightarrow> tagree n \<rho> \<rho>' \<Longrightarrow> inst \<rho>' t = inst \<rho> t"
  by (rule inst_tagree) (auto intro: tyw_tagree)

lemma instd_tyw_tagree:
  assumes "tinv ar n \<theta> A" "\<forall>T\<in>dtys dp. tyw ar \<theta> A T" "tagree n \<rho> \<rho>'"
  shows "instd \<rho>' dp = instd \<rho> dp"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have "tsubst \<rho>' T = tsubst \<rho> T" if "T \<in> snd ` set rb" for T
    using assms dp that by (auto intro: tyw_tagree)
  then have "instb \<rho>' rb = instb \<rho> rb" by (force simp: instb_def intro!: map_cong)
  with assms dp show ?thesis by (simp add: inst_tyw_tagree)
qed


lemma below_mono: "below m t \<Longrightarrow> m \<le> m' \<Longrightarrow> below m' t"
  by (auto simp: below_def)

lemma pcinv_transfer:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' []"
    and ext: "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
  shows "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
proof -
  note pi = pinvD[OF pcinvD(1)[OF pc]] and pi' = pinvD[OF pcinvD(1)[OF pc']]
  have ac': "tacyc (tyenv env')" by (rule tinv_tacyc[OF pi'(2)])
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar (tyenv env') A T) \<and> ptyped env' W dp \<and>
      dp_below (maxidx env') dp \<and> dsolved \<sigma> (instd \<rho>' dp)" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb t u where dpe: "dp = (rb, t, u)" by (cases dp)
    from pi(4)[OF dp] dpe obtain T where w: "swf_dp ar dp" and tw: "\<forall>T\<in>dtys dp. tyw ar (tyenv env) A T"
      and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T"
      and bl: "below (maxidx env) t" "below (maxidx env) u"
      by auto
    have "ptyped env' W dp"
      using typed_wcons[OF ac' ext(1) pi(6) pi'(6) ty(1)] typed_wcons[OF ac' ext(1) pi(6) pi'(6) ty(2)] dpe
      by auto
    moreover have "\<forall>T\<in>dtys dp. tyw ar (tyenv env') A T" using tw tyw_textends[OF ac' ext(1)] by blast
    moreover have "dp_below (maxidx env') dp" using bl below_mono[OF _ ext(2)] dpe by simp
    moreover have "dsolved \<sigma> (instd \<rho>' dp)"
      using pcinvD(4)[OF pc dp] instd_tyw_tagree[OF pi(2) tw ext(3)] by simp
    ultimately show ?thesis using w by blast
  qed
  with pc' show ?thesis by (auto simp: pcinv_def pinv_def)
qed

text \<open>An extension of the type environment that keeps the bindings of the terms:\<close>

lemma pcinv_text:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and te: "tenv env' = tenv env" "textends (tyenv env) (tyenv env')" "maxidx env \<le> maxidx env'"
    and ti: "tinv ar (maxidx env') (tyenv env') A" "tsorted alg (tyenv env')"
    and g: "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
  shows "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
proof (rule pcinv_transfer[OF pc _ te(2,3) g(2)])
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'"
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  note ei = penv_invD[OF pi(1)]
  have ac': "tacyc ?\<theta>'" "tcons_env ?\<theta>'" using tinv_tacyc[OF ti(1)] tinv_tcons_env[OF ti(1)] by simp_all
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" using pcinvD(2)[OF pc] by (simp add: gsol_def)
  have sol': "tsol ?\<theta>' \<rho>'" using g(1) by (simp add: gsol_def)
  have ety: "etys env' = etys env" by (rule etys_same_tenv[OF te(1)])
  have twe: "tyw ar ?\<theta>' A T" if "T \<in> etys env'" for T
    using that ety pi(3) tyw_textends[OF ac'(1) te(2)] by blast
  have twW: "tyw ar ?\<theta>' A (W x)" for x using pi(5) tyw_textends[OF ac'(1) te(2)] by blast
  have wc: "wcons W env'"
    using pi(6) te(1) by (auto simp: wcons_def simp del: split_paired_All dest: arg_cong[of _ _ "tnorm ?\<theta>'"])
      (metis ac'(1) te(2) tnorm_textends)
  have etv: "etvars env' \<subseteq> tvars_env ?\<theta>' \<union> A"
    using pi(3) tvars_env_textends[OF te(2)] ety by (fastforce simp: etvars_def tyw_def)
  have "penv_inv alg ar W env'"
    unfolding penv_inv_def
  proof (intro conjI)
    show "tinv ar (maxidx env') ?\<theta>' (etvars env')" by (rule tinv_subset[OF ti(1) etv])
    show "tsorted alg ?\<theta>'" by (rule ti(2))
    show "nacyc env'" using ei(3) nacyc_same_tenv[OF te(1)] by simp
    show "pwf_env ar env'" using ei(4) te(1) by (simp add: pwf_env_def)
    show "wt_env W env'"
      using pi(1) wt_env_textends[OF ac'(1) te(2,1)] by (simp add: penv_inv_def)
    show "fresh_env env'" by (rule fresh_env_same[OF te(1,3) ei(6)])
  qed
  moreover have "ityp \<rho>' env' W = ityp \<rho> env W"
  proof
    fix x
    have tc: "tcons ?\<theta> (W x)" "tcons ?\<theta>' (W x)" using tyw_tcons[OF pi(2) pi(5)] tyw_tcons[OF ti(1) twW] by simp_all
    have "ityp \<rho>' env' W x = tsubst \<rho>' (W x)"
      using wcons_tctx[OF wc] tsubst_tnorm[OF ac' sol' tc(2)] by simp
    also have "\<dots> = tsubst \<rho> (W x)" by (rule tyw_tagree[OF pi(2) pi(5) g(2)])
    also have "\<dots> = ityp \<rho> env W x"
      using wcons_tctx[OF pi(6)] tsubst_tnorm[OF ac sol tc(1)] by simp
    finally show "ityp \<rho>' env' W x = ityp \<rho> env W x" .
  qed
  moreover have "vt_lookup (tenv (instE \<rho>' env')) x = vt_lookup (tenv (instE \<rho> env)) x" for x
  proof (cases "vt_lookup (tenv env) x")
    case (Some p)
    then obtain U u where b: "vt_lookup (tenv env) x = Some (U, u)" by (cases p) auto
    have "insert U (tys u) \<subseteq> etys env" by (rule etysI[OF b])
    then have "tsubst \<rho>' U = tsubst \<rho> U" "inst \<rho>' u = inst \<rho> u"
      using pi(3) by (auto intro: tyw_tagree[OF pi(2) _ g(2)] inst_tyw_tagree[OF pi(2) _ g(2)])
    then show ?thesis using b te(1) by simp
  qed (simp add: te(1))
  then have "sat \<sigma> (instE \<rho>' env') \<longleftrightarrow> sat \<sigma> (instE \<rho> env)" by (simp add: sat_def)
  ultimately show "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' []"
    using pcinvD(3)[OF pc] ti(1) twe twW wc g(1)
    by (auto simp: pcinv_def pinv_def solution_def simp del: split_paired_All)
qed



subsection \<open>Results of simplification steps\<close>

text \<open>Shapes of the collected pairs; they are stable under extensions of the type environment.\<close>

definition pff_shape :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "pff_shape env W dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<exists>B. typed env W (map snd rb) t B \<and> typed env W (map snd rb) u B) \<and>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> is_Var (head_of u))"

definition pfr_shape :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "pfr_shape env W dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<exists>B. typed env W (map snd rb) t B \<and> typed env W (map snd rb) u B) \<and>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> is_rigid (head_of u))"

lemma pff_shape_wcons:
  "pff_shape env W dp \<Longrightarrow> tacyc (tyenv env') \<Longrightarrow> textends (tyenv env) (tyenv env') \<Longrightarrow>
    wcons W env \<Longrightarrow> wcons W env' \<Longrightarrow> pff_shape env' W dp"
  by (cases dp) (auto simp: pff_shape_def dest: typed_wcons)

lemma pfr_shape_wcons:
  "pfr_shape env W dp \<Longrightarrow> tacyc (tyenv env') \<Longrightarrow> textends (tyenv env) (tyenv env') \<Longrightarrow>
    wcons W env \<Longrightarrow> wcons W env' \<Longrightarrow> pfr_shape env' W dp"
  by (cases dp) (auto simp: pfr_shape_def dest: typed_wcons)

text \<open>
  The flexible heads of a term are applied to as many arguments as their arity in the type
  environment \<open>\<theta>\<close> (\<open>hsat\<close>). The flex-flex pairs are saturated in the type environments of their
  classification, which grow from the end of the list to its front (\<open>fch\<close>): later type
  bindings may increase the arities.
\<close>

definition hsat :: "tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> bool" where
  "hsat \<theta> W s \<longleftrightarrow>
    (\<forall>X U. head_of s = Var X U \<longrightarrow> length (snd (strip_comb s)) = length (arg_types (tnorm \<theta> (W X))))"

fun fch :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> tyenv \<Rightarrow> tyenv \<Rightarrow> dpair list \<Rightarrow> bool" where
  "fch W \<theta> \<theta>0 [] \<longleftrightarrow> textends \<theta>0 \<theta>"
| "fch W \<theta> \<theta>0 ((rb, t, u) # dps) \<longleftrightarrow>
    (\<exists>\<theta>'. tacyc \<theta>' \<and> textends \<theta>' \<theta> \<and> hsat \<theta>' W t \<and> hsat \<theta>' W u \<and> fch W \<theta>' \<theta>0 dps)"

lemma fch_up: "fch W \<theta> \<theta>0 dps \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> fch W \<theta>' \<theta>0 dps"
  by (cases "(W, \<theta>, \<theta>0, dps)" rule: fch.cases) (auto intro: textends_trans)

lemma fch_down: "fch W \<theta> \<theta>1 dps \<Longrightarrow> textends \<theta>0 \<theta>1 \<Longrightarrow> fch W \<theta> \<theta>0 dps"
  by (induction W \<theta> \<theta>1 dps rule: fch.induct) (auto intro: textends_trans)

lemma fch_append: "fch W \<theta>2 \<theta>1 xs \<Longrightarrow> fch W \<theta>1 \<theta>0 ys \<Longrightarrow> fch W \<theta>2 \<theta>0 (xs @ ys)"
  by (induction W \<theta>2 \<theta>1 xs rule: fch.induct) (auto intro: fch_up)

lemma typed_hsat:
  assumes "typed env W Ts t B" "\<not> is_funT (tnorm (tyenv env) B)" "wcons W env"
  shows "hsat (tyenv env) W t"
  unfolding hsat_def
proof (intro allI impI)
  fix X U assume h: "head_of t = Var X U"
  let ?\<theta> = "tyenv env" and ?as = "snd (strip_comb t)"
  have "t = list_comb (Var X U) ?as" using head_of_list_comb[of t] h by simp
  with assms(1) have "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (list_comb (Var X (tnorm ?\<theta> U))
      (map (tnormt ?\<theta>) ?as)) (tnorm ?\<theta> B)"
    by (metis typed_def tnormt_list_comb tnormt.simps(3))
  then obtain Us where "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (Var X (tnorm ?\<theta> U))
      (foldr fun_type Us (tnorm ?\<theta> B))" "length Us = length ?as"
    by (auto simp: has_type_list_comb dest: list_all2_lengthD)
  then have "tnorm ?\<theta> (W X) = foldr fun_type Us (tnorm ?\<theta> B)" "length Us = length ?as"
    using wcons_tctx[OF assms(3)] by (auto elim: has_type_elims)
  then show "length ?as = length (arg_types (tnorm ?\<theta> (W X)))" using arg_res_type_fun[OF assms(2)] by simp
qed

text \<open>The variables of the instances of pairs:\<close>

abbreviation ivps :: "tinst \<Rightarrow> dpair list \<Rightarrow> (indexname \<times> ptyp) set" where
  "ivps \<rho> dps \<equiv> vps_dps (map (instd \<rho>) dps)"

text \<open>
  The result of simplifying the pairs \<open>dps\<close> in state \<open>(env, ffs, frs)\<close>, with the solution
  \<open>\<rho>\<close> of the type environment, is the state \<open>(env', ffs', frs')\<close>, with the solution \<open>\<rho>'\<close>: new
  pairs are added in front, the invariant holds, \<open>\<rho>'\<close> extends \<open>\<rho>\<close>, and the bindings of the
  instance only make variables reachable that were reachable from the instance of \<open>dps\<close>.
\<close>

definition psres :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> dpair list \<Rightarrow> sstate \<Rightarrow> tinst \<Rightarrow> sstate \<Rightarrow> bool" where
  "psres alg ar A W \<tau>' \<sigma> \<rho> dps st \<rho>' st' \<longleftrightarrow> (case (st, st') of ((env, ffs, frs), (env', ffs', frs')) \<Rightarrow>
    \<exists>ffn frn. ffs' = ffn @ ffs \<and> frs' = frn @ frs \<and> pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn) \<and>
      pextends env' env \<and> maxidx env \<le> maxidx env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      (\<forall>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)) \<and>
      ivps \<rho>' (ffn @ frn) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps) \<and>
      (\<forall>dp\<in>set ffn. pff_shape env' W dp) \<and> (\<forall>dp\<in>set frn. pfr_shape env' W dp) \<and>
      (\<forall>dp\<in>set (ffn @ frn). heads_unb env dp) \<and> fch W (tyenv env') (tyenv env) ffn)"

lemma psresD:
  assumes "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' st'"
  obtains env' ffn frn where "st' = (env', ffn @ ffs, frn @ frs)" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn)"
    "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    "ivps \<rho>' (ffn @ frn) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
  using assms by (cases st') (auto simp: psres_def)

lemma psresI:
  assumes "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn)"
    "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    "ivps \<rho>' (ffn @ frn) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
  shows "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' (env', ffn @ ffs, frn @ frs)"
  using assms by (auto simp: psres_def)

lemma pcinv_Nil: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env []"
  by (simp add: pcinv_def pinv_def)

lemma psres_refl:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [] \<Longrightarrow> psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho> (env, ffs, frs)"
  using psresI[of alg ar A W \<rho> \<tau>' \<sigma> env "[]" "[]" env \<rho> dps ffs frs] reach_subset[of _ _ "instE \<rho> env"]
  by auto

lemma ivps_tagree:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" "tagree (maxidx env) \<rho> \<rho>'"
  shows "map (instd \<rho>') dps = map (instd \<rho>) dps"
proof -
  note pi = pinvD[OF pcinvD(1)[OF assms(1)]]
  show ?thesis using instd_tyw_tagree[OF pi(2) _ assms(2)] pi(4) by auto
qed

lemma psres_trans:
  assumes "psres alg ar A W \<tau>' \<sigma> \<rho> dps1 (env, ffs, frs) \<rho>1 st1" "psres alg ar A W \<tau>' \<sigma> \<rho>1 dps2 st1 \<rho>2 st2"
    and same: "map (instd \<rho>1) dps2 = map (instd \<rho>) dps2"
  shows "psres alg ar A W \<tau>' \<sigma> \<rho> (dps1 @ dps2) (env, ffs, frs) \<rho>2 st2"
proof -
  from psresD[OF assms(1)] obtain env1 ffn1 frn1 where s1: "st1 = (env1, ffn1 @ ffs, frn1 @ frs)"
    "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (ffn1 @ frn1)" "pextends env1 env" "maxidx env \<le> maxidx env1"
    "tagree (maxidx env) \<rho> \<rho>1"
    "\<And>X. reach (instE \<rho>1 env1) X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps1)"
    "ivps \<rho>1 (ffn1 @ frn1) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps1)"
    "\<And>dp. dp \<in> set ffn1 \<Longrightarrow> pff_shape env1 W dp" "\<And>dp. dp \<in> set frn1 \<Longrightarrow> pfr_shape env1 W dp"
    "\<And>dp. dp \<in> set (ffn1 @ frn1) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env1) (tyenv env) ffn1"
    by blast
  from psresD[OF assms(2)[unfolded s1(1)]] obtain env2 ffn2 frn2 where
    s2: "st2 = (env2, ffn2 @ ffn1 @ ffs, frn2 @ frn1 @ frs)"
    "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 (ffn2 @ frn2)" "pextends env2 env1" "maxidx env1 \<le> maxidx env2"
    "tagree (maxidx env1) \<rho>1 \<rho>2"
    "\<And>X. reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho>1 env1) (X \<union> ivps \<rho>1 dps2)"
    "ivps \<rho>2 (ffn2 @ frn2) \<subseteq> reach (instE \<rho>1 env1) (ivps \<rho>1 dps2)"
    "\<And>dp. dp \<in> set ffn2 \<Longrightarrow> pff_shape env2 W dp" "\<And>dp. dp \<in> set frn2 \<Longrightarrow> pfr_shape env2 W dp"
    "\<And>dp. dp \<in> set (ffn2 @ frn2) \<Longrightarrow> heads_unb env1 dp" "fch W (tyenv env2) (tyenv env1) ffn2"
    by blast
  have i2: "ivps \<rho>1 dps2 = ivps \<rho> dps2" using same by simp
  have r: "reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> (dps1 @ dps2))" for X
  proof -
    have "reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho>1 env1) (X \<union> ivps \<rho> dps2)" using s2(6) i2 by simp
    also have "\<dots> \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps2 \<union> ivps \<rho> dps1)" by (rule s1(6))
    finally show ?thesis by (auto simp: Un_ac)
  qed
  note pi1 = pinvD[OF pcinvD(1)[OF s1(2)]] and pi2 = pinvD[OF pcinvD(1)[OF s2(2)]]
  have ac2: "tacyc (tyenv env2)" by (rule tinv_tacyc[OF pi2(2)])
  have te: "textends (tyenv env1) (tyenv env2)" using s2(3) by (simp add: pextends_def)
  have c1: "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 (ffn1 @ frn1)"
    by (rule pcinv_transfer[OF s1(2) pcinv_Nil[OF s2(2)] te s2(4,5)])
  have c: "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 ((ffn2 @ ffn1) @ frn2 @ frn1)"
    using c1 s2(2) by (auto simp: pcinv_def pinv_def)
  have i1: "ivps \<rho>2 (ffn1 @ frn1) = ivps \<rho>1 (ffn1 @ frn1)"
    using ivps_tagree[OF s1(2) s2(5)] by simp
  have vv: "ivps \<rho>2 ((ffn2 @ ffn1) @ frn2 @ frn1) \<subseteq> reach (instE \<rho> env) (ivps \<rho> (dps1 @ dps2))"
  proof -
    have "ivps \<rho>2 (ffn2 @ frn2) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps2 \<union> ivps \<rho> dps1)"
      using s2(7) i2 s1(6)[of "ivps \<rho> dps2"] by auto
    moreover have "ivps \<rho>2 (ffn1 @ frn1) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps2 \<union> ivps \<rho> dps1)"
      using s1(7) i1 reach_subset[of "ivps \<rho> dps1" "ivps \<rho> dps2 \<union> ivps \<rho> dps1" "instE \<rho> env"] by auto
    ultimately show ?thesis by (auto simp: Un_ac)
  qed
  have ex: "pextends env2 env" using s2(3) s1(3) by (rule pextends_trans)
  have mx: "maxidx env \<le> maxidx env2" using s1(4) s2(4) by simp
  have ag: "tagree (maxidx env) \<rho> \<rho>2" using tagree_trans[OF s1(5) s2(5) s1(4)] .
  have ffh: "pff_shape env2 W dp" if "dp \<in> set (ffn2 @ ffn1)" for dp
    using that s2(8) s1(8) pff_shape_wcons[OF _ ac2 te pi1(6) pi2(6)] by (metis Un_iff set_append)
  have frh: "pfr_shape env2 W dp" if "dp \<in> set (frn2 @ frn1)" for dp
    using that s2(9) s1(9) pfr_shape_wcons[OF _ ac2 te pi1(6) pi2(6)] by (metis Un_iff set_append)
  have hh: "heads_unb env dp" if "dp \<in> set ((ffn2 @ ffn1) @ frn2 @ frn1)" for dp
    using that s1(10) s2(10) heads_unb_extends[OF _ pextendsD(1)[OF s1(3)]] by (metis Un_iff set_append)
  have "psres alg ar A W \<tau>' \<sigma> \<rho> (dps1 @ dps2) (env, ffs, frs) \<rho>2
      (env2, (ffn2 @ ffn1) @ ffs, (frn2 @ frn1) @ frs)"
    by (rule psresI[OF c ex mx ag r vv ffh frh hh fch_append[OF s2(11) s1(11)]])
  then show ?thesis using s2(1) by simp
qed

lemma psres_mono_dps:
  assumes "psres alg ar A W \<tau>' \<sigma> \<rho> dps' (env, ffs, frs) \<rho>' st'"
    "ivps \<rho> dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
  shows "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' st'"
proof -
  let ?e = "instE \<rho> env"
  have m: "reach ?e (X \<union> ivps \<rho> dps') \<subseteq> reach ?e (X \<union> ivps \<rho> dps)" for X
    using assms(2) by (intro reach_mono) (auto intro: set_mp[OF reach_incl] set_mp[OF reach_subset])
  have m': "reach ?e (ivps \<rho> dps') \<subseteq> reach ?e (ivps \<rho> dps)"
    using assms(2) by (rule reach_mono)
  from psresD[OF assms(1)] obtain env' ffn frn where s: "st' = (env', ffn @ ffs, frn @ frs)"
    "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn)" "pextends env' env" "maxidx env \<le> maxidx env'"
    "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach ?e (X \<union> ivps \<rho> dps')"
    "ivps \<rho>' (ffn @ frn) \<subseteq> reach ?e (ivps \<rho> dps')"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env') (tyenv env) ffn"
    by blast
  have "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' (env', ffn @ ffs, frn @ frs)"
  proof (rule psresI[OF s(2-5) _ _ s(8-11)])
    show "reach (instE \<rho>' env') X \<subseteq> reach ?e (X \<union> ivps \<rho> dps)" for X using s(6)[of X] m[of X] by blast
    show "ivps \<rho>' (ffn @ frn) \<subseteq> reach ?e (ivps \<rho> dps)" using s(7) m' by blast
  qed
  with s(1) show ?thesis by simp
qed


text \<open>The arguments of rigid-rigid pairs with equal heads.\<close>

lemma simrands_pcomplete:
  assumes F: "\<And>i st \<rho>a. i < length as \<Longrightarrow> pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) [] \<Longrightarrow>
      pextends (fst st) eo \<Longrightarrow> maxidx eo \<le> maxidx (fst st) \<Longrightarrow> tagree (maxidx eo) \<rho>o \<rho>a \<Longrightarrow>
      \<exists>st' \<rho>b. okW (F (rb, as ! i, bs ! i) st) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho>a [(rb, as ! i, bs ! i)] st \<rho>b st'"
    and h: "\<nexists>f u. h = f $ u" "\<nexists>f u. h' = f $ u"
    and same: "\<And>\<rho>'. tagree (maxidx eo) \<rho>o \<rho>' \<Longrightarrow>
      map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) = map (instd \<rho>o) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs))"
  shows "length as = length bs \<Longrightarrow> pcinv alg ar A W \<rho>1 \<tau>' \<sigma> (fst st) [] \<Longrightarrow> pextends (fst st) eo \<Longrightarrow>
    maxidx eo \<le> maxidx (fst st) \<Longrightarrow> tagree (maxidx eo) \<rho>o \<rho>1 \<Longrightarrow>
    \<exists>st' \<rho>2. okW (simrands F rb u0 (list_comb h as) (list_comb h' bs) st) st' \<and>
      psres alg ar A W \<tau>' \<sigma> \<rho>1 (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) st \<rho>2 st'"
  using F same
proof (induction as arbitrary: bs st \<rho>1 rule: rev_induct)
  case Nil
  then have "bs = []" by simp
  moreover have "simrands F rb u0 h h' st = returnW st" using h by (cases h; cases h') simp_all
  ultimately show ?case using psres_refl[OF Nil.prems(2)] by (cases st) auto
next
  case (snoc a as)
  obtain env1 ffs1 frs1 where st: "st = (env1, ffs1, frs1)" by (cases st)
  from snoc.prems(1) obtain b bs' where bs: "bs = bs' @ [b]" "length as = length bs'"
    by (metis length_Suc_conv_rev)
  have zs: "map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs) =
      map (\<lambda>(a, b). (rb, a, b)) (zip as bs') @ [(rb, a, b)]"
    using bs by simp
  have F': "\<exists>st' \<rho>2. okW (F (rb, as ! i, bs' ! i) st) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho>1 [(rb, as ! i, bs' ! i)] st \<rho>2 st'"
    if "i < length as" "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> (fst st) []" "pextends (fst st) eo"
      "maxidx eo \<le> maxidx (fst st)" "tagree (maxidx eo) \<rho>o \<rho>1" for i st \<rho>1
    using snoc.prems(6)[where i = i and st = st and \<rho>a = \<rho>1] that bs by (simp add: nth_append)
  have sameL: "map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) @ [instd \<rho>' (rb, a, b)] =
      map (instd \<rho>o) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) @ [instd \<rho>o (rb, a, b)]"
    if "tagree (maxidx eo) \<rho>o \<rho>'" for \<rho>'
    using snoc.prems(7)[OF that] unfolding zs by simp
  have same': "map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) =
      map (instd \<rho>o) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs'))"
    and samel: "instd \<rho>' (rb, a, b) = instd \<rho>o (rb, a, b)"
    if "tagree (maxidx eo) \<rho>o \<rho>'" for \<rho>'
    using sameL[OF that] by (simp_all only: append1_eq_conv)
  from snoc.IH[OF bs(2) snoc.prems(2-5) F' same'] obtain st1 \<rho>1' where
    r1: "okW (simrands F rb u0 (list_comb h as) (list_comb h' bs') st) st1"
      "psres alg ar A W \<tau>' \<sigma> \<rho>1 (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) st \<rho>1' st1"
    by blast
  from psresD[OF r1(2)[unfolded st]] obtain env2 ffn frn where
    s1: "st1 = (env2, ffn @ ffs1, frn @ frs1)" "pcinv alg ar A W \<rho>1' \<tau>' \<sigma> env2 (ffn @ frn)"
      "pextends env2 env1" "maxidx env1 \<le> maxidx env2" "tagree (maxidx env1) \<rho>1 \<rho>1'"
    by blast
  have c1: "pcinv alg ar A W \<rho>1' \<tau>' \<sigma> (fst st1) []" using pcinv_Nil[OF s1(2)] s1(1) by simp
  have e1: "pextends (fst st1) eo" using pextends_trans[OF s1(3)] snoc.prems(3) st s1(1) by simp
  have m1: "maxidx eo \<le> maxidx (fst st1)" using snoc.prems(4) s1(1,4) st by simp
  have a1: "tagree (maxidx eo) \<rho>o \<rho>1'"
    using tagree_trans[OF snoc.prems(5) s1(5)] snoc.prems(4) st by simp
  from snoc.prems(6)[where i = "length as" and st = st1 and \<rho>a = \<rho>1'] c1 e1 m1 a1 bs obtain st2 \<rho>2 where
    r2: "okW (F (rb, a, b) st1) st2" "psres alg ar A W \<tau>' \<sigma> \<rho>1' [(rb, a, b)] st1 \<rho>2 st2"
    by (auto simp: nth_append)
  have sm: "map (instd \<rho>1') [(rb, a, b)] = map (instd \<rho>1) [(rb, a, b)]"
    using samel[OF a1] samel[OF snoc.prems(5)] by simp
  have "okW (simrands F rb u0 (list_comb h (as @ [a])) (list_comb h' bs) st) st2"
    using r1(1) r2(1) bs by (cases st1) (fastforce simp: list_comb_snoc)
  moreover have "psres alg ar A W \<tau>' \<sigma> \<rho>1 (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st \<rho>2 st2"
    using psres_trans[OF r1(2)[unfolded st] r2(2) sm] zs st by simp
  ultimately show ?case by blast
qed



subsection \<open>Assignments\<close>

lemma get_eta_var_pinst:
  "get_eta_var rb n t = returnW (v, T) \<Longrightarrow> get_eta_var (instb \<rho> rb) n (inst \<rho> t) = returnW (v, tsubst \<rho> T)"
  by (induction rb n t rule: get_eta_var.induct) (auto simp: returnW_def raiseW_def split: if_splits)

lemma get_eta_var_ptnorm:
  "get_eta_var rb n t = returnW (v, T) \<Longrightarrow> get_eta_var (tnormb \<theta> rb) n (tnormt \<theta> t) = returnW (v, tnorm \<theta> T)"
  by (induction rb n t rule: get_eta_var.induct) (auto simp: returnW_def raiseW_def split: if_splits)

lemma get_eta_var_head: "get_eta_var rb n t = returnW (v, T) \<Longrightarrow> head_of t = Var v T"
  by (induction rb n t rule: get_eta_var.induct) (auto simp: returnW_def raiseW_def split: if_splits)

lemma tnormt_rlist_abs: "tnormt \<theta> (rlist_abs rb t) = rlist_abs (tnormb \<theta> rb) (tnormt \<theta> t)"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma tys_rlist_abs: "tys (rlist_abs rb t) = snd ` set rb \<union> tys t"
  by (induction rb t rule: rlist_abs.induct) auto

lemma is_rigid_inst[simp]: "is_rigid (inst \<rho> h) \<longleftrightarrow> is_rigid h"
  by (cases h) (auto simp: is_rigid_def)

lemma fresh_env_instE[simp]: "fresh_env (instE \<rho> env) \<longleftrightarrow> fresh_env env"
  unfolding fresh_env_def
proof (intro iffI allI impI)
  fix x U u
  assume H: "\<forall>x U u. vt_lookup (tenv (instE \<rho> env)) x = Some (U, u) \<longrightarrow> snd x \<le> maxidx (instE \<rho> env) \<and>
      below (maxidx (instE \<rho> env)) u"
    and b: "vt_lookup (tenv env) x = Some (U, u)"
  from H[rule_format, of x "tsubst \<rho> U" "inst \<rho> u"] b show "snd x \<le> maxidx env \<and> below (maxidx env) u" by simp
next
  fix x U u
  assume H: "\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<le> maxidx env \<and> below (maxidx env) u"
    and b: "vt_lookup (tenv (instE \<rho> env)) x = Some (U, u)"
  from b obtain U0 u0 where "vt_lookup (tenv env) x = Some (U0, u0)" "u = inst \<rho> u0" by auto
  with H[rule_format, of x U0 u0] show "snd x \<le> maxidx (instE \<rho> env) \<and> below (maxidx (instE \<rho> env)) u"
    by simp
qed

lemma snd_nth_tnormb[simp]: "k < length rb \<Longrightarrow> snd (tnormb \<theta> rb ! k) = tnorm \<theta> (snd (rb ! k))"
  by (simp add: tnormb_def case_prod_beta)

lemma length_tnormb[simp]: "length (tnormb \<theta> rb) = length rb"
  by (simp add: tnormb_def)

text \<open>
  \<^const>\<open>assignment\<close> on a flex-rigid pair of a base type solved by the instance, whose flexible
  head is unbound: it gives up with \<open>ASSIGN\<close>, or it binds the variable and keeps the solution,
  without changing the type environment. The ground instance need not be \<open>\<eta>\<close>-long, so the
  monomorphic result does not apply as a whole; its parts do.
\<close>

lemma assignment_pcomplete:
  assumes inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t, u)]"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
      "\<not> is_funT B"
    and xu: "\<And>x T. head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None"
    and hu: "is_rigid (head_of u)"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>env'. okW (assignment alg rb t u env) env' \<and> pcinv alg ar A W \<rho> \<tau>' \<sigma> env' [] \<and> pextends env' env \<and>
      tyenv env' = tyenv env \<and> maxidx env' = maxidx env \<and>
      (\<forall>X. reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> u))))"
proof -
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W"
  note pc = pcinvD[OF inv]
  note pi = pinvD[OF pc(1)]
  note ei = penv_invD[OF pi(1)]
  have sol: "tsol ?\<theta> \<rho>" using pc(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  from pi(4)[of "(rb, t, u)"] have swd: "swf_dp ar (rb, t, u)"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note ci = pcinv_cinv[OF inv]
  note eii = env_invD[OF cinvD(1)[OF ci]]
  note isol = cinvD(2)[OF ci]
  have dsi: "dsolved \<sigma> (instb \<rho> rb, inst \<rho> t, inst \<rho> u)" using cinvD(3)[OF ci] by simp
  have tcB: "tcons ?\<theta> B" using tcons_tnorm[OF ac(1), of B] ty(3) by simp
  have tct: "\<forall>U\<in>set (map snd rb) \<union> tys t. tcons ?\<theta> U" and tcu: "\<forall>U\<in>set (map snd rb) \<union> tys u. tcons ?\<theta> U"
    using twd tcU by auto
  have tyi: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> t) (tsubst \<rho> B)"
    "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> u) (tsubst \<rho> B)"
    using typed_inst[OF ac sol tct tcB ty(1)] typed_inst[OF ac sol tcu tcB ty(2)] by (simp_all add: map_snd_instb)
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: assignment_def bindW_def raiseW_def)
  next
    case 2
    then have gev: "okW (get_eta_var rb 0 t) (v, T)" by (simp add: returnW_def)
    have gevi: "okW (get_eta_var (instb \<rho> rb) 0 (inst \<rho> t)) (v, tsubst \<rho> T)"
      using get_eta_var_pinst[OF 2] by (simp add: returnW_def)
    have gevn: "okW (get_eta_var (tnormb ?\<theta> rb) 0 (tnormt ?\<theta> t)) (v, tnorm ?\<theta> T)"
      using get_eta_var_ptnorm[OF 2] by (simp add: returnW_def)
    have nt: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> t) B"
      and nu: "has_type (tctx env W) (map snd (tnormb ?\<theta> rb)) (tnormt ?\<theta> u) B"
      using ty(1-3) by (simp_all add: typed_def)
    from get_eta_var_type[OF gevn _ nt] have Tn: "tnorm ?\<theta> T = foldr fun_type (rev (map snd (tnormb ?\<theta> rb))) B"
      and Vv: "tctx env W v = tnorm ?\<theta> T"
      by simp_all
    have ht: "head_of t = Var v T" by (rule get_eta_var_head[OF 2])
    have vu: "vt_lookup (tenv env) v = None" by (rule xu[OF ht])
    have tT: "T \<in> tys t" using vps_tys[OF vps_head_of[OF ht]] by simp
    have twT: "tyw ar ?\<theta> A T" and tcT: "tcons ?\<theta> T" using twd tT tcU by auto
    have Vvi: "?V v = tsubst \<rho> T" using Vv tsubst_tnorm[OF ac sol tcT] by simp
    have tyok: "tyok env" by (rule tyok_tinv[OF pi(2)])
    have lkd: "lkdec \<rho> env (vps u \<union> bvps env)"
      by (rule hyp_lkdec[OF typed_hyp[OF pi(1) sol ty(2) _ bl(2)]]) (use tcu in auto)
    from rigid_occurs_term_terminates[OF eii(1,2,3) has_type_vtyped[OF tyi(2)], of v] obtain oci
      where oci: "rigid_occurs_term (instE \<rho> env) v (inst \<rho> u) = return oci" by blast
    from rigid_occurs_term_pinst[OF oci[unfolded return_def] tyok lkd] obtain r
      where "rigid_occurs_term env v u = Some r" "Ok oci = instr \<rho> id r" by blast
    then have oc: "rigid_occurs_term env v u = return oci" by (cases r) (auto simp: return_def)
    show ?thesis
    proof (cases oci)
      case Rigid
      have "ok (rigid_occurs_term (instE \<rho> env) v (inst \<rho> u)) Rigid" using oci Rigid by (simp add: return_def)
      moreover have "vt_lookup (tenv (instE \<rho> env)) v = None" using vu by simp
      moreover have "hrig (instE \<rho> env) (inst \<rho> u)" by (rule hrig_rigid) (simp add: hu)
      ultimately have False
        using rigid_occurs_unsolvable[OF gevi _ eii(2,3) isol _ tyi(1,2) _ dsi] by blast
      then show ?thesis ..
    next
      case Nonrigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case NoOcc
      from body_type_ptnorm[OF ac tcT Tn ty(4)] obtain B1 where bt: "body_type env T = return B1"
        and B1: "tnorm ?\<theta> B1 = B" "tcons ?\<theta> B1" by blast
      from env_fastype_pterm[OF ac tcu] nu obtain T2 where
        ft0: "ok (env_fastype env (map snd rb) u) T2" "tnorm ?\<theta> T2 = B" by auto
      have ft: "ok (fastype env rb u) T2" using ft0 by (simp add: fastype_def)
      have tcT2: "tcons ?\<theta> T2" using fastype_tnorm[OF ac ft] tcu by auto
      have cu: "cunify_types alg B1 T2 env = returnW env"
        by (rule cunify_types_same_mod[OF ac B1(2) tcT2]) (simp add: B1(1) ft0(2))
      from update_unbound_ok[OF vu, of T "rlist_abs rb u"] obtain env' where
        upd: "update (v, T) (rlist_abs rb u) env = Some (Ok env')" by blast
      have ok: "okW (assignment alg rb t u env) env'"
        using 2 oc NoOcc bt ft cu upd by (simp add: assignment_def return_def)
      note up = ok_update[OF upd]
      have updi: "ok (update (v, tsubst \<rho> T) (inst \<rho> (rlist_abs rb u)) (instE \<rho> env)) (instE \<rho> env')"
        using update_inst[of v \<rho> T "rlist_abs rb u" env] upd by simp
      have eqv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb u)))"
      proof -
        have "mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (dB.Var (code (AVar v)))"
          using mk_subst_equiv[OF conjunct1[OF get_eta_var_equiv[OF gevi]] solutionD(1)[OF isol]] .
        then have "mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> t))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))" by simp
        from equiv_trans[OF equiv_sym[OF this] dsolvedD[OF dsi]] show ?thesis by (simp add: inst_rlist_abs)
      qed
      have tyrl: "typed env W [] (rlist_abs rb u) T"
      proof -
        have "has_type (tctx env W) (map snd (tnormb ?\<theta> rb) @ []) (tnormt ?\<theta> u) B" using nu by simp
        from has_type_rlist_abs[OF this] Tn show ?thesis by (simp add: typed_def tnormt_rlist_abs)
      qed
      have twr: "\<forall>U\<in>tys (rlist_abs rb u). tyw ar ?\<theta> A U" using twd by (auto simp: tys_rlist_abs)
      have tcr: "\<forall>U\<in>set [] \<union> tys (rlist_abs rb u). tcons ?\<theta> U" using twr tcU by auto
      have tyr: "has_type ?V [] (inst \<rho> (rlist_abs rb u)) (tsubst \<rho> T)"
        using typed_inst[OF ac sol tcr tcT tyrl] by simp
      have Fm: "snd v \<le> maxidx (instE \<rho> env)" using below_vps[OF bl(1) vps_head_of[OF ht]] by simp
      have tm: "below (maxidx (instE \<rho> env)) (inst \<rho> (rlist_abs rb u))" using bl(2) by (simp add: below_rlist_abs)
      note su = solution_update[OF isol eii(4) eii(3) updi eqv Vvi tyr Fm tm]
      have acy: "acyc (instE \<rho> env')"
      proof -
        note upi = ok_update[OF updi]
        have d: "dep (instE \<rho> env') = dep (instE \<rho> env) \<union>
            (\<lambda>y. (y, (v, tsubst \<rho> T))) ` vps (inst \<rho> (rlist_abs rb u))"
          by (rule dep_update[OF upi(2,1)])
        have "ok (rigid_occurs_term (instE \<rho> env) v (inst \<rho> u)) NoOcc" using oci NoOcc by (simp add: return_def)
        from rigid_occurs_term_complete[OF this _ eii(1)]
        have "(v, tsubst \<rho> T) \<notin> reach (instE \<rho> env) (vps (inst \<rho> (rlist_abs rb u)))"
          by (auto simp: occ_in_def vps_rlist_abs inst_rlist_abs)
        from acyclic_update[OF d this] eii(1) show ?thesis by (simp add: acyc_def)
      qed
      have lk': "vt_lookup (tenv env') x = (if x = v then Some (T, rlist_abs rb u) else vt_lookup (tenv env) x)"
        for x using up(2) by simp
      have te': "tyenv env' = tyenv env" "maxidx env' = maxidx env" using up(3,4) by simp_all
      have wc': "wcons W env'"
        using pi(6) Vv wcons_tctx[OF pi(6), of v] te'(1) unfolding wcons_def
        by (auto simp: lk' simp del: split_paired_All)
      have tctx': "tctx env' W x = tctx env W x" for x
        using wcons_tctx[OF wc'] wcons_tctx[OF pi(6)] te'(1) by simp
      have ityp': "ityp \<rho> env' W = ?V" using tctx' by simp
      have typed': "typed env' W Ts s S \<longleftrightarrow> typed env W Ts s S" for Ts s S
        using tctx' te'(1) by (simp add: typed_def)
      have etys': "etys env' \<subseteq> insert T (tys (rlist_abs rb u) \<union> etys env)" by (rule etys_update[OF upd])
      have twe': "\<forall>U\<in>etys env'. tyw ar ?\<theta> A U" using etys' twr twT pi(3) by blast
      have etv': "etvars env' \<subseteq> tvars_env ?\<theta> \<union> A" using twe' by (fastforce simp: etvars_def tyw_def)
      have "penv_inv alg ar W env'"
        unfolding penv_inv_def
      proof (intro conjI)
        show "tinv ar (maxidx env') (tyenv env') (etvars env')" using tinv_subset[OF pi(2) etv'] te' by simp
        show "tsorted alg (tyenv env')" using ei(2) te' by simp
        show "nacyc env'" using acyc_instE[OF su(2)] acy by simp
        show "pwf_env ar env'"
        proof -
          have "pwf_term ar 0 (rlist_abs rb u)"
            using swf_tm_binding[of ar rb u] swd by (simp add: pwf_term_def twft_tys)
          moreover have "wft ar T" using twT by (simp add: tyw_def)
          ultimately show ?thesis using ei(4) by (auto simp: pwf_env_def lk')
        qed
        show "wt_env W env'" using pi(1) tyrl by (auto simp: penv_inv_def wt_env_def lk' typed')
        show "fresh_env env'" using su(3) by simp
      qed
      moreover have "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' []"
        using calculation pi(2,5) twe' wc' pc(2) su(1) te' ityp'
        by (auto simp: pcinv_def pinv_def simp del: split_paired_All)
      moreover have "pextends env' env" using ok_update_extends[OF upd] te' by (simp add: pextends_def)
      moreover have "reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> u))" for X
        using reach_update[OF updi] by (simp add: inst_rlist_abs vps_rlist_abs)
      ultimately show ?thesis using ok te' by blast
    qed
  qed
qed



subsection \<open>Type unification at rigid-rigid pairs\<close>

lemma reach_lookup_eq: "(\<And>x. vt_lookup (tenv e1) x = vt_lookup (tenv e2) x) \<Longrightarrow> reach e1 X = reach e2 X"
  by (simp add: reach_def dep_def lk_def)

lemma instE_tagree_lookup:
  assumes "tinv ar (maxidx env) (tyenv env) A" "\<forall>T\<in>etys env. tyw ar (tyenv env) A T"
    "tenv env' = tenv env" "tagree (maxidx env) \<rho> \<rho>'"
  shows "vt_lookup (tenv (instE \<rho>' env')) x = vt_lookup (tenv (instE \<rho> env)) x"
proof (cases "vt_lookup (tenv env) x")
  case (Some p)
  then obtain U u where b: "vt_lookup (tenv env) x = Some (U, u)" by (cases p) auto
  have "insert U (tys u) \<subseteq> etys env" by (rule etysI[OF b])
  then have "tsubst \<rho>' U = tsubst \<rho> U" "inst \<rho>' u = inst \<rho> u"
    using assms(2) by (auto intro: tyw_tagree[OF assms(1) _ assms(4)] inst_tyw_tagree[OF assms(1) _ assms(4)])
  then show ?thesis using b assms(3) by simp
qed (simp add: assms(3))

lemma tsol_tnorm:
  assumes ac: "tacyc \<theta>"
  shows "tsol \<theta> (\<lambda>w S. tnorm \<theta> (TVar w S))"
  unfolding tsol_def
proof (intro allI impI)
  fix v S U assume "vt_lookup \<theta> v = Some (S, U)"
  then have "tnorm \<theta> (TVar v S) = tnorm \<theta> U" using tnorm_TVar[OF ac] by simp
  also have "\<dots> = tsubst (\<lambda>w S. tnorm \<theta> (TVar w S)) U" by (rule tnorm_tsubst)
  finally show "tnorm \<theta> (TVar v S) = tsubst (\<lambda>w S. tnorm \<theta> (TVar w S)) U" .
qed

lemma tnorm_eq_tsol: "tacyc \<theta> \<Longrightarrow> (\<And>\<rho>. tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<Longrightarrow> tnorm \<theta> T = tnorm \<theta> U"
  using tsol_tnorm[of \<theta>] by (simp add: tnorm_tsubst[of \<theta> T] tnorm_tsubst[of \<theta> U])

context wf_algebra
begin

text \<open>
  The types of the heads of a rigid-rigid pair are unified. Their instances are equal, so type
  unification succeeds, and an extension \<open>\<rho>'\<close> of \<open>\<rho>\<close> solves the new type environment.
\<close>

lemma cunify_types_pcomplete:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and tw: "tyw ar (tyenv env) A T" "tyw ar (tyenv env) A U" and eq: "tsubst \<rho> T = tsubst \<rho> U"
  obtains env' \<rho>' where "cunify_types alg T U env = returnW env'" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps"
    "tenv env' = tenv env" "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X = reach (instE \<rho> env) X" "tnorm (tyenv env') T = tnorm (tyenv env') U"
proof -
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  note ei = penv_invD[OF pi(1)]
  have g: "gsol alg ar (tyenv env) \<rho>" by (rule pcinvD(2)[OF pc])
  then have ws: "wsinst alg \<rho>" and sol: "tsol (tyenv env) \<rho>" by (simp_all add: gsol_def)
  from unify_types_poly[OF pi(2) ei(2) tw] ws sol eq obtain env' where
    u: "unify_types alg T U env = Some (Ok env')" "tenv env' = tenv env"
      "tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env) (maxidx env) (tyenv env') (maxidx env')"
      "tsorted alg (tyenv env')" "\<And>\<rho>. tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by blast
  from tstep_gsol[OF u(3) g eq] obtain \<rho>' where g': "gsol alg ar (tyenv env') \<rho>'" "tagree (maxidx env) \<rho> \<rho>'"
    by blast
  note ts = tstepD[OF u(3)]
  have pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps" by (rule pcinv_text[OF pc u(2) ts(1,2,3) u(4) g'])
  have cu: "cunify_types alg T U env = returnW env'" using u(1) by (simp add: cunify_types_def)
  have ext: "pextends env' env" using u(2) ts(1) by (simp add: pextends_def extends_def)
  have "reach (instE \<rho>' env') X = reach (instE \<rho> env) X" for X
    by (rule reach_lookup_eq) (rule instE_tagree_lookup[OF pi(2) _ u(2) g'(2)], use pi(3) in blast)
  moreover have "tnorm (tyenv env') T = tnorm (tyenv env') U"
    by (rule tnorm_eq_tsol[OF tinv_tacyc[OF ts(3)] u(5)])
  ultimately show ?thesis using that[OF cu pc' u(2) ext ts(2) g'(2)] by blast
qed

end



subsection \<open>One simplification step\<close>

lemma pcinv_swap: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t, u)] \<Longrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, u, t)]"
  by (auto simp: pcinv_def pinv_def intro: dsolved_sym)

lemma typed_head_Var:
  assumes "typed env W Ts t B" "head_of t = Var x X"
  obtains Us where "tnorm (tyenv env) X = foldr fun_type Us (tnorm (tyenv env) B)"
proof -
  let ?\<theta> = "tyenv env"
  obtain as where t: "t = list_comb (Var x X) as" using head_of_list_comb[of t] assms(2) by metis
  have "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (list_comb (Var x (tnorm ?\<theta> X)) (map (tnormt ?\<theta>) as))
      (tnorm ?\<theta> B)"
    using assms(1) t by (simp add: typed_def)
  then obtain Us where "has_type (tctx env W) (map (tnorm ?\<theta>) Ts) (Var x (tnorm ?\<theta> X))
      (foldr fun_type Us (tnorm ?\<theta> B))"
    by (auto simp: has_type_list_comb)
  then have "tnorm ?\<theta> X = foldr fun_type Us (tnorm ?\<theta> B)" by (auto elim: has_type_elims)
  then show ?thesis by (rule that)
qed

lemma head_pcases:
  assumes "has_type V Ts (inst \<rho> t) T" "\<not> is_Abs (head_of t)"
  shows "(\<exists>x X. head_of t = Var x X) \<or> is_rigid (head_of t)"
proof -
  have "\<not> is_Abs (head_of (inst \<rho> t))" using assms(2) by simp
  then show ?thesis
  proof (rule head_cases[OF assms(1)])
    fix x U assume "head_of (inst \<rho> t) = Var x U"
    then show ?thesis by (cases "head_of t") auto
  next
    assume "is_rigid (head_of (inst \<rho> t))"
    then show ?thesis by simp
  qed
qed

lemma tys_head_of: "tys (head_of t) \<subseteq> tys t"
  by (induction t) auto

context wf_algebra
begin

text \<open>One step of \<^const>\<open>SIMPL0\<close> on a head-normalized pair.\<close>

lemma SIMPL0_step_pcomplete:
  assumes inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t, u)]"
    and ty: "typed env W (map snd rb) t B" "typed env W (map snd rb) u B" "tnorm (tyenv env) B = B"
      "\<not> is_funT B"
    and nAt: "\<not> is_Abs t" "\<not> is_Abs u"
    and nA: "\<not> is_Abs (head_of t)" "\<not> is_Abs (head_of u)"
    and ut: "\<And>F U. head_of t = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and IH: "\<And>i st as bs Us \<rho>a. is_rigid (head_of t) \<Longrightarrow> t = list_comb (head_of t) as \<Longrightarrow>
      has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> (head_of t)) (foldr fun_type Us (tsubst \<rho> B)) \<Longrightarrow>
      list_all2 (has_type (ityp \<rho> env W) (map snd (instb \<rho> rb))) (map (inst \<rho>) as) Us \<Longrightarrow> i < length as \<Longrightarrow>
      pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) [(rb, as ! i, bs ! i)] \<Longrightarrow> pextends (fst st) env \<Longrightarrow>
      maxidx env \<le> maxidx (fst st) \<Longrightarrow> tagree (maxidx env) \<rho> \<rho>a \<Longrightarrow>
      \<exists>st' \<rho>b. okW (F (rb, as ! i, bs ! i) st) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho>a [(rb, as ! i, bs ! i)] st \<rho>b st'"
  shows "\<exists>st' \<rho>'. okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st' \<and>
    psres alg ar A W \<tau>' \<sigma> \<rho> [(rb, t, u)] (env, ffs, frs) \<rho>' st'"
proof -
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W" and ?dp = "(rb, t, u)" and ?Ts = "map snd (instb \<rho> rb)"
  note pc = pcinvD[OF inv]
  note pi = pinvD[OF pc(1)]
  have sol: "tsol ?\<theta> \<rho>" using pc(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  from pi(4)[of ?dp] have swd: "swf_dp ar ?dp"
    and twd: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar ?\<theta> A U"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  note ci = pcinv_cinv[OF inv]
  note isol = cinvD(2)[OF ci]
  note \<sigma> = solutionD[OF isol]
  have dsi: "dsolved \<sigma> (instb \<rho> rb, inst \<rho> t, inst \<rho> u)" using cinvD(3)[OF ci] by simp
  have tcB: "tcons ?\<theta> B" using tcons_tnorm[OF ac(1), of B] ty(3) by simp
  have tct: "\<forall>U\<in>set (map snd rb) \<union> tys t. tcons ?\<theta> U" and tcu: "\<forall>U\<in>set (map snd rb) \<union> tys u. tcons ?\<theta> U"
    using twd tcU by auto
  have tyi: "has_type ?V ?Ts (inst \<rho> t) (tsubst \<rho> B)" "has_type ?V ?Ts (inst \<rho> u) (tsubst \<rho> B)"
    using typed_inst[OF ac sol tct tcB ty(1)] typed_inst[OF ac sol tcu tcB ty(2)] by (simp_all add: map_snd_instb)
  have rsub: "reach (instE \<rho> env) X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> [?dp])" for X
    by (rule reach_subset) auto
  have vsub: "ivps \<rho> [?dp] \<subseteq> reach (instE \<rho> env) (ivps \<rho> [?dp])" by (rule reach_incl)
  have hb: "heads_unb env (rb, t, u)" "heads_unb env (rb, u, t)" using ut uu by (auto simp: heads_unb_def)
  have keep_fr: "psres alg ar A W \<tau>' \<sigma> \<rho> [?dp] (env, ffs, frs) \<rho> (env, ffs, (rb, t, u) # frs)"
    if "pfr_shape env W (rb, t, u)"
    using psresI[of alg ar A W \<rho> \<tau>' \<sigma> env "[]" "[(rb, t, u)]" env \<rho> "[?dp]" ffs frs] inv rsub vsub hb that
    by simp
  have keep_fr': "psres alg ar A W \<tau>' \<sigma> \<rho> [?dp] (env, ffs, frs) \<rho> (env, ffs, (rb, u, t) # frs)"
    if "pfr_shape env W (rb, u, t)"
    using psresI[of alg ar A W \<rho> \<tau>' \<sigma> env "[]" "[(rb, u, t)]" env \<rho> "[?dp]" ffs frs] pcinv_swap[OF inv]
      rsub vsub hb that
    by (simp add: Un_commute)
  have asg: "psres alg ar A W \<tau>' \<sigma> \<rho> [?dp] (env, ffs, frs) \<rho> (env', ffs, frs)"
    if "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' []" "pextends env' env" "maxidx env' = maxidx env"
      "\<And>X. reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> s))" "s = t \<or> s = u" for env' s
  proof -
    have "reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> [?dp])" for X
      using that(4)[of X] reach_subset[of "X \<union> vps (inst \<rho> s)" "X \<union> ivps \<rho> [?dp]" "instE \<rho> env"] that(5)
      by auto
    then show ?thesis
      using psresI[of alg ar A W \<rho> \<tau>' \<sigma> env' "[]" "[]" env \<rho> "[?dp]" ffs frs] that(1-3)
        pextendsD(2)[OF that(2)] by simp
  qed
  from head_pcases[OF tyi(1) nA(1)] head_pcases[OF tyi(2) nA(2)]
  consider (VV) x X y Y where "head_of t = Var x X" "head_of u = Var y Y"
    | (VR) x X where "head_of t = Var x X" "is_rigid (head_of u)"
    | (RV) y Y where "is_rigid (head_of t)" "head_of u = Var y Y"
    | (RR) "is_rigid (head_of t)" "is_rigid (head_of u)"
    by blast
  then show ?thesis
  proof cases
    case VV
    obtain Us where X: "tnorm ?\<theta> X = foldr fun_type Us B" using typed_head_Var[OF ty(1) VV(1)] ty(3) by metis
    obtain Us' where Y: "tnorm ?\<theta> Y = foldr fun_type Us' B" using typed_head_Var[OF ty(2) VV(2)] ty(3) by metis
    have tX: "tcons ?\<theta> X" "tcons ?\<theta> Y"
      using vps_tys[OF vps_head_of[OF VV(1)]] vps_tys[OF vps_head_of[OF VV(2)]] tct tcu by auto
    from body_type_ptnorm[OF ac tX(1) X ty(4)] obtain B1 where
      b1: "body_type env X = return B1" "tnorm ?\<theta> B1 = B" "tcons ?\<theta> B1" by blast
    from body_type_ptnorm[OF ac tX(2) Y ty(4)] obtain B2 where
      b2: "body_type env Y = return B2" "tnorm ?\<theta> B2 = B" "tcons ?\<theta> B2" by blast
    have cu: "cunify_types alg B1 B2 env = returnW env"
      by (rule cunify_types_same_mod[OF ac b1(3) b2(3)]) (simp add: b1(2) b2(2))
    have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ?dp # ffs, frs)"
      using VV b1(1) b2(1) cu by (simp add: SIMPL0_step_def return_def)
    moreover have "pff_shape env W ?dp" using ty nAt VV by (auto simp: pff_shape_def)
    moreover have "fch W ?\<theta> ?\<theta> [?dp]"
      using typed_hsat[OF ty(1) _ pi(6)] typed_hsat[OF ty(2) _ pi(6)] ty(3,4) ac(1) by auto
    ultimately show ?thesis
      using psresI[of alg ar A W \<rho> \<tau>' \<sigma> env "[?dp]" "[]" env \<rho> "[?dp]" ffs frs] inv rsub vsub hb by auto
  next
    case VR
    have fr: "pfr_shape env W ?dp" using ty nAt VR by (auto simp: pfr_shape_def)
    from assignment_pcomplete[OF inv ty _ VR(2)] ut
    consider evs where "assignment alg rb t u env = Some (evs, UErr ASSIGN)"
      | env' where "okW (assignment alg rb t u env) env'" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' []" "pextends env' env"
          "tyenv env' = tyenv env" "maxidx env' = maxidx env"
          "\<And>X. reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> u))"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ffs, ?dp # frs)"
        using VR 1 by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr[OF fr] show ?thesis by blast
    next
      case 2
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env', ffs, frs)"
        using VR 2(1) by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF 2(2,3,5,6)] show ?thesis by blast
    qed
  next
    case RV
    have fr: "pfr_shape env W (rb, u, t)" using ty nAt RV by (auto simp: pfr_shape_def)
    from assignment_pcomplete[OF pcinv_swap[OF inv] ty(2,1,3,4) _ RV(1)] uu
    consider evs where "assignment alg rb u t env = Some (evs, UErr ASSIGN)"
      | env' where "okW (assignment alg rb u t env) env'" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' []" "pextends env' env"
          "tyenv env' = tyenv env" "maxidx env' = maxidx env"
          "\<And>X. reach (instE \<rho> env') X \<subseteq> reach (instE \<rho> env) (X \<union> vps (inst \<rho> t))"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env, ffs, (rb, u, t) # frs)"
        using RV 1 by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr'[OF fr] show ?thesis by blast
    next
      case 2
      have "okW (SIMPL0_step alg F ?dp env ffs frs) (env', ffs, frs)"
        using RV 2(1) by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF 2(2,3,5,6)] show ?thesis by blast
    qed
  next
    case RR
    define h where "h = head_of t"
    define as where "as = snd (strip_comb t)"
    define h' where "h' = head_of u"
    define bs where "bs = snd (strip_comb u)"
    have t: "t = list_comb h as" using head_of_list_comb[of t] by (simp add: h_def as_def)
    have u0: "u = list_comb h' bs" using head_of_list_comb[of u] by (simp add: bs_def h'_def)
    have rig: "is_rigid h" "is_rigid h'" using RR by (simp_all add: h_def h'_def)
    have rigi: "is_rigid (inst \<rho> h)" "is_rigid (inst \<rho> h')" using rig by simp_all
    have ti: "inst \<rho> t = list_comb (inst \<rho> h) (map (inst \<rho>) as)" using t by (simp add: inst_list_comb)
    have ui: "inst \<rho> u = list_comb (inst \<rho> h') (map (inst \<rho>) bs)" using u0 by (simp add: inst_list_comb)
    from tyi(1) ti obtain Us where tyh: "has_type ?V ?Ts (inst \<rho> h) (foldr fun_type Us (tsubst \<rho> B))"
      and tyas: "list_all2 (has_type ?V ?Ts) (map (inst \<rho>) as) Us"
      by (auto simp: has_type_list_comb)
    note at = conjunct2[OF rigid_tr[OF rigi(1) \<sigma>(3)]] conjunct2[OF rigid_tr[OF rigi(2) \<sigma>(3)]]
    have "mk_subst \<sigma> (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u))"
      using dsolvedD[OF dsi] by (simp add: tr_rlist_abs mk_subst_Abs_m Abs_m_equiv_reflect)
    then have "tr (inst \<rho> h) \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) (map (inst \<rho>) as) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr (inst \<rho> h') \<degree>\<degree> map (\<lambda>b. mk_subst \<sigma> (tr b)) (map (inst \<rho>) bs)"
      using rigid_tr[OF rigi(1) \<sigma>(3)] rigid_tr[OF rigi(2) \<sigma>(3)] ti ui
      by (simp add: tr_list_comb comp_def)
    from atom_apps_equiv[OF at this] have trh: "tr (inst \<rho> h) = tr (inst \<rho> h')"
      and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma> (tr a)) (map (inst \<rho>) as))
        (map (\<lambda>b. mk_subst \<sigma> (tr b)) (map (inst \<rho>) bs))"
      by simp_all
    have hu: "inst \<rho> h' = inst \<rho> h" using tr_rigid_inj[OF rigi(2,1)] trh by simp
    have len: "length as = length bs" using list_all2_lengthD[OF args] by simp
    have h0: "\<nexists>f u. h = f $ u" "\<nexists>f u. h' = f $ u" unfolding h_def h'_def using head_of_not_App by blast+
    have twh: "\<forall>U\<in>tys h \<union> tys h'. tyw ar ?\<theta> A U"
      using twd tys_head_of[of t] tys_head_of[of u] by (auto simp: h_def h'_def)
    have "\<exists>env1 \<rho>1. SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs) \<and>
        pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [?dp] \<and> tenv env1 = tenv env \<and> pextends env1 env \<and>
        maxidx env \<le> maxidx env1 \<and> tagree (maxidx env) \<rho> \<rho>1 \<and>
        (\<forall>X. reach (instE \<rho>1 env1) X = reach (instE \<rho> env) X) \<and> tnormt (tyenv env1) h' = tnormt (tyenv env1) h"
    proof (cases h)
      case (Const a T)
      from hu Const obtain U where h': "h' = Const a U" "tsubst \<rho> U = tsubst \<rho> T" by (cases h') auto
      have tw: "tyw ar ?\<theta> A T" "tyw ar ?\<theta> A U" using twh Const h'(1) by auto
      from cunify_types_pcomplete[OF inv tw h'(2)[symmetric]] obtain env1 \<rho>1 where
        c: "cunify_types alg T U env = returnW env1" "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [?dp]" "tenv env1 = tenv env"
          "pextends env1 env" "maxidx env \<le> maxidx env1" "tagree (maxidx env) \<rho> \<rho>1"
          "\<And>X. reach (instE \<rho>1 env1) X = reach (instE \<rho> env) X" "tnorm (tyenv env1) T = tnorm (tyenv env1) U"
        by blast
      have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
        using Const h'(1) c(1) by (simp add: SIMPL0_step_def h_def h'_def bindW_def returnW_def option.map_ident option.map_id)
      with c Const h'(1) show ?thesis by (intro exI[of _ env1] exI[of _ \<rho>1]) auto
    next
      case (Free a T)
      from hu Free obtain U where h': "h' = Free a U" "tsubst \<rho> U = tsubst \<rho> T" by (cases h') auto
      have tw: "tyw ar ?\<theta> A T" "tyw ar ?\<theta> A U" using twh Free h'(1) by auto
      from cunify_types_pcomplete[OF inv tw h'(2)[symmetric]] obtain env1 \<rho>1 where
        c: "cunify_types alg T U env = returnW env1" "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [?dp]" "tenv env1 = tenv env"
          "pextends env1 env" "maxidx env \<le> maxidx env1" "tagree (maxidx env) \<rho> \<rho>1"
          "\<And>X. reach (instE \<rho>1 env1) X = reach (instE \<rho> env) X" "tnorm (tyenv env1) T = tnorm (tyenv env1) U"
        by blast
      have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
        using Free h'(1) c(1) by (simp add: SIMPL0_step_def h_def h'_def bindW_def returnW_def option.map_ident option.map_id)
      with c Free h'(1) show ?thesis by (intro exI[of _ env1] exI[of _ \<rho>1]) auto
    next
      case (Bound i)
      with hu have h': "h' = Bound i" by (cases h') auto
      have "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env, ffs, frs)"
        using Bound h' by (simp add: SIMPL0_step_def h_def h'_def)
      with inv h' Bound show ?thesis by (intro exI[of _ env] exI[of _ \<rho>]) auto
    qed (use rig in \<open>auto simp: is_rigid_def\<close>)
    then obtain env1 \<rho>1 where s1: "SIMPL0_step alg F ?dp env ffs frs = simrands F rb u t u (env1, ffs, frs)"
      "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [?dp]" "tenv env1 = tenv env" "pextends env1 env"
      "maxidx env \<le> maxidx env1" "tagree (maxidx env) \<rho> \<rho>1"
      "\<And>X. reach (instE \<rho>1 env1) X = reach (instE \<rho> env) X" "tnormt (tyenv env1) h' = tnormt (tyenv env1) h"
      by blast
    let ?\<theta>1 = "tyenv env1" and ?V1 = "tctx env1 W" and ?Ts1 = "map (tnorm (tyenv env1)) (map snd rb)"
    let ?args = "map (\<lambda>(a, b). (rb, a, b)) (zip as bs)"
    note pi1 = pinvD[OF pcinvD(1)[OF s1(2)]]
    have ac1: "tacyc ?\<theta>1" by (rule tinv_tacyc[OF pi1(2)])
    have te1: "textends ?\<theta> ?\<theta>1" using s1(4) by (simp add: pextends_def)
    have ty1: "typed env1 W (map snd rb) t B" "typed env1 W (map snd rb) u B"
      using typed_wcons[OF ac1 te1 pi(6) pi1(6) ty(1)] typed_wcons[OF ac1 te1 pi(6) pi1(6) ty(2)] by simp_all
    have nt1: "has_type ?V1 ?Ts1 (list_comb (tnormt ?\<theta>1 h) (map (tnormt ?\<theta>1) as)) (tnorm ?\<theta>1 B)"
      using ty1(1) t by (simp add: typed_def)
    have nu1: "has_type ?V1 ?Ts1 (list_comb (tnormt ?\<theta>1 h) (map (tnormt ?\<theta>1) bs)) (tnorm ?\<theta>1 B)"
      using ty1(2) u0 s1(8) by (simp add: typed_def)
    from nt1 obtain Vs where hV: "has_type ?V1 ?Ts1 (tnormt ?\<theta>1 h) (foldr fun_type Vs (tnorm ?\<theta>1 B))"
      and aV: "list_all2 (has_type ?V1 ?Ts1) (map (tnormt ?\<theta>1) as) Vs"
      by (auto simp: has_type_list_comb)
    from nu1 obtain Vs' where hV': "has_type ?V1 ?Ts1 (tnormt ?\<theta>1 h) (foldr fun_type Vs' (tnorm ?\<theta>1 B))"
      and bV: "list_all2 (has_type ?V1 ?Ts1) (map (tnormt ?\<theta>1) bs) Vs'"
      by (auto simp: has_type_list_comb)
    have lV: "length Vs = length as" "length Vs' = length bs"
      using list_all2_lengthD[OF aV] list_all2_lengthD[OF bV] by simp_all
    have VV: "Vs' = Vs"
      using foldr_fun_type_inj[OF _ has_type_unique[OF hV hV']] lV len by auto
    have nV: "tnorm ?\<theta>1 (Vs ! i) = Vs ! i" if "i < length as" for i
    proof (rule has_type_normal[OF list_all2_nthD[OF aV] ac1])
      show "i < length (map (tnormt ?\<theta>1) as)" using that by simp
      show "\<forall>x. tnorm ?\<theta>1 (?V1 x) = ?V1 x" by (simp add: tctx_normal[OF ac1])
      show "\<forall>T\<in>set ?Ts1. tnorm ?\<theta>1 T = T" by (auto simp: tnorm_idem[OF ac1])
      show "\<forall>T\<in>tys (map (tnormt ?\<theta>1) as ! i). tnorm ?\<theta>1 T = T"
        using that by (auto simp: tys_tnormt tnorm_idem[OF ac1])
    qed
    have tyarg: "typed env1 W (map snd rb) (as ! i) (Vs ! i)" "typed env1 W (map snd rb) (bs ! i) (Vs ! i)"
      if i: "i < length as" for i
      using list_all2_nthD[OF aV] list_all2_nthD[OF bV] i len lV VV nV[OF i] by (simp_all add: typed_def)
    have dsa: "dsolved \<sigma> (instb \<rho> rb, inst \<rho> (as ! i), inst \<rho> (bs ! i))" if "i < length as" for i
    proof (rule dsolvedI)
      have "mk_subst \<sigma> (tr (inst \<rho> (as ! i))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (bs ! i)))"
        using list_all2_nthD[OF args] that len by simp
      then show "mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> (as ! i)))) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          mk_subst \<sigma> (tr (rlist_abs (instb \<rho> rb) (inst \<rho> (bs ! i))))"
        by (simp add: tr_rlist_abs mk_subst_Abs_m equiv_Abs_m)
    qed
    have twa: "\<forall>U\<in>dtys (rb, as ! i, bs ! i). tyw ar ?\<theta> A U" if "i < length as" for i
      using twd that len t u0 by (auto simp: tys_list_comb)
    have pca: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [(rb, as ! i, bs ! i)]" if i: "i < length as" for i
    proof -
      have "swf_dp ar (rb, as ! i, bs ! i)" using swd i len t u0 by (simp add: swf_tm_list_comb)
      moreover have "\<forall>U\<in>dtys (rb, as ! i, bs ! i). tyw ar ?\<theta>1 A U"
        using twa[OF i] tyw_textends[OF ac1 te1] by blast
      moreover have "ptyped env1 W (rb, as ! i, bs ! i)" using tyarg[OF i] by auto
      moreover have "dp_below (maxidx env1) (rb, as ! i, bs ! i)"
        using bl i len t u0 below_mono[OF _ s1(5)] by (simp add: below_list_comb)
      moreover have "dsolved \<sigma> (instd \<rho>1 (rb, as ! i, bs ! i))"
        using dsa[OF i] instd_tyw_tagree[OF pi(2) twa[OF i] s1(6)] by simp
      ultimately show ?thesis using pcinv_Nil[OF s1(2)] by (auto simp: pcinv_def pinv_def)
    qed
    have F: "\<exists>st' \<rho>b. okW (F (rb, as ! i, bs ! i) st) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho>a [(rb, as ! i, bs ! i)] st \<rho>b st'"
      if i: "i < length as" and st: "pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) []" "pextends (fst st) env1"
        "maxidx env1 \<le> maxidx (fst st)" "tagree (maxidx env1) \<rho>1 \<rho>a" for i st \<rho>a
    proof (rule IH[OF RR(1)])
      show "t = list_comb (head_of t) as" using t by (simp add: h_def)
      show "has_type ?V ?Ts (inst \<rho> (head_of t)) (foldr fun_type Us (tsubst \<rho> B))" using tyh by (simp add: h_def)
      show "list_all2 (has_type ?V ?Ts) (map (inst \<rho>) as) Us" by (rule tyas)
      show "i < length as" by (rule i)
      have te: "textends ?\<theta>1 (tyenv (fst st))" using st(2) by (simp add: pextends_def)
      show "pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) [(rb, as ! i, bs ! i)]"
        by (rule pcinv_transfer[OF pca[OF i] st(1) te st(3,4)])
      show "pextends (fst st) env" by (rule pextends_trans[OF st(2) s1(4)])
      show "maxidx env \<le> maxidx (fst st)" using s1(5) st(3) by simp
      show "tagree (maxidx env) \<rho> \<rho>a" by (rule tagree_trans[OF s1(6) st(4) s1(5)])
    qed
    have same: "map (instd \<rho>') ?args = map (instd \<rho>1) ?args" if "tagree (maxidx env1) \<rho>1 \<rho>'" for \<rho>'
    proof -
      have "instd \<rho>' dp = instd \<rho>1 dp" if "dp \<in> set ?args" for dp
      proof -
        from that obtain i where i: "i < length as" "dp = (rb, as ! i, bs ! i)"
          using len by (auto simp: in_set_zip)
        from pinvD(4)[OF pcinvD(1)[OF pca[OF i(1)]]] i(2)
        have "\<forall>U\<in>dtys dp. tyw ar ?\<theta>1 A U" by simp
        from instd_tyw_tagree[OF pi1(2) this \<open>tagree (maxidx env1) \<rho>1 \<rho>'\<close>] show ?thesis .
      qed
      then show ?thesis by simp
    qed
    have same0: "map (instd \<rho>1) ?args = map (instd \<rho>) ?args"
    proof -
      have "instd \<rho>1 dp = instd \<rho> dp" if "dp \<in> set ?args" for dp
      proof -
        from that obtain i where i: "i < length as" "dp = (rb, as ! i, bs ! i)"
          using len by (auto simp: in_set_zip)
        from instd_tyw_tagree[OF pi(2) twa[OF i(1)] s1(6)] i(2) show ?thesis by simp
      qed
      then show ?thesis by simp
    qed
    have "\<exists>st' \<rho>2. okW (simrands F rb u (list_comb h as) (list_comb h' bs) (env1, ffs, frs)) st' \<and>
        psres alg ar A W \<tau>' \<sigma> \<rho>1 ?args (env1, ffs, frs) \<rho>2 st'"
      by (rule simrands_pcomplete[where eo = env1 and \<rho>o = \<rho>1, OF F h0 same len])
        (use pcinv_Nil[OF s1(2)] in simp_all)
    then obtain st' \<rho>2 where sr: "okW (simrands F rb u (list_comb h as) (list_comb h' bs) (env1, ffs, frs)) st'"
      "psres alg ar A W \<tau>' \<sigma> \<rho>1 ?args (env1, ffs, frs) \<rho>2 st'"
      by blast
    have p0: "psres alg ar A W \<tau>' \<sigma> \<rho> [] (env, ffs, frs) \<rho>1 (env1, [] @ ffs, [] @ frs)"
      by (rule psresI) (use pcinv_Nil[OF s1(2)] s1(4-7) in \<open>auto simp: pextends_def\<close>)
    from psres_trans[OF p0[simplified] sr(2) same0] have "psres alg ar A W \<tau>' \<sigma> \<rho> ?args (env, ffs, frs) \<rho>2 st'"
      by simp
    moreover have "ivps \<rho> ?args \<subseteq> reach (instE \<rho> env) (ivps \<rho> [?dp])"
    proof -
      have "ivps \<rho> ?args \<subseteq> ivps \<rho> [?dp]"
      proof
        fix y assume "y \<in> ivps \<rho> ?args"
        then obtain a b where ab: "(a, b) \<in> set (zip as bs)" "y \<in> vps (inst \<rho> a) \<union> vps (inst \<rho> b)" by auto
        then have "a \<in> set as" "b \<in> set bs" by (auto dest: set_zip_leftD set_zip_rightD)
        with ab(2) ti ui show "y \<in> ivps \<rho> [?dp]" by (auto simp: vps_list_comb)
      qed
      then show ?thesis using reach_incl[of "ivps \<rho> [?dp]" "instE \<rho> env"] by blast
    qed
    ultimately have "psres alg ar A W \<tau>' \<sigma> \<rho> [?dp] (env, ffs, frs) \<rho>2 st'" by (rule psres_mono_dps)
    moreover have "okW (SIMPL0_step alg F ?dp env ffs frs) st'"
      using s1(1) sr(1) by (simp add: t[symmetric] u0[symmetric])
    ultimately show ?thesis by blast
  qed
qed

end



subsection \<open>Completeness of \<open>SIMPL0\<close>\<close>

text \<open>The typing of the instance is stable under extensions:\<close>

lemma ityp_pcinv:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and pc': "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' dps'"
    and te: "textends (tyenv env) (tyenv env')" and ag: "tagree (maxidx env) \<rho> \<rho>'"
  shows "ityp \<rho>' env' W = ityp \<rho> env W"
proof
  fix x
  note pi = pinvD[OF pcinvD(1)[OF pc]] and pi' = pinvD[OF pcinvD(1)[OF pc']]
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  have ac': "tacyc (tyenv env')" "tcons_env (tyenv env')"
    using tinv_tacyc[OF pi'(2)] tinv_tcons_env[OF pi'(2)] by simp_all
  have sol: "tsol (tyenv env) \<rho>" "tsol (tyenv env') \<rho>'"
    using pcinvD(2)[OF pc] pcinvD(2)[OF pc'] by (simp_all add: gsol_def)
  have tc: "tcons (tyenv env) (W x)" "tcons (tyenv env') (W x)"
    using tyw_tcons[OF pi(2) pi(5)] tyw_tcons[OF pi'(2) pi'(5)] by simp_all
  have "ityp \<rho>' env' W x = tsubst \<rho>' (W x)"
    using wcons_tctx[OF pi'(6)] tsubst_tnorm[OF ac' sol(2) tc(2)] by simp
  also have "\<dots> = tsubst \<rho> (W x)" by (rule tyw_tagree[OF pi(2) pi(5) ag])
  also have "\<dots> = ityp \<rho> env W x" using wcons_tctx[OF pi(6)] tsubst_tnorm[OF ac sol(1) tc(1)] by simp
  finally show "ityp \<rho>' env' W x = ityp \<rho> env W x" .
qed

context wf_algebra
begin

lemma SIMPL0_pcomplete_aux:
  "dsz \<tau>' \<sigma> (instb \<rho> rb) (inst \<rho> t) T < n \<Longrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb, t, u)] \<Longrightarrow>
    has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> t) T \<Longrightarrow>
    \<exists>st' \<rho>'. okW (SIMPL0 alg (rb, t, u) (env, ffs, frs)) st' \<and>
      psres alg ar A W \<tau>' \<sigma> \<rho> [(rb, t, u)] (env, ffs, frs) \<rho>' st'"
proof (induction n arbitrary: rb t u T env ffs frs \<rho>)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note inv = Suc.prems(2)
  let ?\<theta> = "tyenv env" and ?V = "ityp \<rho> env W"
  note pc = pcinvD[OF inv]
  note pi = pinvD[OF pc(1)]
  have sol: "tsol ?\<theta> \<rho>" using pc(2) by (simp add: gsol_def)
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF pi(2)] tinv_tcons_env[OF pi(2)] by simp_all
  note isol = cinvD(2)[OF pcinv_cinv[OF inv]]
  note \<sigma> = solutionD[OF isol]
  obtain rb' t' u' T0 where hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    and inv': "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [(rb', t', u')]"
    and T0: "tnorm ?\<theta> T0 = T0" and tyt0: "typed env W (map snd rb) t T0"
    and rbn: "map (tnorm ?\<theta>) (map snd rb') = rev (arg_types T0) @ map (tnorm ?\<theta>) (map snd rb)"
    and ty': "typed env W (map snd rb') t' (res_type T0)" "typed env W (map snd rb') u' (res_type T0)"
    and nAt: "\<not> is_Abs t'" "\<not> is_Abs u'"
    and nA: "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    and ut: "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and vt: "vps (inst \<rho> t') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> t))"
      "vps (inst \<rho> u') \<subseteq> reach (instE \<rho> env) (vps (inst \<rho> u))"
    and eq: "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb' t'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs rb t)))"
    by (rule head_norm_dpair_pcomplete[OF inv]) blast
  define B where "B = res_type T0"
  have nfB: "\<not> is_funT B" by (simp add: B_def res_type_base)
  have Bn: "tnorm ?\<theta> B = B" using tnorm_res_type[OF T0] by (simp add: B_def)
  from pi(4)[of "(rb, t, u)"] have tw: "\<forall>U\<in>snd ` set rb \<union> tys t. tyw ar ?\<theta> A U" by auto
  from pinvD(4)[OF pcinvD(1)[OF inv'], of "(rb', t', u')"]
  have tw': "\<forall>U\<in>snd ` set rb' \<union> tys t'. tyw ar ?\<theta> A U" by auto
  have tcU: "tcons ?\<theta> U" if "tyw ar ?\<theta> A U" for U by (rule tyw_tcons[OF pi(2) that])
  have tsn: "tsubst \<rho> (tnorm ?\<theta> U) = tsubst \<rho> U" if "tyw ar ?\<theta> A U" for U
    by (rule tsubst_tnorm[OF ac sol tcU[OF that]])
  have tcT0: "tcons ?\<theta> T0" using tcons_tnorm[OF ac(1), of T0] T0 by simp
  have tcB: "tcons ?\<theta> B" using tcons_tnorm[OF ac(1), of B] Bn by simp
  have tyi: "has_type ?V (map snd (instb \<rho> rb)) (inst \<rho> t) (tsubst \<rho> T0)"
    using typed_inst[OF ac sol _ tcT0 tyt0] tw tcU by (auto simp: map_snd_instb)
  have TT0: "T = tsubst \<rho> T0" by (rule has_type_unique[OF Suc.prems(3) tyi])
  have tyi': "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> t') (tsubst \<rho> B)"
    using typed_inst[OF ac sol _ tcB ty'(1)[folded B_def]] tw' tcU by (auto simp: map_snd_instb)
  have m': "map (tsubst \<rho>) (map snd rb') = map (tsubst \<rho>) (map (tnorm ?\<theta>) (map snd rb'))"
    and m: "map (tsubst \<rho>) (map snd rb) = map (tsubst \<rho>) (map (tnorm ?\<theta>) (map snd rb))"
    using tw tw' tsn by auto
  have TT: "foldr fun_type (rev (map snd (instb \<rho> rb'))) (tsubst \<rho> B) =
      foldr fun_type (rev (map snd (instb \<rho> rb))) T"
  proof -
    have "map snd (instb \<rho> rb') = rev (map (tsubst \<rho>) (arg_types T0)) @ map snd (instb \<rho> rb)"
      using arg_cong[OF rbn, of "map (tsubst \<rho>)"] m m' by (simp add: map_snd_instb rev_map)
    then show ?thesis
      using arg_res_type[of T0] TT0 by (simp add: B_def tsubst_foldr_fun[symmetric])
  qed
  have dszeq: "dsz \<tau>' \<sigma> (instb \<rho> rb') (inst \<rho> t') (tsubst \<rho> B) = dsz \<tau>' \<sigma> (instb \<rho> rb) (inst \<rho> t) T"
    by (rule dsz_equiv[OF Suc.prems(3) tyi' TT _ \<sigma>(1,2)]) (use eq in \<open>simp add: inst_rlist_abs\<close>)
  have "\<exists>st' \<rho>'. okW (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) st' \<and>
      psres alg ar A W \<tau>' \<sigma> \<rho> [(rb', t', u')] (env, ffs, frs) \<rho>' st'"
  proof (rule SIMPL0_step_pcomplete[OF inv' ty'[folded B_def] Bn nfB nAt nA ut uu])
    fix i and st :: sstate and as bs Us \<rho>a
    assume rig: "is_rigid (head_of t')" and t': "t' = list_comb (head_of t') as"
      and tyh: "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> (head_of t')) (foldr fun_type Us (tsubst \<rho> B))"
      and tyas: "list_all2 (has_type ?V (map snd (instb \<rho> rb'))) (map (inst \<rho>) as) Us" and i: "i < length as"
      and ci: "pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) [(rb', as ! i, bs ! i)]" and ex: "pextends (fst st) env"
      and mx: "maxidx env \<le> maxidx (fst st)" and ag: "tagree (maxidx env) \<rho> \<rho>a"
    have "dsz \<tau>' \<sigma> (instb \<rho> rb') (map (inst \<rho>) as ! i) (Us ! i) <
        dsz \<tau>' \<sigma> (instb \<rho> rb') (list_comb (inst \<rho> (head_of t')) (map (inst \<rho>) as)) (tsubst \<rho> B)"
      by (rule dsz_args[OF tyh tyas _ \<sigma>(1,2,3)]) (use rig i in simp_all)
    moreover have "inst \<rho> t' = list_comb (inst \<rho> (head_of t')) (map (inst \<rho>) as)"
      by (subst t') (simp add: inst_list_comb)
    ultimately have lt0: "dsz \<tau>' \<sigma> (instb \<rho> rb') (inst \<rho> (as ! i)) (Us ! i) < n"
      using dszeq Suc.prems(1) i by simp
    have tyi0: "has_type ?V (map snd (instb \<rho> rb')) (inst \<rho> (as ! i)) (Us ! i)"
      using list_all2_nthD[OF tyas] i by simp
    have te: "textends ?\<theta> (tyenv (fst st))" using ex by (simp add: pextends_def)
    have ity: "ityp \<rho>a (fst st) W = ?V" by (rule ityp_pcinv[OF inv ci te ag])
    have twa: "\<forall>U\<in>snd ` set rb' \<union> tys (as ! i). tyw ar ?\<theta> A U"
    proof -
      have "tys (as ! i) \<subseteq> tys t'" using i by (subst t') (auto simp: tys_list_comb)
      with tw' show ?thesis by blast
    qed
    have ib: "instb \<rho>a rb' = instb \<rho> rb'"
      using twa by (force simp: instb_def intro!: map_cong tyw_tagree[OF pi(2) _ ag])
    have ia: "inst \<rho>a (as ! i) = inst \<rho> (as ! i)" using twa inst_tyw_tagree[OF pi(2) _ ag] by blast
    obtain env1 ffs1 frs1 where st: "st = (env1, ffs1, frs1)" by (cases st)
    from Suc.IH[where rb = rb' and t = "as ! i" and u = "bs ! i" and T = "Us ! i" and env = env1
        and ffs = ffs1 and frs = frs1 and \<rho> = \<rho>a]
      lt0 tyi0 ci ity ib ia st
    show "\<exists>st' \<rho>b. okW (SIMPL0 alg (rb', as ! i, bs ! i) st) st' \<and>
        psres alg ar A W \<tau>' \<sigma> \<rho>a [(rb', as ! i, bs ! i)] st \<rho>b st'"
      by simp
  qed
  then obtain st' \<rho>' where st': "okW (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) st'"
    "psres alg ar A W \<tau>' \<sigma> \<rho> [(rb', t', u')] (env, ffs, frs) \<rho>' st'" by blast
  have "okW (SIMPL0 alg (rb, t, u) (env, ffs, frs)) st'"
    using hd st'(1) by (subst SIMPL0_unfold) auto
  moreover have "psres alg ar A W \<tau>' \<sigma> \<rho> [(rb, t, u)] (env, ffs, frs) \<rho>' st'"
  proof (rule psres_mono_dps[OF st'(2)])
    show "ivps \<rho> [(rb', t', u')] \<subseteq> reach (instE \<rho> env) (ivps \<rho> [(rb, t, u)])"
      using vt reach_subset[of "vps (inst \<rho> t)" "vps (inst \<rho> t) \<union> vps (inst \<rho> u)" "instE \<rho> env"]
        reach_subset[of "vps (inst \<rho> u)" "vps (inst \<rho> t) \<union> vps (inst \<rho> u)" "instE \<rho> env"]
      by auto
  qed
  ultimately show ?case by blast
qed

theorem SIMPL0_pcomplete:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [dp]"
  shows "\<exists>st' \<rho>'. okW (SIMPL0 alg dp (env, ffs, frs)) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho> [dp] (env, ffs, frs) \<rho>' st'"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from pcinv_cinv[OF assms] dp obtain T where
    "has_type (ityp \<rho> env W) (map snd (instb \<rho> rb)) (inst \<rho> t) T"
    by (auto simp: cinv_def map_snd_instb)
  from SIMPL0_pcomplete_aux[OF lessI assms[unfolded dp] this, of ffs frs] dp show ?thesis by blast
qed

end



subsection \<open>Completeness of \<open>SIMPL\<close>\<close>

lemma psres_set:
  "set dps = set dps' \<Longrightarrow> psres alg ar A W \<tau>' \<sigma> \<rho> dps st \<rho>' st' = psres alg ar A W \<tau>' \<sigma> \<rho> dps' st \<rho>' st'"
  by (simp add: psres_def)

context wf_algebra
begin

lemma foldrW_SIMPL0_pcomplete:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow>
    \<exists>st' \<rho>'. okW (foldrW (SIMPL0 alg) dps (env, [], [])) st' \<and>
      psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, [], []) \<rho>' st'"
proof (induction dps)
  case Nil
  then show ?case using psres_refl[OF pcinv_Nil[OF Nil]] by fastforce
next
  case (Cons dp dps)
  from Cons.prems have c1: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env [dp]" and c2: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    by (simp_all add: pcinv_def pinv_def)
  from Cons.IH[OF c2] obtain st1 \<rho>1 where r1: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) st1"
    "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, [], []) \<rho>1 st1" by blast
  from psresD[OF r1(2)] obtain env1 ffn frn where s1: "st1 = (env1, ffn @ [], frn @ [])"
    "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (ffn @ frn)" "pextends env1 env" "maxidx env \<le> maxidx env1"
    "tagree (maxidx env) \<rho> \<rho>1"
    by blast
  have "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 [dp]"
    by (rule pcinv_transfer[OF c1 pcinv_Nil[OF s1(2)] pextendsD(2)[OF s1(3)] s1(4,5)])
  from SIMPL0_pcomplete[OF this, of ffn frn] obtain st2 \<rho>2 where
    r2: "okW (SIMPL0 alg dp (env1, ffn, frn)) st2" "psres alg ar A W \<tau>' \<sigma> \<rho>1 [dp] (env1, ffn, frn) \<rho>2 st2"
    by blast
  have "okW (foldrW (SIMPL0 alg) (dp # dps) (env, [], [])) st2" using r1(1) r2(1) s1(1) by auto
  moreover have "psres alg ar A W \<tau>' \<sigma> \<rho> (dp # dps) (env, [], []) \<rho>2 st2"
    using psres_trans[OF r1(2)[unfolded s1(1) append_Nil2] r2(2) ivps_tagree[OF c1 s1(5)]]
      psres_set[of "dps @ [dp]" "dp # dps"]
    by simp
  ultimately show ?case by blast
qed

end

text \<open>Lookups of variables that are typed consistently with the bindings do not clash:\<close>

lemma lookup_wcons:
  assumes ok: "tyok env" and wc: "wcons W env" and T: "tcons (tyenv env) T" "tnorm (tyenv env) T = tnorm (tyenv env) (W x)"
    and b: "\<And>U u. vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tcons (tyenv env) U"
  shows "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
proof (cases "vt_lookup (tenv env) x")
  case (Some p)
  then obtain U u where l: "vt_lookup (tenv env) x = Some (U, u)" by (cases p) auto
  have "tnorm (tyenv env) U = tnorm (tyenv env) (W x)" using wc l unfolding wcons_def by blast
  with T(2) have "tnorm (tyenv env) T = tnorm (tyenv env) U" by simp
  moreover have "unified (tyenv env) T U = return (tnorm (tyenv env) T = tnorm (tyenv env) U)"
    using unified_ok ok T(1) b[OF l] by (simp add: tyok_def)
  ultimately show ?thesis using l by (simp add: lookup_def)
qed (simp add: lookup_def)

definition pvtyped :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> bool" where
  "pvtyped env W t \<longleftrightarrow> (\<forall>(x, T)\<in>vps t. tcons (tyenv env) T \<and> tnorm (tyenv env) T = tnorm (tyenv env) (W x))"

lemma changed_ptyped:
  assumes ok: "tyok env" and wc: "wcons W env"
    and b: "\<And>x U u. vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tcons (tyenv env) U"
  shows "pvtyped env W t \<Longrightarrow> changed env t = return (\<exists>x T. head_of t = Var x T \<and> vt_lookup (tenv env) x \<noteq> None)"
proof (induction t)
  case (Var x T)
  then have "tcons (tyenv env) T" "tnorm (tyenv env) T = tnorm (tyenv env) (W x)" by (auto simp: pvtyped_def)
  from lookup_wcons[OF ok wc this b] show ?case by (cases "vt_lookup (tenv env) x") (auto simp: return_def)
next
  case (App f u)
  then show ?case by (simp add: pvtyped_def)
qed (simp_all add: return_def)


lemma extends_instE_tagree:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" and ex: "extends env1 env" and ag: "tagree (maxidx env) \<rho> \<rho>1"
  shows "extends (instE \<rho>1 env1) (instE \<rho> env)"
  unfolding extends_def
proof (intro allI impI)
  fix x b assume "vt_lookup (tenv (instE \<rho> env)) x = Some b"
  then obtain U u where l: "vt_lookup (tenv env) x = Some (U, u)" "b = (tsubst \<rho> U, inst \<rho> u)" by auto
  note pi = pinvD[OF pcinvD(1)[OF pc]]
  have "insert U (tys u) \<subseteq> etys env" by (rule etysI[OF l(1)])
  then have "tsubst \<rho>1 U = tsubst \<rho> U" "inst \<rho>1 u = inst \<rho> u"
    using pi(3) by (auto intro: tyw_tagree[OF pi(2) _ ag] inst_tyw_tagree[OF pi(2) _ ag])
  moreover have "vt_lookup (tenv env1) x = Some (U, u)" using ex l(1) unfolding extends_def by blast
  ultimately show "vt_lookup (tenv (instE \<rho>1 env1)) x = Some b" using l(2) by simp
qed

lemma pvtyped_pcinv:
  assumes "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" "(rb, t, u) \<in> set dps"
  shows "pvtyped env W t" "pvtyped env W u"
proof -
  note pi = pinvD[OF pcinvD(1)[OF assms(1)]]
  from pi(4)[OF assms(2)] obtain T where tw: "\<forall>U\<in>snd ` set rb \<union> tys t \<union> tys u. tyw ar (tyenv env) A U"
    and ty: "typed env W (map snd rb) t T" "typed env W (map snd rb) u T" by auto
  have "pvtyped env W s" if "s = t \<or> s = u" "typed env W (map snd rb) s T" for s
    unfolding pvtyped_def
  proof (intro ballI, clarify)
    fix x U assume xU: "(x, U) \<in> vps s"
    have "tyw ar (tyenv env) A U" using tw vps_tys[OF xU] that(1) by auto
    then show "tcons (tyenv env) U \<and> tnorm (tyenv env) U = tnorm (tyenv env) (W x)"
      using tyw_tcons[OF pi(2)] typed_vps[OF that(2) xU] wcons_tctx[OF pi(6)] by simp
  qed
  then show "pvtyped env W t" "pvtyped env W u" using ty by blast+
qed

text \<open>The result of \<^const>\<open>SIMPL\<close>: no head variable of the pairs is bound any more.\<close>

definition psimpl_res :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> tinst \<Rightarrow> sstate \<Rightarrow> bool" where
  "psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>' st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffs @ frs) \<and> pextends env' env \<and> maxidx env \<le> maxidx env' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and>
    (\<forall>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)) \<and>
    ivps \<rho>' (ffs @ frs) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps) \<and>
    (\<forall>dp\<in>set ffs. pff_shape env' W dp) \<and> (\<forall>dp\<in>set frs. pfr_shape env' W dp) \<and>
    (\<forall>dp\<in>set (ffs @ frs). heads_unb env' dp) \<and> fch W (tyenv env') (tyenv env) ffs)"

context wf_algebra
begin

lemma SIMPL_pcomplete_aux:
  "card (unb (instE \<rho> env) (ivps \<rho> dps)) < n \<Longrightarrow> pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow>
    \<exists>st' \<rho>'. okW (SIMPL alg env dps) st' \<and> psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>' st'"
proof (induction n arbitrary: env dps \<rho>)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from foldrW_SIMPL0_pcomplete[OF Suc.prems(2)] obtain st1 \<rho>1 where
    r1: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) st1" "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, [], []) \<rho>1 st1"
    by blast
  from psresD[OF r1(2)] obtain env1 ffs frs where s1: "st1 = (env1, ffs @ [], frs @ [])"
    "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (ffs @ frs)" "pextends env1 env" "maxidx env \<le> maxidx env1"
    "tagree (maxidx env) \<rho> \<rho>1"
    "\<And>X. reach (instE \<rho>1 env1) X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    "ivps \<rho>1 (ffs @ frs) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    "\<And>dp. dp \<in> set ffs \<Longrightarrow> pff_shape env1 W dp" "\<And>dp. dp \<in> set frs \<Longrightarrow> pfr_shape env1 W dp"
    "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env dp" "fch W (tyenv env1) (tyenv env) ffs"
    by blast
  let ?\<theta>1 = "tyenv env1"
  note pi1 = pinvD[OF pcinvD(1)[OF s1(2)]]
  have ok1: "tyok env1" by (rule tyok_tinv[OF pi1(2)])
  have bt1: "tcons ?\<theta>1 U" if "vt_lookup (tenv env1) x = Some (U, u)" for x U u
    using etysI[OF that] pi1(3) tyw_tcons[OF pi1(2)] by blast
  define dps' where "dps' = frs @ ffs"
  have c1: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 dps'" using s1(2) by (auto simp: pcinv_def pinv_def dps'_def)
  define ch where "ch = (\<lambda>s. \<exists>x T. head_of s = Var x T \<and> vt_lookup (tenv env1) x \<noteq> None)"
  have ex: "existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) dps' =
    return (\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
  proof (rule existsM_return)
    fix dp assume dp: "dp \<in> set dps'"
    obtain rb t u where dp0: "dp = (rb, t, u)" by (cases dp)
    note pv = pvtyped_pcinv[OF c1 dp[unfolded dp0]]
    show "(case dp of (_, t, u) \<Rightarrow> do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) =
      return (case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
      by (auto simp: dp0 changed_ptyped[OF ok1 pi1(6) bt1 pv(1)] changed_ptyped[OF ok1 pi1(6) bt1 pv(2)]
        ch_def return_def)
  qed
  have body: "SIMPL alg env dps = do {
      st \<leftarrow> foldrW (SIMPL0 alg) dps (env, [], []);
      case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st}}"
    by (subst SIMPL.simps) (rule refl)
  show ?case
  proof (cases "\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u")
    case False
    have "okW (SIMPL alg env dps) st1" using r1(1) s1(1) ex False
      by (subst body) (auto simp: dps'_def return_def)
    moreover have "heads_unb env1 dp" if "dp \<in> set (ffs @ frs)" for dp
    proof -
      obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
      with that have "(rb, t, u) \<in> set dps'" by (auto simp: dps'_def)
      with False have "\<not> ch t" "\<not> ch u" by auto
      then show ?thesis unfolding dp heads_unb_def prod.case ch_def by blast
    qed
    ultimately show ?thesis using s1 by (intro exI[of _ st1] exI[of _ \<rho>1]) (auto simp: psimpl_res_def)
  next
    case True
    then obtain rb t u where dp: "(rb, t, u) \<in> set dps'" and cht: "ch t \<or> ch u" by blast
    obtain s x T where s: "s \<in> {t, u}" "head_of s = Var x T" "vt_lookup (tenv env1) x \<noteq> None"
      using cht unfolding ch_def by blast
    have hb: "heads_unb env (rb, t, u)" using s1(10) dp by (auto simp: dps'_def)
    then have xu: "vt_lookup (tenv env) x = None" using s(1,2) unfolding heads_unb_def prod.case by blast
    let ?y = "(x, tsubst \<rho>1 T)"
    have "?y \<in> vps (inst \<rho>1 s)" using vps_head_of[OF s(2)] by (force simp: vps_inst)
    moreover have "vps (inst \<rho>1 s) \<subseteq> ivps \<rho>1 dps'" using dp s(1) by force
    moreover have "ivps \<rho>1 dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)" using s1(7) by (auto simp: dps'_def)
    ultimately have xr: "?y \<in> reach (instE \<rho> env) (ivps \<rho> dps)" by blast
    have xin: "?y \<in> unb (instE \<rho> env) (ivps \<rho> dps)" using xr xu by (simp add: unb_def lk_def)
    have xout: "?y \<notin> unb (instE \<rho>1 env1) (ivps \<rho>1 dps')"
    proof -
      from s(3) obtain U w where b: "vt_lookup (tenv env1) x = Some (U, w)" by auto
      have pv: "pvtyped env1 W s" using pvtyped_pcinv[OF c1 dp] s(1) by auto
      then have T: "tcons ?\<theta>1 T" "tnorm ?\<theta>1 T = tnorm ?\<theta>1 (W x)"
        using vps_head_of[OF s(2)] by (auto simp: pvtyped_def)
      have "tnorm ?\<theta>1 U = tnorm ?\<theta>1 (W x)" using pi1(6) b unfolding wcons_def by blast
      moreover have ac1: "tacyc ?\<theta>1" "tcons_env ?\<theta>1" using tinv_tacyc[OF pi1(2)] tinv_tcons_env[OF pi1(2)] by simp_all
      moreover have "tsol ?\<theta>1 \<rho>1" using pcinvD(2)[OF s1(2)] by (simp add: gsol_def)
      ultimately have "tsubst \<rho>1 U = tsubst \<rho>1 T"
        using tsubst_tnorm[OF ac1, of \<rho>1 U] tsubst_tnorm[OF ac1, of \<rho>1 T] T bt1[OF b] by simp
      with b show ?thesis by (simp add: unb_def lk_def)
    qed
    have v1: "ivps \<rho>1 dps' \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)" using s1(7) by (auto simp: dps'_def)
    have exi: "extends (instE \<rho>1 env1) (instE \<rho> env)"
      by (rule extends_instE_tagree[OF Suc.prems(2) pextendsD(1)[OF s1(3)] s1(5)])
    have sub: "unb (instE \<rho>1 env1) (ivps \<rho>1 dps') \<subseteq> unb (instE \<rho> env) (ivps \<rho> dps)"
    proof
      fix y assume y: "y \<in> unb (instE \<rho>1 env1) (ivps \<rho>1 dps')"
      then have "y \<in> reach (instE \<rho>1 env1) (ivps \<rho>1 dps')" by (simp add: unb_def)
      with s1(6) have "y \<in> reach (instE \<rho> env) (ivps \<rho>1 dps' \<union> ivps \<rho> dps)" by blast
      then have "y \<in> reach (instE \<rho> env) (ivps \<rho> dps)"
        using reach_absorb[OF v1, of "{}"] by simp
      moreover have "lk (instE \<rho> env) (fst y) (snd y) = None"
        using y extends_lk[OF exi] by (cases "lk (instE \<rho> env) (fst y) (snd y)") (auto simp: unb_def)
      ultimately show "y \<in> unb (instE \<rho> env) (ivps \<rho> dps)" by (simp add: unb_def)
    qed
    have "finite (vps_dp dp)" for dp by (cases dp) simp
    then have fin: "finite (unb (instE \<rho> env) (ivps \<rho> dps))" by (intro finite_unb) simp
    have "card (unb (instE \<rho>1 env1) (ivps \<rho>1 dps')) < card (unb (instE \<rho> env) (ivps \<rho> dps))"
      using sub xin xout by (intro psubset_card_mono[OF fin]) blast
    with Suc.prems(1) have lt: "card (unb (instE \<rho>1 env1) (ivps \<rho>1 dps')) < n" by simp
    from Suc.IH[OF lt c1] obtain st' \<rho>2 where r2: "okW (SIMPL alg env1 dps') st'"
      "psimpl_res alg ar A W \<tau>' \<sigma> \<rho>1 dps' env1 \<rho>2 st'" by blast
    have "okW (SIMPL alg env dps) st'" using r1(1) s1(1) ex True r2(1)
      by (subst body) (auto simp: dps'_def return_def)
    moreover have "psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>2 st'"
    proof -
      obtain env2 ffs2 frs2 where st': "st' = (env2, ffs2, frs2)" by (cases st')
      from r2(2) st' have r: "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 (ffs2 @ frs2)" "pextends env2 env1"
        "maxidx env1 \<le> maxidx env2" "tagree (maxidx env1) \<rho>1 \<rho>2"
        "\<And>X. reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho>1 env1) (X \<union> ivps \<rho>1 dps')"
        "ivps \<rho>2 (ffs2 @ frs2) \<subseteq> reach (instE \<rho>1 env1) (ivps \<rho>1 dps')"
        "\<forall>dp\<in>set ffs2. pff_shape env2 W dp" "\<forall>dp\<in>set frs2. pfr_shape env2 W dp"
        "\<forall>dp\<in>set (ffs2 @ frs2). heads_unb env2 dp" "fch W (tyenv env2) (tyenv env1) ffs2"
        by (auto simp: psimpl_res_def)
      have "reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)" for X
        using r(5)[of X] s1(6)[of "X \<union> ivps \<rho>1 dps'"] reach_absorb[OF v1, of X] by (auto simp: Un_ac)
      moreover have "ivps \<rho>2 (ffs2 @ frs2) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
        using r(6) s1(6)[of "ivps \<rho>1 dps'"] reach_absorb[OF v1, of "{}"] by auto
      moreover have "pextends env2 env" by (rule pextends_trans[OF r(2) s1(3)])
      moreover have "maxidx env \<le> maxidx env2" using s1(4) r(3) by simp
      moreover have "tagree (maxidx env) \<rho> \<rho>2" by (rule tagree_trans[OF s1(5) r(4) s1(4)])
      moreover have "fch W (tyenv env2) (tyenv env) ffs2" using fch_down[OF r(10) pextendsD(2)[OF s1(3)]] .
      ultimately show ?thesis using r st' by (simp add: psimpl_res_def)
    qed
    ultimately show ?thesis by blast
  qed
qed

theorem SIMPL_pcomplete:
  "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps \<Longrightarrow>
    \<exists>st' \<rho>'. okW (SIMPL alg env dps) st' \<and> psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>' st'"
  using SIMPL_pcomplete_aux[OF lessI] by blast

end

end
