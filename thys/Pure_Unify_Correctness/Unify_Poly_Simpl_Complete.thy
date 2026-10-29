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
      (\<forall>dp\<in>set (ffn @ frn). heads_unb env dp))"

lemma psresD:
  assumes "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' st'"
  obtains env' ffn frn where "st' = (env', ffn @ ffs, frn @ frs)" "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn)"
    "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    "ivps \<rho>' (ffn @ frn) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
  using assms by (cases st') (auto simp: psres_def)

lemma psresI:
  assumes "pcinv alg ar A W \<rho>' \<tau>' \<sigma> env' (ffn @ frn)"
    "pextends env' env" "maxidx env \<le> maxidx env'" "tagree (maxidx env) \<rho> \<rho>'"
    "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    "ivps \<rho>' (ffn @ frn) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> pff_shape env' W dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> pfr_shape env' W dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
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
    "\<And>dp. dp \<in> set (ffn1 @ frn1) \<Longrightarrow> heads_unb env dp"
    by blast
  from psresD[OF assms(2)[unfolded s1(1)]] obtain env2 ffn2 frn2 where
    s2: "st2 = (env2, ffn2 @ ffn1 @ ffs, frn2 @ frn1 @ frs)"
    "pcinv alg ar A W \<rho>2 \<tau>' \<sigma> env2 (ffn2 @ frn2)" "pextends env2 env1" "maxidx env1 \<le> maxidx env2"
    "tagree (maxidx env1) \<rho>1 \<rho>2"
    "\<And>X. reach (instE \<rho>2 env2) X \<subseteq> reach (instE \<rho>1 env1) (X \<union> ivps \<rho>1 dps2)"
    "ivps \<rho>2 (ffn2 @ frn2) \<subseteq> reach (instE \<rho>1 env1) (ivps \<rho>1 dps2)"
    "\<And>dp. dp \<in> set ffn2 \<Longrightarrow> pff_shape env2 W dp" "\<And>dp. dp \<in> set frn2 \<Longrightarrow> pfr_shape env2 W dp"
    "\<And>dp. dp \<in> set (ffn2 @ frn2) \<Longrightarrow> heads_unb env1 dp"
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
    by (rule psresI[OF c ex mx ag r vv ffh frh hh])
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
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
    by blast
  have "psres alg ar A W \<tau>' \<sigma> \<rho> dps (env, ffs, frs) \<rho>' (env', ffn @ ffs, frn @ frs)"
  proof (rule psresI[OF s(2-5) _ _ s(8-10)])
    show "reach (instE \<rho>' env') X \<subseteq> reach ?e (X \<union> ivps \<rho> dps)" for X using s(6)[of X] m[of X] by blast
    show "ivps \<rho>' (ffn @ frn) \<subseteq> reach ?e (ivps \<rho> dps)" using s(7) m' by blast
  qed
  with s(1) show ?thesis by simp
qed


text \<open>The arguments of rigid-rigid pairs with equal heads.\<close>

lemma simrands_pcomplete:
  assumes F: "\<And>i st \<rho>a. i < length as \<Longrightarrow> pcinv alg ar A W \<rho>a \<tau>' \<sigma> (fst st) [] \<Longrightarrow>
      pextends (fst st) e0 \<Longrightarrow> maxidx e0 \<le> maxidx (fst st) \<Longrightarrow> tagree (maxidx e0) \<rho>0 \<rho>a \<Longrightarrow>
      \<exists>st' \<rho>b. okW (F (rb, as ! i, bs ! i) st) st' \<and> psres alg ar A W \<tau>' \<sigma> \<rho>a [(rb, as ! i, bs ! i)] st \<rho>b st'"
    and h: "\<nexists>f u. h = f $ u"
    and same: "\<And>\<rho>'. tagree (maxidx e0) \<rho>0 \<rho>' \<Longrightarrow>
      map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) = map (instd \<rho>0) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs))"
  shows "length as = length bs \<Longrightarrow> pcinv alg ar A W \<rho>1 \<tau>' \<sigma> (fst st) [] \<Longrightarrow> pextends (fst st) e0 \<Longrightarrow>
    maxidx e0 \<le> maxidx (fst st) \<Longrightarrow> tagree (maxidx e0) \<rho>0 \<rho>1 \<Longrightarrow>
    \<exists>st' \<rho>2. okW (simrands F rb u0 (list_comb h as) (list_comb h bs) st) st' \<and>
      psres alg ar A W \<tau>' \<sigma> \<rho>1 (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) st \<rho>2 st'"
  using F same
proof (induction as arbitrary: bs st \<rho>1 rule: rev_induct)
  case Nil
  then have "bs = []" by simp
  moreover have "simrands F rb u0 h h st = returnW st" using h by (cases h) simp_all
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
    if "i < length as" "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> (fst st) []" "pextends (fst st) e0"
      "maxidx e0 \<le> maxidx (fst st)" "tagree (maxidx e0) \<rho>0 \<rho>1" for i st \<rho>1
    using snoc.prems(6)[where i = i and st = st and \<rho>a = \<rho>1] that bs by (simp add: nth_append)
  have sameL: "map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) @ [instd \<rho>' (rb, a, b)] =
      map (instd \<rho>0) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) @ [instd \<rho>0 (rb, a, b)]"
    if "tagree (maxidx e0) \<rho>0 \<rho>'" for \<rho>'
    using snoc.prems(7)[OF that] unfolding zs by simp
  have same': "map (instd \<rho>') (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) =
      map (instd \<rho>0) (map (\<lambda>(a, b). (rb, a, b)) (zip as bs'))"
    and samel: "instd \<rho>' (rb, a, b) = instd \<rho>0 (rb, a, b)"
    if "tagree (maxidx e0) \<rho>0 \<rho>'" for \<rho>'
    using sameL[OF that] by (simp_all only: append1_eq_conv)
  from snoc.IH[OF bs(2) snoc.prems(2-5) F' same'] obtain st1 \<rho>1' where
    r1: "okW (simrands F rb u0 (list_comb h as) (list_comb h bs') st) st1"
      "psres alg ar A W \<tau>' \<sigma> \<rho>1 (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) st \<rho>1' st1"
    by blast
  from psresD[OF r1(2)[unfolded st]] obtain env2 ffn frn where
    s1: "st1 = (env2, ffn @ ffs1, frn @ frs1)" "pcinv alg ar A W \<rho>1' \<tau>' \<sigma> env2 (ffn @ frn)"
      "pextends env2 env1" "maxidx env1 \<le> maxidx env2" "tagree (maxidx env1) \<rho>1 \<rho>1'"
    by blast
  have c1: "pcinv alg ar A W \<rho>1' \<tau>' \<sigma> (fst st1) []" using pcinv_Nil[OF s1(2)] s1(1) by simp
  have e1: "pextends (fst st1) e0" using pextends_trans[OF s1(3)] snoc.prems(3) st s1(1) by simp
  have m1: "maxidx e0 \<le> maxidx (fst st1)" using snoc.prems(4) s1(1,4) st by simp
  have a1: "tagree (maxidx e0) \<rho>0 \<rho>1'"
    using tagree_trans[OF snoc.prems(5) s1(5)] snoc.prems(4) st by simp
  from snoc.prems(6)[where i = "length as" and st = st1 and \<rho>a = \<rho>1'] c1 e1 m1 a1 bs obtain st2 \<rho>2 where
    r2: "okW (F (rb, a, b) st1) st2" "psres alg ar A W \<tau>' \<sigma> \<rho>1' [(rb, a, b)] st1 \<rho>2 st2"
    by (auto simp: nth_append)
  have sm: "map (instd \<rho>1') [(rb, a, b)] = map (instd \<rho>1) [(rb, a, b)]"
    using samel[OF a1] samel[OF snoc.prems(5)] by simp
  have "okW (simrands F rb u0 (list_comb h (as @ [a])) (list_comb h bs) st) st2"
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

end
