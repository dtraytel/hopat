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

end
