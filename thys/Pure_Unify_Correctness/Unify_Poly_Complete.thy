section \<open>Problems with Type Variables: Completeness of Higher-Order Unification\<close>

theory Unify_Poly_Complete
  imports Unify_Poly_Flexflex_Complete Unify_Complete
begin

context csig
begin

text \<open>
  Completeness of \<^const>\<open>hounifiers\<close> for problems with type variables, up to the search bound
  and for solutions that satisfy the arity bound \<open>k\<close>: the analogue of theory
  \<^theory>\<open>Pure_Unify_Correctness.Unify_Complete\<close>. A solution consists of a ground instance \<open>\<rho>\<close>
  of the type variables and a solution \<open>\<sigma>\<close> of the ground instance of the problem. The search
  tree has a unifier with flex-flex pairs whose ground instance under an extension of \<open>\<rho>\<close> is
  satisfied, together with its flex-flex pairs, by an extension of \<open>\<sigma>\<close>.

  The proof is by induction on the measure of the ground instance: \<^const>\<open>SIMPL\<close> does not
  increase it (@{thm [source] wf_csig.SIMPL_pcomplete}), and \<^const>\<open>MATCH\<close> strictly decreases it
  (@{thm [source] wf_csig.MATCH_pcomplete}). The flex-flex pairs at the leaves are treated by
  \<^const>\<open>add_ffpair\<close> (@{thm [source] foldrW_padd_ffpair_complete}).
\<close>

subsection \<open>The search tree\<close>

definition pmu :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> tinst \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> nat" where
  "pmu \<tau>' \<sigma> \<rho> env dps = sum (vsz \<tau>' \<sigma>) (unb (instE \<rho> env) (ivps \<rho> dps))"

text \<open>\<^const>\<open>SIMPL\<close> does not increase the measure.\<close>

lemma psimpl_res_mu:
  assumes pc: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps"
    and sr: "psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>' (env', ffs, frs)"
  shows "pmu \<tau>' \<sigma> \<rho>' env' (frs @ ffs) \<le> pmu \<tau>' \<sigma> \<rho> env dps"
proof -
  from sr have ext: "pextends env env'" and ag: "tagree (maxidx env) \<rho> \<rho>'"
    and r: "\<And>X. reach (instE \<rho>' env') X \<subseteq> reach (instE \<rho> env) (X \<union> ivps \<rho> dps)"
    and v: "ivps \<rho>' (ffs @ frs) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)"
    by (auto simp: psimpl_res_def)
  have exi: "extends (instE \<rho> env) (instE \<rho>' env')" by (rule extends_instE_tagree[OF pc pextendsD(1)[OF ext] ag])
  have v': "ivps \<rho>' (frs @ ffs) \<subseteq> reach (instE \<rho> env) (ivps \<rho> dps)" using v by auto
  have sub: "unb (instE \<rho>' env') (ivps \<rho>' (frs @ ffs)) \<subseteq> unb (instE \<rho> env) (ivps \<rho> dps)"
  proof
    fix y assume y: "y \<in> unb (instE \<rho>' env') (ivps \<rho>' (frs @ ffs))"
    then have "y \<in> reach (instE \<rho> env) (ivps \<rho>' (frs @ ffs) \<union> ivps \<rho> dps)" using r by (auto simp: unb_def)
    then have "y \<in> reach (instE \<rho> env) (ivps \<rho> dps)"
      using reach_absorb[OF v', of "{}"] by simp
    moreover have "lk (instE \<rho> env) (fst y) (snd y) = None"
      using y extends_lk[OF exi] by (cases "lk (instE \<rho> env) (fst y) (snd y)") (auto simp: unb_def)
    ultimately show "y \<in> unb (instE \<rho> env) (ivps \<rho> dps)" by (simp add: unb_def)
  qed
  have "finite (vps_dp dp)" for dp by (cases dp) simp
  then have "finite (unb (instE \<rho> env) (ivps \<rho> dps))" by (intro finite_unb) simp
  from sum_mono2[OF this sub, of "vsz \<tau>' \<sigma>"] show ?thesis by (simp add: pmu_def)
qed

text \<open>A flex-rigid pair contributes the instance of its unbound head variable to the measure.\<close>

lemma pmu_pos:
  assumes "pfr_shape env W dp" "heads_unb env dp" "dp \<in> set dps"
  shows "0 < pmu \<tau>' \<sigma> \<rho> env dps"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from assms(1) obtain v T where ht: "head_of t = Var v T"
    by (auto simp: pfr_shape_def dp elim!: is_Var.elims)
  have "vt_lookup (tenv env) v = None" using assms(2) ht by (cases v) (auto simp: heads_unb_def dp)
  then have "lk (instE \<rho> env) v (tsubst \<rho> T) = None" by (simp add: lk_def)
  moreover have "(v, tsubst \<rho> T) \<in> ivps \<rho> dps"
    using vps_head_of[OF ht] assms(3) by (force simp: dp vps_inst)
  ultimately have y: "(v, tsubst \<rho> T) \<in> unb (instE \<rho> env) (ivps \<rho> dps)"
    using reach_incl[of "ivps \<rho> dps" "instE \<rho> env"] by (auto simp: unb_def)
  have "finite (vps_dp dp)" for dp by (cases dp) simp
  then have "finite (unb (instE \<rho> env) (ivps \<rho> dps))" by (intro finite_unb) simp
  from member_le_sum[OF y _ this, of "vsz \<tau>' \<sigma>"] vsz_pos[of \<tau>' \<sigma> "(v, tsubst \<rho> T)"] show ?thesis
    by (simp add: pmu_def)
qed

end

context wf_csig
begin

text \<open>
  The search tree below a node with a solution whose measure fits into the search bound has a
  unifier whose ground instance is satisfied by an extension of the solution.
\<close>

theorem psearch_complete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and "pcinv alg ar A W \<rho> \<tau>' \<sigma> env dps" "kokA k \<rho> (tyenv env) A"
    "pmu \<tau>' \<sigma> \<rho> env dps = 0 \<or>
      int_of_integer td + int (pmu \<tau>' \<sigma> \<rho> env dps) \<le> int_of_integer (cfg_search_bound cfg) + 1"
  shows "\<exists>env' tps \<sigma>' \<rho>'. (\<forall>R. ev cfg (S_AddUnify td env dps R) (El_R env' tps)) \<and>
    gsol alg ar (tyenv env') \<rho>' \<and> closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> tagree (maxidx env) \<rho> \<rho>'"
  using assms(3-5)
proof (induction "pmu \<tau>' \<sigma> \<rho> env dps" arbitrary: W \<sigma> \<rho> env dps td rule: less_induct)
  case less
  from SIMPL_pcomplete[OF less.prems(1)] obtain st' \<rho>1 where
    sp: "okW (SIMPL alg env dps) st'" and sr: "psimpl_res alg ar A W \<tau>' \<sigma> \<rho> dps env \<rho>1 st'"
    by blast
  obtain env1 ffs frs where st': "st' = (env1, ffs, frs)" by (cases st')
  from sr st' have c1: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (ffs @ frs)" and pe1: "pextends env env1"
    and mx1: "maxidx env \<le> maxidx env1" and ta1: "tagree (maxidx env) \<rho> \<rho>1"
    and ffsh: "\<forall>dp\<in>set ffs. pff_shape env1 W dp" and frsh: "\<forall>dp\<in>set frs. pfr_shape env1 W dp"
    and hu: "\<forall>dp\<in>set (ffs @ frs). heads_unb env1 dp" and fc: "fch W (tyenv env1) (tyenv env) ffs"
    by (auto simp: psimpl_res_def)
  have mu1: "pmu \<tau>' \<sigma> \<rho>1 env1 (frs @ ffs) \<le> pmu \<tau>' \<sigma> \<rho> env dps"
    by (rule psimpl_res_mu[OF less.prems(1) sr[unfolded st']])
  note pi = pinvD[OF pcinvD(1)[OF less.prems(1)]]
  note pi1 = pinvD[OF pcinvD(1)[OF c1]]
  have kk1: "kokA k \<rho>1 (tyenv env1) A"
  proof (rule kokA_textends[OF pi(2) _ pextendsD(2)[OF pe1] _ ta1 _ pi1(2) less.prems(2)])
    show "tacyc (tyenv env1)" "tcons_env (tyenv env1)" using tinv_tacyc[OF pi1(2)] tinv_tcons_env[OF pi1(2)] by simp_all
    show "tsol (tyenv env1) \<rho>1" using pcinvD(2)[OF c1] by (simp add: gsol_def)
  qed
  have sp': "okW (SIMPL (cfg_alg cfg) env dps) (env1, ffs, frs)" using sp st' cfg(1) by simp
  show ?case
  proof (cases frs)
    case Nil
    have "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 ffs" using c1 Nil by simp
    from foldrW_padd_ffpair_complete[OF this _ fc] ffsh hu Nil obtain env' tps' W' \<sigma>' where
      r0: "okW (foldrW (add_ffpair alg) ffs (env1, [])) (env', tps')" "pcinv alg ar A W' \<rho>1 \<tau>' \<sigma>' env' []"
      "tsolved \<sigma>' (itps \<rho>1 tps')" "agree (maxidx env1) \<sigma> \<sigma>'" "tyenv env' = tyenv env1"
      by auto
    have "ev cfg (S_AddUnify td env dps R) (El_R (fst (env', tps')) (snd (env', tps')))" for R
      using ev.au_res[OF sp'[unfolded Nil] r0(1)[folded cfg(1)]] .
    moreover note s = solutionD[OF pcinvD(3)[OF r0(2)]]
    moreover have "gsol alg ar (tyenv env') \<rho>1" using pcinvD(2)[OF r0(2)] .
    moreover have "agree (maxidx env) \<sigma> \<sigma>'" by (rule agree_mono[OF r0(4) mx1])
    ultimately show ?thesis using r0(3) ta1 by auto
  next
    case (Cons dp frs')
    have c2: "pcinv alg ar A W \<rho>1 \<tau>' \<sigma> env1 (dp # (frs' @ ffs))"
      using c1 Cons by (auto simp: pcinv_def pinv_def)
    have frdp: "pfr_shape env1 W dp" and hdp: "heads_unb env1 dp" using frsh hu Cons by auto
    have mueq: "pmu \<tau>' \<sigma> \<rho>1 env1 (dp # (frs' @ ffs)) = pmu \<tau>' \<sigma> \<rho>1 env1 (frs @ ffs)"
      using Cons by (simp add: pmu_def Un_ac)
    have "0 < pmu \<tau>' \<sigma> \<rho>1 env1 (frs @ ffs)" using pmu_pos[OF frdp hdp, of "frs @ ffs"] Cons by simp
    with mu1 less.prems(3) have "\<not> int_of_integer td > int_of_integer (cfg_search_bound cfg)" by linarith
    then have bound: "\<not> td > cfg_search_bound cfg" by (simp add: less_integer.rep_eq)
    from MATCH_pcomplete[OF cfg c2 kk1 frdp hdp, folded pmu_def] obtain ms env'' dps'' W'' \<sigma>'' \<rho>'' where
      m: "okW (MATCH cfg env1 dp (frs' @ ffs)) ms" "ev cfg ms (El_E env'' dps'')"
      "pcinv alg ar A W'' \<rho>'' \<tau>' \<sigma>'' env'' dps''" "kokA k \<rho>'' (tyenv env'') A"
      "agree (maxidx env1) \<sigma> \<sigma>''" "tagree (maxidx env1) \<rho>1 \<rho>''" "maxidx env1 \<le> maxidx env''"
      "pmu \<tau>' \<sigma>'' \<rho>'' env'' dps'' < pmu \<tau>' \<sigma> \<rho>1 env1 (dp # (frs' @ ffs))"
      by blast
    have lt: "pmu \<tau>' \<sigma>'' \<rho>'' env'' dps'' < pmu \<tau>' \<sigma> \<rho> env dps" using m(8) mueq mu1 by simp
    have "pmu \<tau>' \<sigma>'' \<rho>'' env'' dps'' = 0 \<or>
        int_of_integer (td + 1) + int (pmu \<tau>' \<sigma>'' \<rho>'' env'' dps'') \<le> int_of_integer (cfg_search_bound cfg) + 1"
      using lt less.prems(3) by (auto simp: plus_integer.rep_eq)
    from less.hyps[OF lt m(3,4) this] obtain env' tps \<sigma>' \<rho>' where
      ih: "\<forall>R. ev cfg (S_AddUnify (td + 1) env'' dps'' R) (El_R env' tps)" "gsol alg ar (tyenv env') \<rho>'"
      "closed_on UNIV \<sigma>'" "sat \<sigma>' (instE \<rho>' env')" "tsolved \<sigma>' (itps \<rho>' tps)"
      "agree (maxidx env'') \<sigma>'' \<sigma>'" "tagree (maxidx env'') \<rho>'' \<rho>'"
      by blast
    have "ev cfg (S_AddUnify td env dps R) (El_R env' tps)" for R
    proof (rule ev.au_match[OF sp'[unfolded Cons] bound m(1)])
      show "ev cfg (S_ItRight (td + 1) ms R) (El_R env' tps)" by (rule ev.ir_head[OF m(2)]) (use ih(1) in blast)
    qed
    moreover have "agree (maxidx env) \<sigma> \<sigma>'"
      using agree_mono[OF agree_trans[OF m(5) ih(6) m(7)] mx1] .
    moreover have "tagree (maxidx env) \<rho> \<rho>'"
      using tagree_trans[OF ta1 tagree_trans[OF m(6) ih(7) m(7)] mx1] .
    ultimately show ?thesis using ih(2-5) by blast
  qed
qed

end


context wf_csig
begin

subsection \<open>Completeness of \<open>hounifiers\<close>\<close>

text \<open>
  For a problem in the invariant and a solution, consisting of a ground instance \<open>\<rho>\<close> of the type
  variables that satisfies the arity bound and a well-typed solution \<open>\<sigma>\<close> of the ground instance
  of size at most the search bound, every terminating enumeration of the unifiers of
  \<^const>\<open>hounifiers\<close> contains a unifier with flex-flex pairs whose ground instance under an
  extension of \<open>\<rho>\<close> is, with its pairs, satisfied by an extension of \<open>\<sigma>\<close>.
\<close>

theorem hounifiers_pcomplete:
  assumes cfg: "cfg_alg cfg = alg" "k = nat_of_integer (cfg_arity_bound cfg)"
    and inv: "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus)" and kk: "kokA k \<rho> (tyenv env) A"
    and bound: "pmu \<tau>' \<sigma> \<rho> env (map (\<lambda>(t, u). (rb, t, u)) tus) \<le> nat_of_integer (cfg_search_bound cfg)"
    and es: "evals cfg (hounifiers rb env tus) xs"
  shows "\<exists>env' tps \<sigma>' \<rho>'. El_R env' tps \<in> set xs \<and> gsol alg ar (tyenv env') \<rho>' \<and>
    closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
    agree (maxidx env) \<sigma> \<sigma>' \<and> tagree (maxidx env) \<rho> \<rho>'"
proof -
  have "pmu \<tau>' \<sigma> \<rho> env (map (\<lambda>(t, u). (rb, t, u)) tus) = 0 \<or>
      int_of_integer 1 + int (pmu \<tau>' \<sigma> \<rho> env (map (\<lambda>(t, u). (rb, t, u)) tus)) \<le>
        int_of_integer (cfg_search_bound cfg) + 1"
    using bound by (auto simp: nat_of_integer.rep_eq)
  from psearch_complete[OF cfg inv kk this] obtain env' tps \<sigma>' \<rho>' where
    "\<forall>R. ev cfg (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) R) (El_R env' tps)"
    "gsol alg ar (tyenv env') \<rho>'" "closed_on UNIV \<sigma>'" "sat \<sigma>' (instE \<rho>' env')" "tsolved \<sigma>' (itps \<rho>' tps)"
    "agree (maxidx env) \<sigma> \<sigma>'" "tagree (maxidx env) \<rho> \<rho>'"
    by blast
  moreover from this(1) have "El_R env' tps \<in> set xs"
    using evals_ev[OF es] by (simp add: hounifiers_def)
  ultimately show ?thesis by blast
qed

end

end
