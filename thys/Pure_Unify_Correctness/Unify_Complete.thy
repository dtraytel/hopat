section \<open>Completeness of Higher-Order Unification\<close>

theory Unify_Complete
  imports Unify_Flexflex_Complete Unify_Dfs
begin

text \<open>
  Completeness of \<^const>\<open>hounifiers\<close> up to the search bound: for every well-typed solution
  \<open>\<sigma>\<close> of the problem whose size (\<^const>\<open>mu\<close>, the sum of the sizes of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal forms
  of the values of the variables) does not exceed the search bound, the search tree has a
  unifier with flex-flex pairs that is satisfied, together with its flex-flex pairs, by an
  extension \<open>\<sigma>'\<close> of \<open>\<sigma>\<close>: \<open>\<sigma>\<close> is an instance of the unifier on the variables of the problem. By
  the adequacy of the depth-first search (theory \<open>Unify_Dfs\<close>), every enumeration of the
  unifiers that terminates contains such a unifier.

  The proof is by induction on the measure: \<^const>\<open>SIMPL\<close> does not increase it
  (@{thm [source] SIMPL_complete}), and \<^const>\<open>MATCH\<close> strictly decreases it
  (@{thm [source] MATCH_complete}). The flex-flex pairs at the leaves are treated by
  \<^const>\<open>add_ffpair\<close> (@{thm [source] foldrW_add_ffpair_complete}).
\<close>

subsection \<open>The search tree\<close>

lemma vsz_pos: "0 < vsz \<tau>' \<sigma> y"
  by (simp add: vsz_def lsize_pos)

text \<open>\<^const>\<open>SIMPL\<close> does not increase the measure.\<close>

lemma simpl_res_mu:
  assumes "simpl_res ar V \<tau>' \<sigma> dps env (env', ffs, frs)"
  shows "mu \<tau>' \<sigma> env' (frs @ ffs) \<le> mu \<tau>' \<sigma> env dps"
proof -
  from assms have ext: "extends env' env" and r: "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps)"
    and v: "vps_dps (ffs @ frs) \<subseteq> reach env (vps_dps dps)"
    by (auto simp: simpl_res_def)
  have sub: "unb env' (vps_dps (frs @ ffs)) \<subseteq> unb env (vps_dps dps)"
  proof
    fix y assume y: "y \<in> unb env' (vps_dps (frs @ ffs))"
    then have "y \<in> reach env (vps_dps (frs @ ffs) \<union> vps_dps dps)" using r by (auto simp: unb_def)
    moreover have "vps_dps (frs @ ffs) \<subseteq> reach env (vps_dps dps)" using v by auto
    ultimately have "y \<in> reach env (vps_dps dps)"
      using reach_absorb[of "vps_dps (frs @ ffs)" env "vps_dps dps" "{}"] by simp
    moreover have "lk env (fst y) (snd y) = None"
      using y extends_lk[OF ext] by (cases "lk env (fst y) (snd y)") (auto simp: unb_def)
    ultimately show "y \<in> unb env (vps_dps dps)" by (simp add: unb_def)
  qed
  have "finite (vps_dp dp)" for dp by (cases dp) simp
  then have "finite (unb env (vps_dps dps))" by (intro finite_unb) simp
  from sum_mono2[OF this sub, of "vsz \<tau>' \<sigma>"] show ?thesis unfolding mu_def by simp
qed

text \<open>A flex-rigid pair contributes its unbound head variable to the measure.\<close>

lemma mu_pos:
  assumes "fr_shape V dp" "heads_unb env dp" "dp \<in> set dps"
  shows "0 < mu \<tau>' \<sigma> env dps"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from assms(1) obtain v T where ht: "head_of t = Var v T" by (auto simp: fr_shape_def dp elim!: is_Var.elims)
  have "vt_lookup (tenv env) v = None" using assms(2) ht by (cases v) (auto simp: heads_unb_def dp)
  moreover have "(v, T) \<in> vps_dps dps"
    using vps_head_of[OF ht] assms(3) by (auto simp: dp intro!: bexI[of _ "(rb, t, u)"])
  ultimately have y: "(v, T) \<in> unb env (vps_dps dps)"
    using reach_incl[of "vps_dps dps" env] by (auto simp: unb_def lk_def)
  have "finite (vps_dp dp)" for dp by (cases dp) simp
  then have "finite (unb env (vps_dps dps))" by (intro finite_unb) simp
  from member_le_sum[OF y _ this, of "vsz \<tau>' \<sigma>"] vsz_pos[of \<tau>' \<sigma> "(v, T)"] show ?thesis
    by (simp add: mu_def)
qed

text \<open>
  The search tree below a node with a solution whose measure fits into the search bound has a
  unifier that is satisfied by an extension of the solution.
\<close>

theorem search_complete:
  assumes "cinv ar V \<tau>' \<sigma> env dps"
    "mu \<tau>' \<sigma> env dps = 0 \<or>
      int_of_integer td + int (mu \<tau>' \<sigma> env dps) \<le> int_of_integer (cfg_search_bound cfg) + 1"
  shows "\<exists>env' tps \<sigma>'. (\<forall>R. ev cfg (S_AddUnify td env dps R) (El_R env' tps)) \<and>
    closed_on UNIV \<sigma>' \<and> sat \<sigma>' env' \<and> tsolved \<sigma>' tps \<and> agree (maxidx env) \<sigma> \<sigma>'"
  using assms
proof (induction "mu \<tau>' \<sigma> env dps" arbitrary: V \<sigma> env dps td rule: less_induct)
  case less
  from SIMPL_complete[OF less.prems(1), of "cfg_alg cfg"] obtain st' where
    sp: "okW (SIMPL (cfg_alg cfg) env dps) st'" and sr: "simpl_res ar V \<tau>' \<sigma> dps env st'"
    by blast
  obtain env1 ffs frs where st': "st' = (env1, ffs, frs)" by (cases st')
  from sr st' have c1: "cinv ar V \<tau>' \<sigma> env1 (ffs @ frs)" and mx1: "maxidx env1 = maxidx env"
    and ffsh: "\<forall>dp\<in>set ffs. ff_shape V dp" and frsh: "\<forall>dp\<in>set frs. fr_shape V dp"
    and hu: "\<forall>dp\<in>set (ffs @ frs). heads_unb env1 dp"
    by (auto simp: simpl_res_def)
  have mu1: "mu \<tau>' \<sigma> env1 (frs @ ffs) \<le> mu \<tau>' \<sigma> env dps" using simpl_res_mu[OF sr[unfolded st']] .
  show ?case
  proof (cases frs)
    case Nil
    have "cinv ar V \<tau>' \<sigma> env1 ffs" using c1 Nil by simp
    from foldrW_add_ffpair_complete[OF this, of "cfg_alg cfg"] ffsh hu obtain env' tps' V' \<sigma>' where
      r0: "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) (env', tps')" "cinv ar V' \<tau>' \<sigma>' env' []"
      "tsolved \<sigma>' tps'" "agree (maxidx env1) \<sigma> \<sigma>'"
      by auto
    define r where "r = (env', tps')"
    have r: "okW (foldrW (add_ffpair (cfg_alg cfg)) ffs (env1, [])) r" "solution V' \<tau>' \<sigma>' (fst r)"
      "tsolved \<sigma>' (snd r)" "agree (maxidx env1) \<sigma> \<sigma>'"
      using r0 cinvD(2)[OF r0(2)] by (simp_all add: r_def)
    have "ev cfg (S_AddUnify td env dps R) (El_R (fst r) (snd r))" for R
      using ev.au_res[OF sp[unfolded st' Nil] r(1)] .
    then show ?thesis using r(2-4) mx1 solutionD[OF r(2)] by auto
  next
    case (Cons dp frs')
    have c2: "cinv ar V \<tau>' \<sigma> env1 (dp # (frs' @ ffs))" using c1 Cons by (auto simp: cinv_def)
    have frdp: "fr_shape V dp" and hdp: "heads_unb env1 dp" using frsh hu Cons by auto
    have mueq: "mu \<tau>' \<sigma> env1 (dp # (frs' @ ffs)) = mu \<tau>' \<sigma> env1 (frs @ ffs)"
      using Cons by (simp add: mu_def)
    have "0 < mu \<tau>' \<sigma> env1 (frs @ ffs)" using mu_pos[OF frdp hdp] Cons by simp
    with mu1 less.prems(2) have "\<not> int_of_integer td > int_of_integer (cfg_search_bound cfg)" by linarith
    then have bound: "\<not> td > cfg_search_bound cfg" by (simp add: less_integer.rep_eq)
    from MATCH_complete[OF c2 frdp hdp, of cfg] obtain ms env'' dps'' V'' \<sigma>'' where
      m: "okW (MATCH cfg env1 dp (frs' @ ffs)) ms" "ev cfg ms (El_E env'' dps'')"
      "cinv ar V'' \<tau>' \<sigma>'' env'' dps''" "agree (maxidx env1) \<sigma> \<sigma>''" "maxidx env1 \<le> maxidx env''"
      "mu \<tau>' \<sigma>'' env'' dps'' < mu \<tau>' \<sigma> env1 (dp # (frs' @ ffs))"
      by blast
    have lt: "mu \<tau>' \<sigma>'' env'' dps'' < mu \<tau>' \<sigma> env dps" using m(6) mueq mu1 by simp
    have "mu \<tau>' \<sigma>'' env'' dps'' = 0 \<or>
        int_of_integer (td + 1) + int (mu \<tau>' \<sigma>'' env'' dps'') \<le> int_of_integer (cfg_search_bound cfg) + 1"
      using lt less.prems(2) by (auto simp: plus_integer.rep_eq)
    from less.hyps[OF lt m(3) this] obtain env' tps \<sigma>' where
      ih: "\<forall>R. ev cfg (S_AddUnify (td + 1) env'' dps'' R) (El_R env' tps)" "closed_on UNIV \<sigma>'"
      "sat \<sigma>' env'" "tsolved \<sigma>' tps" "agree (maxidx env'') \<sigma>'' \<sigma>'"
      by blast
    have "ev cfg (S_AddUnify td env dps R) (El_R env' tps)" for R
    proof (rule ev.au_match[OF sp[unfolded st' Cons] bound m(1)])
      show "ev cfg (S_ItRight (td + 1) ms R) (El_R env' tps)" by (rule ev.ir_head[OF m(2)]) (use ih(1) in blast)
    qed
    moreover have "agree (maxidx env) \<sigma> \<sigma>'" using agree_trans[OF m(4) ih(5) m(5)] mx1 by simp
    ultimately show ?thesis using ih(2-4) by blast
  qed
qed


subsection \<open>Completeness of \<open>hounifiers\<close>\<close>

text \<open>
  For a problem in the invariant (in particular, with well-typed terms and environment) and a
  well-typed solution \<open>\<sigma>\<close> of size at most the search bound, every terminating enumeration of the
  unifiers of \<^const>\<open>hounifiers\<close> contains a unifier with flex-flex pairs that, with its pairs,
  is satisfied by an extension of \<open>\<sigma>\<close>.
\<close>

theorem hounifiers_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and bound: "mu \<tau>' \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus) \<le> nat_of_integer (cfg_search_bound cfg)"
    and es: "evals cfg (hounifiers rb env tus) xs"
  shows "\<exists>env' tps \<sigma>'. El_R env' tps \<in> set xs \<and>
    closed_on UNIV \<sigma>' \<and> sat \<sigma>' env' \<and> tsolved \<sigma>' tps \<and> agree (maxidx env) \<sigma> \<sigma>'"
proof -
  have "mu \<tau>' \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus) = 0 \<or>
      int_of_integer 1 + int (mu \<tau>' \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus)) \<le>
        int_of_integer (cfg_search_bound cfg) + 1"
    using bound by (auto simp: nat_of_integer.rep_eq)
  from search_complete[OF inv this] obtain env' tps \<sigma>' where
    "\<forall>R. ev cfg (S_AddUnify 1 env (map (\<lambda>(t, u). (rb, t, u)) tus) R) (El_R env' tps)"
    "closed_on UNIV \<sigma>'" "sat \<sigma>' env'" "tsolved \<sigma>' tps" "agree (maxidx env) \<sigma> \<sigma>'"
    by blast
  moreover from this(1) have "El_R env' tps \<in> set xs"
    using evals_ev[OF es] by (simp add: hounifiers_def)
  ultimately show ?thesis by blast
qed

end
