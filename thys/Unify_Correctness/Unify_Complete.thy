section \<open>Completeness of Higher-Order Unification\<close>

theory Unify_Complete
  imports Unify_Match_Complete Unify_Flexflex_Complete Unify_Pull_Fin Unify_Sound
begin

context pure_sig
begin

text \<open>
  Completeness of the search \<^const>\<open>hounifiers\<close> and of \<^const>\<open>unifiers\<close>, up to the search bound
  and for solutions that satisfy the arity condition \<^const>\<open>mcp_kokK\<close> for the arity bound of the
  configuration: for a problem in the invariants \<^const>\<open>sinv\<close> of the termination proof with a
  solution \<open>(\<rho>, \<sigma>)\<close> (\<^const>\<open>scinv\<close>), the search has a unifier with flex-flex pairs and a solution of
  its environment and its pairs that agrees with \<open>(\<rho>, \<sigma>)\<close> on the (type) variables of index at
  most \<^const>\<open>maxidx\<close> of the problem's environment.

  The proof is by induction on the measure \<^const>\<open>mcp_meas\<close> of the solution: \<^const>\<open>SIMPL\<close> does
  not increase it (@{thm [source] SIMPL_meas}), and \<^const>\<open>MATCH\<close> strictly decreases it
  (@{thm [source] MATCH_complete}); hence a node with a flex-rigid pair has a positive measure, and
  its depth is within the search bound. The flex-flex pairs at the leaves are treated by
  \<^const>\<open>add_ffpair\<close>, which raises no exception on the flex-flex pairs of \<^const>\<open>SIMPL\<close>
  (@{thm [source] SIMPL_add_ffpair_ok}) and keeps their solutions
  (@{thm [source] foldrW_add_ffpair_complete_aux}).
\<close>

subsection \<open>Simplification\<close>

text \<open>\<^const>\<open>SIMPL\<close> succeeds on a problem with a solution, with an agreeing solution of its result:\<close>

lemma uc_SIMPL_ok:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env dps" and inv: "scinv \<rho> \<sigma> env dps X A"
  obtains env' ffs frs \<rho>' \<sigma>' where "okW (SIMPL alg env dps) (env', ffs, frs)"
    "simpl_post A K X env (env', ffs, frs)" "scinv \<rho>' \<sigma>' env' (frs @ ffs) X A"
    "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  have cu: "cuok (SIMPL alg env dps) (simpl_post A K X env)" by (rule SIMPL_term[OF fin si])
  obtain st where ok: "okW (SIMPL alg env dps) st" and P: "simpl_post A K X env st"
  proof (cases "\<exists>evs. SIMPL alg env dps = Some (evs, Err CANTUNIFY)")
    case True
    then obtain evs where "SIMPL alg env dps = Some (evs, Err CANTUNIFY)" by blast
    with SIMPL_complete[OF this fin si inv] show ?thesis by simp
  next
    case False
    with cu that show ?thesis unfolding xokW_def by blast
  qed
  obtain env' ffs frs where st: "st = (env', ffs, frs)" by (cases st)
  from ok obtain evs where "SIMPL alg env dps = Some (evs, Ok st)" by blast
  from SIMPL_complete[OF this fin si inv] st obtain \<rho>' \<sigma>' where
    "scinv \<rho>' \<sigma>' env' (frs @ ffs) X A" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    by auto
  with ok P st that show ?thesis by blast
qed


subsection \<open>The flex-flex pairs of \<^const>\<open>SIMPL\<close>\<close>

text \<open>
  The analogue of @{thm [source] foldrW_add_ffpair_complete} for the flex-flex pairs of a result of
  \<^const>\<open>SIMPL\<close> without flex-rigid pairs, which need not satisfy \<^const>\<open>ffeta\<close>: the treatment
  succeeds by @{thm [source] SIMPL_add_ffpair_ok}, and a solution of the pairs extends to a
  solution of the resulting environment and the remaining pairs.
\<close>

lemma uc_ffpair_complete:
  assumes fin: "finite X" "finite K" and si: "sinv A K X env dps"
    and ok: "okW (SIMPL alg env dps) (env', ffs, [])" and inv: "scinv \<rho> \<sigma> env' ffs X A"
  shows "\<exists>env'' tps \<sigma>'. okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps) \<and>
    scinv \<rho> \<sigma>' env'' (tdps tps) X A \<and> sagree (maxidx env') \<sigma> \<sigma>' \<and> tyenv env'' = tyenv env' \<and>
    extends env' env''"
proof -
  from SIMPL_add_ffpair_ok[OF fin si ok] obtain env'' tps where
    f: "okW (foldrW (add_ffpair alg) ffs (env', [])) (env'', tps)" and fv: "finv A K env' env''" by blast
  have ei'': "einv A K env''" and th: "tyenv env'' = tyenv env'" and ext: "extends env' env''"
    using fv by (simp_all add: finv_def)
  have "simpl_post A K X env (env', ffs, [])" by (rule cuok_okW_P[OF SIMPL_term[OF fin si] ok])
  then have si': "sinv A K X env' ffs" by (simp add: simpl_post_def)
  note i = scinvD[OF inv]
  have p: "\<forall>(rb, t, u)\<in>set ffs. upok A env' rb X t u" by (rule sc_sinv_pok[OF si'])
  have tsol': "tsol (tyenv env'') \<rho>" using solutionD(2)[OF i(1)] th by simp
  have dv: "dvars ffs \<subseteq> X \<union> evars env'"
    using p unfolding dvars_def by (fastforce dest: upokD(1,2))
  have vi: "vinv \<rho> env' (X \<union> dvars (ffs @ tdps []))"
    using vinv_hn[of \<rho> env' X X "dvars ffs"] i(3) dv by simp
  from foldrW_add_ffpair_complete_aux[OF f tsol' i(1,2) _ vi] i(6,7) obtain \<sigma>' where
    sol': "solution \<rho> \<sigma>' env''" and sa: "sagree (maxidx env') \<sigma> \<sigma>'" and ds': "dsolved \<rho> \<sigma>' (tdps tps)"
    by auto
  have ds: "dstep env' ffs env'' (tdps tps)" using foldrW_add_ffpair_sound[OF f] by simp
  have tv: "tvinv A env''" using ei'' by (simp add: einv_def)
  have "scinv \<rho> \<sigma>' env'' (tdps tps) X A"
    by (rule scinv_step[OF inv p ds sol' tagree_refl sa ds' tv]) (simp add: th)
  with f sa th ext show ?thesis by blast
qed


subsection \<open>The search\<close>

text \<open>
  The search below a node with a solution whose measure fits into the search bound has a unifier
  with flex-flex pairs, with a solution of its environment and pairs that agrees with the
  solution of the node on its variables.
\<close>

theorem search_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and "finite X" "finite K" "sinv A K X env dps" "scinv \<rho> \<sigma> env dps X A"
    "mcp_kokK k \<rho> (tyenv env) A K"
    "mcp_meas \<rho> \<sigma> env X = 0 \<or>
      int_of_integer td + int (mcp_meas \<rho> \<sigma> env X) \<le> int_of_integer (cfg_search_bound cfg) + 1"
  shows "\<exists>env' tps \<rho>' \<sigma>' X' A'. (\<forall>R. ev cfg (S_AddUnify td env dps R) (El_R env' tps)) \<and>
    X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
  using assms(3-)
proof (induction "mcp_meas \<rho> \<sigma> env X" arbitrary: A K X env dps \<rho> \<sigma> td rule: less_induct)
  case less
  note fin = less.prems(1,2) and si = less.prems(3) and inv = less.prems(4) and kk = less.prems(5)
    and bd = less.prems(6)
  obtain env1 ffs frs \<rho>1 \<sigma>1 where
    ok: "okW (SIMPL alg env dps) (env1, ffs, frs)" and post: "simpl_post A K X env (env1, ffs, frs)"
    and inv1: "scinv \<rho>1 \<sigma>1 env1 (frs @ ffs) X A"
    and ag1: "tagree (maxidx env) \<rho> \<rho>1" "sagree (maxidx env) \<sigma> \<sigma>1"
    by (rule uc_SIMPL_ok[OF fin si inv])
  from post have si1: "sinv A K X env1 (frs @ ffs)" and frsh: "\<forall>dp\<in>set frs. fr_shape env1 dp"
    and ss: "sstep A K X env env1"
    by (simp_all add: simpl_post_def)
  have ext1: "extends env env1" and tve1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    using ss by (simp_all add: sstep_def)
  have mx1: "maxidx env \<le> maxidx env1" and tx1: "textends (tyenv env) (tyenv env1)"
    using ext1 by (simp_all add: extends_def)
  have ei: "einv A K env" and ei1: "einv A K env1" using si si1 by (simp_all add: sinv_def)
  note x = einvD[OF ei] and x1 = einvD[OF ei1] and i = scinvD[OF inv]
    and sd1 = solutionD[OF scinvD(1)[OF inv1]]
  have "mcp_kokK k \<rho>1 (tyenv env1) A (K \<union> {})"
    by (rule mcp_kokK_ext[OF kk tx1 x1(6) x1(7) sd1(2) ag1(1) tvinv_tbelow[OF i(4) order_refl] x(6)
          tinv_tcons[OF x1(2)] tve1]) simp_all
  then have kk1: "mcp_kokK k \<rho>1 (tyenv env1) A K" by simp
  have me1: "mcp_meas \<rho>1 \<sigma>1 env1 X \<le> mcp_meas \<rho> \<sigma> env X" by (rule SIMPL_meas[OF ok fin si inv inv1 ag1])
  have ok': "okW (SIMPL (cfg_alg cfg) env dps) (env1, ffs, frs)" using ok cfg by simp
  show ?case
  proof (cases frs)
    case Nil
    have inv1': "scinv \<rho>1 \<sigma>1 env1 ffs X A" using inv1 Nil by simp
    from uc_ffpair_complete[OF fin si ok[unfolded Nil] inv1'] obtain env' tps \<sigma>' where
      f: "okW (foldrW (add_ffpair alg) ffs (env1, [])) (env', tps)"
      and inv': "scinv \<rho>1 \<sigma>' env' (tdps tps) X A" and sa: "sagree (maxidx env1) \<sigma>1 \<sigma>'"
      by auto
    have "ev cfg (S_AddUnify td env dps R) (El_R env' tps)" for R
      using ev.au_res[OF ok'[unfolded Nil] f[folded cfg]] by simp
    moreover have "sagree (maxidx env) \<sigma> \<sigma>'" by (rule sagree_trans[OF ag1(2) sa mx1])
    ultimately show ?thesis using inv' ag1(1) by blast
  next
    case (Cons dp frs')
    have si2: "sinv A K X env1 (dp # (frs' @ ffs))" using si1 Cons by simp
    have inv2: "scinv \<rho>1 \<sigma>1 env1 (dp # (frs' @ ffs)) X A" using inv1 Cons by simp
    have fr: "fr_shape env1 dp" using frsh Cons by simp
    have sh: "frs_shape dp" by (rule SIMPL_frs_shape[OF ok[unfolded Cons]])
    obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
    have mo: "MATCH_ok env1 dp" using sinv_MATCH_ok[OF sh[unfolded dp] si2[unfolded dp]] by (simp add: dp)
    from MATCH_complete[OF cfg k fin si2 fr mo inv2 kk1] obtain ms x where
      m: "okW (MATCH cfg env1 dp (frs' @ ffs)) ms" "ev cfg ms x" "mcp_mres A K X env1 \<rho>1 \<sigma>1 k x"
      by blast
    from m(3) obtain env2 dps2 A2 K2 X2 \<rho>2 \<sigma>2 where x: "x = El_E env2 dps2"
      and r: "finite X2" "finite K2" "A \<subseteq> A2" "K \<subseteq> K2" "X \<subseteq> X2" "sinv A2 K2 X2 env2 dps2"
        "scinv \<rho>2 \<sigma>2 env2 dps2 X2 A2" "extends env1 env2" "tagree (maxidx env1) \<rho>1 \<rho>2"
        "sagree (maxidx env1) \<sigma>1 \<sigma>2" "mcp_kokK k \<rho>2 (tyenv env2) A2 K2"
        "mcp_meas \<rho>2 \<sigma>2 env2 X2 < mcp_meas \<rho>1 \<sigma>1 env1 X"
      unfolding mcp_mres_def by blast
    have lt: "mcp_meas \<rho>2 \<sigma>2 env2 X2 < mcp_meas \<rho> \<sigma> env X" using r(12) me1 by simp
    then have pos: "0 < mcp_meas \<rho> \<sigma> env X" by simp
    with bd have bd': "int_of_integer td + int (mcp_meas \<rho> \<sigma> env X) \<le> int_of_integer (cfg_search_bound cfg) + 1"
      by simp
    with pos have "\<not> int_of_integer td > int_of_integer (cfg_search_bound cfg)" by linarith
    then have bound: "\<not> td > cfg_search_bound cfg" by (simp add: less_integer.rep_eq)
    have "mcp_meas \<rho>2 \<sigma>2 env2 X2 = 0 \<or>
        int_of_integer (td + 1) + int (mcp_meas \<rho>2 \<sigma>2 env2 X2) \<le> int_of_integer (cfg_search_bound cfg) + 1"
      using lt bd' by auto
    from less.hyps[OF lt r(1,2,6,7,11) this] obtain env' tps \<rho>' \<sigma>' X' A' where
      ih: "\<forall>R. ev cfg (S_AddUnify (td + 1) env2 dps2 R) (El_R env' tps)" "X2 \<subseteq> X'" "A2 \<subseteq> A'"
        "scinv \<rho>' \<sigma>' env' (tdps tps) X' A'" "tagree (maxidx env2) \<rho>2 \<rho>'" "sagree (maxidx env2) \<sigma>2 \<sigma>'"
      by blast
    have mx2: "maxidx env1 \<le> maxidx env2" using r(8) by (simp add: extends_def)
    have "\<forall>R. ev cfg (S_AddUnify td env dps R) (El_R env' tps)"
    proof
      fix R
      show "ev cfg (S_AddUnify td env dps R) (El_R env' tps)"
      proof (rule ev.au_match[OF ok'[unfolded Cons] bound m(1)])
        show "ev cfg (S_ItRight (td + 1) ms R) (El_R env' tps)"
          by (rule ev.ir_head[OF m(2)[unfolded x]]) (use ih(1) in blast)
      qed
    qed
    moreover have "X \<subseteq> X'" "A \<subseteq> A'" using r(3,5) ih(2,3) by blast+
    moreover have "tagree (maxidx env) \<rho> \<rho>'"
      by (rule tagree_trans[OF ag1(1) tagree_trans[OF r(9) ih(5) mx2] mx1])
    moreover have "sagree (maxidx env) \<sigma> \<sigma>'"
      by (rule sagree_trans[OF ag1(2) sagree_trans[OF r(10) ih(6) mx2] mx1])
    ultimately show ?thesis using ih(4) by blast
  qed
qed


subsection \<open>Completeness of \<^const>\<open>hounifiers\<close>\<close>

text \<open>
  For a problem in the invariants with a solution that satisfies the arity condition and whose
  measure is at most the search bound, the search of \<^const>\<open>hounifiers\<close> has a unifier with a
  solution of its environment and flex-flex pairs that agrees with the given one.
\<close>

theorem hounifiers_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and inv: "scinv \<rho> \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
  shows "\<exists>env' tps \<rho>' \<sigma>' X' A'. ev cfg (hounifiers rb env tus) (El_R env' tps) \<and>
    X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  have "mcp_meas \<rho> \<sigma> env X = 0 \<or>
      int_of_integer 1 + int (mcp_meas \<rho> \<sigma> env X) \<le> int_of_integer (cfg_search_bound cfg) + 1"
    using bound by (auto simp: nat_of_integer.rep_eq)
  from search_complete[OF cfg k fin si inv kk this] show ?thesis
    unfolding hounifiers_def by blast
qed

corollary hounifiers_complete_evals:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and inv: "scinv \<rho> \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
    and es: "evals cfg (hounifiers rb env tus) xs"
  shows "\<exists>env' tps \<rho>' \<sigma>' X' A'. El_R env' tps \<in> set xs \<and>
    X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
  using hounifiers_complete[OF cfg k fin si inv kk bound] evals_ev[OF es] by blast

text \<open>Together with finiteness (@{thm [source] hounifiers_fin}): pulling the search until it is
  exhausted terminates, and the unifiers it yields include one with an agreeing solution.\<close>

corollary hounifiers_complete_fin:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and inv: "scinv \<rho> \<sigma> env (map (\<lambda>(t, u). (rb, t, u)) tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
  obtains xs where "evals cfg (hounifiers rb env tus) xs" "\<forall>x\<in>set xs. rres A env x"
    "\<exists>env' tps \<rho>' \<sigma>' X' A'. El_R env' tps \<in> set xs \<and>
      X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  from hounifiers_fin[OF cfg fin si] obtain xs where
    es: "evals cfg (hounifiers rb env tus) xs" and rs: "\<forall>x\<in>set xs. rres A env x"
    unfolding fin_def by blast
  from hounifiers_complete_evals[OF cfg k fin si inv kk bound es] es rs that show ?thesis by blast
qed


subsection \<open>Completeness of \<^const>\<open>unifiers\<close>\<close>

text \<open>
  The pattern unification of the input pairs, one after the other: a solution of the original
  problem extends to a solution of each intermediate environment, and \<open>Unif\<close> is not raised. The
  pairs keep their meaning in the agreeing solutions, since their variables and type variables
  are those of the original environment \<open>env0\<close>.
\<close>

lemma uc_foldM_unify_complete:
  assumes p0: "\<forall>(t, u)\<in>set tus0. upok A env0 [] X t u" and inv0: "scinv \<rho>0 \<sigma>0 env0 (tdps tus0) X A"
  shows "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<Longrightarrow> set tus \<subseteq> set tus0 \<Longrightarrow>
    scinv \<rho> \<sigma> env [] X A \<Longrightarrow> tagree (maxidx env0) \<rho>0 \<rho> \<Longrightarrow> sagree (maxidx env0) \<sigma>0 \<sigma> \<Longrightarrow>
    extends env0 env \<Longrightarrow> tvars_env (tyenv env0) \<subseteq> tvars_env (tyenv env) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>\<rho>' \<sigma>'. scinv \<rho>' \<sigma>' env' [] X A \<and>
      tagree (maxidx env0) \<rho>0 \<rho>' \<and> sagree (maxidx env0) \<sigma>0 \<sigma>'))"
proof (induction tus arbitrary: env \<rho> \<sigma> r)
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons tu tus)
  obtain t u where tu: "tu = (t, u)" by (cases tu)
  have tu0: "(t, u) \<in> set tus0" using Cons.prems(2) tu by simp
  have p: "upok A env0 [] X t u" using p0 tu0 by blast
  note pd = upokD[OF p] and i0 = scinvD[OF inv0] and i = scinvD[OF Cons.prems(3)]
  have ext0: "extends env0 env" by (rule Cons.prems(6))
  from Cons.prems(1) tu obtain r1 where u1: "unify alg t u env = Some r1"
    by (cases "unify alg t u env") (simp_all add: bindM_def)
  have "\<exists>e T. e \<turnstile> inst \<rho>0 t : T \<and> e \<turnstile> inst \<rho>0 u : T"
    using i0(6) tu0 unfolding dtyped_def by fastforce
  then obtain e T where ty0: "e \<turnstile> inst \<rho>0 t : T" "e \<turnstile> inst \<rho>0 u : T" by blast
  have eq0: "ap \<rho>0 \<sigma>0 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>0 \<sigma>0 u"
    using i0(7) tu0 unfolding dsolved_def by fastforce
  note a = sc_pok_agree[OF p i0(4) i0(3) Cons.prems(4,5)]
  let ?Y = "X \<union> (vars t \<union> vars u)"
  have Ysub: "vars t \<union> vars u \<subseteq> X \<union> evars env" using pd(1,2) evars_extends[OF ext0] by blast
  have viY: "vinv \<rho> env ?Y" using vinv_hn[of \<rho> env X X "vars t \<union> vars u"] i(3) Ysub by simp
  have tvt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3,4) Cons.prems(7) by blast+
  have vtY: "btvars [] \<union> vtvars ?Y \<subseteq> tvars_env (tyenv env) \<union> A"
    using i(5) tvt vtvars_vars[of t] vtvars_vars[of u] by (auto simp: vtvars_def btvars_def)
  have ci: "cinv \<rho> \<sigma> env e [] ?Y A" unfolding cinv_def using i(1,2,4) viY vtY by (simp add: bs_env_Nil)
  have ct: "cterm \<rho> env e [] A t T" "cterm \<rho> env e [] A u T"
    unfolding cterm_def using ty0 a(1,2) pd(7,8) tvt by simp_all
  have eq: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using eq0 a(3,4) by simp
  have c: "ccon \<rho> \<sigma> env e [] ?Y A (Some r1)"
    by (rule step_cpD[OF unif_complete[OF u1[unfolded unify_def]] ci _ ct eq]) blast
  show ?case
  proof (cases r1)
    case (Err e')
    then have "r = Err e'" using Cons.prems(1) u1 tu by (simp add: bindM_def)
    with c Err show ?thesis by (simp add: ccon_def)
  next
    case (Ok env1)
    from c Ok obtain \<rho>1 \<sigma>1 where c1: "cinv \<rho>1 \<sigma>1 env1 e [] ?Y A" "tagree (maxidx env) \<rho> \<rho>1"
      "sagree (maxidx env) \<sigma> \<sigma>1" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
      unfolding ccon_def by auto
    have ext1: "extends env env1" by (rule step_okD(1)[OF unif_sound[OF u1[unfolded unify_def] Ok]])
    have inv1: "scinv \<rho>1 \<sigma>1 env1 [] X A"
      using c1(1) vinv_mono[of \<rho>1 env1 ?Y X] unfolding cinv_def scinv_def by auto
    have f1: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env1 = Some r"
      using Cons.prems(1) u1 Ok tu by (simp add: bindM_def)
    have mx: "maxidx env0 \<le> maxidx env" using ext0 by (simp add: extends_def)
    from Cons.IH[OF f1 _ inv1 tagree_trans[OF Cons.prems(4) c1(2) mx] sagree_trans[OF Cons.prems(5) c1(3) mx]
        extends_trans[OF ext0 ext1]] Cons.prems(2,7) c1(4)
    show ?thesis by auto
  qed
qed

text \<open>
  Completeness of \<^const>\<open>unifiers\<close>, as for \<^const>\<open>hounifiers\<close> on the pairs under no binders.
  The arity condition and the search bound are needed only when pattern unification gives up.
\<close>

theorem unifiers_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (tdps tus)" and inv: "scinv \<rho> \<sigma> env (tdps tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
    and un: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs"
  shows "\<exists>env' tps \<rho>' \<sigma>' X' A'. El_R env' tps \<in> set xs \<and>
    X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  have p0: "\<forall>(t, u)\<in>set tus. upok A env [] X t u" using sc_sinv_pok[OF si] by auto
  obtain r where r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r"
    using un by (cases "foldM (\<lambda>(t, u) env. unify alg t u env) tus env")
      (simp_all add: unifiers_def handle_def bindM_def)
  have inv0: "scinv \<rho> \<sigma> env [] X A" by (rule scinv_mono[OF inv]) simp
  note fc = uc_foldM_unify_complete[OF p0 inv r order_refl inv0 tagree_refl sagree_refl extends_refl order_refl]
  show ?thesis
  proof (cases r)
    case (Ok env')
    with r un have "s = S_Single (El_R env' [])" by (simp add: unifiers_def handle_def bindM_def return_def)
    with es have "xs = [El_R env' []]" by (simp add: evals_Single)
    with fc Ok show ?thesis by fastforce
  next
    case (Err e)
    show ?thesis
    proof (cases e)
      case Pattern
      with r Err un have "s = hounifiers [] env tus"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      with es hounifiers_complete_evals[OF cfg k fin si inv kk bound] show ?thesis by simp
    next
      case (Unif tr)
      with fc Err show ?thesis by simp
    qed (use r Err un in \<open>simp_all add: unifiers_def handle_def bindM_def raise_def\<close>)
  qed
qed

end

end
