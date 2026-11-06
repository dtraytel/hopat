section \<open>Completeness of the Results of Higher-Order Unification\<close>

theory Unify_Results2
  imports Unify_Complete Unify_Results
begin

context pure_sig
begin

text \<open>
  Together with finiteness (@{thm [source] unifiers_fin}): on a well-formed problem with a solution
  within the bounds of the configuration, \<^const>\<open>unifiers\<close> returns a sequence whose enumeration
  terminates, all of whose unifiers satisfy the result invariant \<^const>\<open>uresult\<close>, and one of which
  has a solution that agrees with the given one (@{thm [source] unifiers_complete}).
\<close>

corollary unifiers_complete_fin:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (tdps tus)" and inv: "scinv \<rho> \<sigma> env (tdps tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
  obtains s xs where "unifiers alg env tus = Some (Ok s)" "evals cfg s xs" "\<forall>x\<in>set xs. uresult A env tus x"
    "\<exists>env' tps \<rho>' \<sigma>' X' A'. El_R env' tps \<in> set xs \<and>
      X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  from unifiers_fin[OF cfg fin si] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (uresult A env tus)" by blast
  from f obtain xs where es: "evals cfg s xs" and r: "\<forall>x\<in>set xs. uresult A env tus x"
    unfolding fin_def by blast
  show thesis by (rule that[OF u es r unifiers_complete[OF cfg k fin si inv kk bound u es]])
qed


subsection \<open>The results applied\<close>

text \<open>
  After smashing its flex-flex pairs (as \<open>Unify.smash_unifiers\<close> does), a unifier unifies every
  pair of the problem when it is applied, and so do the results of \<open>Envir.norm_term\<close>:
\<close>

theorem unifiers_smash_env_apply:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and sm: "okW (smash_flexflex (env', tps)) env''" and tu: "(t, u) \<in> set tus"
  shows "env_apply env'' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> env_apply env'' u"
    and "ok (norm_term env'' t) t' \<Longrightarrow> ok (norm_term env'' u) u' \<Longrightarrow> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
proof -
  obtain e2 where sm2: "okW (smash_flexflex (env', tps)) e2" and ds: "dstep env (tdps tus) e2 []"
    and "tyenv e2 = tyenv env'"
    and ex: "\<exists>A' K' X'. finite X' \<and> finite K' \<and> A \<subseteq> A' \<and> ffres A' K' X' e2 []"
    by (rule unifiers_smash[OF cfg fin si u es x])
  from ex obtain A' K' X' where A': "A \<subseteq> A'" and ff: "ffres A' K' X' e2 []" by blast
  have e2: "e2 = env''" by (rule okW_det[OF sm2 sm])
  have ei'': "einv A' K' env''" and wi'': "winv env'' X'" using ff e2 by (simp_all add: ffres_def)
  note e'' = einvD[OF ei''] and c = canonical_solution[OF ei'' wi'']
  let ?\<rho> = "tsol0 (tyenv env'')" and ?\<sigma> = "esol (tsol0 (tyenv env'')) env''"
  have ext: "extends env env''" using dstepD(1)[OF ds] e2 by simp
  have ei: "einv A K env" and wi: "winv env X" and p: "\<forall>(rb, t, u)\<in>set (tdps tus). pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have \<rho>0: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF c(5) ext])
  have w: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi \<rho>0 c(4)] by blast+
  have dt: "dtyped ?\<rho> (tdps tus)" by (rule sinv_dtyped[OF si \<rho>0 c(4)])
  have vi: "vinv ?\<rho> env (X \<union> dvars (tdps tus))" by (rule ur_vinv_sub[OF w(2)]) (use sinv_dvars[OF si] in blast)
  note D = dstepD(2)[OF ds[unfolded e2] c(5) extends_refl w(1) dt vi]
  have viX: "vinv ?\<rho> env'' X" using D by simp
  have "dsolved ?\<rho> ?\<sigma> (tdps tus)" using D c(1) by simp
  from this[unfolded dsolved_tdps] tu have eq: "ap ?\<rho> ?\<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho> ?\<sigma> u" by blast
  have ptu: "pok A env [] X t u" using p tu by auto
  have tvs: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'')"
    using ext tvars_env_textends unfolding extends_def by blast
  have app: "env_apply env'' v = ap ?\<rho> ?\<sigma> v" if v: "v = t \<or> v = u" for v
  proof (rule env_apply_tsol0[OF e''(1) e''(3)])
    show "ttvars v \<subseteq> tvars_env (tyenv env'') \<union> A'" using pokD(3,4)[OF ptu] tvs A' v by blast
    have "vars v \<subseteq> X \<union> evars env''" using pokD(1,2)[OF ptu] evars_extends[OF ext] v by blast
    then show "vcons ?\<rho> (vars v \<union> evars env'')"
      using viX by (auto simp: vinv_def intro: vcons_mono)
  qed
  show "env_apply env'' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> env_apply env'' u" using eq app by simp
  assume nt: "ok (norm_term env'' t) t'" and nu: "ok (norm_term env'' u) u'"
  have nac: "acyc env''" "closed_env env''" "tacyc (tyenv env'')"
    using e''(3,6) wt_env_closed_env[OF c(2)] by blast+
  from pokD(9)[OF ptu \<rho>0 c(4)] obtain e T where "e \<turnstile> inst ?\<rho> t : T" "e \<turnstile> inst ?\<rho> u : T" by blast
  then have ws: "wt (env_apply env'' t)" "wt (env_apply env'' u)"
    using wt_ap[OF _ solutionD(3)[OF c(1)]] app by simp_all
  have "env_apply env'' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "env_apply env'' u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
    using conv_beta_eta[OF ws(1) norm_term_env_apply(1)[OF nt nac]]
      conv_beta_eta[OF ws(2) norm_term_env_apply(1)[OF nu nac]] .
  with eq app show "t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'" by (metis conv_sym conv_trans)
qed

text \<open>
  Most generality: a solution of the problem within the bounds of the configuration is, on the
  terms of the problem and up to new variables, an instance of the application of one of the
  unifiers, by a solution of its flex-flex pairs.
\<close>

corollary unifiers_most_general:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (tdps tus)" and inv: "scinv \<rho> \<sigma> env (tdps tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs"
  shows "\<exists>env' tps \<rho>' \<sigma>'. El_R env' tps \<in> set xs \<and> solution \<rho>' \<sigma>' env' \<and> dsolved \<rho>' \<sigma>' (tdps tps) \<and>
    tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
    (\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' (env_apply env' t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<and> ap \<rho>' \<sigma>' (env_apply env' u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"
proof -
  from unifiers_complete[OF cfg k fin si inv kk bound u es] obtain env' tps \<rho>' \<sigma>' X' A' where
    x: "El_R env' tps \<in> set xs" and X': "X \<subseteq> X'" and inv': "scinv \<rho>' \<sigma>' env' (tdps tps) X' A'"
    and ag: "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    by blast
  note r = unifiers_uresult[OF cfg fin si u es x]
  from uresultD(3)[OF r] obtain A'' K'' X'' e0 where A'': "A \<subseteq> A''" and ff: "ffres A'' K'' X'' env' tps"
    by blast
  have ext: "extends env env'" by (rule uresultD(2)[OF r])
  have ei': "einv A'' K'' env'" using ff by (simp add: ffres_def)
  note e' = einvD[OF ei'] and i' = scinvD[OF inv'] and i = scinvD[OF inv]
  have ei: "einv A K env" and p: "\<forall>(rb, t, u)\<in>set (tdps tus). pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have tvs: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    using ext tvars_env_textends unfolding extends_def by blast
  have fac: "ap \<rho>' \<sigma>' (env_apply env' v) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> v"
    if vv: "vars v \<subseteq> X \<union> evars env" and tv: "ttvars v \<subseteq> tvars_env (tyenv env) \<union> A"
      and tyv: "e \<turnstile> inst \<rho> v : T" for v e T
  proof -
    have tb: "tbelow (maxidx env) (ttvars v)" using tvinv_tbelow[OF einvD(1)[OF ei]] tv by blast
    have vb: "below (maxidx env) (vars v)"
      using i(3) vv unfolding vinv_def below_def by blast
    have ty': "e \<turnstile> inst \<rho>' v : T" using tyv inst_agree[OF ag(1) tb] by simp
    have vY: "vars v \<subseteq> X' \<union> evars env'" using vv X' evars_extends[OF ext] by blast
    have tt: "ttvars v \<subseteq> tvars_env (tyenv env') \<union> A''" using tv tvs A'' by blast
    have vc: "vcons \<rho>' (X' \<union> evars env')" using i'(3) by (simp add: vinv_def)
    have "ap \<rho>' \<sigma>' (env_apply env' v) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' v"
      by (rule ap_env_apply[OF i'(1) e'(3) i'(2) vc Un_upper2 vY ty' e'(6,7) unf_tcons[OF e'(1) e'(3) tt]])
    moreover have "ap \<rho>' \<sigma>' v = ap \<rho> \<sigma> v" by (rule ap_agree[OF ag tb vb])
    ultimately show ?thesis by simp
  qed
  have "ap \<rho>' \<sigma>' (env_apply env' t) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<and> ap \<rho>' \<sigma>' (env_apply env' u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    if tu: "(t, u) \<in> set tus" for t u
  proof -
    have ptu: "pok A env [] X t u" using p tu by auto
    from i(6) tu obtain e T where "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by (auto simp: dtyped_def)
    then show ?thesis using fac[of t] fac[of u] pokD(1-4)[OF ptu] by blast
  qed
  with x i'(1,7) ag show ?thesis by blast
qed

end

end
