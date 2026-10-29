section \<open>Soundness of Higher-Order Unification\<close>

theory Unify_Correctness
  imports Unify_Occurs Unify_Pull
begin

text \<open>
  The results about the model of \<^file>\<open>~~/src/Pure/unify.ML\<close> (session \<open>Pure_Unify\<close>),
  collected in one place. As for \<^const>\<open>Pure_Pattern.unify\<close> (session
  \<open>Pure_Pattern_Correctness\<close>), a Pure term is interpreted as a de Bruijn term \<^typ>\<open>dB\<close> of
  session \<open>Nipkow_Grobauer_Pattern\<close> through \<^const>\<open>tr\<close>, and an environment denotes the closed
  substitutions \<open>\<sigma>\<close> that satisfy its bindings modulo \<open>\<beta>\<eta>\<close> (\<^const>\<open>sat\<close>). Two terms are
  \<^emph>\<open>equivalent in\<close> \<open>env\<close> (\<open>env \<Turnstile> s \<approx> t\<close>, \<^const>\<open>env_equiv\<close>) if every such \<open>\<sigma>\<close> makes their
  translations \<open>\<beta>\<eta>\<close>-equal.

  We prove soundness of the whole search of \<open>unify.ML\<close>, from the individual steps up to the
  lazy enumeration \<^const>\<open>Pure_Unify.pull\<close>:
  \<^item> the on-the-fly \<open>\<eta>\<close>-normalization \<^const>\<open>eta_norm\<close> and the assignment step
    \<^const>\<open>assignment\<close> (below);
  \<^item> the occurs checks \<^const>\<open>occurs_terms\<close> and \<^const>\<open>rigid_occurs_term\<close>, which are sound
    and, for acyclic environments, complete with respect to reachability through the bindings
    (theory \<open>Unify_Occurs\<close>); assignments keep the environment acyclic;
  \<^item> the simplification phase \<^const>\<open>SIMPL\<close>: the resulting pairs and environment reduce
    the input pairs (theory \<open>Unify_Simpl\<close>), and the flex-rigid pairs are saturated
    (theory \<open>Unify_Shape\<close>);
  \<^item> the projections and imitations of \<^const>\<open>MATCH\<close> (theory \<open>Unify_Match\<close>), stated as an
    invariant \<^const>\<open>sinv\<close> of the lazy sequences with one rule per closure;
  \<^item> the treatment of the remaining flex-flex pairs \<^const>\<open>add_ffpair\<close> (theory
    \<open>Unify_Flexflex\<close>);
  \<^item> pulling the sequences (theory \<open>Unify_Pull\<close>): every element of the sequence of
    \<^const>\<open>hounifiers\<close> is a unifier.

  Completeness of the search up to the search bound is proved in theory \<open>Unify_Complete\<close>.
\<close>


subsection \<open>Soundness of on-the-fly \<open>\<eta>\<close>-normalization\<close>

text \<open>
  \<^const>\<open>eta_norm\<close> only \<open>\<eta>\<close>-expands its argument (relative to the term's fast type), so on a
  proper term in an environment with an empty type environment it returns a proper term that
  is \<open>\<beta>\<eta>\<close>-equivalent to the input, and hence equivalent to it in every environment.
\<close>

theorem eta_norm_sound:
  assumes "vt_is_empty (tyenv env)" "ok (eta_norm env rbinder t) t'" "proper t"
  shows "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t" "proper t'" "env \<Turnstile> t \<approx> t'"
  using eta_norm_equiv[OF assms(1,2,3)] env_equiv_eta_norm[OF assms] by simp_all


subsection \<open>Soundness of assignment\<close>

text \<open>
  The assignment step \<^const>\<open>assignment\<close> solves the flexible disagreement pair
  \<open>(rbinder, t, u)\<close>: if it returns \<open>env'\<close>, then \<open>env'\<close> extends \<open>env\<close> and, for every closed
  \<open>\<sigma>\<close> satisfying \<open>env'\<close>, the two sides, closed by abstracting over the binder, are
  \<open>\<beta>\<eta>\<close>-equal.
\<close>

theorem assignment_sound':
  assumes "okW (assignment alg rbinder t u env) env'"
  shows "extends env' env"
    and "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow>
      mk_subst \<sigma> (tr (rlist_abs rbinder t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rbinder u))"
  using assignment_sound[OF assms] by (auto dest: env_equivD)



subsection \<open>Occurs checks\<close>

text \<open>
  For acyclic environments, \<^const>\<open>occurs_terms\<close> decides whether the variable is reachable
  from the terms through the bindings (@{thm [source] occurs_terms_correct}), and
  \<^const>\<open>rigid_occurs_term\<close> reports an occurrence exactly when there is one
  (@{thm [source] rigid_occurs_term_sound}, @{thm [source] rigid_occurs_term_complete}).
  Assignments keep the environment acyclic (@{thm [source] assignment_acyc}).
\<close>


subsection \<open>Simplification\<close>

text \<open>\<^const>\<open>SIMPL\<close> keeps the state well-formed, and a solution of its result solves its input.\<close>

theorem SIMPL_sound'':
  assumes "okW (SIMPL alg env dpairs) st'" "wf_env ar env" "\<forall>dp\<in>set dpairs. wf_dp ar dp"
  shows "wf_st ar st'" "extends (fst st') env"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow>
      dsolved_all \<sigma> dpairs"
proof -
  from assms(1) obtain evs where "SIMPL alg env dpairs = Some (evs, UOk st')" by blast
  from SIMPL_sound[OF this _ assms(2,3), of st'] have "wf_st ar st'" "simp_rel dpairs (env, [], []) st'"
    by simp_all
  then show "wf_st ar st'" "extends (fst st') env"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow>
      dsolved_all \<sigma> dpairs"
    by (auto dest: simp_relD)
qed


subsection \<open>Enumeration of unifiers\<close>

text \<open>
  The sequence \<open>hounifiers rb env tus\<close> of well-formed input satisfies the invariant, and
  pulling a sequence that satisfies the invariant yields a unifier and a rest that satisfies it
  again. Hence every element of the enumeration is a unifier: it extends the input
  environment, and every closed substitution that satisfies it and solves its remaining
  flex-flex pairs solves the input pairs.
\<close>

theorem hounifiers_sound:
  assumes "wf_env ar env0" "binders_ok ar rb" "\<forall>(t, u)\<in>set tus. wf_tm ar rb t \<and> wf_tm ar rb u"
  shows "sinv ar (GR env0 (map (\<lambda>(t, u). (rb, t, u)) tus)) (hounifiers rb env0 tus)"
    and "sinv ar (GR env0 dps0) s \<Longrightarrow> pull cfg s = Some r \<Longrightarrow> snd r = UOk (Some (x, s')) \<Longrightarrow>
      \<exists>env tps. x = El_R env tps \<and> unifier env0 dps0 env tps \<and> sinv ar (GR env0 dps0) s'"
    and "unifier env0 (map (\<lambda>(t, u). (rb, t, u)) tus) env tps \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow>
      sat \<sigma> env \<Longrightarrow> \<forall>(t', u')\<in>set tps. mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u') \<Longrightarrow>
      (t, u) \<in> set tus \<Longrightarrow>
      mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))"
proof -
  show "sinv ar (GR env0 (map (\<lambda>(t, u). (rb, t, u)) tus)) (hounifiers rb env0 tus)"
    by (rule hounifiers_sinv[OF assms])
next
  assume "sinv ar (GR env0 dps0) s" "pull cfg s = Some r" "snd r = UOk (Some (x, s'))"
  from pull_unifier[OF this] show "\<exists>env tps. x = El_R env tps \<and> unifier env0 dps0 env tps \<and>
      sinv ar (GR env0 dps0) s'" by blast
next
  assume "unifier env0 (map (\<lambda>(t, u). (rb, t, u)) tus) env tps" "closed_on UNIV \<sigma>" "sat \<sigma> env"
    "\<forall>(t', u')\<in>set tps. mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u')" "(t, u) \<in> set tus"
  from hounifiers_unifier(2)[OF this]
  show "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))" .
qed

end
