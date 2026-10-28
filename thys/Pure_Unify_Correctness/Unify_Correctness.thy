section \<open>Correctness of the Steps of Higher-Order Unification\<close>

theory Unify_Correctness
  imports Unify_Soundness
begin

text \<open>
  The results about the model of \<^file>\<open>~~/src/Pure/unify.ML\<close> (session \<open>Pure_Unify\<close>),
  collected in one place. As for \<^const>\<open>Pure_Pattern.unify\<close> (session
  \<open>Pure_Pattern_Correctness\<close>), a Pure term is interpreted as a de Bruijn term \<^typ>\<open>dB\<close> of
  session \<open>Nipkow_Grobauer_Pattern\<close> through \<^const>\<open>tr\<close>, and an environment denotes the closed
  substitutions \<open>\<sigma>\<close> that satisfy its bindings modulo \<open>\<beta>\<eta>\<close> (\<^const>\<open>sat\<close>). Two terms are
  \<^emph>\<open>equivalent in\<close> \<open>env\<close> (\<open>env \<Turnstile> s \<approx> t\<close>, \<^const>\<open>env_equiv\<close>) if every such \<open>\<sigma>\<close> makes their
  translations \<open>\<beta>\<eta>\<close>-equal.

  We treat the two functions of \<open>unify.ML\<close> that, on their own, solve a disagreement pair:
  the on-the-fly \<open>\<eta>\<close>-normalization \<^const>\<open>eta_norm\<close> and the assignment \<^const>\<open>assignment\<close>.
  Both are proved \<^emph>\<open>sound\<close>: the environment they return still identifies the terms they
  were given. These are the building blocks of \<open>SIMPL\<close> (Huet's simplification phase); the
  soundness of the full enumeration of unifiers (\<open>SIMPL\<close>, \<open>MATCH\<close> and the lazy search
  \<^const>\<open>Pure_Unify.pull\<close>) is not formalized here and is instead supported by the exhaustive
  differential test against Pure's \<open>Unify\<close> (theory \<open>Pure_Unify.Pure_Unify_Test\<close>).
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

end
