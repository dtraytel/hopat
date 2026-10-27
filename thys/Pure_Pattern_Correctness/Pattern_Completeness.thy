section \<open>Completeness of Pattern Unification\<close>

theory Pattern_Completeness
  imports Pattern_Soundness
begin

text \<open>
  Completeness of \<^const>\<open>unify\<close>: let \<open>\<sigma>\<close> be a solution of \<open>env\<close> (a closed, well-typed substitution
  satisfying the bindings of \<open>env\<close>) that unifies \<open>s\<close> and \<open>t\<close> modulo \<open>\<beta>\<eta>\<close>. For arbitrary
  well-typed \<open>s\<close> and \<open>t\<close>, \<^const>\<open>unify\<close> either gives up (\<open>Pattern\<close>) or returns an environment
  \<open>env'\<close> such that \<open>\<sigma>\<close> extends (on the new variables only) to a solution of \<open>env'\<close>. Together with
  @{thm [source] unify_sound}, \<open>env'\<close> is a most general unifier of \<open>s\<close> and \<open>t\<close> relative to \<open>env\<close>.
\<close>

theorem unify_complete:
  assumes un: "unify alg s t env = Some r"
    and wf: "wf_env ar env" and ety: "env_typed V env" and fr: "fresh_env env"
    and ws: "wf_term ar 0 s" and wt: "wf_term ar 0 t"
    and tys: "has_type V [] s T" and tyt: "has_type V [] t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    and sol: "solution V \<tau>' \<sigma> env" and uni: "unifies \<sigma> (tr s) (tr t)"
  shows "r = Err Pattern \<or> (\<exists>env'. r = Ok env' \<and>
    (\<exists>V' \<sigma>'. agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env'))"
proof -
  have bok: "binders_ok ar []" by (simp add: binders_ok_def)
  from unif_complete[OF un[unfolded unify_def] wf bok ety fr _ _ _ _ bs bt sol uni] ws wt tys tyt
  have c: "no_unif (Some r)" "\<And>env'. r = Ok env' \<Longrightarrow> \<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
    by simp_all
  show ?thesis
  proof (cases r)
    case (Ok env')
    with c(2) show ?thesis by (auto simp: sol_ext_def)
  next
    case (Err e)
    with unify_sound(6)[OF un wf ety fr ws wt tys tyt bs bt] c(1) show ?thesis
      by (auto simp: no_unif_def)
  qed
qed

text \<open>
  On \<open>\<beta>\<close>-normal patterns in a finite, acyclic environment of patterns, \<^const>\<open>unify\<close> terminates
  (@{thm [source] unify_term}) and does not give up (@{thm [source] unify_sound}), so it returns a
  most general unifier whenever a unifier exists.
\<close>

theorem unify_complete_pattern:
  assumes "fin_env env" "acyc env" "wf_env ar env" "env_ppat env" "fresh_env env"
    and "env_typed V env"
    and "wf_term ar 0 s" "wf_term ar 0 t" "ppat s" "ppat t"
    and "has_type V [] s T" "has_type V [] t T" "below (maxidx env) s" "below (maxidx env) t"
    and "solution V \<tau>' \<sigma> env" "unifies \<sigma> (tr s) (tr t)"
  shows "\<exists>env'. unify alg s t env = Some (Ok env') \<and>
    (\<exists>V' \<sigma>'. agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env')"
proof -
  from unify_term[OF assms(1-5,7-10,13,14)] obtain r where un: "unify alg s t env = Some r"
    by blast
  from unify_complete[OF un assms(3,6,5,7,8,11-16)] unify_sound(5)[OF un assms(3,6,5,7,8,11-14)]
    assms(4,9,10) un
  show ?thesis by auto
qed

end
