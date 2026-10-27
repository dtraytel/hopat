section \<open>Soundness of Pattern Unification\<close>

theory Pattern_Soundness
  imports Pattern_Exceptions Pattern_Termination
begin

text \<open>
  Soundness of \<^const>\<open>unify\<close> on well-typed terms \<open>s\<close> and \<open>t\<close> (not necessarily patterns or
  \<open>\<beta>\<close>-normal) in a well-formed, well-typed environment \<open>env\<close> whose variables are not newer than
  \<open>maxidx env\<close>. Every possible result is characterised:
  \<^item> \<open>Ok env'\<close>: \<open>env'\<close> extends \<open>env\<close>, every closed substitution satisfying \<open>env'\<close> satisfies \<open>env\<close>
    and unifies \<open>s\<close> and \<open>t\<close> modulo \<open>\<beta>\<eta>\<close>, and \<open>env'\<close> is again well-formed, well-typed (for an
    extension of the typing of the variables) and fresh. If the inputs are patterns in a finite,
    acyclic environment of patterns, then so is \<open>env'\<close>; hence unification problems can be chained,
    as in \<open>Unify.unifiers\<close>.
  \<^item> \<open>Err (Unif _)\<close>: no solution of \<open>env\<close> unifies \<open>s\<close> and \<open>t\<close>. \<open>Unify.unifiers\<close> treats this
    exception as final.
  \<^item> \<open>Err Pattern\<close> (give up): \<open>s\<close>, \<open>t\<close> or a binding of \<open>env\<close> is not a pattern.
  \<^item> No other exception is raised.
  Nontermination (result \<^const>\<open>None\<close>) is excluded for patterns by @{thm [source] unify_term}.
\<close>

theorem unify_sound:
  assumes un: "unify alg s t env = Some r"
    and wf: "wf_env ar env" and ety: "env_typed V env" and fr: "fresh_env env"
    and ws: "wf_term ar 0 s" and wt: "wf_term ar 0 t"
    and tys: "has_type V [] s T" and tyt: "has_type V [] t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
  shows "r = Ok env' \<Longrightarrow> extends env' env \<and> wf_env ar env' \<and>
      (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> sat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t))"
    and "r = Ok env' \<Longrightarrow>
      \<exists>V'. agreeV (maxidx env) V V' \<and> env_typed V' env' \<and> fresh_env env' \<and> maxidx env \<le> maxidx env'"
    and "r = Ok env' \<Longrightarrow> fin_env env \<Longrightarrow> acyc env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow>
      fin_env env' \<and> acyc env' \<and> env_ppat env'"
    and "r = Err (Unif u) \<Longrightarrow> solution V \<tau>' \<sigma> env \<Longrightarrow> \<not> unifies \<sigma> (tr s) (tr t)"
    and "r = Err Pattern \<Longrightarrow> \<not> ppat s \<or> \<not> ppat t \<or> \<not> env_ppat env"
    and "r = Err e \<Longrightarrow> e = Pattern \<or> (\<exists>u. e = Unif u)"
proof -
  have bok: "binders_ok ar []" by (simp add: binders_ok_def)
  have un': "unif alg [] s t env = Some r" using un by (simp add: unify_def)
  have ws': "wf_term ar (length ([] :: binders)) s" and wt': "wf_term ar (length ([] :: binders)) t"
    using ws wt by simp_all
  have tys': "has_type V (map snd ([] :: binders)) s T" and tyt': "has_type V (map snd ([] :: binders)) t T"
    using tys tyt by simp_all
  note ex = unif_exn[OF un' wf bok ety fr ws' wt' tys' tyt' bs bt]
  show "r = Ok env' \<Longrightarrow> extends env' env \<and> wf_env ar env' \<and>
      (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> sat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t))"
    using unify_sound_Ok[OF _ wf ws wt] un by blast
  show "r = Ok env' \<Longrightarrow>
      \<exists>V'. agreeV (maxidx env) V V' \<and> env_typed V' env' \<and> fresh_env env' \<and> maxidx env \<le> maxidx env'"
    using ex by (auto simp: ty_ext_def)
  show "fin_env env' \<and> acyc env' \<and> env_ppat env'"
    if r: "r = Ok env'" and "fin_env env" "acyc env" "env_ppat env" and ps: "ppat s" and pt: "ppat t"
  proof -
    have ti: "tinv ar env" using that(2-4) wf by (simp add: tinv_def)
    from unif_term[OF refl ti fr bok ws' wt' ps pt bs bt] obtain r' where
      "unif alg [] s t env = Some r'" "uq ar env [s, t] r'" by blast
    with un' r show ?thesis by (simp add: uq_def tinv_def)
  qed
  show "\<not> unifies \<sigma> (tr s) (tr t)" if r: "r = Err (Unif u)" and sol: "solution V \<tau>' \<sigma> env"
  proof
    assume uni: "unifies \<sigma> (tr s) (tr t)"
    from unif_complete[OF un' wf bok ety fr ws' wt' tys' tyt' bs bt sol uni]
    have "no_unif (Some r)" by simp
    with r show False by (simp add: no_unif_def)
  qed
  show "r = Err Pattern \<Longrightarrow> \<not> ppat s \<or> \<not> ppat t \<or> \<not> env_ppat env" using ex by blast
  show "r = Err e \<Longrightarrow> e = Pattern \<or> (\<exists>u. e = Unif u)" using ex by (simp add: fails_ok_def exn_ok_def)
qed

end
