section \<open>Correctness of Pattern Unification\<close>

theory Pattern_Correctness
  imports Pattern_Termination
begin

text \<open>
  The main results about \<^const>\<open>unify\<close>, collected in one place. A unification problem
  \<open>s =?= t\<close> relative to an environment \<open>env\<close> is well-formed if
  \<^item> \<open>env\<close> satisfies the invariant \<^const>\<open>env_inv\<close>: it is acyclic, well-formed, typed by \<open>V\<close>
    (an assignment of types to its variables), and fresh (its variables and bindings are not
    newer than \<open>maxidx env\<close>);
  \<^item> \<open>s\<close> and \<open>t\<close> are well-formed closed terms of the same type \<open>T\<close> whose variables are not newer
    than \<open>maxidx env\<close>.
  Neither \<open>s\<close>, \<open>t\<close> nor the bindings of \<open>env\<close> need to be patterns or \<open>\<beta>\<close>-normal.

  Terms are compared via their translation \<^const>\<open>tr\<close> into de Bruijn terms modulo \<open>\<beta>\<eta>\<close>.
  A solution of \<open>env\<close> (\<^const>\<open>solution\<close>) is a closed, well-typed substitution that fixes
  constants and free variables and satisfies the bindings of \<open>env\<close>. The problem is unifiable if a
  solution of \<open>env\<close> unifies \<open>s\<close> and \<open>t\<close>.
\<close>

locale unif_problem =
  fixes ar :: "name \<Rightarrow> nat" and V :: "indexname \<Rightarrow> ptyp" and env :: env
    and s t :: pterm and T :: ptyp
  assumes env: "env_inv ar V env"
    and wf_s: "wf_term ar 0 s" and wf_t: "wf_term ar 0 t"
    and typed_s: "has_type V [] s T" and typed_t: "has_type V [] t T"
    and below_s: "below (maxidx env) s" and below_t: "below (maxidx env) t"
begin

abbreviation unifiable :: bool where
  "unifiable \<equiv> \<exists>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"

text \<open>The results of the inductions over \<^const>\<open>unif\<close>, instantiated to the problem:\<close>

lemma binders_ok_Nil: "binders_ok ar []"
  by (simp add: binders_ok_def)

lemma unif_exn': "unify alg s t env = Some r \<Longrightarrow>
    fails_ok (Some r) \<and> (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> r \<noteq> Err Pattern) \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> (ppat s \<and> ppat t \<and> env_ppat env \<longrightarrow> env_ppat env'))"
  using unif_exn[of alg "[]" s t env r ar V T] env_invD[OF env] binders_ok_Nil wf_s wf_t typed_s typed_t
    below_s below_t
  by (simp add: unify_def)

lemma unif_complete': "unify alg s t env = Some r \<Longrightarrow> solution V \<tau>' \<sigma> env \<Longrightarrow>
    unifies \<sigma> (tr s) (tr t) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
  using unif_complete[of alg "[]" s t env r ar V T \<tau>' \<sigma>] env_invD[OF env] binders_ok_Nil wf_s wf_t
    typed_s typed_t below_s below_t
  by (simp add: unify_def)

lemma unif_term': "\<exists>r. unify alg s t env = Some r \<and> uq ar V env [s, t] r"
  using unif_term[OF refl env binders_ok_Nil, of s t T alg] wf_s wf_t typed_s typed_t below_s below_t
  by (simp add: unify_def)


subsection \<open>Termination\<close>

text \<open>\<^const>\<open>unify\<close> terminates; it returns an environment, fails, or gives up.\<close>

theorem terminates: "\<exists>r. unify alg s t env = Some r"
  using unif_term' by blast

theorem result:
  assumes "unify alg s t env = Some r"
  shows "(\<exists>env'. r = Ok env') \<or> (\<exists>u. r = Err (Unif u)) \<or> r = Err Pattern"
  using unif_exn'[OF assms] by (cases r) (auto simp: fails_ok_def exn_ok_def)


subsection \<open>Successful unification\<close>

text \<open>
  A returned environment \<open>env'\<close> extends \<open>env\<close> and satisfies the invariant again (for a typing that
  agrees with \<open>V\<close> on the old variables), so that unification problems can be chained, as in
  \<open>Unify.unifiers\<close>.
\<close>

theorem Ok_inv:
  assumes "unify alg s t env = Some (Ok env')"
  shows "\<exists>V'. env_inv ar V' env' \<and> agreeV (maxidx env) V V' \<and> extends env' env \<and>
    maxidx env \<le> maxidx env'"
  using unif_term'[of alg] assms by (auto simp: uq_def)

text \<open>
  A returned environment \<open>env'\<close> is a most general unifier of \<open>s\<close> and \<open>t\<close> relative to \<open>env\<close>:
  its solutions unify \<open>s\<close> and \<open>t\<close>, and every solution of \<open>env\<close> that unifies \<open>s\<close> and \<open>t\<close>
  extends (on the new variables) to a solution of \<open>env'\<close>. Every acyclic environment has a
  solution, so the problem is unifiable.
\<close>

theorem Ok_sound:
  assumes "unify alg s t env = Some (Ok env')" "closed_on UNIV \<sigma>" "sat \<sigma> env'"
  shows "sat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
  using unify_sound_Ok(3)[OF assms(1) env_invD(2)[OF env] wf_s wf_t assms(2,3)] .

theorem Ok_most_general:
  assumes "unify alg s t env = Some (Ok env')" "solution V \<tau>' \<sigma> env" "unifies \<sigma> (tr s) (tr t)"
  shows "\<exists>V' \<sigma>'. agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env'"
  using unif_complete'[OF assms] by (auto simp: sol_ext_def)

theorem Ok_unifiable:
  assumes un: "unify alg s t env = Some (Ok env')"
  shows unifiable
proof -
  from Ok_inv[OF un] obtain V' where inv: "env_inv ar V' env'" and agV: "agreeV (maxidx env) V V'"
    by blast
  note i = env_invD[OF inv]
  note es = env_solution[OF i(1,2,3)]
  let ?\<sigma> = "env_sol env' V'"
  from Ok_sound[OF un] solutionD(1,4)[OF es(1)] have sat: "sat ?\<sigma> env" and uni: "unifies ?\<sigma> (tr s) (tr t)"
    by blast+
  have rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (?\<sigma> n). rigid_code m" using es(2) by blast
  define \<sigma>'' where "\<sigma>'' = (\<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> maxidx env < snd x then dB.Var (code (AFree STR '''' (V x)))
      else ?\<sigma> n
  | _ \<Rightarrow> ?\<sigma> n)"
  note rt = solution_retype[OF es(1) rig agV, folded \<sigma>''_def]
  have "sat \<sigma>'' env" by (rule sat_agree[OF sat env_invD(4)[OF env] rt(4)])
  moreover have "unifies \<sigma>'' (tr s) (tr t)"
    using uni mk_subst_agree[OF below_s rt(4)] mk_subst_agree[OF below_t rt(4)] by (simp add: unifies_def)
  ultimately show ?thesis using rt(1-3) by (auto simp: solution_def)
qed

theorem Ok_patterns:
  "unify alg s t env = Some (Ok env') \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow> env_ppat env \<Longrightarrow> env_ppat env'"
  using unif_exn' by blast


subsection \<open>Failure\<close>

text \<open>Failure with \<open>Unif\<close> is final: the problem is not unifiable.\<close>

theorem Unif_not_unifiable:
  assumes "unify alg s t env = Some (Err (Unif u))"
  shows "\<not> unifiable"
  using unif_complete'[OF assms] by (auto simp: no_unif_def)

text \<open>\<^const>\<open>unify\<close> gives up only on problems that are not patterns.\<close>

theorem Pattern_not_pattern:
  assumes "unify alg s t env = Some (Err Pattern)"
  shows "\<not> (ppat s \<and> ppat t \<and> env_ppat env)"
  using unif_exn'[OF assms] by blast


subsection \<open>Decidability on patterns\<close>

text \<open>
  Hence on \<open>\<beta>\<close>-normal patterns in an environment of patterns, \<^const>\<open>unify\<close> decides
  unifiability. On other problems, it may give up both on unifiable problems
  (\<open>?F =?= c ((\<lambda>x. d) ?F)\<close>) and on non-unifiable ones (\<open>f (?F a) (?F a) =?= f b c\<close>).
\<close>

corollary decides:
  assumes "ppat s" "ppat t" "env_ppat env"
  shows "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable"
proof -
  from terminates obtain r where un: "unify alg s t env = Some r" by blast
  have "r \<noteq> Err Pattern" using Pattern_not_pattern un assms by blast
  with result[OF un] consider env' where "r = Ok env'" | u where "r = Err (Unif u)" by blast
  then show "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> unifiable"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> unifiable"
    using un Ok_unifiable Unif_not_unifiable by (cases; auto)+
qed

end

end
