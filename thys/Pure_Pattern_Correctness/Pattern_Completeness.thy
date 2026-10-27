section \<open>Completeness of Pattern Unification\<close>

theory Pattern_Completeness
  imports Pattern_Soundness Pattern_Solutions
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
  On \<open>\<beta>\<close>-normal patterns in an acyclic environment of patterns, \<^const>\<open>unify\<close> terminates
  (@{thm [source] unify_term}) and does not give up (@{thm [source] unify_sound}), so it returns a
  most general unifier whenever a unifier exists.
\<close>

theorem unify_complete_pattern:
  assumes "acyc env" "wf_env ar env" "env_ppat env" "fresh_env env"
    and "env_typed V env"
    and "wf_term ar 0 s" "wf_term ar 0 t" "ppat s" "ppat t"
    and "has_type V [] s T" "has_type V [] t T" "below (maxidx env) s" "below (maxidx env) t"
    and "solution V \<tau>' \<sigma> env" "unifies \<sigma> (tr s) (tr t)"
  shows "\<exists>env'. unify alg s t env = Some (Ok env') \<and>
    (\<exists>V' \<sigma>'. agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and> solution V' \<tau>' \<sigma>' env')"
proof -
  from unify_term[OF assms(1-4,6-9,12,13)] obtain r where un: "unify alg s t env = Some r"
    by blast
  from unify_complete[OF un assms(2,5,4,6,7,10-15)] unify_sound(5)[OF un assms(2,5,4,6,7,10-13)]
    assms(3,8,9) un
  show ?thesis by auto
qed


subsection \<open>Unification of patterns is decidable\<close>

text \<open>
  A solution whose values contain only rigid atoms can be retyped: new variables (beyond \<open>k\<close>) are
  mapped to free variables of the type given by the old typing.
\<close>

lemma solution_retype:
  assumes sol: "solution V' (tau V') \<sigma> env'" and rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (\<sigma> n). rigid_code m"
    and ag: "agreeV k V V'"
  defines "\<sigma>'' \<equiv> \<lambda>n. case atom_of n of
    AVar x \<Rightarrow> if n = code (AVar x) \<and> k < snd x then dB.Var (code (AFree STR '''' (V x))) else \<sigma> n
  | _ \<Rightarrow> \<sigma> n"
  shows "closed_on UNIV \<sigma>''" "typed_on (range code) (tau V) (tau V) \<sigma>''" "rigid_subst \<sigma>''"
    "agree k \<sigma> \<sigma>''"
proof -
  note s = solutionD[OF sol]
  show "closed_on UNIV \<sigma>''"
    unfolding closed_on_def
  proof
    fix n show "no_loose_bound (\<sigma>'' n) 0"
      using closed_onD[OF s(1)] by (auto simp: \<sigma>''_def split: atom.splits)
  qed
  show "rigid_subst \<sigma>''"
    using s(3) by (auto simp: rigid_subst_def rigid_code_def \<sigma>''_def)
  show "agree k \<sigma> \<sigma>''"
    by (auto simp: agree_def \<sigma>''_def split: atom.splits if_splits)
  show "typed_on (range code) (tau V) (tau V) \<sigma>''"
    unfolding typed_on_def
  proof (intro ballI allI)
    fix n e assume "n \<in> range code"
    then obtain a where n: "n = code a" by blast
    have retype: "(e, tau V) \<turnstile> \<sigma> n : U" if "(e, tau V') \<turnstile> \<sigma> n : U" for U
    proof (rule typing_free_cong[OF that])
      fix F assume "F \<in> FV (\<sigma> n)"
      from rig \<open>n \<in> range code\<close> this have "rigid_code F" by blast
      then show "tau V' F = tau V F" by (auto simp: rigid_code_def)
    qed
    show "(e, tau V) \<turnstile> \<sigma>'' n : tau V n"
    proof (cases a)
      case (AVar x)
      show ?thesis
      proof (cases "k < snd x")
        case False
        with ag have "V' x = V x" by (cases x) (simp add: agreeV_def)
        with typed_onD[OF s(2) \<open>n \<in> range code\<close>, of e] retype False show ?thesis
          by (simp add: \<sigma>''_def n AVar)
      qed (auto simp: \<sigma>''_def n AVar)
    qed (use rigid_substD[OF s(3)] in \<open>auto simp: \<sigma>''_def n\<close>)
  qed
qed

text \<open>
  On \<open>\<beta>\<close>-normal patterns in an acyclic environment of patterns, \<^const>\<open>unify\<close> is a decision
  procedure for unifiability relative to the environment: it returns an environment if a solution
  of \<open>env\<close> unifies \<open>s\<close> and \<open>t\<close>, and raises \<open>Unif\<close> otherwise.
\<close>

theorem unify_decides:
  assumes ac: "acyc env" and wf: "wf_env ar env" and epp: "env_ppat env" and fr: "fresh_env env"
    and ety: "env_typed V env"
    and ws: "wf_term ar 0 s" and wt: "wf_term ar 0 t" and ps: "ppat s" and pt: "ppat t"
    and tys: "has_type V [] s T" and tyt: "has_type V [] t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
  shows "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow>
      (\<exists>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env \<and> unifies \<sigma> (tr s) (tr t))"
    and "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow>
      \<not> (\<exists>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env \<and> unifies \<sigma> (tr s) (tr t))"
proof -
  let ?U = "\<exists>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
  note snd = unify_sound[OF _ wf ety fr ws wt tys tyt bs bt]
  have ok: ?U if un: "unify alg s t env = Some (Ok env')" for env'
  proof -
    note s1 = snd(1)[OF un refl] and s3 = snd(3)[OF un refl ac epp ps pt]
    from snd(2)[OF un refl] obtain V' where agV: "agreeV (maxidx env) V V'"
      and ety': "env_typed V' env'" and fr': "fresh_env env'" by blast
    note es = env_solution[OF conjunct1[OF s3] conjunct1[OF conjunct2[OF s1]] ety']
    let ?\<sigma> = "env_sol env' V'"
    from s1 solutionD(1,4)[OF es(1)] have sat: "sat ?\<sigma> env" and uni: "unifies ?\<sigma> (tr s) (tr t)"
      by blast+
    have rig: "\<forall>n\<in>range code. \<forall>m\<in>FV (?\<sigma> n). rigid_code m" using es(2) by blast
    note rt = solution_retype[OF es(1) rig agV]
    define \<sigma>'' where "\<sigma>'' = (\<lambda>n. case atom_of n of
      AVar x \<Rightarrow> if n = code (AVar x) \<and> maxidx env < snd x then dB.Var (code (AFree STR '''' (V x)))
        else ?\<sigma> n
    | _ \<Rightarrow> ?\<sigma> n)"
    note rt = rt[folded \<sigma>''_def]
    have "sat \<sigma>'' env" by (rule sat_agree[OF sat fr rt(4)])
    moreover have "unifies \<sigma>'' (tr s) (tr t)"
      using uni mk_subst_agree[OF bs rt(4)] mk_subst_agree[OF bt rt(4)] by (simp add: unifies_def)
    ultimately show ?thesis using rt(1-3) by (auto simp: solution_def)
  qed
  show "(\<exists>env'. unify alg s t env = Some (Ok env')) \<longleftrightarrow> ?U"
    using ok unify_complete_pattern[OF ac wf epp fr ety ws wt ps pt tys tyt bs bt] by blast
  obtain r where un: "unify alg s t env = Some r"
    using unify_term[OF ac wf epp fr ws wt ps pt bs bt] by blast
  have "r \<noteq> Err Pattern" using snd(5)[OF un] epp ps pt by blast
  moreover have "(\<exists>u. r = Err (Unif u)) \<longleftrightarrow> \<not> ?U"
  proof
    assume "\<exists>u. r = Err (Unif u)"
    then show "\<not> ?U" using snd(4)[OF un] by blast
  next
    assume nU: "\<not> ?U"
    show "\<exists>u. r = Err (Unif u)"
    proof (cases r)
      case (Ok env')
      with ok un nU show ?thesis by blast
    next
      case (Err e)
      with snd(6)[OF un] \<open>r \<noteq> Err Pattern\<close> show ?thesis by blast
    qed
  qed
  ultimately show "(\<exists>u. unify alg s t env = Some (Err (Unif u))) \<longleftrightarrow> \<not> ?U" using un by simp
qed

end
