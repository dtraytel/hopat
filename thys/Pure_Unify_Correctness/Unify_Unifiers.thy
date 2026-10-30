section \<open>Correctness of \<open>unifiers\<close>\<close>

theory Unify_Unifiers
  imports Unify_Complete Unify_Correctness
begin

text \<open>
  \<^const>\<open>unifiers\<close> first tries pattern unification (\<^const>\<open>Pure_Pattern.unify\<close>) on the pairs in
  turn, and falls back to \<^const>\<open>hounifiers\<close> if a term is not a pattern. On well-typed problems
  with ground types and an acyclic environment, pattern unification is proved terminating,
  sound and complete in session \<open>Pure_Pattern_Correctness\<close> (in the setting of empty type
  environments used here, @{thm [source] unif_term}, @{thm [source] unify_sound_Ok} and
  @{thm [source] unif_complete}), and raises only \<open>Pattern\<close> and \<open>Unif\<close>
  (@{thm [source] unif_exn}). Hence \<^const>\<open>unifiers\<close> is sound and complete as
  \<^const>\<open>hounifiers\<close>.
\<close>

subsection \<open>Well-typed problems\<close>

text \<open>The invariant \<^const>\<open>cinv\<close> without a solution:\<close>

context csig
begin

definition tyinv :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "tyinv ar V env dps \<longleftrightarrow> env_inv ar V env \<and>
    (\<forall>dp\<in>set dps. wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp)"

lemma tyinvD:
  assumes "tyinv ar V env dps"
  shows "env_inv ar V env" "dp \<in> set dps \<Longrightarrow> wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp"
  using assms by (simp_all add: tyinv_def)

lemma cinv_tyinv: "cinv ar V \<tau>' \<sigma> env dps \<longleftrightarrow> tyinv ar V env dps \<and> solution V \<tau>' \<sigma> env \<and> dsolved_all \<sigma> dps"
  by (auto simp: cinv_def tyinv_def)

lemma tyinv_transfer:
  assumes "env_inv ar V' env'" "\<forall>dp\<in>set dps. wf_dp ar dp \<and> dp_typed V dp \<and> dp_below m dp"
    "agreeV m V V'" "m \<le> maxidx env'"
  shows "tyinv ar V' env' dps"
proof -
  have "wf_dp ar dp \<and> dp_typed V' dp \<and> dp_below (maxidx env') dp" if dp: "dp \<in> set dps" for dp
  proof -
    obtain rb a b where dp': "dp = (rb, a, b)" by (cases dp)
    have h: "wf_dp ar dp \<and> dp_typed V dp \<and> dp_below m dp" using assms(2) dp by blast
    then obtain U where "wf_dp ar dp" "has_type V (map snd rb) a U" "has_type V (map snd rb) b U"
      "below m a" "below m b" using dp' by auto
    with assms(3,4) dp' show ?thesis by (auto intro: has_type_agreeV below_mono)
  qed
  with assms(1) show ?thesis by (simp add: tyinv_def)
qed

abbreviation dps_of :: "(pterm \<times> pterm) list \<Rightarrow> dpair list" where
  "dps_of tus \<equiv> map (\<lambda>(t, u). ([], t, u)) tus"

lemma dsolved_Nil: "dsolved \<sigma> ([], t, u) \<longleftrightarrow> unifies \<sigma> (tr t) (tr u)"
  by (simp add: dsolved_def unifies_def)


subsection \<open>Pattern unification of a list of pairs\<close>

lemma foldM_unify:
  assumes "tyinv ar V env (dps_of tus)"
  shows "\<exists>r. foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<and> fails_ok (Some r) \<and>
    (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V'. env_inv ar V' env' \<and> agreeV (maxidx env) V V') \<and>
      extends env' env \<and> maxidx env \<le> maxidx env' \<and>
      (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> dsolved_all \<sigma> (dps_of tus))) \<and>
    (\<forall>\<tau>' \<sigma>. solution V \<tau>' \<sigma> env \<longrightarrow> dsolved_all \<sigma> (dps_of tus) \<longrightarrow> no_unif (Some r) \<and>
      (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env')))"
  using assms
proof (induction tus arbitrary: V env)
  case Nil
  note ei = env_invD[OF tyinvD(1)[OF Nil]]
  show ?case using Nil ei sol_ext_refl[of V _ _ env ar]
    by (auto simp: return_def fails_ok_def tyinv_def)
next
  case (Cons tu tus)
  obtain t u where tu: "tu = (t, u)" by (cases tu)
  note ei = env_invD[OF tyinvD(1)[OF Cons.prems]]
  from tyinvD(2)[OF Cons.prems, of "([], t, u)"] tu obtain T where
    wt: "wf_term ar 0 t" "wf_term ar 0 u" and ty: "has_type V [] t T" "has_type V [] u T"
    and bl: "below (maxidx env) t" "below (maxidx env) u"
    by (auto simp: wf_tm_def wf_term_def)
  have bok: "binders_ok ar []" by (simp add: binders_ok_def)
  note ut = unif_term[where bs = "[]", simplified]
  note ue = unif_exn[where binders = "[]", simplified]
  note uc = unif_complete[where binders = "[]", simplified]
  from ut[OF refl tyinvD(1)[OF Cons.prems] bok wt ty bl, of alg]
  obtain r1 where r1: "unify alg t u env = Some r1" and q1: "uq ar V env [t, u] r1"
    by (auto simp: unify_def)
  have ex1: "fails_ok (Some r1)"
    using ue[OF r1[unfolded unify_def] ei(2) bok ei(3,4) wt ty bl] by simp
  have cp1: "no_unif (Some r1) \<and> (\<forall>env'. r1 = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
    if "solution V \<tau>' \<sigma> env" "unifies \<sigma> (tr t) (tr u)" for \<tau>' \<sigma>
    using uc[OF r1[unfolded unify_def] ei(2) bok ei(3,4) wt ty bl that] by simp
  show ?case
  proof (cases r1)
    case (Err e)
    have "foldM (\<lambda>(t, u) env. unify alg t u env) (tu # tus) env = Some (Err e)"
      using r1 Err tu by (simp add: bindM_def)
    then show ?thesis using ex1 cp1 Err tu by (auto simp: dsolved_Nil)
  next
    case (Ok e1)
    from q1 Ok obtain W1 where e1: "env_inv ar W1 e1" "agreeV (maxidx env) V W1" "extends e1 env"
      "maxidx env \<le> maxidx e1"
      by (auto simp: uq_def)
    have ti1: "tyinv ar W1 e1 (dps_of tus)"
      by (rule tyinv_transfer[OF e1(1) _ e1(2,4)]) (use tyinvD(2)[OF Cons.prems] in auto)
    from Cons.IH[OF ti1] obtain r2 where r2: "foldM (\<lambda>(t, u) env. unify alg t u env) tus e1 = Some r2"
      and ex2: "fails_ok (Some r2)"
      and ok2: "\<And>env'. r2 = Ok env' \<Longrightarrow> (\<exists>V'. env_inv ar V' env' \<and> agreeV (maxidx e1) W1 V') \<and>
        extends env' e1 \<and> maxidx e1 \<le> maxidx env' \<and>
        (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> dsolved_all \<sigma> (dps_of tus))"
      by blast
    have f: "foldM (\<lambda>(t, u) env. unify alg t u env) (tu # tus) env = Some r2"
      using r1 Ok tu r2 by (simp add: bindM_def)
    have snd1: "sat \<sigma> env \<and> unifies \<sigma> (tr t) (tr u)" if "closed_on UNIV \<sigma>" "sat \<sigma> e1" for \<sigma>
      using unify_sound_Ok(3)[OF r1[unfolded Ok] ei(2) wt that] .
    have okc: "(\<exists>V'. env_inv ar V' env' \<and> agreeV (maxidx env) V V') \<and>
        extends env' env \<and> maxidx env \<le> maxidx env' \<and>
        (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> dsolved_all \<sigma> (dps_of (tu # tus)))"
      if "r2 = Ok env'" for env'
    proof -
      note o = ok2[OF that]
      from o obtain V' where "env_inv ar V' env'" "agreeV (maxidx e1) W1 V'" by blast
      then have "\<exists>V'. env_inv ar V' env' \<and> agreeV (maxidx env) V V'"
        using agreeV_trans[OF e1(2) _ e1(4)] by blast
      moreover have "\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> dsolved_all \<sigma> (dps_of (tu # tus))"
        using o snd1 sat_extends tu by (fastforce simp: dsolved_Nil)
      ultimately show ?thesis using o e1(3,4) extends_trans[of env' e1 env] by auto
    qed
    have cpc: "no_unif (Some r2) \<and> (\<forall>env'. r2 = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
      if sol: "solution V \<tau>' \<sigma> env" and ds: "dsolved_all \<sigma> (dps_of (tu # tus))" for \<tau>' \<sigma>
    proof -
      have "unifies \<sigma> (tr t) (tr u)" using ds tu by (simp add: dsolved_Nil)
      from cp1[OF sol this] Ok obtain V1 \<sigma>1 where se: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 e1" by blast
      then have se1: "agreeV (maxidx env) V V1" "agree (maxidx env) \<sigma> \<sigma>1" "solution V1 \<tau>' \<sigma>1 e1"
        "env_typed V1 e1" "fresh_env e1" "wf_env ar e1" by (simp_all add: sol_ext_def)
      have "env_inv ar V1 e1" using env_invD(1)[OF e1(1)] se1(4-6) by (simp add: env_inv_def)
      then have ti: "tyinv ar V1 e1 (dps_of tus)"
        by (rule tyinv_transfer[OF _ _ se1(1) e1(4)]) (use tyinvD(2)[OF Cons.prems] in auto)
      have "dsolved_all \<sigma>1 (dps_of tus)"
      proof
        fix dp assume dp: "dp \<in> set (dps_of tus)"
        then obtain a b where "dp = ([], a, b)" "(a, b) \<in> set tus" by auto
        moreover have "below (maxidx env) a" "below (maxidx env) b"
          using tyinvD(2)[OF Cons.prems, of dp] dp \<open>dp = ([], a, b)\<close> by auto
        ultimately show "dsolved \<sigma>1 dp" using ds mk_subst_agree[OF _ se1(2)] by (auto simp: dsolved_Nil unifies_def)
      qed
      from Cons.IH[OF ti] se1(3) this obtain
        "no_unif (Some r2)" "\<forall>env'. r2 = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V1 \<tau>' \<sigma>1 e1 V' \<sigma>' env')"
        using r2 by auto
      then show ?thesis using sol_ext_trans[OF se] by blast
    qed
    show ?thesis using f ex2 okc cpc by blast
  qed
qed

subsection \<open>The results of \<^const>\<open>unifiers\<close>\<close>

lemma unifiers_cases:
  assumes "tyinv ar V env (dps_of tus)"
  obtains (ok) env' where "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some (Ok env')"
      "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
    | (unif) u where "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some (Err (Unif u))"
      "unifiers alg env tus = Some (Ok S_Empty)"
    | (pattern) "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some (Err Pattern)"
      "unifiers alg env tus = Some (Ok (hounifiers [] env tus))"
proof -
  from foldM_unify[OF assms, of alg] obtain r where
    r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r" and f: "fails_ok (Some r)" by blast
  show thesis
  proof (cases r)
    case (Ok env')
    with r show thesis by (intro ok[of env']) (simp_all add: unifiers_def handle_def bindM_def return_def)
  next
    case (Err e)
    with f have "e = Pattern \<or> (\<exists>u. e = Unif u)" by (simp add: fails_ok_def exn_ok_def)
    with r Err show thesis using unif pattern by (auto simp: unifiers_def handle_def bindM_def return_def)
  qed
qed

text \<open>\<^const>\<open>unifiers\<close> terminates without an exception.\<close>

theorem unifiers_terminates: "tyinv ar V env (dps_of tus) \<Longrightarrow> \<exists>s. unifiers alg env tus = Some (Ok s)"
  by (cases rule: unifiers_cases[of ar V env tus alg]) blast+

lemma pull_Empty: "pull cfg S_Empty = returnW None"
  by (subst pull.simps) simp

lemma pull_Single: "pull cfg (S_Single x) = returnW (Some (x, S_Empty))"
  by (subst pull.simps) simp

lemma evals_Empty: "evals cfg S_Empty xs \<Longrightarrow> xs = []"
  by (auto elim: evals.cases simp: pull_Empty returnW_def)

lemma evals_Single: "evals cfg (S_Single x) xs \<Longrightarrow> xs = [x]"
  by (erule evals.cases) (auto simp: pull_Single returnW_def dest: evals_Empty)

lemma evals_sinv:
  "evals cfg s xs \<Longrightarrow> sinv ar (GR env0 dps0) s \<Longrightarrow> x \<in> set xs \<Longrightarrow>
    \<exists>env tps. x = El_R env tps \<and> unifier env0 dps0 env tps"
proof (induction rule: evals.induct)
  case (Cons s evs y s' xs)
  from pull_unifier[OF Cons.prems(1) Cons.hyps(1)] obtain env tps where
    "y = El_R env tps" "unifier env0 dps0 env tps" "sinv ar (GR env0 dps0) s'" by auto
  with Cons.IH Cons.prems(2) show ?case by auto
qed simp

text \<open>
  Soundness: every element of an enumeration of the result of \<^const>\<open>unifiers\<close> is a unifier,
  as for \<^const>\<open>hounifiers\<close> (@{thm [source] hounifiers_sound}).
\<close>

theorem unifiers_sound:
  assumes "tyinv ar V env (dps_of tus)" "unifiers alg env tus = Some (Ok s)" "evals cfg s xs" "x \<in> set xs"
  shows "\<exists>env' tps. x = El_R env' tps \<and> unifier env (dps_of tus) env' tps"
  using assms(1)
proof (cases rule: unifiers_cases[of ar V env tus alg])
  case (ok env')
  note fo = foldM_unify[OF assms(1), of alg]
  from ok assms(2,3,4) have "x = El_R env' []" by (auto dest: evals_Single)
  moreover have "unifier env (dps_of tus) env' []" using fo ok(1) by (auto simp: unifier_def)
  ultimately show ?thesis by blast
next
  case (unif u)
  with assms(2,3,4) show ?thesis by (auto dest: evals_Empty)
next
  case pattern
  note ei = env_invD[OF tyinvD(1)[OF assms(1)]]
  have "\<forall>(t, u)\<in>set tus. wf_tm ar [] t \<and> wf_tm ar [] u"
    using tyinvD(2)[OF assms(1)] by fastforce
  from hounifiers_sound(1)[OF ei(2) _ this] have "sinv ar (GR env (dps_of tus)) (hounifiers [] env tus)"
    by (simp add: binders_ok_def)
  with pattern assms(2,3,4) show ?thesis by (auto dest: evals_sinv)
qed

text \<open>
  Completeness: for a well-typed solution \<open>\<sigma>\<close> whose size is at most the search bound, every
  terminating enumeration contains a unifier that is satisfied, with its flex-flex pairs, by an
  extension of \<open>\<sigma>\<close>, as for \<^const>\<open>hounifiers\<close> (@{thm [source] hounifiers_complete}). The
  bound is needed only when pattern unification gives up.
\<close>

theorem unifiers_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env (dps_of tus)"
    and bound: "mu \<tau>' \<sigma> env (dps_of tus) \<le> nat_of_integer (cfg_search_bound cfg)"
    and un: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs"
  shows "\<exists>env' tps \<sigma>'. El_R env' tps \<in> set xs \<and>
    closed_on UNIV \<sigma>' \<and> sat \<sigma>' env' \<and> tsolved \<sigma>' tps \<and> agree (maxidx env) \<sigma> \<sigma>'"
proof -
  have ti: "tyinv ar V env (dps_of tus)" and sol: "solution V \<tau>' \<sigma> env" and ds: "dsolved_all \<sigma> (dps_of tus)"
    using inv by (simp_all add: cinv_tyinv)
  note fo = foldM_unify[OF ti, of alg]
  have cp: "no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
    if "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r" for r
    using fo sol ds that by auto
  from ti show ?thesis
  proof (cases rule: unifiers_cases[of ar V env tus alg])
    case (ok env')
    from cp[OF ok(1)] obtain V' \<sigma>' where "sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'" by blast
    then have "closed_on UNIV \<sigma>'" "sat \<sigma>' env'" "agree (maxidx env) \<sigma> \<sigma>'"
      by (auto simp: sol_ext_def dest: solutionD)
    moreover have "El_R env' [] \<in> set xs" using ok un es by (auto dest: evals_Single)
    ultimately show ?thesis by (intro exI[of _ env'] exI[of _ "[]"] exI[of _ \<sigma>']) (simp add: tsolved_def)
  next
    case (unif u)
    with cp[OF unif(1)] show ?thesis by (simp add: no_unif_def)
  next
    case pattern
    with un have "s = hounifiers [] env tus" by simp
    with es have "evals cfg (hounifiers [] env tus) xs" by simp
    from hounifiers_complete[OF _ _ this, of ar V \<tau>' \<sigma>] inv bound show ?thesis by simp
  qed
qed

end

end
