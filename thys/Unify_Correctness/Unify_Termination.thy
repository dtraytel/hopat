section \<open>Termination of \<open>unifiers\<close>\<close>

theory Unify_Termination
  imports Unify_Search_Termination
begin

context pure_sig_gen
begin

subsection \<open>Termination of \<^const>\<open>unifiers\<close>\<close>

lemma foldM_unify_c:
  assumes fin: "finite X" "finite K"
  shows "einv A K env \<Longrightarrow> winv env X \<Longrightarrow> \<forall>(t, u)\<in>set tus. upok A env [] X t u \<Longrightarrow>
    \<exists>r. foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r \<and> upostc A K env X r"
proof (induction tus arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def upostc_refl)
next
  case (Cons p tus)
  obtain a b where p: "p = (a, b)" by force
  have pab: "upok A env [] X a b" using Cons.prems(3) p by simp
  obtain r1 where r1: "unify alg a b env = Some r1" "upostc A K env X r1"
    using unif_term_c[OF fin Cons.prems(1,2) pab] by (auto simp: unify_def dcut_def)
  show ?case
  proof (cases r1)
    case (Err e)
    then show ?thesis using r1 p by (simp add: bindM_def)
  next
    case (Ok env1)
    note u1 = upostc_OkD[OF r1(2)[unfolded Ok]]
    have ps1: "\<forall>(t, u)\<in>set tus. upok A env1 [] X t u"
      using Cons.prems(3) upok_mono[OF _ u1(3,4)] by auto
    from Cons.IH[OF u1(1,2) ps1] obtain r2 where
      r2: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env1 = Some r2" "upostc A K env1 X r2" by blast
    show ?thesis using r1(1) Ok r2(1) upostc_trans[OF r1(2)[unfolded Ok] r2(2)] p by (simp add: bindM_def)
  qed
qed

text \<open>
  \<^const>\<open>unifiers\<close> terminates on problems that satisfy the invariant of the search, also when a
  name occurs at two types: it returns a sequence whose enumeration is finite and ends normally or
  with one of the exceptions of \<^const>\<open>gexn\<close>, or it raises the clash of the two types of a name or
  the failure of \<open>mk_ff_list\<close> in pattern unification (only with loose names).
\<close>

theorem unifiers_cfin:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). ([], t, u)) tus)"
  shows "(\<exists>sq. unifiers alg env tus = return sq \<and> cfin cfg sq (\<lambda>_. True)) \<or>
    (\<exists>e. unifiers alg env tus = raise e \<and> (clashx e \<or> loose \<noteq> {} \<and> e = Failure (STR ''mk_ff_list'')))"
proof -
  have ei: "einv A K env" and wi: "winv env X" and ps: "\<forall>(t, u)\<in>set tus. upok A env [] X t u"
    using si by (auto simp: sinv_def)
  obtain r where r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r" "upostc A K env X r"
    using foldM_unify_c[OF fin ei wi ps] by blast
  have ho: "cfin cfg (hounifiers [] env tus) (\<lambda>_. True)"
    by (rule cfin_mono[OF hounifiers_cfin[OF cfg fin si]]) simp
  show ?thesis
  proof (cases r)
    case (Ok env')
    then show ?thesis using r(1) by (simp add: unifiers_def bindM_def return_def handle_def cfin_Single)
  next
    case (Err e)
    with r(2) have pe: "perr e" by simp
    then show ?thesis using r(1) Err ho
      by (cases e) (auto simp: unifiers_def bindM_def return_def handle_def raise_def)
  qed
qed

end

end
