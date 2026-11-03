section \<open>Soundness of Higher-Order Unification\<close>

theory Unify_Sound
  imports Unify_Pull_Sound
begin

context pure_sig
begin

text \<open>
  \<^const>\<open>unifiers\<close> tries pattern unification first and falls back to \<^const>\<open>hounifiers\<close> if
  a term is not a pattern. Every element of an enumeration of its result is a unifier with
  flex-flex pairs: a step from the input pairs to the flex-flex pairs.
\<close>

lemma evals_Empty: "evals cfg S_Empty xs \<Longrightarrow> xs = []"
  by (erule evals.cases) (auto simp: pull_simps returnW_def)

lemma evals_Single: "evals cfg (S_Single y) xs \<Longrightarrow> xs = [y]"
  by (erule evals.cases) (auto simp: pull_simps returnW_def dest: evals_Empty)

lemma foldM_unify_dstep:
  assumes "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) tus env) env'"
  shows "dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env' []"
  using assms
proof (induction rule: ok_foldM_induct)
  case (Nil b)
  then show ?case by (simp add: dstep_refl)
next
  case (Cons x xs b b1 b')
  obtain t u where x: "x = (t, u)" by force
  from Cons.hyps(1) have "unif alg' [] t u b = Some (Ok b1)" by (simp add: x unify_def)
  from unif_sound[OF this refl] have "dstep b [([], t, u)] b1 []" by (rule step_ok_dstep)
  from dstep_frame[OF this, of "map (\<lambda>(t, u). ([], t, u)) xs"] Cons.IH
  show ?case by (simp add: x) (rule dstep_trans)
qed

theorem unifiers_sound:
  assumes u: "unifiers alg' env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "x \<in> set xs"
  shows "\<exists>env' tps. x = El_R env' tps \<and> dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env' (tdps tps)"
proof (cases "foldM (\<lambda>(t, u) env. unify alg' t u env) tus env")
  case None
  with u show ?thesis by (simp add: unifiers_def handle_def bindM_def)
next
  case (Some r)
  show ?thesis
  proof (cases r)
    case (Ok env')
    with Some u have "s = S_Single (El_R env' [])"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    with es have "xs = [El_R env' []]" by (simp add: evals_Single)
    with x have "x = El_R env' []" by simp
    moreover have "dstep env (map (\<lambda>(t, u). ([], t, u)) tus) env' []"
      by (rule foldM_unify_dstep) (use Some Ok in simp)
    ultimately show ?thesis by auto
  next
    case (Err e)
    show ?thesis
    proof (cases e)
      case Pattern
      with Some Err u have "s = hounifiers [] env tus"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      with hounifiers_sound[of cfg "[]" env tus xs x] es x show ?thesis by simp
    next
      case (Unif tr)
      with Some Err u have "s = S_Empty" by (simp add: unifiers_def handle_def bindM_def return_def)
      with es have "xs = []" by (simp add: evals_Empty)
      with x show ?thesis by simp
    qed (use Some Err u in \<open>simp_all add: unifiers_def handle_def bindM_def raise_def\<close>)
  qed
qed

end

end
