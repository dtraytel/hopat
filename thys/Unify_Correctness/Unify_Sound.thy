section \<open>Soundness of Higher-Order Unification\<close>

theory Unify_Sound
  imports Unify_Pull_Fin
begin

context pure_sig
begin

text \<open>
  Every unifier enumerated by \<open>hounifiers\<close> is a step from the input pairs to its flex-flex pairs,
  if the input is in the invariant of the termination proof, in particular if both sides of each
  pair have the same type (theorem @{thm [source] hounifiers_fin_sound}):
\<close>

theorem hounifiers_sound:
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K"
    and si: "sinv A K X env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and es: "evals cfg (hounifiers rb env tus) xs" and x: "x \<in> set xs"
  shows "\<exists>env' tps. x = El_R env' tps \<and> dstep env (map (\<lambda>(t, u). (rb, t, u)) tus) env' (tdps tps)"
proof -
  from hounifiers_fin_sound[OF cfg fin si] obtain ys where "evals cfg (hounifiers rb env tus) ys"
    and "\<forall>y\<in>set ys. elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) y"
    unfolding fin_def by blast
  with evals_det[OF es] x have "elem_ok (GR env (map (\<lambda>(t, u). (rb, t, u)) tus)) x" by blast
  then show ?thesis by (cases x) auto
qed

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
  assumes cfg: "cfg_alg cfg = alg" and fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    and u: "unifiers alg' env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "x \<in> set xs"
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
      with es have "evals cfg (hounifiers [] env tus) xs" by simp
      from hounifiers_sound[OF cfg fin si this x] show ?thesis .
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
