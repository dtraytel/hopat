section \<open>Soundness of Higher-Order Unification\<close>

theory Unify_Sound
  imports Unify_Pull_Fin
begin

context pure_sig_gen
begin

text \<open>
  If pattern unification solves all pairs, their solution is a step from the pairs to the empty
  list. This needs no assumption on the names of the variables.
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

end

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

text \<open>
  For problems in which a name occurs with several types, and that pattern unification solves:
  the unifier that \<^const>\<open>unifiers\<close> returns solves the pairs in every solution in which the
  occurrences of each name that the resulting environment binds have one type (as
  @{thm [source] unify_sound_bound_names}; for the search of \<^const>\<open>hounifiers\<close> the steps are
  sound in \<open>pure_sig_gen\<close>, but the theorem on the search takes the types of the two sides of a
  flex-rigid pair from the invariant of the termination proof, which needs one type for each
  name).
\<close>

theorem unifiers_pattern_bound_names:
  assumes f: "ok (foldM (\<lambda>(t, u) env. unify alg' t u env) tus env) env'"
    and sol: "solution \<rho> \<sigma> env'" and wte: "wt_env \<rho> env"
    and dt: "dtyped \<rho> (map (\<lambda>(t, u). ([], t, u)) tus)"
    and bl: "below (maxidx env) (dvars (map (\<lambda>(t, u). ([], t, u)) tus) \<union> evars env)"
    and cs: "\<And>x bd T U. vt_lookup (tenv env') x = Some bd \<Longrightarrow>
      (x, T) \<in> dvars (map (\<lambda>(t, u). ([], t, u)) tus) \<union> evars env \<Longrightarrow>
      (x, U) \<in> dvars (map (\<lambda>(t, u). ([], t, u)) tus) \<union> evars env \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  shows "unifiers alg' env tus = Some (Ok (S_Single (El_R env' [])))"
    and "wt_env \<rho> env'" and "dsolved \<rho> \<sigma> (map (\<lambda>(t, u). ([], t, u)) tus)"
proof -
  let ?dps = "map (\<lambda>(t, u). ([], t, u)) tus"
  show "unifiers alg' env tus = Some (Ok (S_Single (El_R env' [])))"
    using f by (simp add: unifiers_def handle_def bindM_def return_def)
  interpret G: pure_sig_gen alg ar ctab "{x. vt_lookup (tenv env') x = None}"
    by (rule pure_sig_gen_axioms)
  have nf: "G.nfree env'" by (auto simp: G.nfree_def)
  have vi: "G.vinv \<rho> env ({} \<union> dvars ?dps)"
    unfolding G.vinv_def G.vcons_def
  proof (intro conjI allI impI)
    fix x T U assume "x \<notin> {x. vt_lookup (tenv env') x = None}"
      and m: "(x, T) \<in> {} \<union> dvars ?dps \<union> evars env" "(x, U) \<in> {} \<union> dvars ?dps \<union> evars env"
    then obtain bd where lk: "vt_lookup (tenv env') x = Some bd" by auto
    from m have "(x, T) \<in> dvars ?dps \<union> evars env" "(x, U) \<in> dvars ?dps \<union> evars env" by simp_all
    from cs[OF lk this] show "tsubst \<rho> T = tsubst \<rho> U" .
  qed (use bl in simp)
  have ds: "G.dstep env ?dps env' []" by (rule G.foldM_unify_dstep[OF f])
  from G.dstepD(2)[OF ds solutionD(2)[OF sol] extends_refl wte dt vi nf] sol
  show "wt_env \<rho> env'" and "dsolved \<rho> \<sigma> ?dps" by (auto simp: dsolved_def)
qed

end

end
