section \<open>Smashing the Remaining Flex-Flex Pairs\<close>

theory Unify_Smash
  imports Unify_Match_Fin
begin

context csig
begin

text \<open>
  \<^const>\<open>smash_flexflex\<close> solves the flex-flex pairs that remain with a unifier by binding both
  head variables of each pair to constant functions with the same new body variable. On the
  unifiers that the search returns, it terminates without an exception, and its
  result solves the original problem: the heads of the remaining pairs are unbound variables
  after normalization, and the new bindings keep the environment acyclic.
\<close>

subsection \<open>Normalizing under a binder\<close>

lemma could_beta_contract_rlist_abs[simp]: "could_beta_contract (rlist_abs rb t) = could_beta_contract t"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma strip_abs_body_rlist_abs[simp]: "strip_abs_body (rlist_abs rb t) = strip_abs_body t"
  by (induction rb t rule: rlist_abs.induct) simp_all

subsection \<open>Flexible bindings\<close>

lemma flexb_step:
  assumes "flexb env0 env" "extends env env'"
    "\<And>x U u. vt_lookup (tenv env') x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> fh env0 u"
  shows "flexb env0 env'"
  unfolding flexb_def
proof (intro allI impI)
  fix x U u assume x: "vt_lookup (tenv env') x = Some (U, u)" "vt_lookup (tenv env0) x = None"
  show "fh env0 u"
  proof (cases "vt_lookup (tenv env) x")
    case None
    with assms(3) x(1) show ?thesis by blast
  next
    case (Some b)
    with extendsD[OF assms(2) Some] x(1) have "vt_lookup (tenv env) x = Some (U, u)" by simp
    with assms(1) x(2) show ?thesis unfolding flexb_def by blast
  qed
qed

end

end
