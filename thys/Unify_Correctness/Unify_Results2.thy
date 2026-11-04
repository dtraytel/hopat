section \<open>Completeness of the Results of Higher-Order Unification\<close>

theory Unify_Results2
  imports Unify_Complete Unify_Results
begin

context pure_sig
begin

text \<open>
  Together with finiteness (@{thm [source] unifiers_fin}): on a well-formed problem with a solution
  within the bounds of the configuration, \<^const>\<open>unifiers\<close> returns a sequence whose enumeration
  terminates, all of whose unifiers satisfy the result invariant \<^const>\<open>uresult\<close>, and one of which
  has a solution that agrees with the given one (@{thm [source] unifiers_complete}).
\<close>

corollary unifiers_complete_fin:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and fin: "finite X" "finite K"
    and si: "sinv A K X env (tdps tus)" and inv: "scinv \<rho> \<sigma> env (tdps tus) X A"
    and kk: "mcp_kokK k \<rho> (tyenv env) A K"
    and bound: "mcp_meas \<rho> \<sigma> env X \<le> nat_of_integer (cfg_search_bound cfg)"
  obtains s xs where "unifiers alg env tus = Some (Ok s)" "evals cfg s xs" "\<forall>x\<in>set xs. uresult A env tus x"
    "\<exists>env' tps \<rho>' \<sigma>' X' A'. El_R env' tps \<in> set xs \<and>
      X \<subseteq> X' \<and> A \<subseteq> A' \<and> scinv \<rho>' \<sigma>' env' (tdps tps) X' A' \<and>
      tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>'"
proof -
  from unifiers_fin[OF cfg fin si] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (uresult A env tus)" by blast
  from f obtain xs where es: "evals cfg s xs" and r: "\<forall>x\<in>set xs. uresult A env tus x"
    unfolding fin_def by blast
  show thesis by (rule that[OF u es r unifiers_complete[OF cfg k fin si inv kk bound u es]])
qed

end

end
