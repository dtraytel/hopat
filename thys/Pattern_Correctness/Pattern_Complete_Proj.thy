section \<open>Completeness of Projection\<close>

theory Pattern_Complete_Proj
  imports Pattern_Complete_Flex
begin

context pure_sig
begin

subsection \<open>Conclusions for computations with a result and an environment\<close>

text \<open>Projection only adds new variables and their bindings; the type environment is unchanged.\<close>

definition pcon :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> ('a \<times> env) M \<Rightarrow> bool" where
  "pcon \<rho> \<sigma> env e bs X A r \<longleftrightarrow> no_unif r \<and> (\<forall>u env'. ok r (u, env') \<longrightarrow> (\<exists>\<sigma>'. cinv \<rho> \<sigma>' env' e bs X A \<and>
    sagree (maxidx env) \<sigma> \<sigma>' \<and> maxidx env \<le> maxidx env' \<and> tyenv env' = tyenv env))"

lemma pcon_return: "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A (return (u, env))"
  unfolding pcon_def by (auto intro!: exI[of _ \<sigma>])

lemma pcon_bindM:
  "no_unif m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A (g x)) \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A (m \<bind> g)"
  unfolding pcon_def by (auto intro!: no_unif_bindM)

lemma pcon_trans:
  assumes "sagree (maxidx env) \<sigma> \<sigma>1" "maxidx env \<le> maxidx env1" "tyenv env1 = tyenv env"
    "pcon \<rho> \<sigma>1 env1 e bs X A r"
  shows "pcon \<rho> \<sigma> env e bs X A r"
  unfolding pcon_def
proof (intro conjI allI impI)
  show "no_unif r" using assms(4) by (simp add: pcon_def)
  fix u env' assume "ok r (u, env')"
  then obtain \<sigma>' where c: "cinv \<rho> \<sigma>' env' e bs X A" "sagree (maxidx env1) \<sigma>1 \<sigma>'"
    "maxidx env1 \<le> maxidx env'" "tyenv env' = tyenv env1"
    using assms(4) unfolding pcon_def by blast
  have "sagree (maxidx env) \<sigma> \<sigma>'" by (rule sagree_trans[OF assms(1) c(2) assms(2)])
  with c assms(2,3) show "\<exists>\<sigma>'. cinv \<rho> \<sigma>' env' e bs X A \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      maxidx env \<le> maxidx env' \<and> tyenv env' = tyenv env"
    by (intro exI[of _ \<sigma>']) simp
qed

lemma pcon_mono: "pcon \<rho> \<sigma> env e bs X A r \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> pcon \<rho> \<sigma> env e bs Y A r"
  unfolding pcon_def by (blast intro: cinv_mono)

lemma cinv_bs:
  "cinv \<rho> \<sigma> env e' bs' X A \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow> btvars bs \<subseteq> btvars bs' \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A"
  unfolding cinv_def by blast

lemma pcon_bs:
  "pcon \<rho> \<sigma> env e' bs' X A r \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow> btvars bs \<subseteq> btvars bs' \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A r"
  unfolding pcon_def by (blast intro: cinv_bs)

lemma cterm_tyenv: "tyenv env' = tyenv env \<Longrightarrow> cterm \<rho> env' e bs A t T \<longleftrightarrow> cterm \<rho> env e bs A t T"
  by (simp add: cterm_def)

text \<open>
  Completeness of \<^const>\<open>pr\<close> at depth \<open>d\<close>, for a solution whose instance of the term has normal
  forms with loose bound variables \<open>\<ge> d\<close> in \<open>d + xs\<close>.
\<close>

definition pr_cp :: "integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> (pterm \<times> env) M \<Rightarrow> bool" where
  "pr_cp xs s env d bs r \<longleftrightarrow> (\<forall>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<longrightarrow> vars s \<subseteq> X \<longrightarrow>
    cterm \<rho> env e bs A s T \<longrightarrow> nf_bounds (ap \<rho> \<sigma> s) d xs \<longrightarrow> pcon \<rho> \<sigma> env e bs X A r)"

lemma pr_cpD:
  "pr_cp xs s env d bs r \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> nf_bounds (ap \<rho> \<sigma> s) d xs \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A r"
  unfolding pr_cp_def by blast

lemma pr_cp_None: "pr_cp xs s env d bs None"
  by (simp add: pr_cp_def pcon_def)

lemma pcon_mapAccM:
  assumes f: "\<And>s env. s \<in> set ss \<Longrightarrow> pr_cp xs s env d bs (f s env)"
  shows "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> \<Union> (vars ` set ss) \<subseteq> X \<Longrightarrow> \<forall>s\<in>set ss. \<exists>T. cterm \<rho> env e bs A s T \<Longrightarrow>
    \<forall>s\<in>set ss. nf_bounds (ap \<rho> \<sigma> s) d xs \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A (mapAccM f ss env)"
  using f
proof (induction ss arbitrary: \<sigma> env)
  case Nil
  then show ?case by (simp add: pcon_return)
next
  case (Cons s ss)
  obtain T where cs: "cterm \<rho> env e bs A s T" using Cons.prems(3) by auto
  have p1: "pcon \<rho> \<sigma> env e bs X A (f s env)"
    using pr_cpD[OF Cons.prems(5)[of s env] Cons.prems(1) _ cs] Cons.prems(2,4) by simp
  show ?case unfolding mapAccM.simps
  proof (rule pcon_bindM)
    show "no_unif (f s env)" using p1 by (simp add: pcon_def)
    fix y1 assume ok1: "ok (f s env) y1"
    obtain y env1 where y1: "y1 = (y, env1)" by force
    from p1 ok1 y1 obtain \<sigma>1 where r1: "cinv \<rho> \<sigma>1 env1 e bs X A" "sagree (maxidx env) \<sigma> \<sigma>1"
      "maxidx env \<le> maxidx env1" "tyenv env1 = tyenv env"
      unfolding pcon_def by blast
    have vi: "vinv \<rho> env X" using Cons.prems(1) by (simp add: cinv_def)
    have ap1: "ap \<rho> \<sigma>1 s' = ap \<rho> \<sigma> s'" if "s' \<in> set ss" for s'
    proof -
      have sub: "vars s' \<subseteq> X" using Cons.prems(2) that by auto
      have b: "\<forall>p\<in>X \<union> evars env. snd (fst p) \<le> maxidx env" using vi by (simp add: vinv_def below_def)
      have "below (maxidx env) (vars s')" unfolding below_def using b sub by blast
      then show ?thesis by (rule ap_sagree[OF r1(2)])
    qed
    have "pcon \<rho> \<sigma>1 env1 e bs X A (mapAccM f ss env1)"
      using Cons.IH[OF r1(1)] Cons.prems(2-5) ap1 cterm_tyenv[OF r1(4)] by simp
    then have "pcon \<rho> \<sigma> env e bs X A (mapAccM f ss env1)" by (rule pcon_trans[OF r1(2,3,4)])
    then show "pcon \<rho> \<sigma> env e bs X A
        ((case y1 of (y, s1) \<Rightarrow> mapAccM f ss s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))))"
      unfolding y1 pcon_def by (auto intro!: no_unif_bindM split: prod.splits)
  qed
qed


subsection \<open>Translating bound variables\<close>

lemma idx_return: "j \<in> set xs \<Longrightarrow> idx xs j = return (bidx xs j)"
  by (induction xs) auto

lemma try_trans_Some: "ok (try_trans xs d i) r \<Longrightarrow> i < d \<or> i - d \<in> set xs \<Longrightarrow> r \<noteq> None"
  by (auto simp: try_trans_def idx_return split: if_splits)

lemma no_unif_trans: "i < d \<or> i - d \<in> set xs \<Longrightarrow> no_unif (trans xs d i)"
  by (auto simp: trans_def idx_return)

end

end
