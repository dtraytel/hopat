section \<open>The Unifiers Enumerated for \<open>bicompose_aux\<close>\<close>

theory Bicompose_Unifiers
  imports Bicompose_Rename
begin

context csig
begin

text \<open>
  \<open>bicompose_aux\<close> pulls the sequences of \<^const>\<open>unifiers\<close> one element at a time
  (\<^const>\<open>upull\<close>). For well-typed problems, such a sequence has a terminating enumeration
  (\<^const>\<open>evals\<close>, by @{thm [source] wf_csig.unifiers_prres}) whose elements are unifiers
  (@{thm [source] wf_csig.unifiers_psound}) with environments in the invariant (\<^const>\<open>prres\<close>). Since
  pulling is deterministic, every rest of the sequence has the same property.
\<close>

lemma evals_pull_Some:
  assumes "evals cfg s xs" "pull cfg s = Some (evs, UOk (Some (x, s')))"
  shows "\<exists>xs'. xs = x # xs' \<and> evals cfg s' xs'"
  using assms(1)
proof cases
  case (Nil evs')
  with assms(2) show ?thesis by simp
next
  case (Cons evs' y s'' xs')
  with assms(2) show ?thesis by auto
qed

lemma evals_pull_None:
  assumes "evals cfg s xs" "pull cfg s = Some (evs, UOk None)"
  shows "xs = []"
  using assms(1) by cases (use assms(2) in auto)

lemma evals_pull_ok:
  assumes "evals cfg s xs"
  shows "\<exists>evs r. pull cfg s = Some (evs, UOk r)"
  using assms by cases auto

text \<open>
  An element of the enumeration of the unifiers of a problem: the properties of all elements of
  the enumeration (e.g.\ @{thm [source] wf_csig.unifiers_prres_rs}) hold for it.
\<close>

definition uelem :: "algebra \<Rightarrow> cfg \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> elem \<Rightarrow> bool" where
  "uelem alg cfg env tus x \<longleftrightarrow>
    (\<exists>s0 xs0. unifiers alg env tus = Some (Ok s0) \<and> evals cfg s0 xs0 \<and> x \<in> set xs0)"

lemma uelem_fin:
  assumes "uelem alg cfg env tus x" "unifiers alg env tus = Some (Ok s)" "fin cfg s P"
  shows "P x"
  using assms evals_det unfolding uelem_def fin_def by fastforce

end

context wf_csig
begin

definition uinv :: "cfg \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> seq \<Rightarrow> bool" where
  "uinv cfg A env tus s \<longleftrightarrow> (\<exists>xs. evals cfg s xs \<and> (\<forall>x\<in>set xs. uelem alg cfg env tus x \<and>
    (\<exists>env' tps. x = El_R env' tps \<and> punifier env (dps_of tus) env' tps \<and> prres alg ar A env' tps)))"

lemma unifiers_uinv:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
  obtains s where "liftMT (unifiers alg env tus) = returnT s" "uinv cfg A env tus s"
proof -
  from unifiers_prres[OF cfg finA pi] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)" by blast
  from f obtain xs where es: "evals cfg s xs"
    and pr: "\<forall>x\<in>set xs. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps"
    by (auto simp: fin_def)
  have "\<forall>x\<in>set xs. uelem alg cfg env tus x \<and> (\<exists>env' tps. x = El_R env' tps \<and>
      punifier env (dps_of tus) env' tps \<and> prres alg ar A env' tps)"
  proof
    fix x assume x: "x \<in> set xs"
    from unifiers_psound[OF finA pi u es x] pr x u es show "uelem alg cfg env tus x \<and> (\<exists>env' tps. x = El_R env' tps \<and>
        punifier env (dps_of tus) env' tps \<and> prres alg ar A env' tps)"
      unfolding uelem_def by fastforce
  qed
  with es have "uinv cfg A env tus s" by (auto simp: uinv_def)
  moreover have "liftMT (unifiers alg env tus) = returnT s"
    using u by (simp add: liftMT_def liftWT_def liftM_def returnT_def)
  ultimately show thesis using that by blast
qed

lemma upull_uinv:
  assumes "uinv cfg A env tus s"
  obtains (none) "upull cfg s = Some ([], TOk None) \<or> (\<exists>evs. upull cfg s = Some (evs, TOk None))"
  | (some) env' tps s' where "okT (upull cfg s) (Some ((env', tps), s'))"
      "punifier env (dps_of tus) env' tps" "prres alg ar A env' tps" "uinv cfg A env tus s'"
      "uelem alg cfg env tus (El_R env' tps)"
proof -
  from assms obtain xs where es: "evals cfg s xs" and el: "\<forall>x\<in>set xs. uelem alg cfg env tus x \<and>
      (\<exists>env' tps. x = El_R env' tps \<and> punifier env (dps_of tus) env' tps \<and> prres alg ar A env' tps)"
    by (auto simp: uinv_def)
  from evals_pull_ok[OF es] obtain evs r where p: "pull cfg s = Some (evs, UOk r)" by blast
  show thesis
  proof (cases r)
    case None
    with p have "upull cfg s = Some (evs, TOk None)"
      by (simp add: upull_def bindW_def liftWT_def returnW_def)
    then show thesis by (intro none) blast
  next
    case (Some xs')
    then obtain x s' where r: "r = Some (x, s')" by (cases xs') auto
    from evals_pull_Some[OF es p[unfolded r]] obtain xs'' where xs: "xs = x # xs''" "evals cfg s' xs''"
      by blast
    from el xs obtain env' tps where x: "x = El_R env' tps" "punifier env (dps_of tus) env' tps"
      "prres alg ar A env' tps" "uelem alg cfg env tus x" by auto
    have "okT (upull cfg s) (Some ((env', tps), s'))"
      using p r x by (auto simp: upull_def bindW_def liftWT_def returnW_def)
    moreover have "uinv cfg A env tus s'" using xs el by (auto simp: uinv_def)
    ultimately show thesis using x by (intro some) simp_all
  qed
qed

lemma upull_uinv_Some:
  assumes "uinv cfg A env tus s" "okT (upull cfg s) (Some ((env', tps), s'))"
  shows "punifier env (dps_of tus) env' tps \<and> prres alg ar A env' tps \<and> uinv cfg A env tus s' \<and>
    uelem alg cfg env tus (El_R env' tps)"
  using assms(1)
proof (cases rule: upull_uinv)
  case none
  with assms(2) show ?thesis by auto
next
  case (some env1 tps1 s1)
  with assms(2) show ?thesis by auto
qed

lemma upull_uinv_ok: "uinv cfg A env tus s \<Longrightarrow> \<exists>r. okT (upull cfg s) r"
  by (cases rule: upull_uinv) auto

end

end
