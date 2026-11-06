section \<open>Semantics of Disagreement Pairs\<close>

theory Unify_Semantics
  imports Unify_Monad
begin

context pure_sig
begin

text \<open>
  A disagreement pair \<open>(rb, t, u)\<close> relates two terms under the binders \<open>rb\<close> (innermost first:
  \<open>Bound 0\<close> refers to \<open>hd rb\<close>). As for pattern unification, a type instantiation \<open>\<rho>\<close> and a
  substitution \<open>\<sigma>\<close> act on a term by \<^const>\<open>ap\<close>; the pair is solved if the instances are
  \<open>\<alpha>\<beta>\<eta>\<close>-equivalent. A pair is well-typed at \<open>\<rho>\<close> if both sides have the same type under the
  instantiated binders, and their loose bound variables are bound by \<open>rb\<close>.
\<close>

definition dvars :: "dpair list \<Rightarrow> (indexname \<times> ptyp) set" where
  "dvars dps = (\<Union>(rb, t, u)\<in>set dps. vars t \<union> vars u)"

definition dsolved :: "tinst \<Rightarrow> vsubst \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dsolved \<rho> \<sigma> dps \<longleftrightarrow> (\<forall>(rb, t, u)\<in>set dps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"

definition dtyped :: "tinst \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dtyped \<rho> dps \<longleftrightarrow> (\<forall>(rb, t, u)\<in>set dps. (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
    \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb))"

lemma dvars_simps [simp]:
  "dvars [] = {}" "dvars ((rb, t, u) # dps) = vars t \<union> vars u \<union> dvars dps" "dvars (dps @ dps') = dvars dps \<union> dvars dps'"
  by (auto simp: dvars_def)

lemma dsolved_simps [simp]:
  "dsolved \<rho> \<sigma> []" "dsolved \<rho> \<sigma> ((rb, t, u) # dps) \<longleftrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<and> dsolved \<rho> \<sigma> dps"
  "dsolved \<rho> \<sigma> (dps @ dps') \<longleftrightarrow> dsolved \<rho> \<sigma> dps \<and> dsolved \<rho> \<sigma> dps'"
  unfolding dsolved_def set_append ball_Un by auto

lemma dtyped_simps [simp]:
  "dtyped \<rho> []"
  "dtyped \<rho> ((rb, t, u) # dps) \<longleftrightarrow> (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
    \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb) \<and> dtyped \<rho> dps"
  "dtyped \<rho> (dps @ dps') \<longleftrightarrow> dtyped \<rho> dps \<and> dtyped \<rho> dps'"
  unfolding dtyped_def set_append ball_Un by auto

lemma dsolved_mono: "dsolved \<rho> \<sigma> dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> dsolved \<rho> \<sigma> dps'"
  and dtyped_mono: "dtyped \<rho> dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> dtyped \<rho> dps'"
  and dvars_mono: "set dps' \<subseteq> set dps \<Longrightarrow> dvars dps' \<subseteq> dvars dps"
  unfolding dsolved_def dtyped_def dvars_def by blast+

lemma dsolved_set: "set dps = set dps' \<Longrightarrow> dsolved \<rho> \<sigma> dps \<longleftrightarrow> dsolved \<rho> \<sigma> dps'"
  and dtyped_set: "set dps = set dps' \<Longrightarrow> dtyped \<rho> dps \<longleftrightarrow> dtyped \<rho> dps'"
  and dvars_set: "set dps = set dps' \<Longrightarrow> dvars dps = dvars dps'"
  unfolding dsolved_def dtyped_def dvars_def by simp_all

text \<open>
  A step from \<open>(env, dps)\<close> to \<open>(env', dps')\<close> extends the environment, and for every type
  instantiation that solves the type environment of a final extension \<open>env''\<close>, it keeps the
  typing invariants of the pattern development, and every solution of \<open>env''\<close> that solves
  \<open>dps'\<close> solves \<open>dps\<close>. The set \<open>X\<close> holds the variables of other pairs, whose types stay
  consistent. This generalises \<^const>\<open>step_ok\<close> of pattern unification to lists of pairs.
\<close>

definition dstep :: "env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dstep env dps env' dps' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> dtyped \<rho> dps \<longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps))"

lemma dstepI:
  assumes "extends env env'"
    and "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps)"
  shows "dstep env dps env' dps'"
  using assms unfolding dstep_def by blast

lemma dstepD:
  assumes "dstep env dps env' dps'"
  shows "extends env env'"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps)"
  using assms unfolding dstep_def by blast+

lemma dstep_refl: "dstep env dps env dps"
  by (rule dstepI) auto

lemma dstep_trans:
  assumes s1: "dstep env dps env1 dps1" and s2: "dstep env1 dps1 env2 dps2"
  shows "dstep env dps env2 dps2"
proof (rule dstepI)
  note e1 = dstepD(1)[OF s1] and e2 = dstepD(1)[OF s2]
  show "extends env env2" by (rule extends_trans[OF e1 e2])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" and ex: "extends env2 env''" and w: "wt_env \<rho> env"
    and d: "dtyped \<rho> dps" and v: "vinv \<rho> env (X \<union> dvars dps)"
  have ex1: "extends env1 env''" by (rule extends_trans[OF e2 ex])
  from dstepD(2)[OF s1 t ex1 w d v] have r1: "wt_env \<rho> env1" "dtyped \<rho> dps1" "vinv \<rho> env1 (X \<union> dvars dps1)"
    "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> dsolved \<rho> \<sigma> dps1 \<Longrightarrow> dsolved \<rho> \<sigma> dps"
    by blast+
  from dstepD(2)[OF s2 t ex r1(1-3)] r1(4)
  show "wt_env \<rho> env2 \<and> dtyped \<rho> dps2 \<and> vinv \<rho> env2 (X \<union> dvars dps2) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps2 \<longrightarrow> dsolved \<rho> \<sigma> dps)"
    by blast
qed

text \<open>Other pairs are carried along unchanged:\<close>

lemma dstep_frame:
  assumes s: "dstep env dps env' dps'"
  shows "dstep env (dps @ fs) env' (dps' @ fs)"
proof (rule dstepI)
  show "extends env env'" by (rule dstepD(1)[OF s])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" and ex: "extends env' env''" and w: "wt_env \<rho> env"
    and d: "dtyped \<rho> (dps @ fs)" and v: "vinv \<rho> env (X \<union> dvars (dps @ fs))"
  have v': "vinv \<rho> env ((X \<union> dvars fs) \<union> dvars dps)" using v by (simp add: Un_ac)
  from dstepD(2)[OF s t ex w _ v'] d
  have r: "wt_env \<rho> env'" "dtyped \<rho> dps'" "vinv \<rho> env' ((X \<union> dvars fs) \<union> dvars dps')"
    "\<And>\<sigma>. solution \<rho> \<sigma> env'' \<Longrightarrow> dsolved \<rho> \<sigma> dps' \<Longrightarrow> dsolved \<rho> \<sigma> dps"
    by auto
  then show "wt_env \<rho> env' \<and> dtyped \<rho> (dps' @ fs) \<and> vinv \<rho> env' (X \<union> dvars (dps' @ fs)) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> (dps' @ fs) \<longrightarrow> dsolved \<rho> \<sigma> (dps @ fs))"
    using d by (simp add: Un_ac)
qed

lemma dstep_set:
  assumes "dstep env dps env' dps'" "set dps = set ds" "set dps' = set ds'"
  shows "dstep env ds env' ds'"
  using assms unfolding dstep_def by (simp add: dsolved_set[OF assms(2)] dtyped_set[OF assms(2)]
    dvars_set[OF assms(2)] dsolved_set[OF assms(3)] dtyped_set[OF assms(3)] dvars_set[OF assms(3)])

text \<open>A sound step of pattern unification is a step on one pair:\<close>

lemma step_ok_dstep:
  assumes "step_ok env bs s t env'"
  shows "dstep env [(bs, s, t)] env' []"
proof (rule dstepI)
  show "extends env env'" by (rule step_okD(1)[OF assms])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env"
    and d: "dtyped \<rho> [(bs, s, t)]" and v: "vinv \<rho> env (X \<union> dvars [(bs, s, t)])"
  from d obtain e T where "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
    "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)" by auto
  with step_okD(2)[OF assms t _ _ _ _, of e T X] v
  show "wt_env \<rho> env' \<and> dtyped \<rho> [] \<and> vinv \<rho> env' (X \<union> dvars []) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> [] \<longrightarrow> dsolved \<rho> \<sigma> [(bs, s, t)])"
    by (simp add: Un_ac)
qed

end

subsection \<open>The pairs connected to terms\<close>

text \<open>\<^const>\<open>connected\<close> splits the pairs into the connected ones and the others:\<close>

lemma close_set: "close vs (ps, qs) = (cs, os) \<Longrightarrow> set cs \<union> set os = fst ` set ps \<union> fst ` set qs"
proof (induction vs "(ps, qs)" arbitrary: ps qs rule: close.induct)
  case (1 vs ps qs)
  let ?P = "\<lambda>(_ :: dpair, ws). \<exists>w\<in>set ws. w \<in> set vs"
  show ?case
  proof (cases "filter ?P qs")
    case Nil
    have "close vs (ps, qs) = (map fst ps, map fst qs)"
      by (subst close.simps) (simp del: close.simps add: Nil)
    with "1.prems" show ?thesis by auto
  next
    case (Cons q qs')
    have "close vs (ps, qs) = close (fold (\<lambda>q. List.union (snd q)) (q # qs') vs) (ps @ q # qs', filter (Not \<circ> ?P) qs)"
      by (subst close.simps) (simp del: close.simps add: Cons)
    with "1.prems" have c: "close (fold (\<lambda>q. List.union (snd q)) (q # qs') vs) (ps @ q # qs', filter (Not \<circ> ?P) qs) = (cs, os)"
      by simp
    have A: "set cs \<union> set os = fst ` set (ps @ q # qs') \<union> fst ` set (filter (Not \<circ> ?P) qs)"
      by (rule "1.hyps"[of "filter ?P qs" "filter (Not \<circ> ?P) qs" q qs', OF _ Cons c])
        (simp add: partition_filter_conv)
    have B: "set qs = set (q # qs') \<union> set (filter (Not \<circ> ?P) qs)"
      unfolding Cons[symmetric] by auto
    show ?thesis unfolding A by (subst B) (simp add: image_Un Un_ac)
  qed
qed

lemma connected_set:
  assumes "ok (connected env ts dps) (cs, os)"
  shows "set cs \<union> set os = set dps"
proof -
  from assms obtain vs xs where m: "ok (mapM (\<lambda>(rb, t, u). do {
          ws \<leftarrow> add_env_vars u env [];
          ws' \<leftarrow> add_env_vars t env ws;
          return ((rb, t, u), unassigned env ws')}) dps) xs" and c: "close (unassigned env vs) ([], xs) = (cs, os)"
    by (auto simp: connected_def)
  have "map fst xs = dps"
    using m unfolding ok_mapM by (induction rule: list_all2_induct) (auto split: prod.splits)
  with close_set[OF c] show ?thesis by (metis image_empty image_set list.set(1) sup_bot_left)
qed

end
