section \<open>Theorems and biresolution\<close>

theory Biresolution_Thm
  imports Biresolution_Correct
begin

text \<open>
  The results of \<^const>\<open>biresolution\<close> of theorems are again theorems: they are valid and
  well-typed, and the indices of their variables are nonnegative. With these facts, theorems
  form an abstract type, and \<^const>\<open>biresolution\<close> is an operation on it.
\<close>


subsection \<open>Freshness of the unifiers\<close>

lemma finite_vt_dom: "finite {v. vt_lookup \<theta> v \<noteq> None}"
  by transfer (simp add: dom_def)

lemma finite_tvars_env: "finite (tvars_env \<theta>)"
proof -
  have "tvars_env \<theta> \<subseteq> (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    by (force simp: tvars_env_def)
  moreover have "finite (\<Union>v\<in>{v. vt_lookup \<theta> v \<noteq> None}.
      insert (v, fst (the (vt_lookup \<theta> v))) (tvars (snd (the (vt_lookup \<theta> v)))))"
    by (rule finite_UN_I[OF finite_vt_dom]) simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma pinv_mono_A:
  assumes "pinv alg ar A W env dps" "A \<subseteq> A'" "scons (tvars_env (tyenv env) \<union> A')"
    "\<forall>p\<in>A'. snd (fst p) \<le> maxidx env"
  shows "pinv alg ar A' W env dps"
  using assms tyw_mono[OF _ assms(2)] unfolding pinv_def tinv_def by blast

context wf_algebra
begin

text \<open>
  The enumerated unifiers do not contain a variable that occurs neither in the problem nor in
  the environment in their flex-flex pairs either (as for @{thm [source] unifiers_fresh}, its
  typing can be chosen freely).
\<close>

theorem unifiers_fresh_tps:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and v: "vt_lookup (tenv env) v = None" "v \<notin> fst ` bvps env"
      "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u" "snd v \<le> maxidx env"
  shows "\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u"
proof -
  note p = pinvD[OF pi]
  define T1 where "T1 = W v"
  define T2 where "T2 = T1 \<rightarrow>\<^sub>T T1"
  have tw: "tyw ar (tyenv env) A T1" "tyw ar (tyenv env) A T2"
    using p(5)[of v] tyw_foldr_fun[of ar "tyenv env" A "[T1]" T1] by (simp_all add: T1_def T2_def)
  have v3: "\<forall>(rb, t, u)\<in>set (dps_of tus). v \<notin> vars t \<and> v \<notin> vars u" using v(3) by auto
  have rs: "\<exists>W' e0. (\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab) \<and> tctx env' W' v = tnorm (tyenv env') T"
    if "T = T1 \<or> T = T2" for T
  proof -
    have tT: "tyw ar (tyenv env) A T" using that tw by blast
    have pi': "pinv alg ar A (W(v := T)) env (dps_of tus)" by (rule pinv_upd[OF pi tT v(1,2) v3])
    have "typed env (W(v := T)) [] (Var v T) T"
      using v(1) by (simp add: typed_def vtyp_def has_type.Var)
    then have "rs_typed ar A [(Var v T, T)] (W(v := T)) env"
      using v(4) tT by (simp add: rs_typed_def below_def)
    from unifiers_prres_rs[OF cfg finA pi' this] obtain s' where
      "unifiers alg env tus = Some (Ok s')"
      "fin cfg s' (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres_rs alg ar A [(Var v T, T)] env' tps)"
      by blast
    with u es x evals_det have "prres_rs alg ar A [(Var v T, T)] env' tps"
      unfolding fin_def by fastforce
    then obtain W' e0 where "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab" "typed env' W' [] (Var v T) T"
      by (auto simp: prres_rs_def rs_typed_def)
    moreover from this(2) have "tctx env' W' v = tnorm (tyenv env') T"
      by (auto simp: typed_def elim: has_type.cases)
    ultimately show ?thesis by blast
  qed
  from rs[of T1] obtain W1 e1 where pi1: "\<forall>ab\<in>set tps. ptpok ar A W1 env' e1 ab"
    and t1: "tctx env' W1 v = tnorm (tyenv env') T1"
    by blast
  from rs[of T2] obtain W2 e2 where pi2: "\<forall>ab\<in>set tps. ptpok ar A W2 env' e2 ab"
    and t2: "tctx env' W2 v = tnorm (tyenv env') T2"
    by blast
  let ?\<theta> = "tyenv env'"
  have neq: "tnorm ?\<theta> T1 \<noteq> tnorm ?\<theta> T2" using fun_type_neq[of "tnorm ?\<theta> T1"] by (simp add: T2_def)
  have ty: "tnorm ?\<theta> Tv = tctx env' W' v"
    if "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab" "(t, u) \<in> set tps" "(v, Tv) \<in> vps t \<union> vps u" for W' e0 t u Tv
  proof -
    from that(1,2) obtain rb a b B where tu: "t = rlist_abs rb a" "u = rlist_abs rb b"
      and ty: "typed env' W' (map snd rb) a B" "typed env' W' (map snd rb) b B"
      by (fastforce simp: ptpok_def)
    from that(3) tu typed_vps[OF typed_rlist_abs[OF ty(1)]] typed_vps[OF typed_rlist_abs[OF ty(2)]]
    show ?thesis by blast
  qed
  show ?thesis
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    show "v \<notin> vars t \<and> v \<notin> vars u"
    proof (rule ccontr)
      assume "\<not> (v \<notin> vars t \<and> v \<notin> vars u)"
      then have "v \<in> fst ` (vps t \<union> vps u)" by (auto simp: vars_vps)
      then obtain Tv where "(v, Tv) \<in> vps t \<union> vps u" by force
      with ty[OF pi1 tu] ty[OF pi2 tu] t1 t2 neq show False by simp
    qed
  qed
qed

text \<open>
  The type environments of the enumerated unifiers do not contain a type variable that is not
  among the type variables \<open>A\<close> of the problem nor in its type environment: with a different
  sort, it could be added to \<open>A\<close>.
\<close>

theorem unifiers_fresh_tvar:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and w: "w \<notin> fst ` (A \<union> tvars_env (tyenv env))" "snd w \<le> maxidx env"
  shows "w \<notin> fst ` tvars_env (tyenv env')"
proof
  assume "w \<in> fst ` tvars_env (tyenv env')"
  then obtain S where wS: "(w, S) \<in> tvars_env (tyenv env')" by force
  define A' where "A' = insert (w, undefined # S) A"
  have pi': "pinv alg ar A' W env (dps_of tus)"
  proof (rule pinv_mono_A[OF pi])
    have "scons (tvars_env (tyenv env) \<union> A)" using pinvD(2)[OF pi] by (simp add: tinv_def)
    then show "scons (tvars_env (tyenv env) \<union> A')"
      unfolding scons_def
    proof (intro allI impI)
      fix v S1 S2 assume sc: "\<forall>v S S'. (v, S) \<in> tvars_env (tyenv env) \<union> A \<longrightarrow> (v, S') \<in> tvars_env (tyenv env) \<union> A \<longrightarrow> S = S'"
        and v: "(v, S1) \<in> tvars_env (tyenv env) \<union> A'" "(v, S2) \<in> tvars_env (tyenv env) \<union> A'"
      show "S1 = S2"
      proof (cases "v = w")
        case True
        have "(w, S') \<notin> tvars_env (tyenv env) \<union> A" for S' using w(1) by force
        with v True show ?thesis by (auto simp: A'_def)
      next
        case False
        with v have "(v, S1) \<in> tvars_env (tyenv env) \<union> A" "(v, S2) \<in> tvars_env (tyenv env) \<union> A"
          by (auto simp: A'_def)
        with sc show ?thesis by blast
      qed
    qed
    have "snd (fst p) \<le> maxidx env" if "p \<in> A" for p
      using tinv_index[OF pinvD(2)[OF pi], of "fst p" "snd p"] that by simp
    with w(2) show "\<forall>p\<in>A'. snd (fst p) \<le> maxidx env" by (auto simp: A'_def)
  qed (auto simp: A'_def)
  from unifiers_prres[OF cfg _ pi'] obtain s' where
    "unifiers alg env tus = Some (Ok s')"
    "fin cfg s' (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A' env' tps)"
    using finA by (auto simp: A'_def)
  with u es x evals_det have "prres alg ar A' env' tps"
    unfolding fin_def by fastforce
  then obtain W' where "pinv alg ar A' W' env' []" by (auto simp: prres_def)
  then have "scons (tvars_env (tyenv env') \<union> A')" using pinvD(2) by (simp add: tinv_def)
  then have "S = undefined # S" using wS unfolding scons_def A'_def by blast
  then show False by simp
qed

end

end
