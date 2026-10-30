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


subsection \<open>Normalized terms\<close>

text \<open>Typed terms contain the constants of Pure at their types.\<close>

lemma cok_App_typed:
  "has_type V Ts s (T \<rightarrow>\<^sub>T U) \<Longrightarrow> has_type V Ts t T \<Longrightarrow> cok s \<Longrightarrow> cok t \<Longrightarrow> cok (s $ t)"
  by (cases s; cases t) (auto elim!: has_type_elims simp: const_typ_ok_def imp_type_def all_type_def propT_def)

lemma has_type_cok: "has_type V Ts t T \<Longrightarrow> cok t"
  by (induction rule: has_type.induct)
    (auto intro: cok_App_typed simp: const_typ_ok_def imp_type_def all_type_def propT_def)

text \<open>The variables of a normalized term occur in the term or in the environment.\<close>

lemma norm_term2_vars:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' \<subseteq> vars t \<union> fst ` bvps env"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note t' = "1.hyps"[unfolded "1.prems"]
  have IH: "vars s' \<subseteq> vars s \<union> fst ` bvps env" if "nt env s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Var xi T'))) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest Var show ?thesis by auto
    next
      case (Some u)
      with lk obtain U where "vt_lookup (tenv env) xi = Some (U, u)" by (auto dest: ok_lookup_Some)
      then have "vars u \<subseteq> fst ` bvps env" unfolding vars_vps by (rule image_mono[OF bvpsI])
      with rest Some IH[of u t'] show ?thesis by auto
    qed
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with t' App have "nt env (subst_bound u b) = Some (Ok t')" by simp
      from IH[OF this] vars_subst_bound[of u b] show ?thesis by (auto simp: App f)
    next
      case False
      with t' App obtain nf where nf: "nt env f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
        with rest have "nt env (subst_bound u b) = Some (Ok t')" by simp
        from IH[OF this] IH[OF nf] vars_subst_bound[of u b] show ?thesis by (auto simp: App nfa)
      next
        case False
        with rest obtain nu where nu: "nt env u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from IH[OF nu] IH[OF nf] show ?thesis by (auto simp: App t'')
      qed
    qed
  qed (use t' in \<open>auto dest!: IH\<close>)
qed

lemma norm_term1_vars:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vars t' \<subseteq> vars t \<union> fst ` bvps env"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note t' = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vars s' \<subseteq> vars s \<union> fst ` bvps env" if "nt te s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl "1.prems"(2)] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest Var show ?thesis by auto
    next
      case (Some u)
      with lk "1.prems"(2) have "vt_lookup (tenv env) xi = Some (T, u)" by (auto dest: ok_lookup1)
      then have "vars u \<subseteq> fst ` bvps env" unfolding vars_vps by (rule image_mono[OF bvpsI])
      with rest Some IH[of u t'] show ?thesis by auto
    qed
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with t' App have "nt te (subst_bound u b) = Some (Ok t')" by simp
      from IH[OF this] vars_subst_bound[of u b] show ?thesis by (auto simp: App f)
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
        with rest have "nt te (subst_bound u b) = Some (Ok t')" by simp
        from IH[OF this] IH[OF nf] vars_subst_bound[of u b] show ?thesis by (auto simp: App nfa)
      next
        case False
        with rest obtain nu where nu: "nt te u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from IH[OF nu] IH[OF nf] show ?thesis by (auto simp: App t'')
      qed
    qed
  qed (use t' in \<open>auto dest!: IH\<close>)
qed

lemma norm_term_vars: "ok (norm_term env t) t' \<Longrightarrow> vars t' \<subseteq> vars t \<union> fst ` bvps env"
  using norm_term1_vars[of "tenv env" t "Ok t'" t' env] norm_term2_vars[of env t "Ok t'" t']
  by (auto simp: norm_term_def split: if_splits)

lemma norm_term_skip_vars: "okT (norm_term_skip env n t) t' \<Longrightarrow> vars t' \<subseteq> vars t \<union> fst ` bvps env"
proof (induction env n t arbitrary: t' rule: norm_term_skip.induct)
  case (1 env n t)
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems" show ?thesis by (auto simp: norm_term_skip.simps dest: norm_term_vars)
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      from "1.prems" n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from T' have "okT (liftMT (norm_type (tyenv env) T)) T'" by simp
      from "1.IH"(2)[OF n aTb refl refl this b'] aTb show ?thesis
        by (auto simp: t' all_const_def dest_all_Some)
    next
      case None
      with "1.prems" n obtain A B where AB: "dest_imp t = Some (A, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with "1.prems" n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from "1.IH"(1)[OF n None AB refl B'] AB show ?thesis
        by (auto simp: t' mk_implies_def implies_def dest_imp_Some)
    qed
  qed
qed

text \<open>The types of terms without bound type variables are normalized.\<close>

lemma tnormt_unb: "tacyc (tyenv env) \<Longrightarrow> unb env t \<Longrightarrow> tnormt (tyenv env) t = t"
  by (induction t) (auto intro!: tnorm_unbound_id)

context wf_algebra
begin

text \<open>
  A typed term without bound (type) variables is well-typed by the typing of the environment,
  with the type variables of the environment.
\<close>

lemma typed_unb_wt_term:
  assumes "tacyc (tyenv env)" "typed env W [] t T" "unb env t" "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
    "below (maxidx env) t" "swf_tm ar [] t"
  shows "wt_term ar (tvars_env (tyenv env) \<union> A) (tctx env W) (maxidx env) t (tnorm (tyenv env) T)"
  using assms by (auto simp: wt_term_def typed_def tnormt_unb tyA_def tyw_def)

lemma norm_term_wt_term:
  assumes pi: "pinv alg ar A W env []" and t: "typed env W [] t T" "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
    "below (maxidx env) t" "swf_tm ar [] t" and n: "ok (norm_term env t) t'"
  shows "wt_term ar (tvars_env (tyenv env) \<union> A) (tctx env W) (maxidx env) t' (tnorm (tyenv env) T)"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  from norm_term_pterm[OF pi g t(1)] t(2,3) obtain t'' where "norm_term env t = return t''"
    "typed env W [] t'' T" "\<forall>U\<in>tys t''. tyw ar (tyenv env) A U" "below (maxidx env) t''"
    by auto
  moreover from this(1) n have "t'' = t'" by (simp add: return_def)
  moreover have "swf_tm ar [] t'"
    using norm_term_swf_tm[OF n penv_inv_swf_env[OF pinvD(1)[OF pi]] t(4)] by simp
  ultimately show ?thesis using norm_term_unb[OF n] tinv_tacyc[OF pinvD(2)[OF pi]]
    by (auto intro: typed_unb_wt_term)
qed

text \<open>
  Normalization that skips lifted assumptions keeps the typing, and the result has no bound
  (type) variables if the skipped assumptions have none.
\<close>

lemma norm_term_skip_typed:
  assumes pi: "pinv alg ar A W env []"
  shows "okT (norm_term_skip env n t) t' \<Longrightarrow> typed env W Ts t propT \<Longrightarrow> cok t \<Longrightarrow>
    \<forall>U\<in>set Ts \<union> tys t. tyw ar (tyenv env) A U \<Longrightarrow> below (maxidx env) t \<Longrightarrow> skip_unb env n t \<Longrightarrow>
    typed env W Ts t' propT \<and> (\<forall>U\<in>tys t'. tyw ar (tyenv env) A U) \<and> below (maxidx env) t' \<and> unb env t'"
proof (induction t arbitrary: n Ts t' rule: measure_induct_rule[of size])
  case (less t)
  note p = pinvD[OF pi]
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF pi])
  show ?case
  proof (cases "n = 0")
    case True
    with less.prems(1) have n: "ok (norm_term env t) t'" by (subst (asm) norm_term_skip.simps) simp
    from norm_term_pterm[OF pi g less.prems(2)] less.prems(4,5) obtain t'' where
      "norm_term env t = return t''" "typed env W Ts t'' propT" "\<forall>U\<in>tys t''. tyw ar (tyenv env) A U"
      "below (maxidx env) t''"
      by auto
    with n norm_term_unb[OF n] show ?thesis by (simp add: return_def)
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      from cok_dest_all[OF less.prems(3) aTb] have t: "t = all_const T $ Abs a T b" and cb: "cok b" by auto
      from less.prems(1) False aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      have tb: "typed env W (T # Ts) b propT" using less.prems(2) t by (simp add: typed_all_const)
      have tw: "\<forall>U\<in>set (T # Ts) \<union> tys b. tyw ar (tyenv env) A U" using less.prems(4) t by auto
      have bb: "below (maxidx env) b" using less.prems(5) t by (simp add: below_def all_const_def)
      have sb: "skip_unb env n b" using less.prems(6) False aTb by (subst (asm) skip_unb.simps) simp
      have "norm_type (tyenv env) T = return (tnorm (tyenv env) T)"
        by (rule norm_type_ok[OF tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] tyw_tcons[OF p(2)]])
          (use less.prems(4) t in auto)
      with T' have T'n: "T' = tnorm (tyenv env) T" by (simp add: return_def)
      from less.IH[OF dest_all_size[OF aTb] b' tb cb tw bb sb]
      have ih: "typed env W (T # Ts) b' propT" "\<forall>U\<in>tys b'. tyw ar (tyenv env) A U"
        "below (maxidx env) b'" "unb env b'"
        by auto
      have "typed env W (T' # Ts) b' propT"
        using ih(1) by (simp add: typed_def T'n tnorm_idem[OF tinv_tacyc[OF p(2)]])
      then have "typed env W Ts t' propT" by (simp add: t' typed_all_const)
      moreover have "tyw ar (tyenv env) A T'"
        unfolding T'n by (rule tyw_tnorm[OF p(2)]) (use less.prems(4) t in auto)
      moreover have "tyw ar (tyenv env) A (all_type T')"
        using tyw_tnorm[OF p(2), of "all_type T"] less.prems(4) t by (auto simp: T'n all_const_def all_type_def)
      moreover have "\<forall>(v, S)\<in>tvars T'. vt_lookup (tyenv env) v = None" using norm_type_unb[OF T'] by blast
      ultimately show ?thesis using ih(2-4) bb
        by (auto simp: t' all_const_def below_def all_type_def propT_def)
    next
      case None
      with less.prems(1) False obtain A0 B where AB: "dest_imp t = Some (A0, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with less.prems(1) False None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A0 B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from cok_dest_imp[OF less.prems(3) AB] have t: "t = implies $ A0 $ B" and cB: "cok B" by auto
      have tA: "typed env W Ts A0 propT" "typed env W Ts B propT"
        using less.prems(2) t by (simp_all add: typed_implies)
      have tw: "\<forall>U\<in>set Ts \<union> tys B. tyw ar (tyenv env) A U" using less.prems(4) t by auto
      have bB: "below (maxidx env) B" using less.prems(5) t by (simp add: below_def implies_def)
      have su: "unb env A0" "skip_unb env (n - 1) B"
        using less.prems(6) False None AB by (subst (asm) skip_unb.simps; simp)+
      from less.IH[OF conjunct2[OF dest_imp_size[OF AB]] B' tA(2) cB tw bB su(2)]
      have ih: "typed env W Ts B' propT" "\<forall>U\<in>tys B'. tyw ar (tyenv env) A U"
        "below (maxidx env) B'" "unb env B'"
        by auto
      have "typed env W Ts t' propT" using ih(1) tA(1) by (simp add: t' mk_implies_def typed_implies)
      then show ?thesis using ih(2-4) su(1) less.prems(4,5)
        by (auto simp: t' t mk_implies_def below_def implies_def imp_type_def propT_def)
    qed
  qed
qed

end

lemma wt_term_list_impliesI:
  assumes "\<forall>X\<in>set Xs. wt_term ar A W m X propT" "wt_term ar A W m Y propT" "Xs \<noteq> [] \<Longrightarrow> tyA ar A imp_type"
  shows "wt_term ar A W m (list_implies Xs Y) propT"
  using assms
proof (induction Xs)
  case (Cons X Xs)
  have r: "wt_term ar A W m (list_implies Xs Y) propT" using Cons by (cases Xs) auto
  have i: "swf_tm ar [] implies" "below m implies" "\<forall>U\<in>tys implies. tyA ar A U"
    using Cons.prems(3) by (simp_all add: implies_imp_type swf_tm_def below_def tyA_def)
  from Cons.prems(1) r i show ?case
    by (auto simp: wt_term_def has_type_implies swf_tm_App below_def)
qed simp

context wf_algebra
begin

text \<open>
  The new theorem of a unifier is well-typed, with the type variables of the unifier and the
  typing of the new premises, if the components of the new theorem are typed in the unifier: the
  flex-flex pairs, the other subgoals and the conclusion by a typing @{term W'}, the new premises by
  a typing @{term W''} that differs from @{term W'} only on renamed variables of the rule.
\<close>

lemma addth_typed:
  assumes ad: "okT (addth ctx A1o na (env', tps)) r"
    and pi': "pinv alg ar A W' env' []" and tps: "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab"
    and BC: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtprop A W' env' X \<and> ibelow (bc_smax ctx) X"
    and pi'': "pinv alg ar A W'' env' []" and As: "\<forall>X\<in>set (na_As na). wtprop A W'' env' X"
    and sk: "bc_lifted ctx \<Longrightarrow> 0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
    and ag: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> bc_smax ctx < snd v \<and> v \<notin> fst ` bvps env' \<and>
      (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
    and imp: "tyA ar (tvars_env (tyenv env') \<union> A) imp_type"
  shows "wt_thm ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') (br_tpairs r) (br_prop r)"
    "vars_thm (br_tpairs r) (br_prop r) \<subseteq>
      vars_thm tps (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)) \<union> fst ` bvps env'"
    "br_env r = env'"
proof -
  let ?A = "tvars_env (tyenv env') \<union> A" and ?W = "tctx env' W''" and ?m = "maxidx env'"
  let ?Bs = "bc_Bs ctx" and ?As = "na_As na" and ?C = "bc_C ctx" and ?bv = "fst ` bvps env'"
  have ac: "tacyc (tyenv env')" by (rule tinv_tacyc[OF pinvD(2)[OF pi']])
  have swf: "swf_env ar env'" by (rule penv_inv_swf_env[OF pinvD(1)[OF pi']])
  text \<open>A term typed by @{term W'} whose variables are not renamed is typed by @{term W''}.\<close>
  have cong: "wt_term ar ?A ?W ?m Y T"
    if "wt_term ar ?A (tctx env' W') ?m Y T" "\<forall>v\<in>vars Y. W'' v = W' v" for Y T
  proof -
    from that(1) have h: "has_type (tctx env' W') [] Y T" by (simp add: wt_term_def)
    have "has_type ?W [] Y T"
      by (rule has_type_vars[OF h]) (use that(2) in \<open>simp add: vtyp_def split: option.splits\<close>)
    with that(1) show ?thesis by (simp add: wt_term_def)
  qed
  text \<open>The other subgoals and the conclusion.\<close>
  have wS: "wt_term ar ?A ?W ?m Y propT \<and> vars Y \<subseteq> vars X \<union> ?bv"
    if X: "X \<in> insert ?C (set ?Bs)" and Y: "Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y" for X Y
  proof -
    from BC X have w: "wtprop A W' env' X" "ibelow (bc_smax ctx) X" by auto
    then have t: "typed env' W' [] X propT" "wfp ar X" "below ?m X" "\<forall>U\<in>tys X. tyw ar (tyenv env') A U"
      by (auto simp: wtprop_def)
    have sw: "swf_tm ar [] X" using t(2) by (simp add: wfp_def swf_tm_def)
    have wY: "wt_term ar ?A (tctx env' W') ?m Y propT \<and> vars Y \<subseteq> vars X \<union> ?bv"
      using Y typed_unb_wt_term[OF ac t(1) _ t(4,3) sw] norm_term_wt_term[OF pi' t(1) t(4,3) sw]
        norm_term_vars[of env' X Y]
      by auto
    have "W'' v = W' v" if v: "v \<in> vars Y" for v
    proof (rule ccontr)
      assume "W'' v \<noteq> W' v"
      with ag have s: "bc_smax ctx < snd v" "v \<notin> ?bv" by blast+
      with wY v have "v \<in> vars X" by blast
      with w(2) s(1) show False by (auto simp: ibelow_def)
    qed
    with wY cong show ?thesis by blast
  qed
  text \<open>The new premises.\<close>
  have wA: "wt_term ar ?A ?W ?m Y propT \<and> vars Y \<subseteq> vars X \<union> ?bv"
    if X: "X \<in> set ?As" and Y: "Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
      okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X" for X Y
  proof -
    from As X have t: "typed env' W'' [] X propT" "wfp ar X" "below ?m X" "\<forall>U\<in>tys X. tyw ar (tyenv env') A U"
      by (auto simp: wtprop_def)
    have sw: "swf_tm ar [] X" "cok X" using t(2) by (simp_all add: wfp_def swf_tm_def)
    have sk: "wt_term ar ?A ?W ?m Y propT"
      if n: "okT (norm_term_skip env' (bc_nlift ctx) X) Y" and u: "skip_unb env' (bc_nlift ctx) X"
    proof -
      from norm_term_skip_typed[OF pi'' n t(1) sw(2) _ t(3) u] t(4)
      have "typed env' W'' [] Y propT" "\<forall>U\<in>tys Y. tyw ar (tyenv env') A U" "below ?m Y" "unb env' Y"
        by auto
      with typed_unb_wt_term[OF ac] norm_term_skip_swf[OF n swf sw] show ?thesis by fastforce
    qed
    from Y show ?thesis
      using typed_unb_wt_term[OF ac t(1) _ t(4,3) sw(1)] norm_term_wt_term[OF pi'' t(1) t(4,3) sw(1)]
        norm_term_vars[of env' X Y] norm_term_skip_vars[of env' "bc_nlift ctx" X Y] sk
      by auto
  qed
  text \<open>The flex-flex pairs.\<close>
  have wT: "\<exists>T. wt_term ar ?A ?W ?m t' T \<and> wt_term ar ?A ?W ?m u' T \<and>
      vars t' \<union> vars u' \<subseteq> vars t \<union> vars u \<union> ?bv"
    if tu: "(t, u) \<in> set tps" and Y: "t' = t \<and> u' = u \<and> env_is_empty env' \<or>
      ok (norm_term env' t) t' \<and> ok (norm_term env' u) u'" for t u t' u'
  proof -
    from tps tu have p: "ptpok ar A W' env' e0 (t, u)" by blast
    then obtain rb a b B where tu': "t = rlist_abs rb a" "u = rlist_abs rb b"
      and tw: "\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar (tyenv env') A U"
      and ty: "typed env' W' (map snd rb) a B" "typed env' W' (map snd rb) b B"
      and bl: "below ?m a" "below ?m b"
      by (auto simp: ptpok_def)
    let ?T = "foldr fun_type (rev (map snd rb)) B"
    have sw: "swf_tm ar [] t" "swf_tm ar [] u" using ptpok_swf[OF p] by auto
    have tt: "typed env' W' [] t ?T" "typed env' W' [] u ?T"
      unfolding tu' by (rule typed_rlist_abs[OF ty(1)], rule typed_rlist_abs[OF ty(2)])
    have tw': "\<forall>U\<in>tys t. tyw ar (tyenv env') A U" "\<forall>U\<in>tys u. tyw ar (tyenv env') A U"
      using tw by (auto simp: tu' tys_rlist_abs)
    have bl': "below ?m t" "below ?m u" using bl by (auto simp: tu' below_def vars_rlist_abs)
    have w: "wt_term ar ?A (tctx env' W') ?m t' (tnorm (tyenv env') ?T) \<and>
        wt_term ar ?A (tctx env' W') ?m u' (tnorm (tyenv env') ?T) \<and> vars t' \<union> vars u' \<subseteq> vars t \<union> vars u \<union> ?bv"
      using Y typed_unb_wt_term[OF ac tt(1) unb_empty tw'(1) bl'(1) sw(1)]
        typed_unb_wt_term[OF ac tt(2) unb_empty tw'(2) bl'(2) sw(2)]
        norm_term_wt_term[OF pi' tt(1) tw'(1) bl'(1) sw(1)] norm_term_wt_term[OF pi' tt(2) tw'(2) bl'(2) sw(2)]
        norm_term_vars[of env' t t'] norm_term_vars[of env' u u']
      by auto
    have "W'' v = W' v" if "v \<in> vars t' \<union> vars u'" for v
      using that w ag tu by blast
    with w cong show ?thesis by blast
  qed
  text \<open>The cases of the new theorem.\<close>
  obtain ntps Hs C' Bs' As' where r: "r = BRes env' ntps (list_implies Hs C') A1o na"
    and nt: "list_all2 (\<lambda>(t, u) (t', u'). t' = t \<and> u' = u \<and> env_is_empty env' \<or>
      ok (norm_term env' t) t' \<and> ok (norm_term env' u) u') tps ntps"
    and H: "Hs = Bs' @ As'" "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y) ?Bs Bs'"
      "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
        okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X) ?As As'"
    and C': "C' = ?C \<and> unb env' ?C \<or> ok (norm_term env' ?C) C'"
  proof -
    have unbS: "unb env' X" if "X \<in> insert ?C (set ?Bs)" "above env' (bc_smax ctx)" for X
      using that BC above_unb by blast
    have refl: "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> R X Y) Xs Xs" if "\<forall>X\<in>set Xs. unb env' X" for R Xs
      using that by (induction Xs) auto
    from ad show thesis
    proof (cases rule: addth_cases)
      case empty
      have "list_all2 (\<lambda>(t, u) (t', u'). t' = t \<and> u' = u \<and> env_is_empty env' \<or>
          ok (norm_term env' t) t' \<and> ok (norm_term env' u) u') tps tps"
        using empty(1) by (auto intro: list.rel_refl_strong)
      with empty refl[of ?Bs] refl[of ?As] unb_empty[OF empty(1)] show thesis
        by (intro that[of tps "?Bs @ ?As" ?C ?Bs ?As]) auto
    next
      case (norm ntps Hs C')
      have nt: "list_all2 (\<lambda>(t, u) (t', u'). t' = t \<and> u' = u \<and> env_is_empty env' \<or>
          ok (norm_term env' t) t' \<and> ok (norm_term env' u) u') tps ntps"
        using norm(3) by (rule list_all2_mono) auto
      from norm(4) show thesis
      proof (elim disjE conjE exE)
        fix As' assume ab: "above env' (bc_smax ctx)" and lf: "bc_lifted ctx" and C: "C' = ?C"
          and Hs: "Hs = ?Bs @ As'"
          and l: "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X') ?As As'"
        from sk[OF lf] have n: "0 \<le> bc_nlift ctx"
          and h: "\<forall>X\<in>set ?As. \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H"
          by auto
        have su: "skip_unb env' (bc_nlift ctx) X" if "X \<in> set ?As" for X
          by (rule skip_unb_take[OF n]) (use h that above_unb[OF ab] in blast)
        have "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X' \<and> X \<in> set ?As) ?As As'"
          using l by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
        then have "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
            okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X) ?As As'"
          by (rule list_all2_mono) (use su in blast)
        with norm(2) nt Hs C refl[of ?Bs] unbS[OF _ ab] show thesis
          by (intro that[of ntps Hs C' ?Bs As']) auto
      next
        fix As' assume ab: "above env' (bc_smax ctx)" and C: "C' = ?C" and Hs: "Hs = ?Bs @ As'"
          and l: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') ?As As'"
        from l have "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
            okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X) ?As As'"
          by (rule list_all2_mono) blast
        with norm(2) nt Hs C refl[of ?Bs] unbS[OF _ ab] show thesis
          by (intro that[of ntps Hs C' ?Bs As']) auto
      next
        assume l: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (?Bs @ ?As) Hs"
          and C: "ok (norm_term env' ?C) C'"
        from l obtain Bs' As' where Hs: "Hs = Bs' @ As'"
          and l1: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') ?Bs Bs'"
          and l2: "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') ?As As'"
          by (auto simp: list_all2_append1)
        from l1 have "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y) ?Bs Bs'"
          by (rule list_all2_mono) blast
        moreover from l2 have "list_all2 (\<lambda>X Y. Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
            okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X) ?As As'"
          by (rule list_all2_mono) blast
        ultimately show thesis using norm(2) nt Hs C by (intro that[of ntps Hs C' Bs' As']) auto
      qed
    qed
  qed
  text \<open>The components of the new theorem.\<close>
  have hB: "wt_term ar ?A ?W ?m Y propT \<and> vars Y \<subseteq> vars (list_implies (?Bs @ ?As) ?C) \<union> ?bv"
    if "Y \<in> set Hs" for Y
  proof -
    from that H(1) consider "Y \<in> set Bs'" | "Y \<in> set As'" by auto
    then show ?thesis
    proof cases
      case 1
      from list_all2_ex2[OF H(2) this] obtain X where "X \<in> set ?Bs" "Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y"
        by blast
      with wS[of X Y] show ?thesis by (auto simp: vars_list_implies)
    next
      case 2
      from list_all2_ex2[OF H(3) this] obtain X where "X \<in> set ?As" "Y = X \<and> unb env' X \<or> ok (norm_term env' X) Y \<or>
          okT (norm_term_skip env' (bc_nlift ctx) X) Y \<and> skip_unb env' (bc_nlift ctx) X"
        by blast
      with wA[of X Y] show ?thesis by (auto simp: vars_list_implies)
    qed
  qed
  have hC: "wt_term ar ?A ?W ?m C' propT \<and> vars C' \<subseteq> vars (list_implies (?Bs @ ?As) ?C) \<union> ?bv"
    using wS[OF _ C'] by (auto simp: vars_list_implies)
  have hT: "\<exists>T. wt_term ar ?A ?W ?m t' T \<and> wt_term ar ?A ?W ?m u' T \<and>
      vars t' \<union> vars u' \<subseteq> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u) \<union> ?bv"
    if "(t', u') \<in> set ntps" for t' u'
  proof -
    from list_all2_ex2[OF nt that] obtain t u where "(t, u) \<in> set tps"
      "t' = t \<and> u' = u \<and> env_is_empty env' \<or> ok (norm_term env' t) t' \<and> ok (norm_term env' u) u'"
      by auto
    with wT[of t u t' u'] show ?thesis by blast
  qed
  have P: "wt_term ar ?A ?W ?m (list_implies Hs C') propT"
    by (rule wt_term_list_impliesI) (use hB hC imp in auto)
  have "cok (list_implies Hs C')" using P by (simp only: wt_term_def) (blast intro: has_type_cok)
  moreover have "\<forall>(t', u')\<in>set ntps. \<exists>T. wt_term ar ?A ?W ?m t' T \<and> wt_term ar ?A ?W ?m u' T"
    using hT by blast
  ultimately show "wt_thm ar ?A ?W ?m (br_tpairs r) (br_prop r)"
    unfolding wt_thm_def using P by (simp add: r)
  show "vars_thm (br_tpairs r) (br_prop r) \<subseteq> vars_thm tps (list_implies (?Bs @ ?As) ?C) \<union> ?bv"
  proof -
    have P: "vars (list_implies Hs C') \<subseteq> vars (list_implies (?Bs @ ?As) ?C) \<union> ?bv"
      using hB hC unfolding vars_list_implies[of Hs] by blast
    have T: "(case p of (t', u') \<Rightarrow> vars t' \<union> vars u') \<subseteq> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u) \<union> ?bv"
      if "p \<in> set ntps" for p
      using hT[of "fst p" "snd p"] that by (auto simp: case_prod_beta)
    show ?thesis unfolding r vars_thm_def bres.sel
      by (intro Un_least UN_least) (use P T in blast)+
  qed
  show "br_env r = env'" by (simp add: r)
qed

text \<open>The maximal index of the enumerated unifiers is at least that of the problem.\<close>

lemma unifiers_maxidx:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
    and u: "unifiers alg env tus = Some (Ok s)" and es: "evals cfg s xs" and x: "El_R env' tps \<in> set xs"
    and te: "vt_is_empty (tenv env)"
  shows "maxidx env \<le> maxidx env'"
proof -
  define v where "v = (STR '''', maxidx env)"
  have "typed env W [] (Var v (W v)) (W v)"
    using te by (simp add: typed_def vtyp_def vt_is_empty_lookup has_type.Var)
  then have "rs_typed ar A [(Var v (W v), W v)] W env"
    using pinvD(5)[OF pi, of v] by (simp add: rs_typed_def below_def v_def)
  from unifiers_prres_rs[OF cfg finA pi this] obtain s' where
    "unifiers alg env tus = Some (Ok s')"
    "fin cfg s' (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres_rs alg ar A [(Var v (W v), W v)] env' tps)"
    by blast
  with u es x evals_det have "prres_rs alg ar A [(Var v (W v), W v)] env' tps"
    unfolding fin_def by fastforce
  then show ?thesis by (auto simp: prres_rs_def rs_typed_def below_def v_def)
qed


subsection \<open>Variables of the problems and the new premises\<close>

text \<open>The variables of the problems of a call are those of the proof state and the rule.\<close>

lemma itsok_vars:
  assumes sp: "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and its: "itsok sp A1o na tus"
    and V: "vars Bi \<subseteq> V" "vars B \<subseteq> V" "\<forall>X\<in>set rAs. vars X \<subseteq> V \<and> cok X"
      "\<forall>(t, u)\<in>set (rtpairs @ stpairs). vars t \<union> vars u \<subseteq> V"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
  shows "\<forall>(t, u)\<in>set tus. vars t \<union> vars u \<subseteq> V"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have bb: "vars (fst BBi) \<union> vars (snd BBi) \<subseteq> V"
  proof (cases lifted)
    case True
    from lift[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0" by blast
    from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" by auto
    have "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    with V(1,2) B Bi show ?thesis by (auto simp: vars_abs_pre vars_lift_pre)
  next
    case False
    with V(1,2) show ?thesis by (simp add: BBi_def)
  qed
  have common: "\<forall>(t, u)\<in>set (BBi # rtpairs @ stpairs). vars t \<union> vars u \<subseteq> V"
    using bb V(4) by (simp add: case_prod_unfold)
  from its consider (res) "tus = BBi # rtpairs @ stpairs"
    | (eres) n asm where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
    unfolding itsok_def by (cases eres_flg; simp add: sp' ctx_def; blast)
  then show ?thesis
  proof cases
    case res
    with common show ?thesis by simp
  next
    case eres
    have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
    obtain A1 As where rA: "rev rAs = A1 # As"
      using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
      using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_def)
    have asm: "asm \<in> set asms" using eres(2-4) er(2) by (simp add: integer_reps)
    have A1: "A1 \<in> set rAs" using rA by (metis list.set_intros(1) set_rev)
    have "vars (rlist_abs params asm) \<union> vars (rlist_abs params concl) \<subseteq> V"
      using tys_vars_assum_problems[OF ap _ asm] V(3) A1 by blast
    moreover have "tus = (rlist_abs params asm, rlist_abs params concl) # BBi # rtpairs @ stpairs"
      using eres(5) er by (simp add: eres_prob_def sp' ctx_def)
    ultimately show ?thesis using common by simp
  qed
qed

text \<open>
  The variables of the new premises have the indices of variables of the premises of the rule
  that stay, or of the subgoal: renaming changes only names.
\<close>

lemma newAs_vars:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
  shows "\<forall>X\<in>set (na_As na). \<forall>x\<in>vars X. \<exists>y\<in>vars (bc_Bi ctx) \<union> (\<Union>X0\<in>set As0. vars X0). snd y = snd x"
proof -
  note nc = newAs_cases[OF na]
  have old: "\<forall>X\<in>set (na_oldAs na). \<forall>x\<in>vars X. \<exists>y\<in>vars (bc_Bi ctx) \<union> (\<Union>X0\<in>set As0. vars X0). snd y = snd x"
    using nc(2)
  proof (elim disjE conjE)
    assume "na_oldAs na = As0"
    then show ?thesis by blast
  next
    let ?r = "rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0"
    assume lf: "bc_lifted ctx" and o: "na_oldAs na = map (strip_apply (ren_term ?r) (bc_Bi ctx)) As0"
    from lr[OF lf] obtain p Bi0 As0' where ls: "lsplit (bc_Bi ctx) = (p, Bi0)"
      and As0: "As0 = map (lift_pre p) As0'"
      by (auto simp: lifted_rule_def)
    from lsplit_ok[OF ls] have Bi: "bc_Bi ctx = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" by auto
    show ?thesis
    proof (intro ballI)
      fix X x assume X: "X \<in> set (na_oldAs na)" and x: "x \<in> vars X"
      from X o As0 obtain X0 where X0: "X0 \<in> set As0'"
        and XX: "X = strip_apply (ren_term ?r) (bc_Bi ctx) (lift_pre p X0)"
        by auto
      have "X = lift_pre p (ren_term ?r X0)" unfolding XX Bi by (rule strip_apply_lift_pre[OF ok at])
      then have "vars X = pvars p \<union> (\<lambda>(x, i). (ren_name (fst ?r) x, i)) ` vars X0"
        by (simp add: vars_lift_pre vars_ren_term)
      with x have "x \<in> pvars p \<or> (\<exists>y\<in>vars X0. snd y = snd x)" by force
      moreover have "pvars p \<subseteq> vars (bc_Bi ctx)" by (simp add: Bi vars_lift_pre)
      moreover have "vars X0 \<subseteq> (\<Union>X0\<in>set As0. vars X0)" using X0 As0 by (auto simp: vars_lift_pre)
      ultimately show "\<exists>y\<in>vars (bc_Bi ctx) \<union> (\<Union>X0\<in>set As0. vars X0). snd y = snd x" by blast
    qed
  qed
  show ?thesis
  proof (intro ballI)
    fix X x assume X: "X \<in> set (na_As na)" and x: "x \<in> vars X"
    from list_all2_ex2[OF nc(1) X] obtain X1 where X1: "X1 \<in> set (na_oldAs na)"
      and f: "if bc_flatten ctx then ok (flatten_params vl n X1) X else X1 = X"
      by blast
    have "vars X \<subseteq> vars X1" using f vars_flatten_params by (auto split: if_splits)
    with old X1 x show "\<exists>y\<in>vars (bc_Bi ctx) \<union> (\<Union>X0\<in>set As0. vars X0). snd y = snd x" by blast
  qed
qed

end

end
