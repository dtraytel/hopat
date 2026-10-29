section \<open>Problems with Type Variables: Soundness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Poly_Flexflex
  imports Unify_Poly_Match Unify_Flexflex
begin

text \<open>
  The soundness proofs of theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Flexflex\<close> for problems
  whose types contain type variables. With a non-empty type environment, \<open>norm_term\<close> also
  normalizes the types of constants and free variables; the result is equivalent for the
  substitutions that respect the type environment.
\<close>


subsection \<open>Normalization\<close>

lemma norm_type_aux_sound:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> (tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> T' = tsubst \<rho> T) \<and> (twf ar \<theta> \<longrightarrow> wft ar T \<longrightarrow> wft ar T')"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  show ?case
  proof (cases T)
    case (Type a Ts)
    from "1.hyps" "1.prems" Type obtain Ts' where m: "ok (mapM (nt \<theta>) Ts) Ts'"
      and T': "T' = Type a Ts'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    from m have l2: "list_all2 (\<lambda>x y. nt \<theta> x = Some (Ok y)) Ts Ts'" by (simp add: ok_mapM)
    have IH: "(tsol \<theta> \<rho> \<longrightarrow> tsubst \<rho> y = tsubst \<rho> x) \<and> (twf ar \<theta> \<longrightarrow> wft ar x \<longrightarrow> wft ar y)"
      if "nt \<theta> x = Some (Ok y)" for x y
      by (rule "1.IH"[OF that refl])
    have "tsol \<theta> \<rho> \<Longrightarrow> map (tsubst \<rho>) Ts' = map (tsubst \<rho>) Ts"
      using l2 IH by (induction rule: list_all2_induct) auto
    moreover have "twf ar \<theta> \<Longrightarrow> \<forall>x\<in>set Ts. wft ar x \<Longrightarrow> \<forall>y\<in>set Ts'. wft ar y"
      using l2 IH by (induction rule: list_all2_induct) auto
    moreover have "length Ts' = length Ts" using l2 by (simp add: list_all2_conv_all_nth)
    ultimately show ?thesis using T' Type by auto
  next
    case (TVar v S)
    from "1.hyps" "1.prems" TVar obtain r' where lk: "ok (type_lookup \<theta> v S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T) T'"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest show ?thesis by (simp add: return_def)
    next
      fix U assume r': "r' = Some U" and l: "vt_lookup \<theta> v = Some (S, U)"
      with rest have "nt \<theta> U = Some (Ok T')" by simp
      from "1.IH"[OF this refl] l TVar show ?thesis by (auto dest: tsolD twfD)
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma ok_norm_type_aux:
  "ok (norm_type_aux \<theta> T) T' \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  "ok (norm_type_aux \<theta> T) T' \<Longrightarrow> twf ar \<theta> \<Longrightarrow> wft ar T \<Longrightarrow> wft ar T'"
  using norm_type_aux_sound[of \<theta> T "Ok T'" T' \<rho> ar] by simp_all

lemma penv_equiv_App: "env \<Turnstile>\<^sub>p s \<approx> s' \<Longrightarrow> env \<Turnstile>\<^sub>p t \<approx> t' \<Longrightarrow> env \<Turnstile>\<^sub>p s $ t \<approx> s' $ t'"
  by (auto simp: penv_equiv_def intro: equiv_App)

lemma penv_equiv_Abs: "env \<Turnstile>\<^sub>p s \<approx> t \<Longrightarrow> env \<Turnstile>\<^sub>p pterm.Abs a T s \<approx> pterm.Abs b U t"
  by (auto simp: penv_equiv_def intro: equiv_Abs)

lemma penv_equiv_types:
  assumes "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> tsubst \<rho> T' = tsubst \<rho> T"
  shows "env \<Turnstile>\<^sub>p Const a T \<approx> Const a T'" "env \<Turnstile>\<^sub>p Free a T \<approx> Free a T'"
proof -
  have eq: "\<sigma> (code (AConst a T)) = \<sigma> (code (AConst a T')) \<and> \<sigma> (code (AFree a T)) = \<sigma> (code (AFree a T'))"
    if "psat \<sigma> env" for \<sigma>
    by (rule trespD[OF psatD(2)[OF that]]) (simp add: assms)
  show "env \<Turnstile>\<^sub>p Const a T \<approx> Const a T'" "env \<Turnstile>\<^sub>p Free a T \<approx> Free a T'"
    by (rule penv_equivI; simp add: eq)+
qed

lemma norm_term2_psound:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> swf_env ar env \<Longrightarrow> proper t \<Longrightarrow> twft ar t \<Longrightarrow>
    proper t' \<and> twft ar t' \<and> env \<Turnstile>\<^sub>p t \<approx> t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  have wf: "swf_env ar env" and t': "ok (case t of
      Const a T \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Const a T'))
    | Free a T \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (Free a T'))
    | pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of
          Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (pterm.Var xi T')))
    | pterm.Abs a T body \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'.
        nt env body \<bind> (\<lambda>body'. return (pterm.Abs a T' body')))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> nt env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF wf])
  show ?case
  proof (cases t)
    case (Const a T)
    with t' obtain T' where n: "ok (norm_type_aux (tyenv env) T) T'" and t'': "t' = Const a T'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have "env \<Turnstile>\<^sub>p Const a T \<approx> Const a T'" by (rule penv_equiv_types(1)[OF ok_norm_type_aux(1)[OF n]])
    with "1.prems" Const t'' ok_norm_type_aux(2)[OF n tw] show ?thesis by simp
  next
    case (Free a T)
    with t' obtain T' where n: "ok (norm_type_aux (tyenv env) T) T'" and t'': "t' = Free a T'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have "env \<Turnstile>\<^sub>p Free a T \<approx> Free a T'" by (rule penv_equiv_types(2)[OF ok_norm_type_aux(1)[OF n]])
    with "1.prems" Free t'' ok_norm_type_aux(2)[OF n tw] show ?thesis by simp
  next
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux (tyenv env) T \<bind> (\<lambda>T'. return (pterm.Var xi T'))) t'"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_lookup_some[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest obtain T' where n: "ok (norm_type_aux (tyenv env) T) T'" and t'': "t' = pterm.Var xi T'"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      have "env \<Turnstile>\<^sub>p pterm.Var xi T \<approx> pterm.Var xi T'" by (simp add: penv_equiv_def)
      with "1.prems" Var t'' ok_norm_type_aux(2)[OF n tw] show ?thesis by simp
    next
      fix U u assume r': "r' = Some u" and l: "vt_lookup (tenv env) xi = Some (U, u)"
      with swf_envD(2)[OF wf] have u: "proper u" "twft ar u" "no_loose_bound (tr u) 0" by auto
      from r' rest have "nt env u = Some (Ok t')" by simp
      from "1.IH"[OF this refl wf u(1,2)] env_equiv_penv[OF env_equiv_lookup'[OF l, of T]] Var u(3)
      show ?thesis by (auto intro: penv_equiv_trans no_loose_bound_mono)
    qed
  next
    case (Abs a T body)
    with t' obtain T' b' where n: "ok (norm_type_aux (tyenv env) T) T'"
      and b: "nt env body = Some (Ok b')" and t'': "t' = pterm.Abs a T' b'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    with "1.IH"[OF b refl wf] "1.prems" Abs ok_norm_type_aux(2)[OF n tw] show ?thesis
      by (auto intro: penv_equiv_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have "nt env (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl wf] "1.prems" App f show ?thesis
        by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
          intro: penv_equiv_trans env_equiv_penv[OF env_equiv_beta])
    next
      case False
      with t' App obtain nf where nf: "nt env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl wf] "1.prems" App
      have nf': "proper nf" "twft ar nf" "env \<Turnstile>\<^sub>p f \<approx> nf"
        "\<And>k. no_loose_bound (tr f) k \<Longrightarrow> no_loose_bound (tr nf) k"
        by auto
      then have fu: "env \<Turnstile>\<^sub>p f $ u \<approx> nf $ u" by (auto intro: penv_equiv_App)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "nt env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl wf] "1.prems" App nf' nfa fu show ?thesis
          by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
            intro: penv_equiv_trans[OF fu] penv_equiv_trans[OF env_equiv_penv[OF env_equiv_beta]])
      next
        case False
        with rest obtain nu where nu: "nt env u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from "1.IH"[OF nu refl wf] "1.prems" App
        have "proper nu" "twft ar nu" "env \<Turnstile>\<^sub>p u \<approx> nu"
          "\<And>k. no_loose_bound (tr u) k \<Longrightarrow> no_loose_bound (tr nu) k"
          by auto
        with nf' t'' App show ?thesis by (auto intro: penv_equiv_App)
      qed
    qed
  qed (use t' "1.prems" in auto)
qed


lemma norm_term1_psound:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> swf_env ar env \<Longrightarrow> proper t \<Longrightarrow> twft ar t \<Longrightarrow>
    proper t' \<and> twft ar t' \<and> env \<Turnstile> t \<approx> t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  have te: "te = tenv env" and wf: "swf_env ar env" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup1 te xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t)
    | pterm.Abs a T body \<Rightarrow> nt te body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> nt te f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    from ok_lookup1[OF lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup te xi = Some (T, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest 1 show ?thesis using "1.prems" by auto
    next
      case 2
      with swf_envD(2)[OF wf] te have u: "proper u" "twft ar u" "no_loose_bound (tr u) 0" by auto
      from 2 rest have "nt te u = Some (Ok t')" by simp
      from "1.IH"[OF this refl te wf u(1,2)] 2 te Var u(3) show ?thesis
        by (auto intro: env_equiv_trans env_equiv_lookup no_loose_bound_mono)
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "nt te body = Some (Ok b')" "t' = pterm.Abs a T b'" by auto
    with "1.IH"[OF this(1) refl te wf] "1.prems" Abs show ?thesis by (auto intro: env_equiv_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have "nt te (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl te wf] "1.prems" App f show ?thesis
        by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
          intro: env_equiv_trans env_equiv_beta)
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl te wf] "1.prems" App
      have nf': "proper nf" "twft ar nf" "env \<Turnstile> f \<approx> nf"
        "\<And>k. no_loose_bound (tr f) k \<Longrightarrow> no_loose_bound (tr nf) k"
        by auto
      then have fu: "env \<Turnstile> f $ u \<approx> nf $ u" by (auto intro: env_equiv_App)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "nt te (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl te wf] "1.prems" App nf' nfa fu show ?thesis
          by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
            intro: env_equiv_trans[OF fu] env_equiv_trans[OF env_equiv_beta])
      next
        case False
        with rest obtain nu where nu: "nt te u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from "1.IH"[OF nu refl te wf] "1.prems" App
        have "proper nu" "twft ar nu" "env \<Turnstile> u \<approx> nu"
          "\<And>k. no_loose_bound (tr u) k \<Longrightarrow> no_loose_bound (tr nu) k"
          by auto
        with nf' t'' App show ?thesis by (auto intro: env_equiv_App)
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

lemma norm_term_swf_tm:
  assumes "ok (norm_term env t) t'" "swf_env ar env" "swf_tm ar rb t"
  shows "swf_tm ar rb t' \<and> env \<Turnstile>\<^sub>p t \<approx> t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    with assms(1,3) show ?thesis by (simp add: norm_term_def)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_psound[OF this refl refl assms(2)] assms(3) show ?thesis
      by (auto simp: swf_tm_def intro: env_equiv_penv)
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_psound[OF this refl assms(2)] assms(3) show ?thesis
      by (auto simp: swf_tm_def)
  qed
qed


subsection \<open>Updating variables\<close>

lemma ok_update_pextends: "ok (update (F, T) t env) env' \<Longrightarrow> pextends env' env"
  using ok_update_extends[of F T t env env'] ok_update(3)[of F T t env env'] by (simp add: pextends_def)

lemma vupdate_psound:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_tm ar [] t \<Longrightarrow> wft ar (snd aU) \<Longrightarrow>
    swf_env ar env' \<and> pextends env' env \<and>
    (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow> \<sigma> (code (AVar (fst aU))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t))"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  have wf: "swf_env ar env" and wt: "swf_tm ar [] t" and gT0: "wft ar T0"
    and up: "ok (case t of
      pterm.Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (pterm.Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using 1 aU by simp_all
  have plain: "?case" if u: "ok (update aU t env) env'"
  proof -
    from u aU have u': "ok (update (v, T0) t env) env'" by simp
    have "swf_env ar env'" using ok_update_swf_env[OF u' wf _ _ gT0] wt by (simp add: swf_tm_def)
    moreover have "pextends env' env" by (rule ok_update_pextends[OF u'])
    moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" if "psat \<sigma> env'" for \<sigma>
      by (rule satD[OF psatD(3)[OF that] ok_update_lookup[OF u']])
    ultimately show ?thesis unfolding aU fst_conv by blast
  qed
  show ?case
  proof (cases t)
    case (Var name' T)
    have mv: "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar name'))" for \<sigma> by (simp add: Var)
    have gT: "wft ar T" using wt Var by (simp add: swf_tm_def)
    consider "v = name'" | "v \<noteq> name'" "indexname_less v name'" | "v \<noteq> name'" "\<not> indexname_less v name'"
      by blast
    then show ?thesis
    proof cases
      case 1
      with up Var aU have "env' = env" by simp
      with 1 Var aU wf show ?thesis by simp
    next
      case 2
      with up Var aU obtain r' where lk: "ok (lookup env name' T) r'"
        and rest: "ok (case r' of None \<Rightarrow> update (name', T) (pterm.Var v T) env
          | Some u \<Rightarrow> vu (v, T0) u env) env'" by auto
      from ok_lookup_some[OF lk] show ?thesis
      proof (elim disjE exE conjE)
        assume "r' = None"
        with rest have u: "ok (update (name', T) (pterm.Var v T) env) env'" by simp
        have "swf_env ar env'" using ok_update_swf_env[OF u wf _ _ gT] gT by simp
        moreover have "pextends env' env" by (rule ok_update_pextends[OF u])
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar name'))" if "psat \<sigma> env'" for \<sigma>
          using satD[OF psatD(3)[OF that] ok_update_lookup[OF u]] by (simp add: equiv_sym)
        ultimately show ?thesis unfolding aU fst_conv mv by blast
      next
        fix U u assume "r' = Some u" and lku: "vt_lookup (tenv env) name' = Some (U, u)"
        with rest have vu: "vu (v, T0) u env = Some (Ok env')" by simp
        have wu: "swf_tm ar [] u" using swf_envD(2)[OF wf lku] by (simp add: swf_tm_def)
        have "swf_env ar env' \<and> pextends env' env \<and> (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow>
            \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u))"
          using "1.IH"[OF vu refl wf wu, unfolded snd_conv fst_conv] gT0 by blast
        then have r: "swf_env ar env'" "pextends env' env"
          "\<And>\<sigma>. psat \<sigma> env' \<Longrightarrow> \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
          by blast+
        have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar name'))" if "psat \<sigma> env'" for \<sigma>
        proof -
          have "psat \<sigma> env" by (rule psat_pextends[OF that r(2)])
          from satD[OF psatD(3)[OF this] lku] r(3)[OF that] show ?thesis by (auto intro: equiv_trans equiv_sym)
        qed
        with r show ?thesis unfolding aU fst_conv mv by blast
      qed
    next
      case 3
      with up Var aU have "ok (update aU t env) env'" by simp
      then show ?thesis by (rule plain)
    qed
  qed (use up plain in auto)
qed

lemma vupdate_pwf:
  assumes "ok (vupdate (v, T) t env) env'" "swf_env ar env" "swf_tm ar [] t" "wft ar T"
  shows "swf_env ar env'" "pextends env' env"
    "psat \<sigma> env' \<Longrightarrow> \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
  using vupdate_psound[OF assms(1) refl assms(2,3)] assms(4) by auto


subsection \<open>Flex-flex assignments\<close>

lemma ff_assign_psound:
  assumes "okW (ff_assign alg env rb t u) env'" "swf_env ar env" "swf_dp ar (rb, t, u)"
  shows "swf_env ar env'" "pextends env' env" "env' \<Turnstile>\<^sub>p rlist_abs rb t \<approx> rlist_abs rb u"
proof -
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF assms(2)])
  have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u"
    using assms(3) by simp_all
  from assms(1) obtain v T b where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and b: "ok (occurs_terms env v [u]) b"
    and rest: "okW (if b then raiseW ASSIGN else do {
        T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
        env' \<leftarrow> cunify_types alg T1 T2 env; liftM (vupdate (v, T) (rlist_abs rb u) env')}) env'"
    by (auto simp: ff_assign_def)
  from rest obtain T1 T2 env1 where bt: "ok (body_type env T) T1" and f: "ok (fastype env rb u) T2"
    and cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (vupdate (v, T) (rlist_abs rb u) env1) env'"
    by (auto split: if_splits)
  have gT: "wft ar T" using get_eta_var_wft[OF gev] wt by (simp add: swf_tm_def)
  have w1: "wft ar T1" using body_type_wft[OF _ refl tw gT] bt by simp
  have w2: "wft ar T2" using fastype_wft[OF f tw bok] wu by (simp add: swf_tm_def)
  note cs = cunify_types_swf[OF cu assms(2) w1 w2]
  have wb: "swf_tm ar [] (rlist_abs rb u)" using swf_tm_binding[OF bok wu] by (simp add: swf_tm_def)
  note vu = vupdate_pwf[OF upd cs(2) wb gT]
  show "swf_env ar env'" by (rule vu(1))
  show "pextends env' env" by (rule pextends_trans[OF vu(2) cs(1)])
  show "env' \<Turnstile>\<^sub>p rlist_abs rb t \<approx> rlist_abs rb u"
  proof (rule penv_equivI)
    fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "psat \<sigma> env'"
    have "tr (rlist_abs rb t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AVar v))" using get_eta_var_equiv[OF gev] by simp
    then have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))"
      using mk_subst_equiv[of "tr (rlist_abs rb t)" "dB.Var (code (AVar v))" \<sigma>] psatD(1)[OF \<sigma>] by simp
    from equiv_trans[OF this vu(3)[OF \<sigma>]]
    show "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))" .
  qed
qed



subsection \<open>Deleting bound variables\<close>

lemma change_bnos_twft: "okW (change_bnos banned lev x) x' \<Longrightarrow> twft ar x' \<longleftrightarrow> twft ar x"
  by (induction banned lev x arbitrary: x' rule: change_bnos.induct) (auto split: if_splits)

lemma clean_term_psound:
  assumes "okW (clean_term banned env t) (env', t')" "swf_env ar env" "swf_tm ar rb t"
    "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    "length rb' = length rb - card (bset banned)"
  shows "swf_env ar env' \<and> pextends env' env \<and> swf_tm ar rb' t' \<and>
    (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow>
      mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr t')))"
proof -
  let ?B = "bset banned" and ?f = "unsquash (bset banned)" and ?m = "length rb - card (bset banned)"
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF assms(2)])
  from assms(1) obtain v T ts where sc: "strip_comb t = (Var v T, ts)"
    by (auto simp: clean_term_def split: prod.splits pterm.splits)
  from swf_tm_strip_comb[OF sc assms(3)] have wv: "swf_tm ar rb (Var v T)"
    and wts: "\<forall>x\<in>set ts. swf_tm ar rb x" by simp_all
  have gT: "wft ar T" using wv by (simp add: swf_tm_def)
  have t: "t = list_comb (Var v T) ts" by (rule strip_comb_list_comb[OF sc])
  let ?n = "length ts"
  from assms(1) sc obtain Ts U fas cas where st: "ok (strip_type env T) (Ts, U)"
    and fa: "okW (flexargs (downto0_list ?n) ts Ts) fas"
    and ca: "okW (foldrW (change_arg (list_all rigid_headed ts) banned) fas []) cas"
    and rest: "okW (let args = sort_args cas; ts' = map fl_t args in
        if decreasing (ilength Ts) args then returnW (env, list_comb (Var v T) ts')
        else (let (env', v') = genvar (fst v) env (foldr fun_type (map fl_T args) U);
                  body = list_comb v' (map (Bound \<circ> fl_j) args) in do {
          env2 \<leftarrow> liftM (vupdate (v, T) (types_abs Ts body) env');
          t' \<leftarrow> liftM (norm_term env2 (list_comb v' ts'));
          returnW (env2, t')})) (env', t')"
    by (auto simp: clean_term_def Let_def split: prod.splits)
  define args where "args = sort_args cas"
  define ts' where "ts' = map fl_t args"
  have gTs: "\<forall>U\<in>set Ts. wft ar U" and gU: "wft ar U" using strip_type_wft[OF st tw gT] by simp_all
  from flexargs_ok[OF fa] have lTs: "length Ts = ?n"
    and fas: "\<forall>a\<in>set fas. \<exists>k<?n. a = Flarg (downto0_list ?n ! k) (ts ! k) (Ts ! k)" by simp_all
  have P: "\<exists>k<?n. fl_j a = integer_of_nat (?n - 1 - k) \<and> fl_T a = Ts ! k \<and>
      okW (change_bnos banned 0 (ts ! k)) (fl_t a)" if "a \<in> set args" for a
  proof -
    from that foldrW_change_arg[OF ca] obtain a0 where "a0 \<in> set fas" "fl_j a = fl_j a0"
      "fl_T a = fl_T a0" "okW (change_bnos banned 0 (fl_t a0)) (fl_t a)"
      by (auto simp: args_def set_sort_args)
    with fas show ?thesis by (fastforce simp: downto0_list_nth)
  qed
  have Pa: "nat_of_integer (fl_j a) < ?n \<and> 0 \<le> fl_j a \<and> wft ar (fl_T a) \<and> swf_tm ar rb' (fl_t a) \<and>
      map_BVars ?f (tr (fl_t a)) = rev (map tr ts) ! nat_of_integer (fl_j a)" if "a \<in> set args" for a
  proof -
    from P[OF that] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)" "fl_T a = Ts ! k"
      and cb: "okW (change_bnos banned 0 (ts ! k)) (fl_t a)" by blast
    have wk: "swf_tm ar rb (ts ! k)" using wts k(1) by simp
    then have pk: "proper (ts ! k)" by (simp add: swf_tm_def)
    from change_bnos_sound[OF cb pk _ assms(4,5)] change_bnos_twft[OF cb] wk
    have "proper (fl_t a)" "twft ar (fl_t a)"
      by (simp_all add: swf_tm_def)
    moreover have "no_loose_bound (tr (fl_t a)) ?m"
      by (rule change_bnos_bound[OF cb pk assms(4,5,6)]) (use wk in \<open>simp add: swf_tm_def\<close>)
    moreover have "map_BVars ?f (tr (fl_t a)) = tr (ts ! k)" by (rule change_bnos_unsquash[OF cb pk assms(4,5)])
    moreover have "rev (map tr ts) ! (?n - 1 - k) = tr (ts ! k)" using k(1) by (simp add: rev_nth)
    moreover have "wft ar (fl_T a)" using gTs k lTs by simp
    moreover have "nat_of_integer (fl_j a) = ?n - 1 - k" "0 \<le> fl_j a"
      using k(2) by (simp_all add: integer_reps)
    ultimately show ?thesis using k(1) assms(7) by (simp add: swf_tm_def)
  qed
  have rel: "list_all2 (\<lambda>k a. k < ?n \<and> map_BVars ?f (tr a) = rev (map tr ts) ! k)
      (map (nat_of_integer \<circ> fl_j) args) ts'"
    unfolding ts'_def list_all2_map1 list_all2_map2 list_all2_conv_all_nth using Pa[OF nth_mem] by auto
  have wts': "\<forall>x\<in>set ts'. swf_tm ar rb' x" using Pa by (auto simp: ts'_def)
  show ?thesis
  proof (cases "decreasing (ilength Ts) args")
    case True
    with rest have env': "env' = env" and t': "t' = list_comb (Var v T) ts'"
      by (simp_all add: Let_def args_def ts'_def)
    have ks: "map (nat_of_integer \<circ> fl_j) args = downs ?n"
      using decreasing_downs[of ?n args] True lTs by (simp add: ilength_eq)
    have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr t'))"
      if \<sigma>: "closed_on UNIV \<sigma>" for \<sigma>
    proof -
      have cl: "no_loose_bound (\<sigma> (code (AVar v))) 0" using \<sigma> by (simp add: closed_onD)
      have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?n (\<sigma> (code (AVar v)) \<degree>\<degree> map BVar (downs ?n))"
        by (rule equiv_sym[OF eta_expand_equiv[OF cl]])
      then have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          Abs_m ?n (\<sigma> (code (AVar v)) \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args))"
        unfolding ks .
      from clean_binding_equiv[OF refl this \<sigma> cl rel]
      show ?thesis unfolding t t' by (simp add: tr_list_comb)
    qed
    moreover have "swf_tm ar rb' t'"
    proof -
      have "swf_tm ar rb' (Var v T)" using gT by (simp add: swf_tm_def)
      with wts' show ?thesis by (simp add: t' swf_tm_list_comb)
    qed
    ultimately show ?thesis using assms(2) env' by (auto dest: psatD(1))
  next
    case False
    obtain env1 v' where g: "genvar (fst v) env (foldr fun_type (map fl_T args) U) = (env1, v')"
      by (cases "genvar (fst v) env (foldr fun_type (map fl_T args) U)")
    define body where "body = list_comb v' (map (Bound \<circ> fl_j) args)"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T) (types_abs Ts body) env1) env2"
      and nt: "ok (norm_term env2 (list_comb v' ts')) t'" and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def)
    note gs = genvar_simps[OF g]
    have gv': "wft ar (foldr fun_type (map fl_T args) U)"
      by (rule wft_foldr_fun_type) (use Pa gU in auto)
    have wv': "swf_tm ar rb'' v'" for rb'' using gs(4) gv' by (simp add: swf_tm_def)
    have wenv1: "swf_env ar env1" by (rule genvar_swf_env[OF g assms(2)])
    have tr_body: "tr body = tr v' \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args)"
      using Pa by (simp add: body_def tr_list_comb comp_def)
    have "proper body" "twft ar body"
      using wv'[of "[]"] Pa by (auto simp: swf_tm_def body_def proper_list_comb twft_list_comb)
    moreover have "no_loose_bound (tr body) (length Ts)"
      using wv'[of "[]"] Pa lTs unfolding tr_body
      by (auto simp: swf_tm_def no_loose_bound_list_app intro: no_loose_bound_mono)
    ultimately have wbody: "swf_cp ar (length Ts) body" by (simp add: swf_cp_def)
    have wabs: "swf_tm ar [] (types_abs Ts body)" by (rule swf_tm_types_abs[OF gTs wbody])
    note vw = vupdate_pwf[OF vu wenv1 wabs gT]
    have ext: "pextends env2 env" using vw(2) genvar_pextends[OF g] by (rule pextends_trans)
    have wl: "swf_tm ar rb' (list_comb v' ts')" using wv' wts' by (simp add: swf_tm_list_comb)
    note nw = norm_term_swf_tm[OF nt vw(1) wl]
    have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr t'))"
      if \<sigma>: "psat \<sigma> env2" for \<sigma>
    proof -
      let ?G = "mk_subst \<sigma> (tr v')"
      have cl: "no_loose_bound ?G 0" using psatD(1)[OF \<sigma>] gs(4) by (simp add: closed_onD)
      have "mk_subst \<sigma> (tr (types_abs Ts body)) =
          Abs_m ?n (?G \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args))"
        using lTs by (simp add: tr_types_abs mk_subst_Abs_m tr_body comp_def)
      with vw(3)[OF \<sigma>] have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          Abs_m ?n (?G \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args))" by simp
      from clean_binding_equiv[OF refl this psatD(1)[OF \<sigma>] cl rel]
      have 1: "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr (list_comb v' ts')))"
        unfolding t by (simp add: tr_list_comb)
      have 2: "map_BVars ?f (mk_subst \<sigma> (tr (list_comb v' ts'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr t'))"
        by (rule map_BVars_equiv[OF penv_equivD[OF conjunct2[OF nw] \<sigma>]])
      show ?thesis by (rule equiv_trans[OF 1 2])
    qed
    with vw(1) ext nw env' show ?thesis by blast
  qed
qed


subsection \<open>Remaining pairs\<close>

lemma penv_equiv_dsolved':
  "env \<Turnstile>\<^sub>p rlist_abs rb s \<approx> rlist_abs rb t \<Longrightarrow> psat \<sigma> env \<Longrightarrow> dsolved \<sigma> (rb, s, t)"
  by (simp add: dsolved_def penv_equivD)

lemma pdsolved_env_equiv:
  assumes "env \<Turnstile>\<^sub>p rlist_abs rb0 t0 \<approx> rlist_abs rb t" "env \<Turnstile>\<^sub>p rlist_abs rb0 u0 \<approx> rlist_abs rb u"
    "psat \<sigma> env" "dsolved \<sigma> (rb, t, u)"
  shows "dsolved \<sigma> (rb0, t0, u0)"
  using penv_equivD[OF assms(1,3)] penv_equivD[OF assms(2,3)] assms(4)
  by (auto simp: dsolved_def intro: equiv_trans equiv_sym)

lemma clean_ffpair_psound:
  assumes "okW (clean_ffpair alg rb t u env tps) (env', tps')" "swf_env ar env" "swf_dp ar (rb, t, u)"
  shows "swf_env ar env' \<and> pextends env' env \<and>
    (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow> dsolved \<sigma> (rb, t, u) \<and> tsolved \<sigma> tps)"
proof -
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  note cb = clean_binder[OF fb]
  have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u"
    using assms(3) by simp_all
  have bok': "sbinders ar rb'" using bok cb(5) by (auto simp: sbinders_def)
  have "(\<exists>env1 t' env2 u'. okW (clean_term banned env t) (env1, t') \<and>
      okW (clean_term banned env1 u) (env2, u') \<and>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')) \<or>
      (env', tps') = (env, add_tpair rb t u tps)"
    using assms(1) fb by (auto simp: clean_ffpair_def Let_def okW_handleW dest!: okW_CHANGE_FAIL_handler)
  then consider (fail) "(env', tps') = (env, add_tpair rb t u tps)"
    | (main) env1 t' env2 u' where "okW (clean_term banned env t) (env1, t')"
      "okW (clean_term banned env1 u) (env2, u')" "okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) (env', tps')"
    by blast
  then show ?thesis
  proof cases
    case fail
    with assms(2) show ?thesis by (auto dest: add_tpair_sound)
  next
    case (main env1 t' env2 u')
    note ct = main(1) and cu = main(2) and ff = main(3)
    note st = clean_term_psound[OF ct assms(2) wt cb(1-4)]
    then have wenv1: "swf_env ar env1" by blast
    note su = clean_term_psound[OF cu wenv1 wu cb(1-4)]
    have wenv2: "swf_env ar env2" and ext2: "pextends env2 env"
      using st su by (blast, blast intro: pextends_trans)
    have wdp': "swf_dp ar (rb', t', u')" using st su bok' by simp
    have sol: "dsolved \<sigma> (rb, t, u)" if \<sigma>: "psat \<sigma> env2" "dsolved \<sigma> (rb', t', u')" for \<sigma>
    proof (rule dsolved_rename[OF _ _ \<sigma>(2)])
      have "psat \<sigma> env1" using psat_pextends[OF \<sigma>(1)] su by blast
      with st show "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr t'))"
        by blast
      from su \<sigma>(1) show "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr u'))"
        by blast
    qed
    from ff_handler[OF ff] consider (fa1) env3 where "okW (ff_assign alg env2 rb' t' u') env3"
        "(env', tps') = (env3, tps)"
      | (fa2) env3 where "okW (ff_assign alg env2 rb' u' t') env3" "(env', tps') = (env3, tps)"
      | (keep) "(env', tps') = (env2, add_tpair rb' t' u' tps)"
      by blast
    then show ?thesis
    proof cases
      case (fa1 env3)
      note fa = fa1(1) and r = fa1(2)
      note fs = ff_assign_psound[OF fa wenv2 wdp']
      have "dsolved \<sigma> (rb, t, u)" if "psat \<sigma> env3" for \<sigma>
        using sol[OF psat_pextends[OF that fs(2)] penv_equiv_dsolved'[OF fs(3) that]] .
      with fs(1,2) ext2 r show ?thesis by (auto intro: pextends_trans)
    next
      case (fa2 env3)
      note fa = fa2(1) and r = fa2(2)
      have wdp'': "swf_dp ar (rb', u', t')" using wdp' by simp
      note fs = ff_assign_psound[OF fa wenv2 wdp'']
      have "dsolved \<sigma> (rb, t, u)" if "psat \<sigma> env3" for \<sigma>
        using sol[OF psat_pextends[OF that fs(2)] penv_equiv_dsolved'[OF penv_equiv_sym[OF fs(3)] that]] .
      with fs(1,2) ext2 r show ?thesis by (auto intro: pextends_trans)
    next
      case keep
      with wenv2 ext2 sol show ?thesis by (auto dest: add_tpair_sound)
    qed
  qed
qed

theorem add_ffpair_psound:
  assumes "okW (add_ffpair alg dp (env, tps)) (env', tps')" "swf_env ar env" "swf_dp ar dp"
  shows "swf_env ar env' \<and> pextends env' env \<and>
    (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow> dsolved \<sigma> dp \<and> tsolved \<sigma> tps)"
proof -
  obtain rb t0 u0 where dp: "dp = (rb, t0, u0)" by (cases dp)
  from assms(1) dp obtain t u where nt: "ok (norm_term env t0) t" and nu: "ok (norm_term env u0) u"
    and rest: "okW (case (head_of t, head_of u) of
        (Var v T, Var w U) \<Rightarrow>
          if v = w then
            (if T = U then returnW (env, add_tpair rb t u tps)
             else raiseW (PExn (Term_Error (STR ''add_ffpair: Var name confusion'') [t, u])))
          else if indexname_less v w then clean_ffpair alg rb u t env tps
          else clean_ffpair alg rb t u env tps
      | _ \<Rightarrow> raiseW (PExn (Term_Error (STR ''add_ffpair: Vars expected'') [t, u]))) (env', tps')"
    by (auto simp: add_ffpair_def)
  have bok: "sbinders ar rb" and wt0: "swf_tm ar rb t0" and wu0: "swf_tm ar rb u0"
    using assms(3) dp by simp_all
  note tn = norm_term_swf_tm[OF nt assms(2) wt0] and un = norm_term_swf_tm[OF nu assms(2) wu0]
  have wdp: "swf_dp ar (rb, t, u)" and wdp': "swf_dp ar (rb, u, t)" using tn un bok by simp_all
  have bk: "dsolved \<sigma> (rb, t0, u0)" if \<sigma>: "psat \<sigma> env" "dsolved \<sigma> (rb, t, u)" for \<sigma>
    by (rule pdsolved_env_equiv[OF penv_equiv_rlist_abs penv_equiv_rlist_abs \<sigma>]) (use tn un in blast)+
  from rest consider (same) "env' = env" "tps' = add_tpair rb t u tps"
    | (tu) "okW (clean_ffpair alg rb t u env tps) (env', tps')"
    | (ut) "okW (clean_ffpair alg rb u t env tps) (env', tps')"
    by (auto split: pterm.splits if_splits)
  then show ?thesis
  proof cases
    case same
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps" if "psat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
      using add_tpair_sound[of \<sigma> rb t u tps] bk[of \<sigma>] that same by (simp add: dp)
    with assms(2) same show ?thesis by simp
  next
    case tu
    note c = clean_ffpair_psound[OF tu assms(2) wdp]
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps" if "psat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
    proof -
      have "psat \<sigma> env" using psat_pextends[OF that(1)] c by blast
      with c that bk[of \<sigma>] show ?thesis by (simp add: dp)
    qed
    with c show ?thesis by blast
  next
    case ut
    note c = clean_ffpair_psound[OF ut assms(2) wdp']
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps" if "psat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
    proof -
      have "psat \<sigma> env" using psat_pextends[OF that(1)] c by blast
      with c that bk[of \<sigma>] show ?thesis by (simp add: dp dsolved_swap)
    qed
    with c show ?thesis by blast
  qed
qed

theorem foldrW_add_ffpair_psound:
  "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env', tps') \<Longrightarrow> swf_env ar env \<Longrightarrow>
    \<forall>dp\<in>set ffs. swf_dp ar dp \<Longrightarrow>
    swf_env ar env' \<and> pextends env' env \<and>
    (\<forall>\<sigma>. psat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow> dsolved_all \<sigma> ffs \<and> tsolved \<sigma> tps)"
proof (induction ffs arbitrary: env' tps')
  case (Cons dp ffs)
  from Cons.prems(1) obtain env1 tps1 where f: "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair alg dp (env1, tps1)) (env', tps')" by auto
  note IH = Cons.IH[OF f Cons.prems(2)] Cons.prems(3)
  then have "swf_env ar env1" by simp
  note A = add_ffpair_psound[OF a this] Cons.prems(3)
  from IH A show ?case by (auto intro: pextends_trans psat_pextends)
qed simp

end
