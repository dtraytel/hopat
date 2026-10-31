section \<open>Soundness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex
  imports Unify_Match
begin

context csig
begin

text \<open>
  At the end of the search, \<open>add_ffpair\<close> simplifies the remaining flex-flex pairs: it deletes
  bound variables that do not occur in both terms (\<open>clean_term\<close>), does the assignments it
  can, and returns the other pairs. We show that the result is a unifier: every substitution
  that satisfies the final environment and solves the returned pairs solves the input pairs.
\<close>


subsection \<open>Normalization\<close>

lemma ok_lookup1:
  "ok (lookup1 te xi T) r \<Longrightarrow>
    r = None \<and> vt_lookup te xi = None \<or> (\<exists>u. r = Some u \<and> vt_lookup te xi = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

lemma norm_term1_sound:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> wf_env ar env \<Longrightarrow> proper t \<Longrightarrow> typs_ok ar t \<Longrightarrow>
    proper t' \<and> typs_ok ar t' \<and> env \<Turnstile> t \<approx> t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  have te: "te = tenv env" and wf: "wf_env ar env" and t': "ok (case t of
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
      with wf_envD(2)[OF wf] te have u: "proper u" "typs_ok ar u" "no_loose_bound (tr u) 0" by auto
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
        by (auto simp: proper_subst_bound typs_ok_subst_bound no_loose_bound_beta
          intro: env_equiv_trans env_equiv_beta)
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl te wf] "1.prems" App
      have nf': "proper nf" "typs_ok ar nf" "env \<Turnstile> f \<approx> nf"
        "\<And>k. no_loose_bound (tr f) k \<Longrightarrow> no_loose_bound (tr nf) k"
        by auto
      then have fu: "env \<Turnstile> f $ u \<approx> nf $ u" by (auto intro: env_equiv_App)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "nt te (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl te wf] "1.prems" App nf' nfa fu show ?thesis
          by (auto simp: proper_subst_bound typs_ok_subst_bound no_loose_bound_beta
            intro: env_equiv_trans[OF fu] env_equiv_trans[OF env_equiv_beta])
      next
        case False
        with rest obtain nu where nu: "nt te u = Some (Ok nu)" and t'': "t' = nf $ nu"
          by (cases nf) auto
        from "1.IH"[OF nu refl te wf] "1.prems" App
        have "proper nu" "typs_ok ar nu" "env \<Turnstile> u \<approx> nu"
          "\<And>k. no_loose_bound (tr u) k \<Longrightarrow> no_loose_bound (tr nu) k"
          by auto
        with nf' t'' App show ?thesis by (auto intro: env_equiv_App)
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

lemma norm_term_wf_tm:
  assumes "ok (norm_term env t) t'" "wf_env ar env" "wf_tm ar rb t"
  shows "wf_tm ar rb t' \<and> env \<Turnstile> t \<approx> t'"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  show ?thesis
  proof (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    case True
    with assms(1,3) show ?thesis by (simp add: norm_term_def)
  next
    case False
    with assms(1) e have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_sound[OF this refl refl assms(2)] assms(3) show ?thesis
      by (auto simp: wf_tm_def)
  qed
qed


subsection \<open>Updating variables\<close>

text \<open>\<open>vupdate (v, T) t\<close> binds \<open>v\<close> to \<open>t\<close>, but a variable-variable binding may go the other way.\<close>

lemma vupdate_sound:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> wf_env ar env \<Longrightarrow> wf_tm ar [] t \<Longrightarrow> ground ar (snd aU) \<Longrightarrow>
    wf_env ar env' \<and> extends env env' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> \<sigma> (code (AVar (fst aU))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t))"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  have wf: "wf_env ar env" and wt: "wf_tm ar [] t" and gT0: "ground ar T0"
    and up: "ok (case t of
      pterm.Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (pterm.Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using 1 aU by simp_all
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  have plain: "?case" if u: "ok (update aU t env) env'"
  proof -
    from u aU have u': "ok (update (v, T0) t env) env'" by simp
    have "wf_env ar env'" using ok_update_wf_env[OF u' wf _ _ gT0] wt by (simp add: wf_tm_def)
    moreover have "extends env env'" by (rule ok_update_extends[OF u'])
    moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" if "sat \<sigma> env'" for \<sigma>
      by (rule satD[OF that ok_update_lookup[OF u']])
    ultimately show ?thesis unfolding aU fst_conv by blast
  qed
  show ?case
  proof (cases t)
    case (Var name' T)
    have mv: "mk_subst \<sigma> (tr t) = \<sigma> (code (AVar name'))" for \<sigma> by (simp add: Var)
    have gT: "ground ar T" using wt Var by (simp add: wf_tm_def)
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
      from ok_lookup[OF e lk] show ?thesis
      proof (elim disjE exE conjE)
        assume "r' = None"
        with rest have u: "ok (update (name', T) (pterm.Var v T) env) env'" by simp
        have "wf_env ar env'" using ok_update_wf_env[OF u wf _ _ gT] gT by simp
        moreover have "extends env env'" by (rule ok_update_extends[OF u])
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar name'))" if "sat \<sigma> env'" for \<sigma>
          using satD[OF that ok_update_lookup[OF u]] by (simp add: equiv_sym)
        ultimately show ?thesis unfolding aU fst_conv mv by blast
      next
        fix u assume "r' = Some u" and lku: "vt_lookup (tenv env) name' = Some (T, u)"
        with rest have vu: "vu (v, T0) u env = Some (Ok env')" by simp
        have wu: "wf_tm ar [] u" using wf_envD(2)[OF wf lku] by (simp add: wf_tm_def)
        have "wf_env ar env' \<and> extends env env' \<and> (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow>
            \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u))"
          using "1.IH"[OF vu refl wf wu, unfolded snd_conv fst_conv] gT0 by blast
        then have r: "wf_env ar env'" "extends env env'"
          "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
          by blast+
        have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar name'))"
          if "closed_on UNIV \<sigma>" "sat \<sigma> env'" for \<sigma>
        proof -
          have "sat \<sigma> env" by (rule sat_extends[OF that(2) r(2)])
          from satD[OF this lku] r(3)[OF that] show ?thesis by (auto intro: equiv_trans equiv_sym)
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

lemma vupdate_wf:
  assumes "ok (vupdate (v, T) t env) env'" "wf_env ar env" "wf_tm ar [] t" "ground ar T"
  shows "wf_env ar env'" "extends env env'"
    "closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> \<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
  using vupdate_sound[OF assms(1) refl assms(2,3)] assms(4) by auto


subsection \<open>Flex-flex assignments\<close>

lemma ff_assign_sound:
  assumes "okW (ff_assign alg env rb t u) env'" "wf_env ar env" "wf_dp ar (rb, t, u)"
  shows "wf_env ar env'" "extends env env'" "env' \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb u"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
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
  have gT: "ground ar T" using get_eta_var_ground[OF gev] wt by (simp add: wf_tm_def)
  have "ground ar T1" by (rule body_type_ground[OF e gT bt])
  moreover have "ground ar T2" using fastype_ground[OF e bok _ f] wu by (simp add: wf_tm_def)
  ultimately have env1: "env1 = env" using cunify_types_ground cu by blast
  have wb: "wf_tm ar [] (rlist_abs rb u)" using wf_tm_binding[OF bok wu] by (simp add: wf_tm_def)
  note vu = vupdate_wf[OF upd[unfolded env1] assms(2) wb gT]
  show "wf_env ar env'" "extends env env'" by (rule vu(1), rule vu(2))
  show "env' \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb u"
  proof (rule env_equivI)
    fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
    have "tr (rlist_abs rb t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AVar v))" using get_eta_var_equiv[OF gev] by simp
    then have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))"
      using mk_subst_equiv[of "tr (rlist_abs rb t)" "dB.Var (code (AVar v))" \<sigma>] \<sigma>(1) by simp
    from equiv_trans[OF this vu(3)[OF \<sigma>]]
    show "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))" .
  qed
qed


subsection \<open>Deleting bound variables\<close>

text \<open>
  \<open>change_bnos banned\<close> deletes the banned loose bound variables: the others are renamed by
  \<open>squash B\<close>, which maps \<open>i\<close> to the number of non-banned indices below \<open>i\<close>. The renaming is
  injective on the non-banned indices, so it can be undone on terms without banned loose bound
  variables.
\<close>

definition squash :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "squash B i = card ({..<i} - B)"

definition shift_at :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "shift_at k f i = (if i < k then i else k + f (i - k))"

lemma shift_at_Suc: "case_nat 0 (\<lambda>a. Suc (shift_at k f a)) = shift_at (Suc k) f"
  by (auto simp: fun_eq_iff shift_at_def split: nat.split)

lemma map_BVars_shift_at_Abs:
  "map_BVars (shift_at k f) (dB.Abs t) = dB.Abs (map_BVars (shift_at (Suc k) f) t)"
  by (simp add: shift_at_Suc[symmetric])

lemma squash_less:
  assumes "i < i'" "i \<notin> B"
  shows "squash B i < squash B i'"
  unfolding squash_def by (rule psubset_card_mono) (use assms in auto)

lemma inj_on_squash: "inj_on (squash B) (- B)"
proof (rule inj_onI)
  fix i i' assume "i \<in> - B" "i' \<in> - B" "squash B i = squash B i'"
  then show "i = i'" using squash_less[of i i' B] squash_less[of i' i B]
    by (cases i i' rule: linorder_cases) auto
qed

lemma squash_bound:
  assumes "B \<subseteq> {..<n}" "i < n" "i \<notin> B"
  shows "squash B i < n - card B"
proof -
  have "squash B i < card ({..<n} - B)" unfolding squash_def
    by (rule psubset_card_mono) (use assms in auto)
  also have "card ({..<n} - B) = n - card B" using assms(1) by (simp add: card_Diff_subset finite_subset)
  finally show ?thesis .
qed

definition unsquash :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "unsquash B = inv_into (- B) (squash B)"

lemma unsquash_squash: "i \<notin> B \<Longrightarrow> unsquash B (squash B i) = i"
  unfolding unsquash_def by (rule inv_into_f_f[OF inj_on_squash]) simp

definition bset :: "integer list \<Rightarrow> nat set" where
  "bset banned = nat_of_integer ` set banned"

lemma nat_of_integer_inj: "inj_on nat_of_integer {i. 0 \<le> i}"
  by (rule inj_onI) (simp add: nat_of_integer_eq_iff)

lemma squash_count:
  assumes "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "0 \<le> k"
  shows "nat_of_integer (k - ilength (filter (\<lambda>j. j < k) banned)) = squash (bset banned) (nat_of_integer k)"
    and "ilength (filter (\<lambda>j. j < k) banned) \<le> k"
proof -
  let ?m = "nat_of_integer k"
  have "length (filter (\<lambda>j. j < k) banned) = card ({j. j < k} \<inter> set banned)"
    using assms(1) by (rule distinct_length_filter)
  also have "{j. j < k} \<inter> set banned = {j\<in>set banned. j < k}" by auto
  also have "card {j\<in>set banned. j < k} = card (nat_of_integer ` {j\<in>set banned. j < k})"
    by (rule card_image[symmetric], rule inj_on_subset[OF nat_of_integer_inj]) (use assms(2) in auto)
  also have "nat_of_integer ` {j\<in>set banned. j < k} = {..<?m} \<inter> bset banned"
    using assms(2,3) by (auto simp: bset_def nat_of_integer_less_iff image_iff)
  finally have c: "length (filter (\<lambda>j. j < k) banned) = card ({..<?m} \<inter> bset banned)" .
  have le: "card ({..<?m} \<inter> bset banned) \<le> ?m"
    using card_mono[of "{..<?m}" "{..<?m} \<inter> bset banned"] by auto
  have "squash (bset banned) ?m = ?m - card ({..<?m} \<inter> bset banned)"
    unfolding squash_def by (simp add: card_Diff_subset_Int)
  moreover have "nat_of_integer (k - integer_of_nat (card ({..<?m} \<inter> bset banned))) =
      ?m - card ({..<?m} \<inter> bset banned)"
    using le assms(3) by (simp add: integer_reps)
  ultimately show "nat_of_integer (k - ilength (filter (\<lambda>j. j < k) banned)) =
      squash (bset banned) (nat_of_integer k)" using c by (simp add: ilength_eq)
  show "ilength (filter (\<lambda>j. j < k) banned) \<le> k"
    using c le assms(3) by (simp add: ilength_eq integer_reps)
qed

lemma change_bnos_sound:
  assumes "okW (change_bnos banned lev x) x'" "proper x" "0 \<le> lev" "distinct banned"
    "\<forall>j\<in>set banned. 0 \<le> j"
  shows "proper x' \<and> (typs_ok ar x' \<longleftrightarrow> typs_ok ar x) \<and>
    tr x' = map_BVars (shift_at (nat_of_integer lev) (squash (bset banned))) (tr x) \<and>
    (\<forall>i\<in>loose_BVars (tr x). nat_of_integer lev \<le> i \<longrightarrow> i - nat_of_integer lev \<notin> bset banned)"
  using assms
proof (induction banned lev x arbitrary: x' rule: change_bnos.induct)
  case (1 banned lev i)
  show ?case
  proof (cases "i < lev")
    case True
    with "1.prems" show ?thesis by (auto simp: shift_at_def integer_reps)
  next
    case False
    with "1.prems"(1) have nb: "i - lev \<notin> set banned"
      and x': "x' = Bound (i - ilength (filter (\<lambda>j. j < i - lev) banned))"
      by (auto split: if_splits)
    have k: "0 \<le> i - lev" using False by simp
    have sq: "nat_of_integer (i - lev - ilength (filter (\<lambda>j. j < i - lev) banned)) =
        squash (bset banned) (nat_of_integer (i - lev))"
      by (rule squash_count(1)[OF "1.prems"(4,5) k])
    have cle: "ilength (filter (\<lambda>j. j < i - lev) banned) \<le> i - lev"
      by (rule squash_count(2)[OF "1.prems"(4,5) k])
    have nl: "nat_of_integer (i - lev) = nat_of_integer i - nat_of_integer lev"
      using False "1.prems"(3) by (simp add: integer_reps nat_diff_distrib)
    have "nat_of_integer (i - ilength (filter (\<lambda>j. j < i - lev) banned)) =
        nat_of_integer lev + nat_of_integer (i - lev - ilength (filter (\<lambda>j. j < i - lev) banned))"
      using cle "1.prems"(3) by (simp add: integer_reps nat_add_distrib[symmetric])
    moreover have "nat_of_integer (i - lev) \<notin> bset banned"
      using nb k "1.prems"(5) by (auto simp: bset_def nat_of_integer_eq_iff)
    moreover have "0 \<le> i - ilength (filter (\<lambda>j. j < i - lev) banned)"
      using cle "1.prems"(3) by (simp add: integer_reps)
    ultimately show ?thesis using x' sq nl False "1.prems"(3)
      by (auto simp: shift_at_def nat_of_integer_less_iff)
  qed
next
  case (2 banned lev a T t)
  from "2.prems"(1) obtain t' where t': "okW (change_bnos banned (lev + 1) t) t'"
    and x': "x' = Abs a T t'" by auto
  have l: "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)"
    using "2.prems"(3) by (simp add: integer_reps)
  from "2.IH"[OF t'] "2.prems" l show ?case
    by (auto simp: x' shift_at_Suc)
next
  case (3 banned lev t u)
  from "3.prems"(1) obtain t' u' where t': "okW (change_bnos banned lev t) t'"
    and u': "okW (change_bnos banned lev u) u'" and x': "x' = t' $ u'" by auto
  from "3.IH"(1)[OF t'] "3.IH"(2)[OF t' u'] "3.prems" show ?case by (auto simp: x')
qed auto


lemma change_bnos_unsquash:
  assumes "okW (change_bnos banned 0 x) x'" "proper x" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
  shows "map_BVars (unsquash (bset banned)) (tr x') = tr x"
proof -
  from change_bnos_sound[OF assms(1,2) _ assms(3,4)]
  have x': "tr x' = map_BVars (squash (bset banned)) (tr x)"
    and nb: "\<forall>i\<in>loose_BVars (tr x). i \<notin> bset banned"
    by (simp_all add: shift_at_def[abs_def])
  have "map_BVars (unsquash (bset banned)) (tr x') = map_BVars (unsquash (bset banned) \<circ> squash (bset banned)) (tr x)"
    by (simp add: x' map_BVars_comp)
  also have "\<dots> = map_BVars id (tr x)"
    by (rule map_BVars_cong) (use nb unsquash_squash in auto)
  finally show ?thesis by (simp add: map_BVars_id)
qed

lemma change_bnos_bound:
  assumes "okW (change_bnos banned 0 x) x'" "proper x" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
    "bset banned \<subseteq> {..<n}" "no_loose_bound (tr x) n"
  shows "no_loose_bound (tr x') (n - card (bset banned))"
proof -
  from change_bnos_sound[OF assms(1,2) _ assms(3,4)]
  have x': "tr x' = map_BVars (squash (bset banned)) (tr x)"
    and nb: "\<forall>i\<in>loose_BVars (tr x). i \<notin> bset banned"
    by (simp_all add: shift_at_def[abs_def])
  have "loose_BVars (tr x) \<subseteq> {0..<n}" by (rule no_loose_bound_BVars[OF assms(6)])
  then have "loose_BVars (tr x') \<subseteq> {..<n - card (bset banned)}"
    using nb squash_bound[OF assms(5)] by (auto simp: x' loose_BVars_map_BVars)
  then show ?thesis by (rule loose_BVars_no_loose_bound)
qed

lemma mk_subst_map_BVars:
  "closed_on UNIV \<sigma> \<Longrightarrow> mk_subst \<sigma> (map_BVars f t) = map_BVars f (mk_subst \<sigma> t)"
  by (induction t arbitrary: f) (auto intro: map_BVars_no_loose[symmetric] closed_onD)

lemma map_BVars_equiv: "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> map_BVars f s \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f t"
  by (rule map_BVars_preserves_closure)


subsection \<open>Flexible arguments\<close>

lemma flexargs_ok:
  "okW (flexargs js ts Ts) fas \<Longrightarrow>
    length js = length ts \<and> length Ts = length ts \<and>
    (\<forall>a\<in>set fas. \<exists>k<length ts. a = Flarg (js ! k) (ts ! k) (Ts ! k))"
proof (induction js ts Ts arbitrary: fas rule: flexargs.induct)
  case (2 j js t ts T Ts)
  then obtain args where "okW (flexargs js ts Ts) args" "fas = Flarg j t T # args" by auto
  with "2.IH"[OF this(1)] show ?case by (fastforce simp: nth_Cons')
qed auto

lemma foldrW_change_arg:
  "okW (foldrW (change_arg del banned) fas acc) cas \<Longrightarrow>
    \<forall>a'\<in>set cas. a' \<in> set acc \<or> (\<exists>a\<in>set fas. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and>
      okW (change_bnos banned 0 (fl_t a)) (fl_t a'))"
proof (induction fas arbitrary: cas)
  case (Cons a fas)
  then obtain cas1 where c1: "okW (foldrW (change_arg del banned) fas acc) cas1"
    and c: "okW (change_arg del banned a cas1) cas" by auto
  obtain j t T where a: "a = Flarg j t T" by (cases a)
  from c a have "cas = cas1 \<or> (\<exists>t'. okW (change_bnos banned 0 t) t' \<and> cas = Flarg j t' T # cas1)"
    by (auto simp: change_arg_def split: if_splits)
  with "Cons.IH"[OF c1] a show ?case by fastforce
qed simp

lemma set_ins_arg: "set (ins_arg x xs) = insert x (set xs)"
  by (induction xs) auto

lemma set_sort_args: "set (sort_args xs) = set xs"
  by (induction xs) (auto simp: set_ins_arg)

lemma length_ins_arg: "length (ins_arg x xs) = Suc (length xs)"
  by (induction xs) auto

lemma not_decreasing_neg: "k < 0 \<Longrightarrow> \<not> decreasing k args"
  by (induction k args rule: decreasing.induct) auto

lemma decreasing_downs:
  "decreasing (integer_of_nat m) args \<Longrightarrow> map (nat_of_integer \<circ> fl_j) args = downs m"
proof (induction args arbitrary: m)
  case Nil
  then show ?case by (simp add: integer_eq_iff)
next
  case (Cons a args)
  show ?case
  proof (cases m)
    case 0
    with Cons.prems not_decreasing_neg[of "-1" args] show ?thesis by simp
  next
    case (Suc m')
    have m1: "integer_of_nat m - 1 = integer_of_nat m'" using Suc by (simp add: integer_eq_iff)
    with Cons.prems have "fl_j a = integer_of_nat m'" "decreasing (integer_of_nat m') args" by simp_all
    with Cons.IH[of m'] Suc show ?thesis by simp
  qed
qed

text \<open>The new variable applied to the kept arguments, for a binding that selects them.\<close>

lemma Abs_m_select_map_BVars:
  assumes "no_loose_bound G 0" "length ts = n" "\<forall>k\<in>set ks. k < n"
    "list_all2 (\<lambda>k a. map_BVars f a = rev ts ! k) ks as"
  shows "Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> as)"
proof -
  have "map (map_BVars f) as = map (\<lambda>k. rev ts ! k) ks"
    using assms(4) by (induction rule: list_all2_induct) auto
  then have "map_BVars f (G \<degree>\<degree> as) = G \<degree>\<degree> map (\<lambda>k. rev ts ! k) ks"
    using map_BVars_no_loose[OF assms(1)] by simp
  with Abs_m_apps_select[OF assms(1-3)] show ?thesis by simp
qed


lemma clean_binding_equiv:
  assumes "length ts = n" "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m n (G \<degree>\<degree> map BVar ks)"
    "closed_on UNIV \<sigma>" "no_loose_bound G 0"
    "list_all2 (\<lambda>k a. k < n \<and> map_BVars f (tr a) = rev (map tr ts) ! k) ks as"
  shows "mk_subst \<sigma> (tr (list_comb (Var v T) ts)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) as)"
proof -
  let ?ts = "map (mk_subst \<sigma> \<circ> tr) ts"
  have e: "mk_subst \<sigma> (tr (list_comb (Var v T) ts)) = \<sigma> (code (AVar v)) \<degree>\<degree> ?ts"
    by (simp add: tr_list_comb)
  have 1: "\<sigma> (code (AVar v)) \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ?ts"
    by (rule equiv_list_app[OF assms(2)]) (simp add: list_all2_refl)
  have 2: "Abs_m n (G \<degree>\<degree> map BVar ks) \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (G \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) as)"
  proof (rule Abs_m_select_map_BVars[OF assms(4)])
    show "length ?ts = n" using assms(1) by simp
    show "\<forall>k\<in>set ks. k < n" using assms(5) by (induction rule: list_all2_induct) auto
    show "list_all2 (\<lambda>k a. map_BVars f a = rev ?ts ! k) ks (map (mk_subst \<sigma> \<circ> tr) as)"
      unfolding list_all2_map2
    proof (rule list_all2_mono[OF assms(5)])
      fix k a assume "k < n \<and> map_BVars f (tr a) = rev (map tr ts) ! k"
      with assms(1,3) show "map_BVars f ((mk_subst \<sigma> \<circ> tr) a) = rev ?ts ! k"
        by (simp add: mk_subst_map_BVars[symmetric] rev_map)
    qed
  qed
  show ?thesis unfolding e by (rule equiv_trans[OF 1 2])
qed

lemma downto0_list_nth: "k < n \<Longrightarrow> downto0_list n ! k = integer_of_nat (n - 1 - k)"
  by (simp add: downto0_list_def rev_nth)

lemma clean_term_sound:
  assumes "okW (clean_term banned env t) (env', t')" "wf_env ar env" "wf_tm ar rb t"
    "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    "length rb' = length rb - card (bset banned)"
  shows "wf_env ar env' \<and> extends env env' \<and> wf_tm ar rb' t' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow>
      mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr t')))"
proof -
  let ?B = "bset banned" and ?f = "unsquash (bset banned)" and ?m = "length rb - card (bset banned)"
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  from assms(1) obtain v T ts where sc: "strip_comb t = (Var v T, ts)"
    by (auto simp: clean_term_def split: prod.splits pterm.splits)
  from wf_tm_strip_comb[OF sc assms(3)] have wv: "wf_tm ar rb (Var v T)"
    and wts: "\<forall>x\<in>set ts. wf_tm ar rb x" by simp_all
  have gT: "ground ar T" using wv by (simp add: wf_tm_def)
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
  have gTs: "\<forall>U\<in>set Ts. ground ar U" and gU: "ground ar U" by (rule strip_type_ground[OF e gT st])+
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
  have Pa: "nat_of_integer (fl_j a) < ?n \<and> 0 \<le> fl_j a \<and> ground ar (fl_T a) \<and> wf_tm ar rb' (fl_t a) \<and>
      map_BVars ?f (tr (fl_t a)) = rev (map tr ts) ! nat_of_integer (fl_j a)" if "a \<in> set args" for a
  proof -
    from P[OF that] obtain k where k: "k < ?n" "fl_j a = integer_of_nat (?n - 1 - k)" "fl_T a = Ts ! k"
      and cb: "okW (change_bnos banned 0 (ts ! k)) (fl_t a)" by blast
    have wk: "wf_tm ar rb (ts ! k)" using wts k(1) by simp
    then have pk: "proper (ts ! k)" by (simp add: wf_tm_def)
    from change_bnos_sound[OF cb pk _ assms(4,5)] wk have "proper (fl_t a)" "typs_ok ar (fl_t a)"
      by (simp_all add: wf_tm_def)
    moreover have "no_loose_bound (tr (fl_t a)) ?m"
      by (rule change_bnos_bound[OF cb pk assms(4,5,6)]) (use wk in \<open>simp add: wf_tm_def\<close>)
    moreover have "map_BVars ?f (tr (fl_t a)) = tr (ts ! k)" by (rule change_bnos_unsquash[OF cb pk assms(4,5)])
    moreover have "rev (map tr ts) ! (?n - 1 - k) = tr (ts ! k)" using k(1) by (simp add: rev_nth)
    moreover have "ground ar (fl_T a)" using gTs k lTs by simp
    moreover have "nat_of_integer (fl_j a) = ?n - 1 - k" "0 \<le> fl_j a"
      using k(2) by (simp_all add: integer_reps)
    ultimately show ?thesis using k(1) assms(7) by (simp add: wf_tm_def)
  qed
  have rel: "list_all2 (\<lambda>k a. k < ?n \<and> map_BVars ?f (tr a) = rev (map tr ts) ! k)
      (map (nat_of_integer \<circ> fl_j) args) ts'"
    unfolding ts'_def list_all2_map1 list_all2_map2 list_all2_conv_all_nth using Pa[OF nth_mem] by auto
  have wts': "\<forall>x\<in>set ts'. wf_tm ar rb' x" using Pa by (auto simp: ts'_def)
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
    moreover have "wf_tm ar rb' t'"
    proof -
      have "wf_tm ar rb' (Var v T)" using gT by (simp add: wf_tm_def)
      with wts' show ?thesis by (simp add: t' wf_tm_list_comb)
    qed
    ultimately show ?thesis using assms(2) env' by simp
  next
    case False
    obtain env1 v' where g: "genvar (fst v) env (foldr fun_type (map fl_T args) U) = (env1, v')"
      by (cases "genvar (fst v) env (foldr fun_type (map fl_T args) U)")
    define body where "body = list_comb v' (map (Bound \<circ> fl_j) args)"
    from rest False g obtain env2 where vu: "ok (vupdate (v, T) (types_abs Ts body) env1) env2"
      and nt: "ok (norm_term env2 (list_comb v' ts')) t'" and env': "env' = env2"
      by (auto simp: Let_def args_def ts'_def body_def)
    note gs = genvar_simps[OF g]
    have gv': "ground ar (foldr fun_type (map fl_T args) U)"
      by (rule ground_foldr_fun_type) (use Pa gU in auto)
    have wv': "wf_tm ar rb'' v'" for rb'' using gs(4) gv' by (simp add: wf_tm_def)
    have wenv1: "wf_env ar env1" by (rule genvar_wf_env[OF g assms(2)])
    have tr_body: "tr body = tr v' \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args)"
      using Pa by (simp add: body_def tr_list_comb comp_def)
    have "proper body" "typs_ok ar body"
      using wv'[of "[]"] Pa by (auto simp: wf_tm_def body_def proper_list_comb typs_ok_list_comb)
    moreover have "no_loose_bound (tr body) (length Ts)"
      using wv'[of "[]"] Pa lTs unfolding tr_body
      by (auto simp: wf_tm_def no_loose_bound_list_app intro: no_loose_bound_mono)
    ultimately have wbody: "wf_cp ar (length Ts) body" by (simp add: wf_cp_def)
    have wabs: "wf_tm ar [] (types_abs Ts body)" by (rule wf_tm_types_abs[OF gTs wbody])
    note vw = vupdate_wf[OF vu wenv1 wabs gT]
    have ext: "extends env env2" using genvar_extends[OF g] vw(2) by (rule extends_trans)
    have wl: "wf_tm ar rb' (list_comb v' ts')" using wv' wts' by (simp add: wf_tm_list_comb)
    note nw = norm_term_wf_tm[OF nt vw(1) wl]
    have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr t'))"
      if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env2" for \<sigma>
    proof -
      let ?G = "mk_subst \<sigma> (tr v')"
      have cl: "no_loose_bound ?G 0" using \<sigma>(1) gs(4) by (simp add: closed_onD)
      have "mk_subst \<sigma> (tr (types_abs Ts body)) =
          Abs_m ?n (?G \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args))"
        using lTs by (simp add: tr_types_abs mk_subst_Abs_m tr_body comp_def)
      with vw(3)[OF \<sigma>] have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          Abs_m ?n (?G \<degree>\<degree> map BVar (map (nat_of_integer \<circ> fl_j) args))" by simp
      from clean_binding_equiv[OF refl this \<sigma>(1) cl rel]
      have 1: "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr (list_comb v' ts')))"
        unfolding t by (simp add: tr_list_comb)
      have 2: "map_BVars ?f (mk_subst \<sigma> (tr (list_comb v' ts'))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars ?f (mk_subst \<sigma> (tr t'))"
        by (rule map_BVars_equiv[OF env_equivD[OF conjunct2[OF nw] \<sigma>]])
      show ?thesis by (rule equiv_trans[OF 1 2])
    qed
    with vw(1) ext nw env' show ?thesis by blast
  qed
qed



subsection \<open>Remaining pairs\<close>

text \<open>The remaining flex-flex pairs are closed terms; a substitution solves them if it makes both
  sides \<open>\<beta>\<eta>\<close>-equal.\<close>

definition tsolved :: "(nat \<Rightarrow> dB) \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "tsolved \<sigma> tps \<longleftrightarrow> (\<forall>(t, u)\<in>set tps. mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u))"

lemma tsolved_Cons: "tsolved \<sigma> ((t, u) # tps) \<longleftrightarrow>
    mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u) \<and> tsolved \<sigma> tps"
  by (simp add: tsolved_def)

lemma aconv_term_tr: "aconv_term t u \<Longrightarrow> tr t = tr u"
  by (induction t u rule: aconv_term.induct) auto

lemma add_tpair_sound:
  "tsolved \<sigma> (add_tpair rb t u tps) \<Longrightarrow> dsolved \<sigma> (rb, t, u) \<and> tsolved \<sigma> tps"
proof (cases "aconv_term t u")
  case True
  assume "tsolved \<sigma> (add_tpair rb t u tps)"
  with True show ?thesis by (simp add: add_tpair_def dsolved_dsolvedB aconv_term_tr)
next
  case False
  assume s: "tsolved \<sigma> (add_tpair rb t u tps)"
  show ?thesis
  proof (cases "\<exists>(t', u')\<in>set tps. aconv_term (rlist_abs rb t) t' \<and> aconv_term (rlist_abs rb u) u'")
    case True
    then obtain t' u' where "(t', u') \<in> set tps" "aconv_term (rlist_abs rb t) t'"
      "aconv_term (rlist_abs rb u) u'" by blast
    moreover from s False True have "tsolved \<sigma> tps" by (simp add: add_tpair_def Let_def)
    ultimately show ?thesis by (auto simp: tsolved_def dsolved_def aconv_term_tr)
  next
    case nex: False
    with s False have "tsolved \<sigma> ((rlist_abs rb t, rlist_abs rb u) # tps)"
      by (simp add: add_tpair_def Let_def)
    then show ?thesis by (simp add: tsolved_Cons dsolved_def)
  qed
qed

lemma add_index_fold:
  assumes "distinct (map fst xs)" "foldr (add_index lt lu) xs ([], []) = (bn, rb')"
  shows "set bn \<subseteq> fst ` set xs \<and> distinct bn \<and> length bn + length rb' = length xs \<and>
    set rb' \<subseteq> snd ` set xs"
  using assms
proof (induction xs arbitrary: bn rb')
  case (Cons x xs)
  obtain bn1 rb1 where f: "foldr (add_index lt lu) xs ([], []) = (bn1, rb1)"
    by (cases "foldr (add_index lt lu) xs ([], [])")
  obtain j xT where x: "x = (j, xT)" by (cases x)
  from Cons.IH[OF _ f] Cons.prems(1) have IH: "set bn1 \<subseteq> fst ` set xs" "distinct bn1"
    "length bn1 + length rb1 = length xs" "set rb1 \<subseteq> snd ` set xs" by simp_all
  from Cons.prems(1) x have "j \<notin> fst ` set xs" by auto
  moreover from Cons.prems(2) f x have "add_index lt lu (j, xT) (bn1, rb1) = (bn, rb')" by simp
  ultimately show ?case using IH x by (auto simp: add_index_def split: if_splits)
qed simp

lemma clean_binder:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  shows "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j" "bset banned \<subseteq> {..<length rb}"
    "length rb' = length rb - card (bset banned)" "set rb' \<subseteq> set rb"
proof -
  have d: "distinct (map fst (zip (upto_list (length rb)) rb))"
    by (simp add: upto_list_def distinct_map inj_on_def integer_eq_iff)
  note f = add_index_fold[OF d assms]
  have "fst ` set (zip (upto_list (length rb)) rb) \<subseteq> set (upto_list (length rb))"
    by (auto dest: set_zip_leftD)
  with f have s: "set banned \<subseteq> integer_of_nat ` {..<length rb}"
    by (auto simp: upto_list_def atLeast0LessThan)
  show db: "distinct banned" using f by simp
  show nn: "\<forall>j\<in>set banned. 0 \<le> j" using s by (auto simp: integer_reps)
  show "bset banned \<subseteq> {..<length rb}" using s by (auto simp: bset_def integer_reps)
  have "card (bset banned) = length banned"
    unfolding bset_def using nn
    by (subst card_image) (auto intro: inj_on_subset[OF nat_of_integer_inj] simp: distinct_card[OF db])
  then show "length rb' = length rb - card (bset banned)" using f by (auto simp: upto_list_def)
  have "snd ` set (zip (upto_list (length rb)) rb) \<subseteq> set rb" by (auto dest: set_zip_rightD)
  with f show "set rb' \<subseteq> set rb" by blast
qed

lemma ff_handler:
  assumes "okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
    (\<lambda>e. case e of
      ASSIGN \<Rightarrow>
        handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
    | _ \<Rightarrow> raiseW e)) r"
  shows "(\<exists>env3. okW (ff_assign alg env2 rb' t' u') env3 \<and> r = (env3, tps)) \<or>
    (\<exists>env3. okW (ff_assign alg env2 rb' u' t') env3 \<and> r = (env3, tps)) \<or>
    r = (env2, add_tpair rb' t' u' tps)"
proof -
  have h1: "okW (case e of ASSIGN \<Rightarrow> handleW m h | _ \<Rightarrow> raiseW e) y \<Longrightarrow>
      okW m y \<or> (\<exists>evs e. m = Some (evs, UErr e) \<and> okW (h e) y)" for e m h y
    by (cases e) (auto simp: okW_handleW)
  have h2: "bindW m f = Some (evs, UOk y) \<Longrightarrow> \<exists>x. okW m x \<and> okW (f x) y" for m f evs y
    using okW_bindW[of m f y] by blast
  from assms show ?thesis
    by (auto simp: okW_handleW returnW_def dest!: h1 h2 okW_ASSIGN_handler)
qed


lemma okW_CHANGE_FAIL_handler:
  "okW (case e of CHANGE_FAIL \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

text \<open>A solution of the cleaned pair solves the original pair: the renamings undo the deletion
  of the banned bound variables.\<close>

lemma dsolved_rename:
  assumes "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr t'))"
    "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr u'))" "dsolved \<sigma> (rb', t', u')"
  shows "dsolved \<sigma> (rb, t, u)"
proof -
  from assms(3) have "mk_subst \<sigma> (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u')"
    by (simp add: dsolved_dsolvedB dsolvedB_unabs)
  then have "map_BVars f (mk_subst \<sigma> (tr t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars f (mk_subst \<sigma> (tr u'))"
    by (rule map_BVars_equiv)
  from equiv_trans[OF equiv_trans[OF assms(1) this] equiv_sym[OF assms(2)]]
  show ?thesis by (simp add: dsolved_dsolvedB dsolvedB_unabs)
qed

lemma clean_ffpair_sound:
  assumes "okW (clean_ffpair alg rb t u env tps) (env', tps')" "wf_env ar env" "wf_dp ar (rb, t, u)"
  shows "wf_env ar env' \<and> extends env env' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow>
      dsolved \<sigma> (rb, t, u) \<and> tsolved \<sigma> tps)"
proof -
  obtain banned rb' where fb: "foldr (add_index (loose_bnos t) (loose_bnos u))
      (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
    by (cases "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], [])")
  note cb = clean_binder[OF fb]
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    using assms(3) by simp_all
  have bok': "binders_ok ar rb'" using bok cb(5) by (auto simp: binders_ok_def)
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
    note st = clean_term_sound[OF ct assms(2) wt cb(1-4)]
    then have wenv1: "wf_env ar env1" by blast
    note su = clean_term_sound[OF cu wenv1 wu cb(1-4)]
    have wenv2: "wf_env ar env2" and ext2: "extends env env2"
      using st su by (blast, blast intro: extends_trans)
    have wdp': "wf_dp ar (rb', t', u')" using st su bok' by simp
    have sol: "dsolved \<sigma> (rb, t, u)" if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env2" "dsolved \<sigma> (rb', t', u')" for \<sigma>
    proof (rule dsolved_rename[OF _ _ \<sigma>(3)])
      have "sat \<sigma> env1" using sat_extends[OF \<sigma>(2)] su by blast
      with st \<sigma>(1) show "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr t'))"
        by blast
      from su \<sigma>(1,2) show "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash (bset banned)) (mk_subst \<sigma> (tr u'))"
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
      note fs = ff_assign_sound[OF fa wenv2 wdp']
      have "dsolved \<sigma> (rb, t, u)" if "closed_on UNIV \<sigma>" "sat \<sigma> env3" for \<sigma>
        using sol[OF that(1) sat_extends[OF that(2) fs(2)] env_equiv_dsolved[OF fs(3) that]] .
      with fs(1,2) ext2 r show ?thesis by (auto intro: extends_trans)
    next
      case (fa2 env3)
      note fa = fa2(1) and r = fa2(2)
      have wdp'': "wf_dp ar (rb', u', t')" using wdp' by simp
      note fs = ff_assign_sound[OF fa wenv2 wdp'']
      have "dsolved \<sigma> (rb, t, u)" if "closed_on UNIV \<sigma>" "sat \<sigma> env3" for \<sigma>
        using sol[OF that(1) sat_extends[OF that(2) fs(2)] env_equiv_dsolved[OF env_equiv_sym[OF fs(3)] that]] .
      with fs(1,2) ext2 r show ?thesis by (auto intro: extends_trans)
    next
      case keep
      with wenv2 ext2 sol show ?thesis by (auto dest: add_tpair_sound)
    qed
  qed
qed


lemma dsolved_swap: "dsolved \<sigma> (rb, u, t) \<Longrightarrow> dsolved \<sigma> (rb, t, u)"
  by (simp add: dsolved_def equiv_sym)

theorem add_ffpair_sound:
  assumes "okW (add_ffpair alg dp (env, tps)) (env', tps')" "wf_env ar env" "wf_dp ar dp"
  shows "wf_env ar env' \<and> extends env env' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow> dsolved \<sigma> dp \<and> tsolved \<sigma> tps)"
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
  have bok: "binders_ok ar rb" and wt0: "wf_tm ar rb t0" and wu0: "wf_tm ar rb u0"
    using assms(3) dp by simp_all
  note tn = norm_term_wf_tm[OF nt assms(2) wt0] and un = norm_term_wf_tm[OF nu assms(2) wu0]
  have wdp: "wf_dp ar (rb, t, u)" and wdp': "wf_dp ar (rb, u, t)" using tn un bok by simp_all
  have bk: "dsolved \<sigma> (rb, t0, u0)"
    if \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env" "dsolved \<sigma> (rb, t, u)" for \<sigma>
    by (rule dsolved_env_equiv[OF env_equiv_rlist_abs env_equiv_rlist_abs \<sigma>]) (use tn un in blast)+
  from rest consider (same) "env' = env" "tps' = add_tpair rb t u tps"
    | (tu) "okW (clean_ffpair alg rb t u env tps) (env', tps')"
    | (ut) "okW (clean_ffpair alg rb u t env tps) (env', tps')"
    by (auto split: pterm.splits if_splits)
  then show ?thesis
  proof cases
    case same
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps"
      if "closed_on UNIV \<sigma>" "sat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
      using add_tpair_sound[of \<sigma> rb t u tps] bk[of \<sigma>] that same by (simp add: dp)
    with assms(2) same show ?thesis by simp
  next
    case tu
    note c = clean_ffpair_sound[OF tu assms(2) wdp]
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps"
      if "closed_on UNIV \<sigma>" "sat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
    proof -
      have "sat \<sigma> env" using sat_extends[OF that(2)] c by blast
      with c that bk[of \<sigma>] show ?thesis by (simp add: dp)
    qed
    with c show ?thesis by blast
  next
    case ut
    note c = clean_ffpair_sound[OF ut assms(2) wdp']
    have "dsolved \<sigma> dp \<and> tsolved \<sigma> tps"
      if "closed_on UNIV \<sigma>" "sat \<sigma> env'" "tsolved \<sigma> tps'" for \<sigma>
    proof -
      have "sat \<sigma> env" using sat_extends[OF that(2)] c by blast
      with c that bk[of \<sigma>] show ?thesis by (simp add: dp dsolved_swap)
    qed
    with c show ?thesis by blast
  qed
qed

theorem foldrW_add_ffpair_sound:
  "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env', tps') \<Longrightarrow> wf_env ar env \<Longrightarrow>
    \<forall>dp\<in>set ffs. wf_dp ar dp \<Longrightarrow>
    wf_env ar env' \<and> extends env env' \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow> tsolved \<sigma> tps' \<longrightarrow>
      dsolved_all \<sigma> ffs \<and> tsolved \<sigma> tps)"
proof (induction ffs arbitrary: env' tps')
  case (Cons dp ffs)
  from Cons.prems(1) obtain env1 tps1 where f: "okW (foldrW (add_ffpair alg) ffs (env, tps)) (env1, tps1)"
    and a: "okW (add_ffpair alg dp (env1, tps1)) (env', tps')" by auto
  note IH = Cons.IH[OF f Cons.prems(2)] Cons.prems(3)
  then have "wf_env ar env1" by simp
  note A = add_ffpair_sound[OF a this] Cons.prems(3)
  from IH A show ?case by (auto intro: extends_trans sat_extends)
qed simp

end

end
