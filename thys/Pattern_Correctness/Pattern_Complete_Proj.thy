section \<open>Completeness of Projection\<close>

theory Pattern_Complete_Proj
  imports Pattern_Complete_Flex
begin

context pure_sig
begin

subsection \<open>Conclusions for computations with a result and an environment\<close>

text \<open>
  Projection only adds new variables and their bindings; the type environment is unchanged. The
  type variables \<open>tv u\<close> of the result \<open>u\<close> are known.
\<close>

definition pcon :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> binders \<Rightarrow>
    (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> ('a \<Rightarrow> (indexname \<times> psort) set) \<Rightarrow>
    ('a \<times> env) M \<Rightarrow> bool" where
  "pcon \<rho> \<sigma> env e bs X A tv r \<longleftrightarrow> no_unif r \<and> (\<forall>u env'. ok r (u, env') \<longrightarrow> (\<exists>\<sigma>'. cinv \<rho> \<sigma>' env' e bs X A \<and>
    sagree (maxidx env) \<sigma> \<sigma>' \<and> maxidx env \<le> maxidx env' \<and> tyenv env' = tyenv env \<and>
    tv u \<subseteq> tvars_env (tyenv env) \<union> A))"

lemma pcon_return:
  "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> tv u \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A tv (return (u, env))"
  unfolding pcon_def by (auto intro!: exI[of _ \<sigma>])

lemma pcon_bindM:
  "no_unif m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A tv (g x)) \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A tv (m \<bind> g)"
  unfolding pcon_def by (auto intro!: no_unif_bindM)

lemma pcon_trans:
  assumes "sagree (maxidx env) \<sigma> \<sigma>1" "maxidx env \<le> maxidx env1" "tyenv env1 = tyenv env"
    "pcon \<rho> \<sigma>1 env1 e bs X A tv r"
  shows "pcon \<rho> \<sigma> env e bs X A tv r"
  unfolding pcon_def
proof (intro conjI allI impI)
  show "no_unif r" using assms(4) by (simp add: pcon_def)
  fix u env' assume "ok r (u, env')"
  then obtain \<sigma>' where c: "cinv \<rho> \<sigma>' env' e bs X A" "sagree (maxidx env1) \<sigma>1 \<sigma>'"
    "maxidx env1 \<le> maxidx env'" "tyenv env' = tyenv env1" "tv u \<subseteq> tvars_env (tyenv env1) \<union> A"
    using assms(4) unfolding pcon_def by blast
  have "sagree (maxidx env) \<sigma> \<sigma>'" by (rule sagree_trans[OF assms(1) c(2) assms(2)])
  with c assms(2,3) show "\<exists>\<sigma>'. cinv \<rho> \<sigma>' env' e bs X A \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      maxidx env \<le> maxidx env' \<and> tyenv env' = tyenv env \<and> tv u \<subseteq> tvars_env (tyenv env) \<union> A"
    by (intro exI[of _ \<sigma>']) simp
qed

lemma pcon_mono: "pcon \<rho> \<sigma> env e bs X A tv r \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> pcon \<rho> \<sigma> env e bs Y A tv r"
  unfolding pcon_def by (blast intro: cinv_mono)

lemma cinv_bs:
  "cinv \<rho> \<sigma> env e' bs' X A \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow> btvars bs \<subseteq> btvars bs' \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A"
  unfolding cinv_def by blast

lemma pcon_bs:
  "pcon \<rho> \<sigma> env e' bs' X A tv r \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow> btvars bs \<subseteq> btvars bs' \<Longrightarrow>
    pcon \<rho> \<sigma> env e bs X A tv r"
  unfolding pcon_def by (blast intro: cinv_bs)

lemma cterm_tyenv: "tyenv env' = tyenv env \<Longrightarrow> cterm \<rho> env' e bs A t T \<longleftrightarrow> cterm \<rho> env e bs A t T"
  by (simp add: cterm_def)

text \<open>
  Completeness of \<^const>\<open>pr\<close> at depth \<open>d\<close>, for a solution whose instance of the term has normal
  forms with loose bound variables \<open>\<ge> d\<close> in \<open>d + xs\<close>.
\<close>

definition pr_cp :: "integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> (pterm \<times> env) M \<Rightarrow> bool" where
  "pr_cp xs s env d bs r \<longleftrightarrow> (\<forall>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<longrightarrow> vars s \<subseteq> X \<longrightarrow>
    cterm \<rho> env e bs A s T \<longrightarrow> nf_bounds (ap \<rho> \<sigma> s) d xs \<longrightarrow> pcon \<rho> \<sigma> env e bs X A ttvars r)"

lemma pr_cpD:
  "pr_cp xs s env d bs r \<Longrightarrow> cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars s \<subseteq> X \<Longrightarrow>
    cterm \<rho> env e bs A s T \<Longrightarrow> nf_bounds (ap \<rho> \<sigma> s) d xs \<Longrightarrow> pcon \<rho> \<sigma> env e bs X A ttvars r"
  unfolding pr_cp_def by blast

lemma pr_cp_None: "pr_cp xs s env d bs None"
  by (simp add: pr_cp_def pcon_def)

lemma pcon_mapAccM:
  assumes f: "\<And>s env. s \<in> set ss \<Longrightarrow> pr_cp xs s env d bs (f s env)"
  shows "cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> \<Union> (vars ` set ss) \<subseteq> X \<Longrightarrow> \<forall>s\<in>set ss. \<exists>T. cterm \<rho> env e bs A s T \<Longrightarrow>
    \<forall>s\<in>set ss. nf_bounds (ap \<rho> \<sigma> s) d xs \<Longrightarrow>
    pcon \<rho> \<sigma> env e bs X A (\<lambda>us. \<Union> (ttvars ` set us)) (mapAccM f ss env)"
  using f
proof (induction ss arbitrary: \<sigma> env)
  case Nil
  then show ?case by (simp add: pcon_return)
next
  case (Cons s ss)
  obtain T where cs: "cterm \<rho> env e bs A s T" using Cons.prems(3) by auto
  have p1: "pcon \<rho> \<sigma> env e bs X A ttvars (f s env)"
    using pr_cpD[OF Cons.prems(5)[of s env] Cons.prems(1) _ cs] Cons.prems(2,4) by simp
  show ?case unfolding mapAccM.simps
  proof (rule pcon_bindM)
    show "no_unif (f s env)" using p1 by (simp add: pcon_def)
    fix y1 assume ok1: "ok (f s env) y1"
    obtain y env1 where y1: "y1 = (y, env1)" by force
    from p1 ok1 y1 obtain \<sigma>1 where r1: "cinv \<rho> \<sigma>1 env1 e bs X A" "sagree (maxidx env) \<sigma> \<sigma>1"
      "maxidx env \<le> maxidx env1" "tyenv env1 = tyenv env" "ttvars y \<subseteq> tvars_env (tyenv env) \<union> A"
      unfolding pcon_def by blast
    have vi: "vinv \<rho> env X" using Cons.prems(1) by (simp add: cinv_def)
    have ap1: "ap \<rho> \<sigma>1 s' = ap \<rho> \<sigma> s'" if "s' \<in> set ss" for s'
    proof -
      have sub: "vars s' \<subseteq> X" using Cons.prems(2) that by auto
      have b: "\<forall>p\<in>X \<union> evars env. snd (fst p) \<le> maxidx env" using vi by (simp add: vinv_def below_def)
      have "below (maxidx env) (vars s')" unfolding below_def using b sub by blast
      then show ?thesis by (rule ap_sagree[OF r1(2)])
    qed
    have "pcon \<rho> \<sigma>1 env1 e bs X A (\<lambda>us. \<Union> (ttvars ` set us)) (mapAccM f ss env1)"
      using Cons.IH[OF r1(1)] Cons.prems(2-5) ap1 cterm_tyenv[OF r1(4)] by simp
    then have p2: "pcon \<rho> \<sigma> env e bs X A (\<lambda>us. \<Union> (ttvars ` set us)) (mapAccM f ss env1)"
      by (rule pcon_trans[OF r1(2,3,4)])
    show "pcon \<rho> \<sigma> env e bs X A (\<lambda>us. \<Union> (ttvars ` set us))
        ((case y1 of (y, s1) \<Rightarrow> mapAccM f ss s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))))"
      using p2 r1(5) unfolding y1 pcon_def by (auto intro!: no_unif_bindM split: prod.splits)
  qed
qed


subsection \<open>Translating bound variables\<close>

lemma idx_return: "j \<in> set xs \<Longrightarrow> idx xs j = return (bidx xs j)"
  by (induction xs) auto

lemma try_trans_Some: "ok (try_trans xs d i) r \<Longrightarrow> i < d \<or> i - d \<in> set xs \<Longrightarrow> r \<noteq> None"
  by (auto simp: try_trans_def idx_return split: if_splits)

lemma no_unif_trans: "i < d \<or> i - d \<in> set xs \<Longrightarrow> no_unif (trans xs d i)"
  by (auto simp: trans_def idx_return)

lemma pcon_bind_return:
  assumes "pcon \<rho> \<sigma> env e bs X A tv m"
    "\<And>y. tv y \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> tv' (g y) \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "pcon \<rho> \<sigma> env e bs X A tv' (m \<bind> (\<lambda>(y, env'). return (g y, env')))"
  using assms unfolding pcon_def by (fastforce intro!: no_unif_bindM split: prod.splits)


subsection \<open>Flex terms\<close>

lemma pcon_pr_flex:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (Var F Fty \<degree>\<degree> ts) \<subseteq> X"
    and c: "cterm \<rho> env e bs A (Var F Fty \<degree>\<degree> ts) T" and nb: "nf_bounds (ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ts)) d xs"
    and d: "0 \<le> d"
  shows "pcon \<rho> \<sigma> env e bs X A ttvars (do {
              js \<leftarrow> ints_of' env ts;
              js' \<leftarrow> mapM (try_trans xs d) js;
              let ks = mk_proj_list js';
              let ls = List.map_filter id js';
              Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
              let (env', H) = genvar (fst F) env Hty;
              t \<leftarrow> mk_hnf bs js H ks;
              env'' \<leftarrow> update (F, Fty) t env';
              return (app H ls, env'')})"
    (is "pcon _ _ _ _ _ _ _ _ ?r")
proof -
  note i = inv[unfolded cinv_def]
  have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and bse: "bs_env \<rho> e bs"
    and vi: "vinv \<rho> env X" and tv0: "tvinv A env" using i by blast+
  have nu: "no_unif ?r"
    by (auto simp: Let_def mk_hnf_def intro!: no_unif_bindM no_unif_ints_of' xok_mapM no_unif_try_trans
        no_unif_type_of_G no_unif_mkabs no_unif_update split: prod.splits)
  have "\<exists>\<sigma>'. cinv \<rho> \<sigma>' env' e bs X A \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and> maxidx env \<le> maxidx env' \<and>
      tyenv env' = tyenv env \<and> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    if ok: "ok ?r (u, env')" for u env'
  proof -
    from ok obtain js js' Hty where js: "ok (ints_of' env ts) js"
      and js': "ok (mapM (try_trans xs d) js) js'"
      and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
      and rest: "ok (let (env1, H) = genvar (fst F) env Hty in
        mk_hnf bs js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
          (\<lambda>env2. return (app H (List.map_filter id js'), env2)))) (u, env')"
      by (auto simp: Let_def)
    obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
    let ?ks = "mk_proj_list js'"
    from rest G obtain t where t: "ok (mkabs bs js (app H ?ks)) t"
      and upd: "ok (update (F, Fty) t env1) env'" and u: "u = app H (List.map_filter id js')"
      by (auto simp: mk_hnf_def)
    note g = genvar_simps[OF G]
    let ?H = "(fst F, maxidx env + 1)"
    note cf = cterm_flex[OF c js sol wte]
    have nb2: "nf_bounds (ap \<rho> \<sigma> (app (Var F Fty) js)) d xs" by (rule nf_bounds_conv[OF cf(2) nb])
    have Xf: "vars (app (Var F Fty) js) \<subseteq> X" using X by (simp add: vars_apps)
    note fd = flex_data[OF inv cf(1)]
    have dis: "distinct js" by (rule ints_of'_distinct[OF js])
    have js0: "\<forall>j\<in>set js. 0 \<le> j" using fd(3) by auto
    let ?u = "\<sigma> F (tsubst \<rho> Fty)"
    have tyu: "e \<turnstile> ?u \<degree>\<degree> map Bound js : T" by (rule typing_apps_Bounds[OF fd(4,5) js0])
    obtain N where N: "?u \<degree>\<degree> map Bound js \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N" "normal N" using normal_form_ex[OF tyu] .
    have cN: "?u \<degree>\<degree> map Bound js \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> N" using beta_eta_conv[OF N(1)] tyu by (auto simp: wt_def)
    have lbN: "k - d \<in> set xs" if "d \<le> k" "loose_bvar1 N k" for k
      using nf_boundsD[OF nb2 N(2) _ that] cN fd(6) by simp
    let ?KS = "map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip js js'))"
    have l2: "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) js js'" using js' by (simp add: ok_mapM)
    then have len: "length js = length js'" by (rule list_all2_lengthD)
    have lb: "k \<in> set ?KS" if "0 \<le> k" "loose_bvar1 N k" for k
    proof -
      have "k \<in> set js" by (rule loose_bvar1_nf[OF fd(4) N(1) that])
      then obtain p where p: "p < length js" "js ! p = k" by (auto simp: in_set_conv_nth)
      have tt: "ok (try_trans xs d k) (js' ! p)" using list_all2_nthD[OF l2 p(1)] p(2) by simp
      have "k < d \<or> k - d \<in> set xs" using lbN[OF _ that(2)] by (cases "d \<le> k") auto
      then have "js' ! p \<noteq> None" by (rule try_trans_Some[OF tt])
      moreover have "(k, js' ! p) \<in> set (zip js js')" using p len by (auto simp: set_zip)
      ultimately show ?thesis by force
    qed
    have KSjs: "set ?KS \<subseteq> set js" by (auto dest: set_zip_leftD)
    note mp = mk_proj_list_bren[OF len]
    have ksKS: "map (bidx js) ?KS = ?ks"
    proof -
      have "map (bidx js) ?KS = map (\<lambda>k. bidx js (bren (rev js) k)) ?ks"
        using arg_cong[OF mp(2), of "map (bidx js)"] by (simp add: comp_def)
      also have "\<dots> = ?ks" using mp(1) bidx_bren[OF dis] by (auto intro!: map_idI)
      finally show ?thesis .
    qed
    have tsol: "tsol (tyenv env) \<rho>" using solutionD(2)[OF sol] .
    have tH: "tsubst \<rho> Hty = map e ?KS \<Rrightarrow> T"
      using type_of_G_sound(1)[OF Hty tsol fd(1)] map_bren_types[OF mp(2) mp(1), of e] by simp
    have tyN: "e \<turnstile> N : T" by (rule subject_reduction_reds[OF N(1) tyu])
    have cert: "\<forall>k\<in>set ?KS. cert_typ alg ar (e k)" using fd(8) KSjs by blast
    let ?w = "sabs e ?KS N"
    note w = strengthen[OF tyN lb cert]
    let ?\<sigma>' = "supd \<sigma> ?H (tsubst \<rho> Hty) ?w"
    have \<sigma>': "wt_subst ?\<sigma>'" using wt_subst_supd[OF solutionD(3)[OF sol] w(1)] w(2) tH by simp
    have sa: "sagree (maxidx env) \<sigma> ?\<sigma>'" by (rule sagree_supd) simp
    have Fold: "snd F \<le> maxidx env" using vi X unfolding vinv_def below_def by (force simp: vars_apps)
    have t': "t = abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (app (Var ?H Hty) ?ks)"
      using t by (simp add: ok_mkabs g(4))
    let ?bsJ = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) js)"
    have sol': "solution \<rho> ?\<sigma>' env'"
    proof (rule solution_extend[OF sol vi sa \<sigma>'])
      show "tyenv env' = tyenv env" using ok_update(3)[OF upd] g(2) by simp
      show "vt_lookup (tenv env') x = Some b" if "vt_lookup (tenv env) x = Some b" for x b
        using that ok_update(1,2)[OF upd] g(1) by auto
      fix x U u0 assume new: "vt_lookup (tenv env') x = Some (U, u0)" "vt_lookup (tenv env) x = None"
      then have x: "x = F" "U = Fty" "u0 = t" using ok_update(2)[OF upd] g(1) by (auto split: if_splits)
      have "F \<noteq> ?H" using Fold by (cases F) auto
      then have "?\<sigma>' F (tsubst \<rho> Fty) = ?u" by (simp add: supd_def)
      moreover have "ap \<rho> ?\<sigma>' t = abs_list ?bsJ (?w \<degree>\<degree> map Bound (map (bidx js) ?KS))"
        unfolding ksKS by (simp add: t' ap_abs_list ap_apps app_apps comp_def)
      moreover have "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bsJ (?w \<degree>\<degree> map Bound (map (bidx js) ?KS))"
        by (rule flex_proj_sem[OF fd(4,5) dis js0 fd(7,8) cN N(2) tyN KSjs lb])
      ultimately show "?\<sigma>' x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma>' u0" using x by simp
    qed
    have tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) js) : T" using cf(1) by (simp add: cterm_def)
    have tH': "tsubst \<rho> Hty = map (\<lambda>k. rev (map e js) ! nat_of_integer k) ?ks \<Rrightarrow> T"
      by (rule type_of_G_sound(1)[OF Hty tsol fd(1)]) simp
    have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF G])
    have wte': "wt_env \<rho> env'"
      using bind_sound(1)[OF t[unfolded g(4)] upd wte1 bse tyF tH' mp(1)] .
    have vi': "vinv \<rho> env' X"
    proof -
      have "vinv \<rho> env1 (vars H \<union> X)" by (rule vinv_genvar[OF G vi])
      then have "vinv \<rho> env1 (X \<union> insert (F, Fty) (vars t))"
        using Xf by (auto simp: t' g(4) app_apps vars_apps elim!: vinv_mono)
      then show ?thesis by (rule vinv_update[OF upd])
    qed
    have tvH: "tvars Hty \<subseteq> tvars_env (tyenv env) \<union> A" by (rule type_of_G_tvars[OF Hty tv0 fd(9)])
    have tv': "tvinv A env'"
    proof (rule tvinv_update[OF upd tvinv_genvar[OF G tv0]])
      note tvH
      moreover have "btvars (map (\<lambda>i. bs ! nat_of_integer i) js) \<subseteq> tvars_env (tyenv env) \<union> A"
        using btvars_nths[OF fd(3)] i by blast
      ultimately show "tvars Fty \<union> ttvars t \<subseteq> tvars_env (tyenv env1) \<union> A"
        using fd(9) g(2) by (auto simp: t' ttvars_abs_list)
    qed
    have ty': "tyenv env' = tyenv env" using ok_update(3)[OF upd] g(2) by simp
    have "cinv \<rho> ?\<sigma>' env' e bs X A" using sol' wte' vi' tv' i ty' by (simp add: cinv_def)
    moreover have "maxidx env \<le> maxidx env'" using ok_update(4)[OF upd] g(3) by simp
    moreover have "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" using tvH by (simp add: u g(4))
    ultimately show ?thesis using sa ty' by blast
  qed
  with nu show ?thesis unfolding pcon_def by blast
qed


subsection \<open>Rigid heads\<close>

lemma pcon_pr_rigid:
  assumes f: "\<And>s env. s \<in> set ts \<Longrightarrow> pr_cp xs s env d bs (f s env)"
    and inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (h \<degree>\<degree> ts) \<subseteq> X"
    and c: "cterm \<rho> env e bs A (h \<degree>\<degree> ts) T" and nb: "nf_bounds (ap \<rho> \<sigma> (h \<degree>\<degree> ts)) d xs"
    and d: "0 \<le> d" and rh: "rigid h"
  shows "pcon \<rho> \<sigma> env e bs X A ttvars (do {
      h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
      (ts', env') \<leftarrow> mapAccM f ts env;
      return (list_comb h' ts', env')})"
proof -
  note i = inv[unfolded cinv_def]
  have \<sigma>: "wt_subst \<sigma>" using i solutionD(3) by blast
  have ty0: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ts) : T" using c by (simp add: cterm_def)
  then have ty: "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: inst_apps)
  then obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
    by (rule list_app_typeE)
  have apeq: "ap \<rho> \<sigma> (h \<degree>\<degree> ts) = inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) ts"
    using rh by (simp add: ap_apps rigid_ap)
  have tya: "e \<turnstile> inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) ts : T" using typing_ap[OF ty0 \<sigma>] apeq by simp
  note na = nf_bounds_apps[OF tya rigid_inst[OF rh] nb[unfolded apeq] d]
  have nbs: "\<forall>s\<in>set ts. nf_bounds (ap \<rho> \<sigma> s) d xs" using na(1) by simp
  have nuh: "no_unif (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h)"
  proof (cases h)
    case (Bound i)
    have "i < d \<or> i - d \<in> set xs" using na(2)[of i] Bound by (cases "d \<le> i") auto
    then show ?thesis using Bound by (auto intro!: no_unif_bindM no_unif_trans)
  qed simp_all
  have cts: "\<forall>s\<in>set ts. \<exists>U. cterm \<rho> env e bs A s U"
  proof
    fix s assume s: "s \<in> set ts"
    then obtain k where k: "k < length ts" "s = ts ! k" by (auto simp: in_set_conv_nth)
    have "e \<turnstile> inst \<rho> s : Us ! k" using typings_nth[OF tts] k by auto
    then show "\<exists>U. cterm \<rho> env e bs A s U"
      using c s by (auto simp: cterm_def loose_bvar_apps ttvars_apps)
  qed
  have Xs: "\<Union> (vars ` set ts) \<subseteq> X" using X by (auto simp: vars_apps)
  have pm: "pcon \<rho> \<sigma> env e bs X A (\<lambda>us. \<Union> (ttvars ` set us)) (mapAccM f ts env)"
    by (rule pcon_mapAccM[OF f inv Xs cts nbs])
  show ?thesis
  proof (rule pcon_bindM[OF nuh])
    fix h' assume h': "ok (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h) h'"
    have "ttvars h' \<subseteq> tvars_env (tyenv env) \<union> A"
      using h' c by (cases h) (auto simp: cterm_def ttvars_apps)
    then show "pcon \<rho> \<sigma> env e bs X A ttvars (mapAccM f ts env \<bind> (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
      by (intro pcon_bind_return[OF pm]) (auto simp: list_comb_apps ttvars_apps)
  qed
qed


subsection \<open>Completeness of \<^const>\<open>pr\<close>\<close>

lemma pr_complete:
  assumes "pr xs s env d bs = Some r"
  shows "0 \<le> d \<Longrightarrow> pr_cp xs s env d bs (Some r)"
  using assms
proof (induction xs s env d bs r rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  note d = "1.prems"(1)
  have IH: "pr_cp xs1 s1 env1 d1 bs1 (prr xs1 s1 env1 d1 bs1)" if "0 \<le> d1" for xs1 s1 env1 d1 bs1
  proof (cases "prr xs1 s1 env1 d1 bs1")
    case None
    then show ?thesis by (simp add: pr_cp_None)
  next
    case (Some r1)
    then show ?thesis using "1.IH"[OF Some that] by simp
  qed
  have body: "head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs) = Some r"
    using "1.hyps" unfolding pr_step_def by simp
  show ?case
    unfolding pr_cp_def
  proof (intro allI impI)
    fix \<rho> \<sigma> e X A T
    assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars s \<subseteq> X" and cs: "cterm \<rho> env e bs A s T"
      and nb: "nf_bounds (ap \<rho> \<sigma> s) d xs"
    note i = inv[unfolded cinv_def]
    have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and bse: "bs_env \<rho> e bs"
      and tv0: "tvinv A env" using i by blast+
    let ?X = "X \<union> evars env"
    have inv': "cinv \<rho> \<sigma> env e bs ?X A"
    proof -
      have "vinv \<rho> env (X \<union> evars env)" using vinv_hn[of \<rho> env X "{}" "evars env"] i by simp
      moreover have "vtvars (evars env) \<subseteq> tvars_env (tyenv env) \<union> A" using vtvars_evars i by blast
      ultimately show ?thesis using i unfolding cinv_def by auto
    qed
    have "pcon \<rho> \<sigma> env e bs ?X A ttvars (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs))"
    proof (rule pcon_bindM[OF no_unif_head_norm'])
      fix s' assume hn: "ok (head_norm env s) s'"
      note h = cterm_head_norm[OF cs hn sol wte tv0]
      have Xs': "vars s' \<subseteq> ?X" using head_norm_vars[OF hn refl] X by blast
      have nb': "nf_bounds (ap \<rho> \<sigma> s') d xs" by (rule nf_bounds_conv[OF h(2) nb])
      show "pcon \<rho> \<sigma> env e bs ?X A ttvars (pr_step prr xs s' env d bs)"
      proof (cases "is_Abs s'")
        case True
        then obtain a T0 t where s': "s' = Abs a T0 t" by (cases s') auto
        have st: "pr_step prr xs s' env d bs =
            prr xs t env (d + 1) ((a, T0) # bs) \<bind> (\<lambda>(t', env'). return (Abs a T0 t', env'))"
          by (simp add: pr_step_def s')
        have tyA: "e \<turnstile> inst \<rho> (Abs a T0 t) : T" using h(1) s' by (simp add: cterm_def)
        then obtain U where c: "cert_typ alg ar (tsubst \<rho> T0)"
          and tt: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> t : U"
          by auto
        have tvT: "tvars T0 \<subseteq> tvars_env (tyenv env) \<union> A" using h(1) s' by (auto simp: cterm_def)
        have inv1: "cinv \<rho> \<sigma> env (e\<langle>0:tsubst \<rho> T0\<rangle>) ((a, T0) # bs) ?X A" by (rule cinv_Cons[OF inv' c tvT])
        have ct: "cterm \<rho> env (e\<langle>0:tsubst \<rho> T0\<rangle>) ((a, T0) # bs) A t U"
          using h(1) s' tt by (auto simp: cterm_def algebra_simps)
        have "e \<turnstile> Abs a (tsubst \<rho> T0) (ap \<rho> \<sigma> t) : T"
          using typing_ap[OF tyA solutionD(3)[OF sol]] by simp
        then have nbt: "nf_bounds (ap \<rho> \<sigma> t) (d + 1) xs"
          using nf_bounds_Abs[OF _ _ d] nb' s' by simp
        have "pcon \<rho> \<sigma> env (e\<langle>0:tsubst \<rho> T0\<rangle>) ((a, T0) # bs) ?X A ttvars (prr xs t env (d + 1) ((a, T0) # bs))"
          by (rule pr_cpD[OF IH inv1 _ ct nbt]) (use Xs' s' d in simp_all)
        then have "pcon \<rho> \<sigma> env e bs ?X A ttvars (prr xs t env (d + 1) ((a, T0) # bs))"
          by (rule pcon_bs[OF _ bse]) (auto simp: btvars_def)
        then show ?thesis unfolding st by (rule pcon_bind_return) (use tvT in simp)
      next
        case nAbs: False
        obtain h0 ts where hts: "strip_comb s' = (h0, ts)" by force
        have s'': "s' = h0 \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
        show ?thesis
        proof (cases "is_Var h0")
          case True
          then obtain F Fty where hF: "h0 = Var F Fty" by (cases h0) auto
          have "pcon \<rho> \<sigma> env e bs ?X A ttvars (do {
              js \<leftarrow> ints_of' env ts;
              js' \<leftarrow> mapM (try_trans xs d) js;
              let ks = mk_proj_list js';
              let ls = List.map_filter id js';
              Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
              let (env', H) = genvar (fst F) env Hty;
              t \<leftarrow> mk_hnf bs js H ks;
              env'' \<leftarrow> update (F, Fty) t env';
              return (app H ls, env'')})"
            by (rule pcon_pr_flex[OF inv' _ _ _ d]) (use Xs' h(1) nb' s'' hF in simp_all)
          then show ?thesis using nAbs hts hF by (simp add: pr_step_def)
        next
          case nVar: False
          show ?thesis
          proof (cases "is_Abs h0")
            case True
            then show ?thesis using nAbs nVar hts by (simp add: pr_step_def pcon_def)
          next
            case nAbsh: False
            have rh: "rigid h0"
              using nVar nAbsh strip_comb_head[OF hts] by (cases h0) auto
            have "pcon \<rho> \<sigma> env e bs ?X A ttvars (do {
                h' \<leftarrow> (case h0 of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h0);
                (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d bs) ts env;
                return (list_comb h' ts', env')})"
              by (rule pcon_pr_rigid[OF IH[OF d] inv' _ _ _ d rh]) (use Xs' h(1) nb' s'' in simp_all)
            then show ?thesis using nAbs nVar nAbsh hts by (simp add: pr_step_def)
          qed
        qed
      qed
    qed
    then have "pcon \<rho> \<sigma> env e bs X A ttvars (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs))"
      by (rule pcon_mono) simp
    then show "pcon \<rho> \<sigma> env e bs X A ttvars (Some r)" by (simp only: body)
  qed
qed

subsection \<open>Flex-rigid problems\<close>

lemma no_unif_rigid_occurs: "rigid_occurs F t env = Some r \<Longrightarrow> no_unif (Some r)"
proof (induction F t env r rule: rigid_occurs.raw_induct[rotated, consumes 1])
  case (1 ro F t env r)
  have IH: "no_unif (ro F' t' env')" for F' t' env' by (rule xok_IH) (rule 1(1))
  have hd: "no_unif (handle (do {_ \<leftarrow> ints_of' env ts; return True})
      (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))" for ts
  proof (rule no_unif_handle)
    fix e assume "do {_ \<leftarrow> ints_of' env ts; return True} = Some (Err e)"
    moreover have "no_unif (do {_ \<leftarrow> ints_of' env ts; return True})"
      by (intro no_unif_bindM no_unif_ints_of') simp
    ultimately have "\<forall>tr. e \<noteq> Unif tr" by (simp add: xok_def)
    then show "no_unif (case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)" by (cases e) auto
  qed
  have "no_unif (do {
      t' \<leftarrow> head_norm env t;
      (case t' of
        Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              Var G _ \<Rightarrow>
                if G = F then
                  handle (do {_ \<leftarrow> ints_of' env ts; return True})
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts)))
    })"
    by (auto simp: Let_def split: pterm.splits prod.splits
        intro!: no_unif_bindM no_unif_head_norm' xok_existsM IH hd)
  then show ?case using 1(2) by simp
qed

lemma no_unif_rigid_occurs': "no_unif (rigid_occurs F t env)"
  by (rule xok_IH) (rule no_unif_rigid_occurs)

lemma proj_cp:
  assumes inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars t \<subseteq> X" and c: "cterm \<rho> env e bs A t T"
    and nb: "nf_bounds (ap \<rho> \<sigma> t) 0 is"
  shows "pcon \<rho> \<sigma> env e bs X A ttvars (proj t env bs is)"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  then show ?thesis using pcon_return[OF inv, of ttvars t] c by (simp add: proj_def cterm_def)
next
  case False
  then have "proj t env bs is = pr is t env 0 bs" by (simp add: proj_def)
  moreover have "pcon \<rho> \<sigma> env e bs X A ttvars (pr is t env 0 bs)"
  proof (cases "pr is t env 0 bs")
    case None
    then show ?thesis by (simp add: pcon_def)
  next
    case (Some r)
    from pr_cpD[OF pr_complete[OF Some order_refl] inv X c nb] Some show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

lemma step_cp_flexrigid:
  assumes dis: "distinct is"
    and occ: "\<And>\<rho> \<sigma> e X A T. cinv \<rho> \<sigma> env e bs X A \<Longrightarrow> vars (app (Var F Fty) is) \<union> vars t \<subseteq> X \<Longrightarrow>
      cterm \<rho> env e bs A (app (Var F Fty) is) T \<Longrightarrow> cterm \<rho> env e bs A t T \<Longrightarrow>
      ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t \<Longrightarrow> \<not> ok (rigid_occurs F t env) True"
  shows "step_cp env bs (app (Var F Fty) is) t (flexrigid env bs F Fty is t)"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume inv: "cinv \<rho> \<sigma> env e bs X A" and X: "vars (app (Var F Fty) is) \<union> vars t \<subseteq> X"
    and cs: "cterm \<rho> env e bs A (app (Var F Fty) is) T" and ct: "cterm \<rho> env e bs A t T"
    and eq: "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  note i = inv[unfolded cinv_def]
  have sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and bse: "bs_env \<rho> e bs"
    and vi: "vinv \<rho> env X" and tv0: "tvinv A env" using i by blast+
  note no_ro = occ[OF inv X cs ct eq]
  note fd = flex_data[OF inv cs]
  have is0: "\<forall>i\<in>set is. 0 \<le> i" using fd(3) by auto
  let ?u = "\<sigma> F (tsubst \<rho> Fty)"
  have tyu: "e \<turnstile> ?u \<degree>\<degree> map Bound is : T" by (rule typing_apps_Bounds[OF fd(4,5) is0])
  have eq': "?u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" using eq fd(6) by simp
  have nb: "nf_bounds (ap \<rho> \<sigma> t) 0 is" by (rule nf_bounds_flex[OF fd(4) tyu eq'])
  have Xt: "vars t \<subseteq> X" using X by blast
  note pj = proj_cp[OF inv Xt ct nb]
  let ?P = "do {(u, env1) \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env1}"
  let ?H = "\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e"
  have nuP: "no_unif ?P"
    using pj unfolding pcon_def by (auto intro!: no_unif_bindM no_unif_mkabs no_unif_update split: prod.splits)
  have nuH: "no_unif (handle ?P ?H)"
  proof (rule no_unif_handle)
    fix ex assume "?P = Some (Err ex)"
    with nuP have "\<forall>tr. ex \<noteq> Unif tr" by (simp add: xok_def)
    then show "no_unif (?H ex)" by (cases ex) auto
  qed
  have nu: "no_unif (flexrigid env bs F Fty is t)"
    unfolding flexrigid_def
  proof (intro no_unif_bindM[OF no_unif_occurs'])
    fix b assume "ok (occurs F t env) b"
    show "no_unif (if b then rigid_occurs F t env \<bind> (\<lambda>b'. if b' then raise (Unif (Ocheck_Fail F t bs env))
        else raise Pattern) else handle ?P ?H)"
    proof (cases b)
      case True
      have "no_unif (rigid_occurs F t env \<bind> (\<lambda>b'. if b' then raise (Unif (Ocheck_Fail F t bs env))
          else raise Pattern))"
      proof (rule no_unif_bindM[OF no_unif_rigid_occurs'])
        fix b' assume "ok (rigid_occurs F t env) b'"
        with no_ro have "\<not> b'" by auto
        then show "no_unif (if b' then raise (Unif (Ocheck_Fail F t bs env)) else raise Pattern)" by simp
      qed
      with True show ?thesis by simp
    qed (use nuH in simp)
  qed
  have "\<exists>\<rho>' \<sigma>'. cinv \<rho>' \<sigma>' env' e bs X A \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and> maxidx env \<le> maxidx env'"
    if fr: "ok (flexrigid env bs F Fty is t) env'" for env'
  proof -
    have nh: False if "ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e) y" for e y
      using that by (cases e) auto
    have "ok ?P env'"
      using fr by (auto simp: flexrigid_def ok_handle split: if_splits dest: nh)
    then obtain u env1 u' where pj1: "ok (proj t env bs is) (u, env1)" and mk: "ok (mkabs bs is u) u'"
      and upd: "ok (update (F, Fty) u' env1) env'"
      by (auto split: prod.splits)
    from pj pj1 obtain \<sigma>1 where r1: "cinv \<rho> \<sigma>1 env1 e bs X A" "sagree (maxidx env) \<sigma> \<sigma>1"
      "maxidx env \<le> maxidx env1" "tyenv env1 = tyenv env" "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
      unfolding pcon_def by blast
    note i1 = r1(1)[unfolded cinv_def]
    have sol1: "solution \<rho> \<sigma>1 env1" and \<sigma>1: "wt_subst \<sigma>1" and vi1: "vinv \<rho> env1 X"
      and tv1: "tvinv A env1" using i1 solutionD(3) by blast+
    have u': "u' = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) u" using mk by (simp add: ok_mkabs)
    have tyt: "e \<turnstile> inst \<rho> t : T" and lbt: "\<not> loose_bvar t (ilength bs)" using ct by (simp_all add: cterm_def)
    have XX: "X \<union> vars t = X" using Xt by blast
    note ps = proj_sound(3)[OF pj1 is0 sol1 extends_refl wte bse tyt _ lbt, of X, unfolded XX, OF vi]
    let ?U = "ap \<rho> \<sigma>1 u"
    let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
    have tyU: "pushes e (map e is) \<turnstile> ?U : T" using ps typing_ap[OF _ \<sigma>1] by blast
    obtain N0 where N0: "?U \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* N0" "normal N0" using normal_form_ex[OF tyU] .
    have lbU: "\<not> loose_bvar ?U (ilength is)"
      using ps closed_substD[of \<sigma>1] \<sigma>1 by (simp add: ap_def wt_subst_def)
    have lbN0: "\<not> loose_bvar N0 (ilength is)" using lbU loose_bvar_reds[OF N0(1)] by auto
    have nx: "nonneg (bren (rev is))" using is0 by (simp add: nonneg_bren)
    let ?NN = "rename (bren (rev is)) 0 N0"
    have nNN: "normal ?NN" using N0(2) nx by (simp add: normal_rename)
    have apt: "ap \<rho> \<sigma>1 t = ap \<rho> \<sigma> t"
      using ap_sagree[OF r1(2)] vi Xt unfolding vinv_def below_def by blast
    have wtt: "wt (ap \<rho> \<sigma>1 t)" using typing_ap[OF tyt \<sigma>1] by (auto simp: wt_def)
    have c1: "ap \<rho> \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 ?U" using ps by blast
    have "wt (rename (bren (rev is)) 0 ?U)" using c1 wtt wt_conv by blast
    then have c2: "rename (bren (rev is)) 0 ?U \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?NN"
      using reds_rename[OF N0(1) nx, of 0] by (intro beta_eta_conv) simp_all
    have c3: "?u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?NN" using eq' apt c1 c2 by (metis conv_trans)
    have bF: "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (rename (bidx is) 0 ?NN)"
      by (rule body_rename[OF fd(4,5) dis is0 fd(7,8) c3 nNN])
    have "rename (bidx is) 0 ?NN = rename (\<lambda>k. k) 0 N0"
      unfolding rename_comp[OF nx]
    proof (rule rename_cong)
      fix k assume "0 \<le> k" "loose_bvar1 N0 (k + 0)"
      then show "bidx is (bren (rev is) k) = k"
        using loose_bvar1_less[OF lbN0] bidx_bren[OF dis] by simp
    qed
    then have rN: "rename (bidx is) 0 ?NN = N0" by (simp add: rename_id)
    have tyU': "pushes e (map snd ?bs) \<turnstile> ?U : T" using tyU by (simp only: fd(7))
    then have "e \<turnstile> abs_list ?bs ?U : map snd ?bs \<Rrightarrow> T" using bs_cert[OF fd(7,8)] by (rule typing_abs_list)
    then have "abs_list ?bs ?U \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs N0"
      by (intro beta_eta_conv reds_abs_list N0(1)) (auto simp: wt_def)
    with bF rN have bind: "?u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>1 u'"
      by (auto simp: u' ap_abs_list intro: conv_sym conv_trans)
    have Fold: "snd F \<le> maxidx env" using vi X unfolding vinv_def below_def by (force simp: vars_apps)
    have sol': "solution \<rho> \<sigma>1 env'"
    proof (rule solution_extend[OF sol1 vi1 sagree_refl \<sigma>1])
      show "tyenv env' = tyenv env1" using ok_update(3)[OF upd] .
      show "vt_lookup (tenv env') x = Some b" if "vt_lookup (tenv env1) x = Some b" for x b
        using that ok_update(1,2)[OF upd] by auto
      fix x U u0 assume new: "vt_lookup (tenv env') x = Some (U, u0)" "vt_lookup (tenv env1) x = None"
      then have x: "x = F" "U = Fty" "u0 = u'" using ok_update(2)[OF upd] by (auto split: if_splits)
      have "\<sigma>1 F (tsubst \<rho> Fty) = ?u" using r1(2) Fold by (cases F) (simp add: sagree_def)
      with bind x show "\<sigma>1 x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>1 u0" by simp
    qed
    have tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" using cs by (simp add: cterm_def)
    have lbF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)" using cs by (simp add: cterm_def)
    have XX2: "X \<union> vars (app (Var F Fty) is) \<union> vars t = X" using X by blast
    have wv: "wt_env \<rho> env' \<and> vinv \<rho> env' X"
      using step_okD(3)[OF flexrigid_step[OF fr] sol' extends_refl wte bse tyF tyt _ lbF lbt, of X]
        vi XX2 by simp
    have tv': "tvinv A env'"
    proof (rule tvinv_update[OF upd tv1])
      have "btvars (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> tvars_env (tyenv env) \<union> A"
        using btvars_nths[OF fd(3)] i by blast
      then show "tvars Fty \<union> ttvars u' \<subseteq> tvars_env (tyenv env1) \<union> A"
        using fd(9) r1(4,5) by (auto simp: u' ttvars_abs_list)
    qed
    have ty': "tyenv env' = tyenv env" using ok_update(3)[OF upd] r1(4) by simp
    have "cinv \<rho> \<sigma>1 env' e bs X A" using sol' wv tv' i ty' by (simp add: cinv_def)
    moreover have "maxidx env \<le> maxidx env'" using ok_update(4)[OF upd] r1(3) by simp
    ultimately show ?thesis using r1(2) ty' by (intro exI[of _ \<rho>] exI[of _ \<sigma>1]) simp
  qed
  with nu show "ccon \<rho> \<sigma> env e bs X A (flexrigid env bs F Fty is t)" unfolding ccon_def by blast
qed

end

end
