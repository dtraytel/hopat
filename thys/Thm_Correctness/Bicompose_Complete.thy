section \<open>Completeness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Complete
  imports Bicompose_Fin "Unify_Correctness.Unify_Results2"
begin

text \<open>
  \<open>bicompose_aux\<close> misses no unifier: for every problem it unifies and every unifier in the
  enumeration of the unifiers of the problem, the finite list of results contains the new theorem
  built for it, unless instantiations of the proof state are forbidden (\<open>match\<close>). With the
  completeness of unification (@{thm [source] pure_sig.unifiers_most_general}), every solution of
  a problem of a call within the bounds of the configuration is an instance of the environment of
  one of the results.
\<close>


subsection \<open>The unifiers to come\<close>

lemma okT_det: "okT m x \<Longrightarrow> okT m y \<Longrightarrow> x = y"
  by auto

lemma evals_pull_Some:
  assumes "evals cfg s xs" "pull cfg s = Some (evs, Ok (Some (x, s')))"
  shows "\<exists>xs'. xs = x # xs' \<and> evals cfg s' xs'"
  using assms(1)
proof cases
  case (Nil evs')
  with assms(2) show ?thesis by simp
next
  case (Cons evs' y s'' xs')
  with assms(2) show ?thesis by auto
qed

lemma evals_pull_None: "evals cfg s xs \<Longrightarrow> pull cfg s = Some (evs, Ok None) \<Longrightarrow> xs = []"
  by (erule evals.cases) auto

text \<open>The unifiers in the enumeration of a sequence:\<close>

definition uels :: "cfg \<Rightarrow> seq \<Rightarrow> (env \<times> (pterm \<times> pterm) list) set" where
  "uels cfg us = {(env', tps). \<exists>xs. evals cfg us xs \<and> El_R env' tps \<in> set xs}"

definition uqel :: "cfg \<Rightarrow> seq uq \<Rightarrow> (env \<times> (pterm \<times> pterm) list) set" where
  "uqel cfg xq = (case xq of UQ_Cell (et, us) \<Rightarrow> insert et (uels cfg us) | UQ_Seq us \<Rightarrow> uels cfg us)"

lemma upull_okT:
  assumes "okT (upull cfg us) rr"
  shows "(rr = None \<and> (\<exists>evs. pull cfg us = Some (evs, Ok None))) \<or>
    (\<exists>env' tps us' evs. rr = Some ((env', tps), us') \<and> pull cfg us = Some (evs, Ok (Some (El_R env' tps, us'))))"
  using assms by (auto simp: upull_def bindW_def liftWT_def returnW_def raiseW_def
      split: option.splits xres.splits elem.splits)

lemma upull_uels_None: "okT (upull cfg us) None \<Longrightarrow> uels cfg us = {}"
  by (auto simp: uels_def dest!: upull_okT dest: evals_pull_None)

lemma upull_uels_Some:
  assumes "okT (upull cfg us) (Some ((env', tps), us'))"
  shows "uels cfg us \<subseteq> insert (env', tps) (uels cfg us')"
proof
  from upull_okT[OF assms] obtain evs where p: "pull cfg us = Some (evs, Ok (Some (El_R env' tps, us')))"
    by blast
  fix et assume "et \<in> uels cfg us"
  then obtain e t xs where et: "et = (e, t)" and es: "evals cfg us xs" and el: "El_R e t \<in> set xs"
    by (auto simp: uels_def)
  from evals_pull_Some[OF es p] obtain xs' where "xs = El_R env' tps # xs'" "evals cfg us' xs'"
    by blast
  with et el show "et \<in> insert (env', tps) (uels cfg us')" by (auto simp: uels_def)
qed

context pure_sig
begin

text \<open>
  The new theorems for the unifiers of a problem \<open>tus\<close>; the new premises are computed with the
  flex-flex pairs of the first unifier.
\<close>

definition upend :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bctx \<Rightarrow> pterm option \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bres set" where
  "upend cfg vl ctx A As0 n dps env tus = {r. \<exists>s0 env1 tps1 xs na env' tps.
    unifiers alg env tus = Some (Ok s0) \<and> evals cfg s0 (El_R env1 tps1 # xs) \<and>
    El_R env' tps \<in> set (El_R env1 tps1 # xs) \<and> okT (newAs vl ctx As0 n dps tps1) na \<and>
    okT (addth ctx A na (env', tps)) r}"

lemma upend_step:
  assumes "unifiers alg env tus = Some (Ok us)" "okT (upull cfg us) rr"
    "r \<in> upend cfg vl ctx A As0 n dps env tus"
  shows "\<exists>env1 tps1 us' na. rr = Some ((env1, tps1), us') \<and> okT (newAs vl ctx As0 n dps tps1) na \<and>
    (\<exists>et\<in>insert (env1, tps1) (uels cfg us'). okT (addth ctx A na et) r)"
proof -
  from assms(3) obtain s0 env1 tps1 xs na env' tps where u0: "unifiers alg env tus = Some (Ok s0)"
    and es: "evals cfg s0 (El_R env1 tps1 # xs)" and el: "El_R env' tps \<in> set (El_R env1 tps1 # xs)"
    and na: "okT (newAs vl ctx As0 n dps tps1) na" and r: "okT (addth ctx A na (env', tps)) r"
    unfolding upend_def mem_Collect_eq by blast
  from u0 assms(1) have "s0 = us" by simp
  note es = es[unfolded this]
  from upull_okT[OF assms(2)] show ?thesis
  proof (elim disjE exE conjE)
    fix evs assume "pull cfg us = Some (evs, Ok None)"
    from evals_pull_None[OF es this] show ?thesis by simp
  next
    fix env1' tps1' us' evs assume rr: "rr = Some ((env1', tps1'), us')"
      and p: "pull cfg us = Some (evs, Ok (Some (El_R env1' tps1', us')))"
    from evals_pull_Some[OF es p] have e: "env1' = env1" "tps1' = tps1" and es': "evals cfg us' xs" by auto
    have "(env', tps) \<in> insert (env1, tps1) (uels cfg us')"
      using el es' by (auto simp: uels_def)
    with rr e na r show ?thesis by blast
  qed
qed

fun tpends :: "bspec \<Rightarrow> bctx \<Rightarrow> eres_data \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> bres set" where
  "tpends sp ctx er [] n = {}"
| "tpends sp ctx er (asm # rest) n =
    (if could_unify asm (er_concl er) then
      upend (sp_cfg sp) (sp_vl sp) ctx (Some (er_A1 er)) (er_As er) n
        [bc_BBi ctx, (er_concl' er, rlist_abs (er_params er) asm)] (er_env er)
        ((rlist_abs (er_params er) asm, er_concl' er) # bc_dpairs ctx)
     else {}) \<union> tpends sp ctx er rest (n + 1)"

text \<open>The results that pulling a sequence of results will yield.\<close>

fun pend :: "bspec \<Rightarrow> seq bseq \<Rightarrow> bres set" where
  "pend sp BS_Empty = {}"
| "pend sp (BS_Its ctx A na xq yq) = {r. \<exists>et\<in>uqel (sp_cfg sp) xq. okT (addth ctx A na et) r} \<union> pend sp yq"
| "pend sp (BS_Tryasms ctx er asms n) = tpends sp ctx er asms n"

lemma tryasms_pend:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg"
  shows "ops = unify_ops (sp_cfg sp) (sp_vl sp) \<Longrightarrow> okT (tryasms ops ctx er asms n) s \<Longrightarrow>
    tpends sp ctx er asms n \<subseteq> pend sp s"
proof (induction ops ctx er asms n arbitrary: s rule: tryasms.induct)
  case (1 ops ctx er n)
  then show ?case by simp
next
  case (2 ops ctx er asm rest n)
  note ops = "2.prems"(1)
  show ?case
  proof (cases "could_unify asm (er_concl er)")
    case False
    with "2.prems"(2) have "okT (tryasms ops ctx er rest (n + 1)) s" by simp
    from "2.IH"(2)[OF False ops this] False show ?thesis by simp
  next
    case True
    let ?asm' = "rlist_abs (er_params er) asm"
    let ?tus = "(?asm', er_concl' er) # bc_dpairs ctx"
    let ?U = "upend (sp_cfg sp) (sp_vl sp) ctx (Some (er_A1 er)) (er_As er) n
      [bc_BBi ctx, (er_concl' er, ?asm')] (er_env er) ?tus"
    from "2.prems"(2) True obtain us rr where us: "okT (bo_unifiers ops (er_env er) ?tus) us"
      and rr: "okT (bo_pull ops us) rr"
      and s: "okT (case rr of None \<Rightarrow> tryasms ops ctx er rest (n + 1)
        | Some ((env, tpairs), us') \<Rightarrow> do {
            na \<leftarrow> newAs (bo_variants ops) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tpairs;
            returnW (BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env, tpairs), us'))
              (BS_Tryasms ctx er rest (n + 1)))}) s"
      by (simp add: Let_def) blast
    have un: "unifiers alg (er_env er) ?tus = Some (Ok us)" using us ops cfg by (simp add: unify_ops_def)
    have rr': "okT (upull (sp_cfg sp) us) rr" using rr ops by (simp add: unify_ops_def)
    show ?thesis
    proof (cases rr)
      case None
      have rrN: "okT (bo_pull ops us) None" using rr None by simp
      from s None have s': "okT (tryasms ops ctx er rest (n + 1)) s" by simp
      have "?U = {}" using upend_step[OF un rr'] None by blast
      with "2.IH"(1)[OF True refl us rrN refl ops s'] True show ?thesis by simp
    next
      case (Some c)
      then obtain env1 tps1 us' where c: "rr = Some ((env1, tps1), us')" by (cases c) auto
      from s c ops obtain na where
        na: "okT (newAs (sp_vl sp) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tps1) na"
        and s': "s = BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env1, tps1), us')) (BS_Tryasms ctx er rest (n + 1))"
        by (auto simp: unify_ops_def)
      have "?U \<subseteq> {r. \<exists>et\<in>insert (env1, tps1) (uels (sp_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na et) r}"
      proof
        fix r assume "r \<in> ?U"
        from upend_step[OF un rr' this] c obtain na' where
          "okT (newAs (sp_vl sp) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tps1) na'"
          and "\<exists>et\<in>insert (env1, tps1) (uels (sp_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na' et) r"
          by blast
        with na show "r \<in> {r. \<exists>et\<in>insert (env1, tps1) (uels (sp_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na et) r}"
          by auto
      qed
      then show ?thesis using True s' by (auto simp: uqel_def)
    qed
  qed
qed


text \<open>Pulling a sequence of results yields one of the results to come, and the rest of them.\<close>

lemma bpull_pend:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ops: "ops = unify_ops (sp_cfg sp) (sp_vl sp)"
  shows "binv sp s \<Longrightarrow> okT (bpull ops s) x \<Longrightarrow>
    (case x of None \<Rightarrow> pend sp s = {} | Some (r, s') \<Rightarrow> pend sp s \<subseteq> insert r (pend sp s'))"
proof (induction "bmu sp s" arbitrary: s x rule: less_induct)
  case less
  show ?case
  proof (cases s)
    case BS_Empty
    then show ?thesis by (cases x) auto
  next
    case (BS_Its ctx A na xq yq)
    from less.prems(1)[unfolded BS_Its] obtain tus where ctx: "ctx = sp_ctx sp" and its: "itsok sp A na tus"
      and uq: "uqinv sp tus xq" and byq: "binv sp yq"
      by (auto elim: binv_ItsE)
    have pw: "pwf (sp_env sp) tus" by (rule itsok_pwf[OF its pa])
    have bp: "bpull ops s = do {
        r \<leftarrow> (case xq of UQ_Cell c \<Rightarrow> returnW (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us);
        case r of
          None \<Rightarrow> bpull ops yq
        | Some (et, us') \<Rightarrow>
            handleW
              (do {th \<leftarrow> addth ctx A na et; returnW (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseW e)}"
      unfolding BS_Its by (subst bpull.simps) simp
    from less.prems(2)[unfolded bp okW_bindW] obtain rr where
      rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnW (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and x: "okT (case rr of None \<Rightarrow> bpull ops yq | Some (et, us') \<Rightarrow> handleW
        (do {th \<leftarrow> addth ctx A na et; returnW (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
        (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseW e)) x"
      by blast
    text \<open>The next unifier, if any.\<close>
    have q: "(rr = None \<longrightarrow> uqel (sp_cfg sp) xq = {} \<and> bmu sp yq < bmu sp s) \<and>
      (\<forall>env' tps us'. rr = Some ((env', tps), us') \<longrightarrow>
        uqel (sp_cfg sp) xq \<subseteq> insert (env', tps) (uels (sp_cfg sp) us') \<and>
        binv sp (BS_Its ctx A na (UQ_Seq us') yq) \<and> bmu sp (BS_Its ctx A na (UQ_Seq us') yq) < bmu sp s)"
    proof (cases xq)
      case (UQ_Cell c)
      obtain env' tps us' where c: "c = ((env', tps), us')" by (cases c) auto
      with UQ_Cell rr have rrc: "rr = Some ((env', tps), us')" by (simp add: returnW_def)
      from uq UQ_Cell c have "fin (sp_cfg sp) us' (ures (sp_env sp) tus)" by (simp add: uqinv_def)
      then have "binv sp (BS_Its ctx A na (UQ_Seq us') yq)"
        unfolding ctx by (intro binv.Its[OF its _ byq]) (simp add: uqinv_def)
      with rrc UQ_Cell c BS_Its show ?thesis by (auto simp: uqel_def)
    next
      case (UQ_Seq us)
      have ui: "fin (sp_cfg sp) us (ures (sp_env sp) tus)" using uq UQ_Seq by (simp add: uqinv_def)
      have rr': "okT (upull (sp_cfg sp) us) rr" using rr UQ_Seq ops by (simp add: unify_ops_def)
      show ?thesis
      proof (rule upull_fin_cases[OF ui pw])
        assume n: "okT (upull (sp_cfg sp) us) None"
        with rr' have "rr = None" by (rule okT_det)
        with n UQ_Seq BS_Its show ?thesis by (simp add: uqel_def upull_uels_None)
      next
        fix env' tps us' assume p: "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))"
          and f': "fin (sp_cfg sp) us' (ures (sp_env sp) tus)"
          and el: "elen (sp_cfg sp) us = Suc (elen (sp_cfg sp) us')"
        from rr' p have rrc: "rr = Some ((env', tps), us')" by (rule okT_det)
        have "binv sp (BS_Its ctx A na (UQ_Seq us') yq)"
          unfolding ctx by (intro binv.Its[OF its _ byq]) (simp add: uqinv_def f')
        with rrc UQ_Seq BS_Its el upull_uels_Some[OF p] show ?thesis by (simp add: uqel_def)
      qed
    qed
    show ?thesis
    proof (cases rr)
      case None
      with x have xy: "okT (bpull ops yq) x" by simp
      from q None have m: "bmu sp yq < bmu sp s" by simp
      from less.hyps[OF m byq xy] q None BS_Its show ?thesis by (cases x) auto
    next
      case (Some c)
      then obtain env' tps us' where c: "rr = Some ((env', tps), us')" by (cases c) auto
      let ?s' = "BS_Its ctx A na (UQ_Seq us') yq"
      from q c have sub: "uqel (sp_cfg sp) xq \<subseteq> insert (env', tps) (uels (sp_cfg sp) us')"
        and b': "binv sp ?s'" and m: "bmu sp ?s' < bmu sp s" by auto
      have x': "okT (handleW (bindW (addth ctx A na (env', tps)) (\<lambda>th. returnW (Some (th, ?s'))))
          (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops ?s' | _ \<Rightarrow> raiseW e)) x"
        using x c by simp
      consider (ok) th where "okT (addth ctx A na (env', tps)) th" "x = Some (th, ?s')"
        | (compose) "\<forall>r. \<not> okT (addth ctx A na (env', tps)) r" "okT (bpull ops ?s') x"
      proof -
        from x' consider "okT (bindW (addth ctx A na (env', tps)) (\<lambda>th. returnW (Some (th, ?s')))) x"
          | evs e where "bindW (addth ctx A na (env', tps)) (\<lambda>th. returnW (Some (th, ?s'))) = Some (evs, Err e)"
            "okT (case e of COMPOSE \<Rightarrow> bpull ops ?s' | _ \<Rightarrow> raiseW e) x"
          unfolding okW_handleW by blast
        then show thesis
        proof cases
          case 1
          then show thesis using that(1) by auto
        next
          case 2
          have "\<not> okT (addth ctx A na (env', tps)) r" for r
            using 2(1) by (auto simp: bindW_def returnW_def)
          moreover have "okT (bpull ops ?s') x" using 2(2) by (cases e) auto
          ultimately show thesis using that(2) by blast
        qed
      qed
      then show ?thesis
      proof cases
        case ok
        have "pend sp s \<subseteq> insert th (pend sp ?s')"
        proof
          fix r assume "r \<in> pend sp s"
          then consider et where "et \<in> uqel (sp_cfg sp) xq" "okT (addth ctx A na et) r" | "r \<in> pend sp yq"
            unfolding BS_Its by auto
          then show "r \<in> insert th (pend sp ?s')"
          proof cases
            case 1
            with sub consider "et = (env', tps)" | "et \<in> uels (sp_cfg sp) us'" by blast
            then show ?thesis
            proof cases
              case 1
              with ok(1) \<open>okT (addth ctx A na et) r\<close> show ?thesis by auto
            next
              case 2
              with \<open>okT (addth ctx A na et) r\<close> show ?thesis by (auto simp: uqel_def)
            qed
          qed simp
        qed
        with ok(2) show ?thesis by simp
      next
        case compose
        have sps: "pend sp s \<subseteq> pend sp ?s'"
        proof
          fix r assume "r \<in> pend sp s"
          then consider et where "et \<in> uqel (sp_cfg sp) xq" "okT (addth ctx A na et) r" | "r \<in> pend sp yq"
            unfolding BS_Its by auto
          then show "r \<in> pend sp ?s'"
          proof cases
            case 1
            with sub compose(1) have "et \<in> uels (sp_cfg sp) us'" by blast
            with 1 show ?thesis by (auto simp: uqel_def)
          qed simp
        qed
        have IH: "case x of None \<Rightarrow> pend sp ?s' = {} | Some (r, s'') \<Rightarrow> pend sp ?s' \<subseteq> insert r (pend sp s'')"
          by (rule less.hyps[OF m b' compose(2)])
        show ?thesis
        proof (cases x)
          case None
          with IH sps show ?thesis by (simp del: pend.simps)
        next
          case (Some p)
          then obtain r s'' where x: "x = Some (r, s'')" by (cases p) auto
          with IH have "pend sp ?s' \<subseteq> insert r (pend sp s'')" by (simp del: pend.simps)
          with sps x show ?thesis by (simp del: pend.simps)
        qed
      qed
    qed
  next
    case (BS_Tryasms ctx er asms n)
    from less.prems(1)[unfolded BS_Tryasms] have er: "sp_eres sp" "1 \<le> n"
      "asms = drop (nat_of_integer n - 1) (asms_of sp)" "ctx = sp_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from tryasms_ok[OF cfg pa er(1) nok ops er(4,5,2,3)] obtain s'' where
      t: "okT (tryasms ops ctx er asms n) s''" and m: "bmu sp s'' < bmu sp (BS_Tryasms ctx er asms n)"
      by blast
    have b'': "binv sp s''" by (rule tryasms_binv[OF cfg pa er(1) ops er(4,5,2,3) t])
    have x'': "okT (bpull ops s'') x"
      using less.prems(2) t unfolding BS_Tryasms by (subst (asm) bpull.simps) auto
    have "pend sp s \<subseteq> pend sp s''" using tryasms_pend[OF cfg ops t] BS_Tryasms by simp
    with less.hyps[OF m[folded BS_Tryasms] b'' x''] show ?thesis by (cases x) auto
  qed
qed

lemma bevals_pend:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ops: "ops = unify_ops (sp_cfg sp) (sp_vl sp)"
  shows "bevals ops s rs \<Longrightarrow> binv sp s \<Longrightarrow> pend sp s \<subseteq> set rs"
proof (induction rule: bevals.induct)
  case (Nil s)
  from bpull_pend[OF assms Nil.prems Nil.hyps] show ?case by simp
next
  case (Cons s r s' rs)
  from Cons.hyps(1) obtain r0 where b: "bpull ops s = Some r0" "snd r0 = Ok (Some (r, s'))" by auto
  from bpull_binv[OF cfg pa b(1) ops b(2) Cons.prems] have "binv sp s'" by simp
  with Cons.IH have "pend sp s' \<subseteq> set rs" by simp
  with bpull_pend[OF assms Cons.prems Cons.hyps(1)] show ?case by auto
qed

lemma tpends_nth:
  "j < length asms \<Longrightarrow> could_unify (asms ! j) (er_concl er) \<Longrightarrow>
    upend (sp_cfg sp) (sp_vl sp) ctx (Some (er_A1 er)) (er_As er) (n + of_nat j)
      [bc_BBi ctx, (er_concl' er, rlist_abs (er_params er) (asms ! j))] (er_env er)
      ((rlist_abs (er_params er) (asms ! j), er_concl' er) # bc_dpairs ctx) \<subseteq> tpends sp ctx er asms n"
proof (induction asms arbitrary: j n)
  case Nil
  then show ?case by simp
next
  case (Cons asm rest)
  show ?case
  proof (cases j)
    case 0
    with Cons.prems show ?thesis by auto
  next
    case (Suc j')
    with Cons.prems have "j' < length rest" "could_unify (rest ! j') (er_concl er)" by auto
    from Cons.IH[OF this, of "n + 1"] Suc show ?thesis by (auto simp: algebra_simps)
  qed
qed



subsection \<open>The quick test of elim-resolution is complete\<close>

lemma matchrands_apps:
  "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> list_all2 could_unify as bs \<Longrightarrow> matchrands (h \<degree>\<degree> as) (h' \<degree>\<degree> bs)"
proof (induction as arbitrary: bs rule: rev_induct)
  case Nil
  then show ?case by (cases h) simp_all
next
  case (snoc a as)
  from snoc.prems(2) obtain bs' b where bs: "bs = bs' @ [b]" "list_all2 could_unify as bs'" "could_unify a b"
    by (auto simp: list_all2_append1 list_all2_Cons1)
  with snoc show ?case by simp
qed

lemma typings_elem: "e \<tturnstile> ts : Us \<Longrightarrow> t \<in> set ts \<Longrightarrow> \<exists>U. e \<turnstile> t : U"
  by (induction ts arbitrary: Us) (auto split: list.splits)

text \<open>If the instances of two terms are equal, then \<open>could_unify\<close> holds.\<close>

lemma could_unify_complete:
  assumes \<sigma>: "wt_subst \<sigma>"
  shows "e \<turnstile> inst \<rho> t : T \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<Longrightarrow> could_unify t u"
proof (induction "size t + size u" arbitrary: t u e T rule: less_induct)
  case less
  obtain h as where sc: "strip_comb t = (h, as)" by (cases "strip_comb t")
  obtain h' bs where sc': "strip_comb u = (h', bs)" by (cases "strip_comb u")
  have t: "t = h \<degree>\<degree> as" and u: "u = h' \<degree>\<degree> bs" using strip_comb_apps sc sc' by blast+
  have hh: "head_of t = h" "head_of u = h'" using sc sc' by (simp_all add: head_of_strip_comb)
  have na: "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)" using strip_comb_head sc sc' by blast+
  have cu: "could_unify t u = (case (h, h') of
      (_, Var _ _) \<Rightarrow> True
    | (Var _ _, _) \<Rightarrow> True
    | (Const a _, Const b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Free a _, Free b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Bound i, Bound j) \<Rightarrow> i = j \<and> matchrands t u
    | (Abs _ _ _, _) \<Rightarrow> True
    | (_, Abs _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
    by (subst could_unify.simps) (simp add: hh)
  show ?case
  proof (cases "rigid h \<and> rigid h'")
    case False
    with na show ?thesis unfolding cu by (cases h; cases h') auto
  next
    case True
    then have rh: "rigid h" "rigid h'" by simp_all
    have apt: "ap \<rho> \<sigma> t = inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) as"
      and apu: "ap \<rho> \<sigma> u = inst \<rho> h' \<degree>\<degree> map (ap \<rho> \<sigma>) bs"
      using rh t u by (simp_all add: ap_apps rigid_ap)
    have wt: "wt (inst \<rho> h \<degree>\<degree> map (ap \<rho> \<sigma>) as)" using wt_ap[OF less.prems(1) \<sigma>] apt by simp
    note ci = conv_atom_apps_inv[OF rigid_inst[OF rh(1)] rigid_inst[OF rh(2)] wt less.prems(2)[unfolded apt apu]]
    have ty: "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) as : T" using less.prems(1) t by (simp add: inst_apps)
    obtain Us where "e \<tturnstile> map (inst \<rho>) as : Us" using ty by (rule list_app_typeE)
    then have tya: "\<exists>U. e \<turnstile> inst \<rho> a : U" if "a \<in> set as" for a
      using that typings_elem[of e "map (inst \<rho>) as" Us "inst \<rho> a"] by auto
    have "list_all2 could_unify as bs"
    proof -
      have l: "list_all2 (\<lambda>a b. ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> b) as bs"
        using ci(2) by (simp add: list_all2_map1 list_all2_map2)
      have "list_all2 (\<lambda>a b. a \<in> set as \<and> b \<in> set bs \<and> ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> b) as bs"
        using l by (auto simp: list_all2_conv_all_nth)
      then show ?thesis
      proof (rule list_all2_mono, elim conjE)
        fix a b assume a: "a \<in> set as" and b: "b \<in> set bs" and eq: "ap \<rho> \<sigma> a \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> b"
        have "size a + size b < size t + size u"
          using size_apps_arg[OF a, of h] size_apps_arg[OF b, of h'] t u by simp
        with tya[OF a] eq show "could_unify a b" using less.hyps by blast
      qed
    qed
    then have "matchrands t u" using t u na(1) by (simp add: matchrands_apps)
    with rh ci(1) show ?thesis unfolding cu by (cases h; cases h') auto
  qed
qed



subsection \<open>Every unifier yields a result\<close>

text \<open>The problems of a call: elim-resolution skips the assumptions that cannot be unified.\<close>

definition probok :: "bspec \<Rightarrow> pterm option \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "probok sp A tus \<longleftrightarrow> (\<not> sp_eres sp \<and> A = None \<and> tus = bc_dpairs (sp_ctx sp)) \<or>
    (sp_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> could_unify asm (er_concl (eres_of sp)) \<and>
      tus = eres_prob sp asm))"

lemma probok_pwf: "probok sp A tus \<Longrightarrow> pinv_all sp \<Longrightarrow> pwf (sp_env sp) tus"
proof (unfold probok_def, elim disjE exE conjE)
  assume "\<not> sp_eres sp" "tus = bc_dpairs (sp_ctx sp)" "pinv_all sp"
  then show "pwf (sp_env sp) tus" by (simp add: pinv_all_def)
next
  fix n asm assume er: "sp_eres sp" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
    "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm" "pinv_all sp"
  have "nat_of_integer n - 1 < length (asms_of sp)" using er(2,3) by (simp add: integer_reps)
  then have "asm \<in> set (asms_of sp)" using er(4) by simp
  with er show "pwf (sp_env sp) tus" by (simp add: pinv_all_def)
qed

lemma bicompose_body_cover:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and rok: "results_ok sp" and nm: "\<not> bc_match (sp_ctx sp)"
    and b: "okT (bicompose_body (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_ctx sp) (sp_env sp) (sp_eres sp)
      (sp_rAs sp)) s"
    and ev: "bevals (unify_ops (sp_cfg sp) (sp_vl sp)) s rs" and pr: "probok sp A tus"
    and un: "unifiers alg (sp_env sp) tus = Some (Ok s0)" and es: "evals (sp_cfg sp) s0 xs0"
    and el: "El_R env' tps \<in> set xs0"
  shows "\<exists>r\<in>set rs. \<exists>na. itsok sp A na tus \<and> okT (addth (sp_ctx sp) A na (env', tps)) r"
proof -
  let ?ops = "unify_ops (sp_cfg sp) (sp_vl sp)"
  have bi: "binv sp s" by (rule bicompose_body_binv[OF b cfg pa])
  have ps: "pend sp s \<subseteq> set rs" by (rule bevals_pend[OF cfg pa nok refl ev bi])
  have pw: "pwf (sp_env sp) tus" by (rule probok_pwf[OF pr pa])
  have "okT (bo_unifiers ?ops (sp_env sp) tus) s0" using un cfg by (simp add: unify_ops_def)
  from unifiers_ures[OF cfg pw this] obtain ys where ys: "evals (sp_cfg sp) s0 ys"
    and ur: "\<forall>y\<in>set ys. ures (sp_env sp) tus y" by (auto simp: fin_def)
  have ys0: "ys = xs0" by (rule evals_det[OF ys es])
  have ue: "ures (sp_env sp) tus (El_R env' tps)" using ur el ys0 by blast
  obtain env1 tps1 xs where xs0: "xs0 = El_R env1 tps1 # xs"
  proof -
    from el obtain x xs where x: "xs0 = x # xs" by (cases xs0) auto
    with ur ys0 have "ures (sp_env sp) tus x" by simp
    from ures_pwf[OF this pw] obtain A0 where "uresult A0 (sp_env sp) tus x" .
    then obtain e1 t1 where "x = El_R e1 t1" by (auto simp: uresult_def)
    with x that show thesis by blast
  qed
  note es0 = es[unfolded xs0] and el0 = el[unfolded xs0]
  have addth_ok: "\<exists>r. okT (addth (sp_ctx sp) A na (env', tps)) r" if "itsok sp A na tus" for na
    using rok that ue nm unfolding results_ok_def by blast
  show ?thesis
  proof (cases "sp_eres sp")
    case False
    with pr have A: "A = None" and tus: "tus = bc_dpairs (sp_ctx sp)" by (auto simp: probok_def)
    from nok False obtain na where
      na: "okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps1) na"
      unfolding newas_ok_def by blast
    have its: "itsok sp A na tus" using False A tus na by (auto simp: itsok_def)
    from addth_ok[OF its] obtain r where r: "okT (addth (sp_ctx sp) A na (env', tps)) r" by blast
    have rU: "r \<in> upend (sp_cfg sp) (sp_vl sp) (sp_ctx sp) A (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)]
        (sp_env sp) tus"
      using un es0 el0 na r unfolding upend_def mem_Collect_eq by blast
    from b False obtain us rr where us: "okT (bo_unifiers ?ops (sp_env sp) (bc_dpairs (sp_ctx sp))) us"
      and rr: "okT (bo_pull ?ops us) rr"
      and s: "okT (case rr of None \<Rightarrow> returnW BS_Empty | Some ((env1, tpairs), us') \<Rightarrow> do {
          na \<leftarrow> newAs (bo_variants ?ops) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tpairs;
          returnW (BS_Its (sp_ctx sp) None na (UQ_Cell ((env1, tpairs), us')) BS_Empty)}) s"
      by (simp add: bicompose_body_def) blast
    have un': "unifiers alg (sp_env sp) tus = Some (Ok us)" using us cfg tus by (simp add: unify_ops_def)
    have rr': "okT (upull (sp_cfg sp) us) rr" using rr by (simp add: unify_ops_def)
    from upend_step[OF un' rr' rU] obtain e1 t1 us' na' where rrc: "rr = Some ((e1, t1), us')"
      and na': "okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] t1) na'"
      and et: "\<exists>et\<in>insert (e1, t1) (uels (sp_cfg sp) us'). okT (addth (sp_ctx sp) A na' et) r"
      by blast
    from s rrc na' have "s = BS_Its (sp_ctx sp) None na' (UQ_Cell ((e1, t1), us')) BS_Empty"
      by (auto simp: unify_ops_def)
    with et A have "r \<in> pend sp s" by (auto simp: uqel_def)
    with ps its r show ?thesis by blast
  next
    case True
    with pr obtain n asm where A: "A = Some (er_A1 (eres_of sp))" and n: "1 \<le> n"
      "nat_of_integer n \<le> length (asms_of sp)" and asm: "asm = asms_of sp ! (nat_of_integer n - 1)"
      and cu: "could_unify asm (er_concl (eres_of sp))" and tus: "tus = eres_prob sp asm"
      by (auto simp: probok_def)
    have n1: "1 \<le> nat_of_integer n" using n(1) by (simp add: integer_reps)
    let ?j = "nat_of_integer n - 1"
    have j: "?j < length (asms_of sp)" using n(2) n1 by simp
    have nj: "1 + of_nat ?j = n" using n(1) n1 by (simp add: integer_reps)
    from nok True n asm obtain na where na: "okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding newas_ok_def by blast
    have its: "itsok sp A na tus" using True A n asm tus na unfolding itsok_def by blast
    from addth_ok[OF its] obtain r where r: "okT (addth (sp_ctx sp) A na (env', tps)) r" by blast
    obtain A1 As where rA: "rev (sp_rAs sp) = A1 # As"
      using n(2) n1 by (cases "rev (sp_rAs sp)") (auto simp: asms_of_def)
    obtain params asms concl where ap: "assum_problems (bc_nlift (sp_ctx sp) + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (bc_nlift (sp_ctx sp) + 1) A1")
    have er: "ER (sp_env sp) params concl (rlist_abs params concl) A1 As = eres_of sp"
      using rA ap by (simp add: eres_of_def)
    have asms: "asms = asms_of sp" using rA ap by (simp add: asms_of_def)
    have eenv: "er_env (eres_of sp) = sp_env sp" by (simp flip: er)
    have t: "okT (tryasms ?ops (sp_ctx sp) (eres_of sp) (asms_of sp) 1) s"
      using b True rA ap er asms by (simp add: bicompose_body_def)
    have cu': "could_unify (asms_of sp ! ?j) (er_concl (eres_of sp))" using cu asm by simp
    have rU: "r \<in> upend (sp_cfg sp) (sp_vl sp) (sp_ctx sp) (Some (er_A1 (eres_of sp))) (er_As (eres_of sp))
        (1 + of_nat ?j) [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) (asms_of sp ! ?j))]
        (er_env (eres_of sp)) ((rlist_abs (er_params (eres_of sp)) (asms_of sp ! ?j), er_concl' (eres_of sp)) #
        bc_dpairs (sp_ctx sp))"
      unfolding nj eenv using un es0 el0 na r A tus asm
      by (simp add: eres_prob_def upend_def) blast
    from tpends_nth[OF j cu', where sp = sp and ctx = "sp_ctx sp" and n = 1] rU
    have "r \<in> tpends sp (sp_ctx sp) (eres_of sp) (asms_of sp) 1" by blast
    with tryasms_pend[OF cfg refl t] have "r \<in> pend sp s" by blast
    with ps its r show ?thesis by blast
  qed
qed


text \<open>For elim-resolution: an assumption whose closure is unified with the closed conclusion passes the quick test.\<close>

lemma could_unify_closure:
  assumes ap: "assum_problems k A1 = (params, asms, concl)" and w: "wtp A1" and asm: "asm \<in> set asms"
    and \<rho>: "cert_inst \<rho>" and \<sigma>: "wt_subst \<sigma>"
    and eq: "ap \<rho> \<sigma> (rlist_abs params asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
  shows "could_unify asm concl" "could_unify concl asm"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev params)" and ?e = "\<lambda>_. propT"
  let ?T = "tsubst \<rho> (map snd (rev params) \<Rrightarrow> propT)"
  have ty: "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> inst \<rho> (rlist_abs params X) : ?T" if "X \<in> insert concl (set asms)" for X
    by (rule typing_inst[OF eres_closure_typed(2)[OF ap w that] cert_inst_inst_ok[OF \<rho>]])
  have i: "inst \<rho> (rlist_abs params X) = abs_list ?bs (inst \<rho> X)" for X
    by (simp add: rlist_abs_abs_list inst_abs_list)
  have a: "ap \<rho> \<sigma> (rlist_abs params X) = abs_list ?bs (ap \<rho> \<sigma> X)" for X
    by (simp add: rlist_abs_abs_list ap_abs_list)
  have eq': "ap \<rho> \<sigma> asm \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> concl"
  proof (rule conv_abs_list_inv)
    show "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> abs_list ?bs (ap \<rho> \<sigma> asm) : ?T"
      using typing_ap[OF ty \<sigma>] asm a by auto
    show "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> abs_list ?bs (ap \<rho> \<sigma> concl) : ?T"
      using typing_ap[OF ty \<sigma>] a by auto
    show "abs_list ?bs (ap \<rho> \<sigma> asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (ap \<rho> \<sigma> concl)" using eq a by simp
  qed
  from ty[of asm] asm i obtain V where "pushes (\<lambda>j. tsubst \<rho> (?e j)) (map snd ?bs) \<turnstile> inst \<rho> asm : V"
    by (auto elim: typing_abs_listE)
  with eq' show "could_unify asm concl" by (intro could_unify_complete[OF \<sigma>])
  from ty[of concl] i obtain V' where "pushes (\<lambda>j. tsubst \<rho> (?e j)) (map snd ?bs) \<turnstile> inst \<rho> concl : V'"
    by (auto elim: typing_abs_listE)
  with conv_sym[OF eq'] show "could_unify concl asm" by (intro could_unify_complete[OF \<sigma>])
qed


subsection \<open>Every solution is an instance of a result\<close>

text \<open>
  The problems of a call of \<open>bicompose_aux\<close> with the rule \<open>\<lbrakk>As\<rbrakk> \<Longrightarrow> B\<close> and the subgoal \<open>Bi\<close>,
  besides the flex-flex pairs: resolution unifies the conclusion of the rule with the subgoal
  (both stripped of the lifted parameters if \<open>lifted\<close>); elim-resolution additionally unifies an
  assumption of the subgoal with the conclusion of the first premise of the rule, closed over
  its parameters.
\<close>

definition bicompose_problem :: "bool \<Rightarrow> bool \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "bicompose_problem lifted eres_flg Bi As B tus \<longleftrightarrow>
    (let BBi = (if lifted then strip_assums2 B Bi else (B, Bi)) in
      (\<not> eres_flg \<and> tus = [BBi]) \<or>
      (eres_flg \<and> (\<exists>A1 As' params asms concl asm. As = A1 # As' \<and>
        assum_problems (count_prems (strip_all_body Bi)) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
        tus = [(rlist_abs params asm, rlist_abs params concl), BBi])))"

text \<open>
  The main theorem on completeness: for a well-typed proof state and a well-typed rule (as for
  soundness, theorem \<open>bicompose_aux_valid\<close>), if instantiations of the proof state are
  allowed, every solution \<open>(\<rho>, \<sigma>)\<close> of a problem of the call and of the flex-flex pairs of both
  theorems, within the bounds of the configuration, is an instance of one of the finitely many
  results: an instance \<open>(\<rho>', \<sigma>')\<close> solves its flex-flex pairs and maps the application of its
  environment to every component of the proof state and the rule to the given instance. Here
  \<open>env\<close> is the environment of the call after the unification of the types of variables, of
  which \<open>\<rho>\<close> must be a solution.
\<close>

theorem bicompose_aux_complete:
  assumes cfg: "cfg_alg cfg = alg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
    and state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies As B)"
      "lifted \<Longrightarrow> lifted_over smax Bi (list_implies As B) (ilength As)"
    and tv: "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies As B))"
    and inc: "incremented \<Longrightarrow> vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies As B))"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted" and vl: "\<And>xs. length (vl xs) = length xs"
    and nm: "\<not> match_flg"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, list_implies As B) (ilength As)) s"
    and ev: "bevals (unify_ops cfg vl) s rs"
    and env: "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
      "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C)
        (rtpairs, list_implies As B) (empty_env (max rmax smax))) (Some env)"
    and pb: "bicompose_problem lifted eres_flg Bi As B tus"
    and sol: "cinst \<rho>" "tsol (tyenv env) \<rho>" "wt_subst \<sigma>"
      "\<forall>(t, u)\<in>set (tus @ rtpairs @ stpairs). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and bound: "mcp_kokK k \<rho> (tyenv env)
        (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies As B))
        (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies As B))"
      "mcp_meas \<rho> \<sigma> env (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies As B))
        \<le> nat_of_integer (cfg_search_bound cfg)"
  shows "\<exists>r\<in>set rs. \<exists>\<rho>' \<sigma>'. (\<forall>(t, u)\<in>set (br_tpairs r). ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u) \<and>
    (\<forall>X\<in>set (C # Bi # B # Bs @ As). ap \<rho>' \<sigma>' (env_apply (br_env r) X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> X)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?R = "list_implies As B" and ?m = "max rmax smax"
  let ?A = "tvars_thm stpairs ?S \<union> tvars_thm rtpairs ?R"
  let ?X = "vars_thm stpairs ?S \<union> vars_thm rtpairs ?R"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  let ?sp = "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs (rev As) B"
  have sp': "?sp = BSpec cfg vl env ctx (rev As) eres_flg"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have sel: "sp_cfg ?sp = cfg" "sp_vl ?sp = vl" "sp_env ?sp = env" "sp_eres ?sp = eres_flg"
    "sp_rAs ?sp = rev As" "sp_ctx ?sp = ctx" by (simp_all add: sp')
  have cs: "bc_dpairs ctx = BBi # rtpairs @ stpairs" "bc_BBi ctx = BBi" "bc_match ctx = match_flg"
    "bc_nlift ctx = nlift" by (simp_all add: ctx_def)
  have sp1: "ok (strip_prems (ilength As) [] ?R) (rev As, B)"
    using strip_prems_list_implies[of As "[]" B] by (simp add: return_def)
  text \<open>The body of the call:\<close>
  have eq: "bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (smax, stpairs, ?S)
      (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, ?R) (ilength As) =
    bindW (if incremented then returnW (Some (empty_env ?m))
        else unify_var_types alg (stpairs, ?S) (rtpairs, ?R) (empty_env ?m))
      (\<lambda>r. case r of None \<Rightarrow> returnW BS_Empty
        | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) ctx env eres_flg (rev As))"
    using sp1 by (simp add: bicompose_aux_def Let_def liftMT_def liftWT_def liftM_def bindT_Some_TOk
        handleT_Some_TOk nlift_def BBi_def ctx_def)
  have r: "okT (if incremented then returnW (Some (empty_env ?m))
      else unify_var_types alg (stpairs, ?S) (rtpairs, ?R) (empty_env ?m)) (Some env)"
    using env by (cases incremented) (simp_all add: returnW_def)
  have b: "okT (bicompose_body (unify_ops cfg vl) ctx env eres_flg (rev As)) s"
  proof -
    from ok[unfolded eq okW_bindW] obtain x where x: "okT (if incremented then returnW (Some (empty_env ?m))
        else unify_var_types alg (stpairs, ?S) (rtpairs, ?R) (empty_env ?m)) x"
      and rest: "okT (case x of None \<Rightarrow> returnW BS_Empty
        | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) ctx env eres_flg (rev As)) s" by blast
    from okT_det[OF x r] rest show ?thesis by simp
  qed
  text \<open>The invariants of the call:\<close>
  have ce: "einv ?A ?A env \<and> vt_is_empty (tenv env) \<and> ?m \<le> maxidx env \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> vcons \<rho> ?X)"
    by (rule call_env[OF state rule(1) tv inc env])
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev (rev As)) B"
    using lifted_over_lifted_rule[OF rule(2) sp1] by simp
  have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
    using lr[OF that] by (auto simp: lifted_rule_def)
  have rule': "wt_thm rmax hr rtpairs (list_implies (rev (rev As)) B)" using rule(1) by simp
  have fA: "finite ?A" by (intro finite_UnI finite_tvars_thm)
  have fX: "finite ?X" by (intro finite_UnI finite_vars_thm)
  have "sinv_all ?A ?A (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev (rev As)) B)) ?sp"
  proof (rule sinv_all_call_spec[OF state rule' lift])
    show "einv ?A ?A env" "finite ?A" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
      using ce fA by simp_all
    show "tvars_thm stpairs ?S \<union> tvars_thm rtpairs (list_implies (rev (rev As)) B) \<subseteq> ?A" by simp
    show "vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev (rev As)) B))"
      if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using ce that by simp
  qed
  then have sa: "sinv_all ?A ?A ?X ?sp" by simp
  have pa: "pinv_all ?sp" by (rule sinv_all_pinv_all[OF sa fA fX])
  have nok: "newas_ok ?sp" by (rule call_newas_ok[OF refl lr fl vl])
  have rok: "results_ok ?sp"
  proof (rule call_results_ok[OF refl state rule' lr _ fA])
    show "einv ?A ?A env" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
      using ce by simp_all
    show "tvars_thm stpairs ?S \<union> tvars_thm rtpairs (list_implies (rev (rev As)) B) \<subseteq> ?A" by simp
    show "vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev (rev As)) B))"
      if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using ce that by simp
  qed (simp_all add: vl)
  text \<open>The problem of the call:\<close>
  have wS: "wtp ?S" "ibelow smax ?S" and wR: "wtp ?R" "ibelow rmax ?R"
    using state rule(1) by (simp_all add: wt_thm_def)
  let ?tus = "tus @ rtpairs @ stpairs"
  obtain A1o where pr: "probok ?sp A1o ?tus" and si: "sinv ?A ?A ?X env (tdps ?tus)"
  proof (cases eres_flg)
    case False
    with pb have tus: "tus = [BBi]" by (simp add: bicompose_problem_def BBi_def Let_def)
    have "probok ?sp None ?tus" unfolding probok_def sel cs using False tus by simp
    moreover have "sinv ?A ?A ?X env (tdps ?tus)"
      using sa False tus unfolding sinv_all_def sel cs by simp
    ultimately show thesis by (rule that)
  next
    case True
    with pb obtain A1 As' params asms concl asm where As: "As = A1 # As'"
      and ap: "assum_problems (count_prems (strip_all_body Bi)) A1 = (params, asms, concl)"
      and asm: "asm \<in> set asms" and tus: "tus = [(rlist_abs params asm, rlist_abs params concl), BBi]"
      by (auto simp: bicompose_problem_def BBi_def Let_def)
    have nl: "nlift + 1 = count_prems (strip_all_body Bi)" using True by (simp add: nlift_def)
    have e: "eres_of ?sp = ER env params concl (rlist_abs params concl) A1 As'" "asms_of ?sp = asms"
      unfolding eres_of_def asms_of_def sel using As ap nl by (simp_all add: cs)
    from asm obtain j where j: "j < length asms" "asm = asms ! j" by (auto simp: in_set_conv_nth)
    let ?n = "integer_of_nat (Suc j)"
    have nn: "nat_of_integer ?n = Suc j" by (simp add: integer_reps nat_eq_iff)
    have n: "1 \<le> ?n" "nat_of_integer ?n \<le> length (asms_of ?sp)" "asm = asms_of ?sp ! (nat_of_integer ?n - 1)"
      using j e(2) nn by (simp_all add: integer_reps)
    have wA1: "wtp A1" using wtp_list_implies[OF wR(1)] As by simp
    have cu: "could_unify asm concl"
    proof (rule could_unify_closure(1)[OF ap wA1 asm cinstD(2)[OF sol(1)] sol(3)])
      show "ap \<rho> \<sigma> (rlist_abs params asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
        using sol(4) tus by simp
    qed
    have tp: "?tus = eres_prob ?sp asm"
      unfolding eres_prob_def e sel cs using tus by simp
    have "probok ?sp (Some (er_A1 (eres_of ?sp))) ?tus"
      unfolding probok_def sel using True n cu e tp by auto
    moreover have "sinv ?A ?A ?X env (tdps ?tus)"
      using sa True asm e(2) tp unfolding sinv_all_def sel by simp
    ultimately show thesis by (rule that)
  qed
  text \<open>The unifiers of the problem:\<close>
  from unifiers_fin[OF cfg fX fA si] obtain s0 where un: "unifiers alg env ?tus = Some (Ok s0)"
    and f0: "fin cfg s0 (uresult ?A env ?tus)" by blast
  from f0 obtain xs0 where es: "evals cfg s0 xs0" by (auto simp: fin_def)
  have ev0: "evars env = {}" using ce by (simp add: evars_def bnds_def vt_is_empty_lookup)
  have bX: "below (maxidx env) ?X"
    using wS(2) wR(2) ce state rule(1) by (fastforce simp: below_def vars_thm_def ibelow_def wt_thm_def)
  have tX: "vtvars ?X \<subseteq> tvars_env (tyenv env) \<union> ?A"
    by (auto simp: vtvars_def vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
  have inv: "scinv \<rho> \<sigma> env (tdps ?tus) ?X ?A"
    unfolding scinv_def
  proof (intro conjI)
    show "solution \<rho> \<sigma> env"
      using sol ce by (simp add: solution_def cinst_def vt_is_empty_lookup)
    show "wt_env \<rho> env" using ce by (simp add: wt_env_def vt_is_empty_lookup)
    show "vinv \<rho> env ?X" using ce sol(2) cinstD(2)[OF sol(1)] bX ev0 by (simp add: vinv_def)
    show "tvinv ?A env" using einvD(1) ce by blast
    show "vtvars ?X \<subseteq> tvars_env (tyenv env) \<union> ?A" by (rule tX)
    show "dtyped \<rho> (tdps ?tus)" by (rule sinv_dtyped[OF si sol(2) cinstD(2)[OF sol(1)]])
    show "dsolved \<rho> \<sigma> (tdps ?tus)" using sol(4) by (simp only: dsolved_tdps)
  qed
  obtain env' tps \<rho>' \<sigma>' where el: "El_R env' tps \<in> set xs0" and sol': "solution \<rho>' \<sigma>' env'"
    and wte': "wt_env \<rho>' env'" and dt': "dtyped \<rho>' (tdps tps)" and ds': "dsolved \<rho>' \<sigma>' (tdps tps)"
    and fac: "\<And>v e T. vars v \<subseteq> ?X \<union> evars env \<Longrightarrow> ttvars v \<subseteq> tvars_env (tyenv env) \<union> ?A \<Longrightarrow>
      e \<turnstile> inst \<rho> v : T \<Longrightarrow> ap \<rho>' \<sigma>' (env_apply env' v) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> v"
    by (rule unifiers_most_general_terms[OF cfg k fX fA si inv bound un es]) blast
  have dsp: "\<forall>(t, u)\<in>set tps. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" using ds' by (simp only: dsolved_tdps)
  text \<open>The result for the unifier:\<close>
  have b': "okT (bicompose_body (unify_ops (sp_cfg ?sp) (sp_vl ?sp)) (sp_ctx ?sp) (sp_env ?sp) (sp_eres ?sp)
      (sp_rAs ?sp)) s" using b by (simp add: sel)
  have "\<exists>r\<in>set rs. \<exists>na. itsok ?sp A1o na ?tus \<and> okT (addth (sp_ctx ?sp) A1o na (env', tps)) r"
  proof (rule bicompose_body_cover[OF _ pa nok rok _ b' _ pr _ _ el])
    show "evals (sp_cfg ?sp) s0 xs0" using es by (simp add: sel)
    show "unifiers alg (sp_env ?sp) ?tus = Some (Ok s0)" using un by (simp add: sel)
  qed (unfold sel cs; simp add: cfg nm ev)+
  then obtain r na where r: "r \<in> set rs" and ad: "okT (addth ctx A1o na (env', tps)) r"
    unfolding sel by blast
  have "(\<forall>(t, u)\<in>set (br_tpairs r). ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u) \<and> br_env r = env'"
    using ad
  proof (cases rule: addth_cases)
    case empty
    with dsp show ?thesis by simp
  next
    case (norm ntps Hs C')
    have nt: "ap \<rho>' \<sigma>' t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' t" if "ok (norm_term env' t) t'" "e \<turnstile> inst \<rho>' t : T" for t t' e T
      using nsoundD(4)[OF norm_term_sound[OF that(1) solutionD(2)[OF sol'] wte'] that(2) sol'] by (simp add: conv_sym)
    have "\<forall>(t', u')\<in>set ntps. ap \<rho>' \<sigma>' t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u'"
    proof (intro ballI, clarify)
      fix t' u' assume "(t', u') \<in> set ntps"
      from list_all2_ex2[OF norm(3) this] obtain t u where tu: "(t, u) \<in> set tps"
        and n: "ok (norm_term env' t) t'" "ok (norm_term env' u) u'" by auto
      from dt' tu obtain e T where ty: "e \<turnstile> inst \<rho>' t : T" "e \<turnstile> inst \<rho>' u : T"
        by (auto simp: dtyped_def)
      have "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" using dsp tu by blast
      with nt[OF n(1) ty(1)] nt[OF n(2) ty(2)] show "ap \<rho>' \<sigma>' t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u'"
        by (meson conv_sym conv_trans)
    qed
    with norm(2) show ?thesis by simp
  qed
  then have tps: "\<forall>(t, u)\<in>set (br_tpairs r). ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
    and benv: "br_env r = env'" by blast+
  text \<open>The components of the proof state and the rule:\<close>
  have "ap \<rho>' \<sigma>' (env_apply (br_env r) X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> X" if X: "X \<in> set (C # Bi # B # Bs @ As)" for X
  proof (unfold benv, rule fac)
    have "vars X \<subseteq> vars ?S \<union> vars ?R" using X by (auto simp: vars_list_implies)
    then show "vars X \<subseteq> ?X \<union> evars env" using vars_tvars_thm(1) by blast
    have "ttvars X \<subseteq> ttvars ?S \<union> ttvars ?R"
      using X ttvars_list_implies(1)[of X "Bs @ [Bi]" C] ttvars_list_implies(2)[of C "Bs @ [Bi]"]
        ttvars_list_implies(1)[of X As B] ttvars_list_implies(2)[of B As] by auto
    then show "ttvars X \<subseteq> tvars_env (tyenv env) \<union> ?A" using vars_tvars_thm(2) by blast
    have "wtp X" using X wtp_list_implies[OF wS(1)] wtp_list_implies[OF wR(1)] by auto
    from typing_inst[OF wtpD(2)[OF this, of "\<lambda>_. propT"] cert_inst_inst_ok[OF cinstD(2)[OF sol(1)]]]
    show "(\<lambda>j. tsubst \<rho> propT) \<turnstile> inst \<rho> X : tsubst \<rho> propT" .
  qed
  with r tps show ?thesis by blast
qed

end

end
