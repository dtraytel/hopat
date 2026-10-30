section \<open>Completeness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Complete
  imports Bicompose_Fin
begin

text \<open>
  \<open>bicompose_aux\<close> misses no unifier: for every problem it unifies and every element of the
  enumeration of the unifiers of the problem, the finite sequence of results contains the new
  theorem built for it, unless instantiations of the proof state are forbidden (\<open>match\<close>).
\<close>


subsection \<open>The results to come\<close>

definition uels :: "cfg \<Rightarrow> seq \<Rightarrow> (env \<times> (pterm \<times> pterm) list) set" where
  "uels cfg us = {(env', tps). \<exists>xs. evals cfg us xs \<and> El_R env' tps \<in> set xs}"

definition uqel :: "cfg \<Rightarrow> seq uq \<Rightarrow> (env \<times> (pterm \<times> pterm) list) set" where
  "uqel cfg xq = (case xq of UQ_Cell (et, us) \<Rightarrow> insert et (uels cfg us) | UQ_Seq us \<Rightarrow> uels cfg us)"

lemma upull_okT:
  assumes "okT (upull cfg us) rr"
  shows "(rr = None \<and> (\<exists>evs. pull cfg us = Some (evs, UOk None))) \<or>
    (\<exists>env' tps us' evs. rr = Some ((env', tps), us') \<and> pull cfg us = Some (evs, UOk (Some (El_R env' tps, us'))))"
  using assms by (auto simp: upull_def bindW_def liftWT_def returnW_def raiseW_def
      split: option.splits ures.splits elem.splits)

lemma uels_None: "pull cfg us = Some (evs, UOk None) \<Longrightarrow> uels cfg us = {}"
  by (auto simp: uels_def dest: evals_pull_None)

lemma uels_Some:
  assumes "pull cfg us = Some (evs, UOk (Some (El_R env' tps, us')))"
  shows "uels cfg us \<subseteq> insert (env', tps) (uels cfg us')"
proof
  fix et assume "et \<in> uels cfg us"
  then obtain e t xs where et: "et = (e, t)" and es: "evals cfg us xs" and el: "El_R e t \<in> set xs"
    by (auto simp: uels_def)
  from evals_pull_Some[OF es assms] obtain xs' where "xs = El_R env' tps # xs'" "evals cfg us' xs'"
    by blast
  with et el show "et \<in> insert (env', tps) (uels cfg us')" by (auto simp: uels_def)
qed

context wf_algebra
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
    fix evs assume "pull cfg us = Some (evs, UOk None)"
    from evals_pull_None[OF es this] show ?thesis by simp
  next
    fix env1' tps1' us' evs assume rr: "rr = Some ((env1', tps1'), us')"
      and p: "pull cfg us = Some (evs, UOk (Some (El_R env1' tps1', us')))"
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
      upend (bs_cfg sp) (bs_vl sp) ctx (Some (er_A1 er)) (er_As er) n
        [bc_BBi ctx, (er_concl' er, rlist_abs (er_params er) asm)] (er_env er)
        ((rlist_abs (er_params er) asm, er_concl' er) # bc_dpairs ctx)
     else {}) \<union> tpends sp ctx er rest (n + 1)"

text \<open>The results that pulling a sequence of results will yield.\<close>

fun pend :: "bspec \<Rightarrow> seq bseq \<Rightarrow> bres set" where
  "pend sp BS_Empty = {}"
| "pend sp (BS_Its ctx A na xq yq) = {r. \<exists>et\<in>uqel (bs_cfg sp) xq. okT (addth ctx A na et) r} \<union> pend sp yq"
| "pend sp (BS_Tryasms ctx er asms n) = tpends sp ctx er asms n"

lemma tryasms_pend:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg"
  shows "ops = unify_ops (bs_cfg sp) (bs_vl sp) \<Longrightarrow> okT (tryasms ops ctx er asms n) s \<Longrightarrow>
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
    let ?U = "upend (bs_cfg sp) (bs_vl sp) ctx (Some (er_A1 er)) (er_As er) n
      [bc_BBi ctx, (er_concl' er, ?asm')] (er_env er) ?tus"
    from "2.prems"(2) True obtain us rr where us: "okT (bo_unifiers ops (er_env er) ?tus) us"
      and rr: "okT (bo_pull ops us) rr"
      and s: "okT (case rr of None \<Rightarrow> tryasms ops ctx er rest (n + 1)
        | Some ((env, tpairs), us') \<Rightarrow> do {
            na \<leftarrow> newAs (bo_variants ops) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tpairs;
            returnT (BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env, tpairs), us'))
              (BS_Tryasms ctx er rest (n + 1)))}) s"
      by (simp add: Let_def) blast
    have un: "unifiers alg (er_env er) ?tus = Some (Ok us)" using us ops cfg by (simp add: unify_ops_def)
    have rr': "okT (upull (bs_cfg sp) us) rr" using rr ops by (simp add: unify_ops_def)
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
        na: "okT (newAs (bs_vl sp) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tps1) na"
        and s': "s = BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env1, tps1), us')) (BS_Tryasms ctx er rest (n + 1))"
        by (auto simp: unify_ops_def)
      have "?U \<subseteq> {r. \<exists>et\<in>insert (env1, tps1) (uels (bs_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na et) r}"
      proof
        fix r assume "r \<in> ?U"
        from upend_step[OF un rr' this] c obtain na' where
          "okT (newAs (bs_vl sp) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tps1) na'"
          and "\<exists>et\<in>insert (env1, tps1) (uels (bs_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na' et) r"
          by blast
        with na show "r \<in> {r. \<exists>et\<in>insert (env1, tps1) (uels (bs_cfg sp) us'). okT (addth ctx (Some (er_A1 er)) na et) r}"
          by auto
      qed
      then show ?thesis using True s' by (auto simp: uqel_def)
    qed
  qed
qed

text \<open>Pulling a sequence of results yields one of the results to come, and the rest of them.\<close>

lemma bpull_pend:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ops: "ops = unify_ops (bs_cfg sp) (bs_vl sp)"
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
    from less.prems(1)[unfolded BS_Its] obtain tus where ctx: "ctx = bs_ctx sp" and its: "itsok sp A na tus"
      and uq: "uqinv sp tus xq" and byq: "binv sp yq"
      by (auto elim: binv_ItsE)
    have bp: "bpull ops s = do {
        r \<leftarrow> (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us);
        case r of
          None \<Rightarrow> bpull ops yq
        | Some (et, us') \<Rightarrow>
            handleT
              (do {th \<leftarrow> addth ctx A na et; returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e)}"
      unfolding BS_Its by (subst bpull.simps) simp
    from less.prems(2)[unfolded bp okT_bindT] obtain rr where
      rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and x: "okT (case rr of None \<Rightarrow> bpull ops yq | Some (et, us') \<Rightarrow> handleT
        (do {th \<leftarrow> addth ctx A na et; returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
        (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e)) x"
      by blast
    text \<open>The next unifier, if any.\<close>
    have q: "(rr = None \<longrightarrow> uqel (bs_cfg sp) xq = {} \<and> bmu sp yq < bmu sp s) \<and>
      (\<forall>env' tps us'. rr = Some ((env', tps), us') \<longrightarrow>
        uqel (bs_cfg sp) xq \<subseteq> insert (env', tps) (uels (bs_cfg sp) us') \<and>
        binv sp (BS_Its ctx A na (UQ_Seq us') yq) \<and> bmu sp (BS_Its ctx A na (UQ_Seq us') yq) < bmu sp s)"
    proof (cases xq)
      case (UQ_Cell c)
      obtain env' tps us' where c: "c = ((env', tps), us')" by (cases c) auto
      with UQ_Cell rr have rrc: "rr = Some ((env', tps), us')" by simp
      from uq UQ_Cell c have "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us'" by (simp add: uqinv_def)
      then have "binv sp (BS_Its ctx A na (UQ_Seq us') yq)"
        unfolding ctx by (intro binv.Its[OF its _ byq]) (simp add: uqinv_def)
      with rrc UQ_Cell c BS_Its show ?thesis by (auto simp: uqel_def)
    next
      case (UQ_Seq us)
      have ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us" using uq UQ_Seq by (simp add: uqinv_def)
      have rr': "okT (upull (bs_cfg sp) us) rr" using rr UQ_Seq ops by (simp add: unify_ops_def)
      from upull_okT[OF rr'] show ?thesis
      proof (elim disjE exE conjE)
        fix evs assume "rr = None" "pull (bs_cfg sp) us = Some (evs, UOk None)"
        with UQ_Seq BS_Its show ?thesis by (simp add: uqel_def uels_None)
      next
        fix env' tps us' evs assume rrc: "rr = Some ((env', tps), us')"
          and p: "pull (bs_cfg sp) us = Some (evs, UOk (Some (El_R env' tps, us')))"
        from upull_uinv_Some[OF ui rr'[unfolded rrc]]
        have ui': "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us'" by simp
        have "binv sp (BS_Its ctx A na (UQ_Seq us') yq)"
          unfolding ctx by (intro binv.Its[OF its _ byq]) (simp add: uqinv_def ui')
        moreover have "elen (bs_cfg sp) us = Suc (elen (bs_cfg sp) us')"
          by (rule uinv_elen[OF ui rr'[unfolded rrc]])
        ultimately show ?thesis using rrc UQ_Seq BS_Its uels_Some[OF p] by (simp add: uqel_def)
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
      from q c have sub: "uqel (bs_cfg sp) xq \<subseteq> insert (env', tps) (uels (bs_cfg sp) us')"
        and b': "binv sp ?s'" and m: "bmu sp ?s' < bmu sp s" by auto
      have x': "okT (handleT (bindT (addth ctx A na (env', tps)) (\<lambda>th. returnT (Some (th, ?s'))))
          (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops ?s' | _ \<Rightarrow> raiseT e)) x"
        using x c by simp
      consider (ok) th where "okT (addth ctx A na (env', tps)) th" "x = Some (th, ?s')"
        | (compose) "\<forall>r. \<not> okT (addth ctx A na (env', tps)) r" "okT (bpull ops ?s') x"
      proof -
        from x' consider "okT (bindT (addth ctx A na (env', tps)) (\<lambda>th. returnT (Some (th, ?s')))) x"
          | evs e where "bindT (addth ctx A na (env', tps)) (\<lambda>th. returnT (Some (th, ?s'))) = Some (evs, TErr e)"
            "okT (case e of COMPOSE \<Rightarrow> bpull ops ?s' | _ \<Rightarrow> raiseT e) x"
          unfolding okT_handleT by blast
        then show thesis
        proof cases
          case 1
          then show thesis using that(1) by auto
        next
          case 2
          have "\<not> okT (addth ctx A na (env', tps)) r" for r
            using 2(1) by (auto simp: bindT_def returnT_def)
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
          then consider et where "et \<in> uqel (bs_cfg sp) xq" "okT (addth ctx A na et) r" | "r \<in> pend sp yq"
            unfolding BS_Its by auto
          then show "r \<in> insert th (pend sp ?s')"
          proof cases
            case 1
            with sub consider "et = (env', tps)" | "et \<in> uels (bs_cfg sp) us'" by blast
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
          then consider et where "et \<in> uqel (bs_cfg sp) xq" "okT (addth ctx A na et) r" | "r \<in> pend sp yq"
            unfolding BS_Its by auto
          then show "r \<in> pend sp ?s'"
          proof cases
            case 1
            with sub compose(1) have "et \<in> uels (bs_cfg sp) us'" by blast
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
    from less.prems(1)[unfolded BS_Tryasms] have er: "bs_eres sp" "1 \<le> n"
      "asms = drop (nat_of_integer n - 1) (asms_of sp)" "ctx = bs_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from tryasms_ok[OF cfg finA pa er(1) nok ops er(4,5,2,3)] obtain s'' where
      t: "okT (tryasms ops ctx er asms n) s''" and m: "bmu sp s'' < bmu sp (BS_Tryasms ctx er asms n)"
      by blast
    have b'': "binv sp s''" by (rule tryasms_binv[OF cfg finA pa er(1) ops er(4,5,2,3) t])
    have x'': "okT (bpull ops s'') x"
      using less.prems(2) t unfolding BS_Tryasms by (subst (asm) bpull.simps) auto
    have "pend sp s \<subseteq> pend sp s''" using tryasms_pend[OF cfg ops t] BS_Tryasms by simp
    with less.hyps[OF m[folded BS_Tryasms] b'' x''] show ?thesis by (cases x) auto
  qed
qed

lemma bevals_pend:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ops: "ops = unify_ops (bs_cfg sp) (bs_vl sp)"
  shows "bevals ops s rs \<Longrightarrow> binv sp s \<Longrightarrow> pend sp s \<subseteq> set rs"
proof (induction rule: bevals.induct)
  case (Nil s)
  from bpull_pend[OF assms Nil.prems Nil.hyps] show ?case by simp
next
  case (Cons s r s' rs)
  from Cons.hyps(1) obtain r0 where b: "bpull ops s = Some r0" "snd r0 = TOk (Some (r, s'))" by auto
  from bpull_binv[OF cfg finA pa b(1) ops b(2) Cons.prems] have "binv sp s'" by simp
  with Cons.IH have "pend sp s' \<subseteq> set rs" by simp
  with bpull_pend[OF assms Cons.prems Cons.hyps(1)] show ?case by auto
qed

lemma tpends_nth:
  "j < length asms \<Longrightarrow> could_unify (asms ! j) (er_concl er) \<Longrightarrow>
    upend (bs_cfg sp) (bs_vl sp) ctx (Some (er_A1 er)) (er_As er) (n + of_nat j)
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


subsection \<open>Every unifier yields a result\<close>

text \<open>The problems of a call: elim-resolution skips the assumptions that cannot be unified.\<close>

definition probok :: "bspec \<Rightarrow> pterm option \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "probok sp A tus \<longleftrightarrow> (\<not> bs_eres sp \<and> A = None \<and> tus = bc_dpairs (bs_ctx sp)) \<or>
    (bs_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> could_unify asm (er_concl (eres_of sp)) \<and>
      tus = eres_prob sp asm))"

lemma bicompose_body_cover:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and rok: "results_ok sp" and nm: "\<not> bc_match (bs_ctx sp)"
    and b: "okT (bicompose_body (unify_ops (bs_cfg sp) (bs_vl sp)) (bs_ctx sp) (bs_env sp) (bs_eres sp)
      (bs_rAs sp)) s"
    and ev: "bevals (unify_ops (bs_cfg sp) (bs_vl sp)) s rs"
    and pr: "probok sp A tus" and ue: "uelem alg (bs_cfg sp) (bs_env sp) tus (El_R env' tps)"
  shows "\<exists>r\<in>set rs. \<exists>na. itsok sp A na tus \<and> okT (addth (bs_ctx sp) A na (env', tps)) r"
proof -
  let ?ops = "unify_ops (bs_cfg sp) (bs_vl sp)"
  have bi: "binv sp s" by (rule bicompose_body_binv[OF b cfg finA pa])
  have ps: "pend sp s \<subseteq> set rs" by (rule bevals_pend[OF cfg finA pa nok refl ev bi])
  from ue obtain s0 xs0 where un: "unifiers alg (bs_env sp) tus = Some (Ok s0)"
    and es: "evals (bs_cfg sp) s0 xs0" and el: "El_R env' tps \<in> set xs0"
    by (auto simp: uelem_def)
  text \<open>The problem is well-typed, so all elements of the enumeration are unifiers.\<close>
  obtain W where pi: "pinv alg ar (bs_A sp) W (bs_env sp) (dps_of tus)"
  proof -
    have "\<exists>asm\<in>set (asms_of sp). tus = eres_prob sp asm" if "bs_eres sp"
    proof -
      from pr that obtain n asm where n: "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        and asm: "asm = asms_of sp ! (nat_of_integer n - 1)" and tus: "tus = eres_prob sp asm"
        by (auto simp: probok_def)
      have "1 \<le> nat_of_integer n" using n(1) by (simp add: integer_reps)
      with n(2) asm have "asm \<in> set (asms_of sp)" by simp
      with tus show ?thesis by blast
    qed
    with pa pr that show thesis by (cases "bs_eres sp") (auto simp: pinv_all_def probok_def)
  qed
  obtain env1 tps1 xs where xs0: "xs0 = El_R env1 tps1 # xs"
  proof -
    from unifiers_uinv[OF cfg finA pi] obtain s1 where
      s1: "liftMT (unifiers alg (bs_env sp) tus) = returnT s1" "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus s1"
      by blast
    from s1(1) un have "s1 = s0" by (simp add: liftMT_def liftWT_def liftM_def returnT_def)
    with s1(2) obtain xs' where e': "evals (bs_cfg sp) s0 xs'"
      and all: "\<forall>x\<in>set xs'. \<exists>env' tps. x = El_R env' tps" unfolding uinv_def by blast
    from evals_det[OF es e'] all el obtain x xs where "xs0 = x # xs" "\<exists>env' tps. x = El_R env' tps"
      by (cases xs0) auto
    with that show thesis by blast
  qed
  note es0 = es[unfolded xs0] and el0 = el[unfolded xs0]
  show ?thesis
  proof (cases "bs_eres sp")
    case False
    with pr have A: "A = None" and tus: "tus = bc_dpairs (bs_ctx sp)" by (auto simp: probok_def)
    from nok False obtain na where
      na: "okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tps1) na"
      unfolding newas_ok_def by blast
    have its: "itsok sp A na tus" using False A tus na by (auto simp: itsok_def)
    from rok its ue nm obtain r where r: "okT (addth (bs_ctx sp) A na (env', tps)) r"
      unfolding results_ok_def by blast
    have rU: "r \<in> upend (bs_cfg sp) (bs_vl sp) (bs_ctx sp) A (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)]
        (bs_env sp) tus"
      using un es0 el0 na r unfolding upend_def mem_Collect_eq by blast
    from b False obtain us rr where us: "okT (bo_unifiers ?ops (bs_env sp) (bc_dpairs (bs_ctx sp))) us"
      and rr: "okT (bo_pull ?ops us) rr"
      and s: "okT (case rr of None \<Rightarrow> returnT BS_Empty | Some ((env1, tpairs), us') \<Rightarrow> do {
          na \<leftarrow> newAs (bo_variants ?ops) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tpairs;
          returnT (BS_Its (bs_ctx sp) None na (UQ_Cell ((env1, tpairs), us')) BS_Empty)}) s"
      by (simp add: bicompose_body_def) blast
    have un': "unifiers alg (bs_env sp) tus = Some (Ok us)" using us cfg tus by (simp add: unify_ops_def)
    have rr': "okT (upull (bs_cfg sp) us) rr" using rr by (simp add: unify_ops_def)
    from upend_step[OF un' rr' rU] obtain e1 t1 us' na' where rrc: "rr = Some ((e1, t1), us')"
      and na': "okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] t1) na'"
      and et: "\<exists>et\<in>insert (e1, t1) (uels (bs_cfg sp) us'). okT (addth (bs_ctx sp) A na' et) r"
      by blast
    from s rrc na' have "s = BS_Its (bs_ctx sp) None na' (UQ_Cell ((e1, t1), us')) BS_Empty"
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
    have nj: "1 + of_nat ?j = n" using n(1) n1 by (simp add: integer_eq_iff integer_reps of_nat_diff)
    from nok True n asm obtain na where na: "okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding newas_ok_def by blast
    have its: "itsok sp A na tus" using True A n asm tus na unfolding itsok_def by blast
    from rok its ue nm obtain r where r: "okT (addth (bs_ctx sp) A na (env', tps)) r"
      unfolding results_ok_def by blast
    obtain A1 As where rA: "rev (bs_rAs sp) = A1 # As"
      using n(2) n1 by (cases "rev (bs_rAs sp)") (auto simp: asms_of_def)
    obtain params asms concl where ap: "assum_problems (bc_nlift (bs_ctx sp) + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (bc_nlift (bs_ctx sp) + 1) A1")
    have er: "ER (bs_env sp) params concl (rlist_abs params concl) A1 As = eres_of sp"
      using rA ap by (simp add: eres_of_def)
    have asms: "asms = asms_of sp" using rA ap by (simp add: asms_of_def)
    have eenv: "er_env (eres_of sp) = bs_env sp" by (simp flip: er)
    have t: "okT (tryasms ?ops (bs_ctx sp) (eres_of sp) (asms_of sp) 1) s"
      using b True rA ap er asms by (simp add: bicompose_body_def)
    have cu': "could_unify (asms_of sp ! ?j) (er_concl (eres_of sp))" using cu asm by simp
    have rU: "r \<in> upend (bs_cfg sp) (bs_vl sp) (bs_ctx sp) (Some (er_A1 (eres_of sp))) (er_As (eres_of sp))
        (1 + of_nat ?j) [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) (asms_of sp ! ?j))]
        (er_env (eres_of sp)) ((rlist_abs (er_params (eres_of sp)) (asms_of sp ! ?j), er_concl' (eres_of sp)) #
        bc_dpairs (bs_ctx sp))"
      unfolding nj eenv using un es0 el0 na r A tus asm
      by (simp add: eres_prob_def upend_def) blast
    from tpends_nth[OF j cu', where sp = sp and ctx = "bs_ctx sp" and n = 1] rU
    have "r \<in> tpends sp (bs_ctx sp) (eres_of sp) (asms_of sp) 1" by blast
    with tryasms_pend[OF cfg refl t] have "r \<in> pend sp s" by blast
    with ps its r show ?thesis by blast
  qed
qed


subsection \<open>The quick test of elim-resolution is sound\<close>

lemma proper_list_comb: "proper (list_comb h ts) \<longleftrightarrow> proper h \<and> (\<forall>t\<in>set ts. proper t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma size_list_comb_head: "size h \<le> size (list_comb h ts)"
proof (induction ts arbitrary: h)
  case (Cons t ts)
  from Cons.IH[of "h $ t"] show ?case by (simp add: list_comb_def)
qed (simp add: list_comb_def)

lemma size_list_comb_arg: "t \<in> set ts \<Longrightarrow> size t < size (list_comb h ts)"
proof (induction ts arbitrary: h)
  case (Cons t' ts)
  have "size (h $ t') \<le> size (list_comb (h $ t') ts)" by (rule size_list_comb_head)
  then have "size t' < size (list_comb h (t' # ts))" by (simp add: list_comb_def)
  moreover have "size t < size (list_comb h (t' # ts))" if "t \<in> set ts"
    using Cons.IH[OF that, of "h $ t'"] by (simp add: list_comb_def)
  ultimately show ?case using Cons.prems by auto
qed simp

lemma proper_rlist_abs: "proper (rlist_abs rb t) \<longleftrightarrow> proper t"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma matchrands_list_comb:
  "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> list_all2 could_unify as bs \<Longrightarrow> matchrands (list_comb h as) (list_comb h' bs)"
proof (induction as arbitrary: bs rule: rev_induct)
  case Nil
  then show ?case by (cases h) (simp_all add: list_comb_def)
next
  case (snoc a as)
  from snoc.prems(2) obtain bs' b where bs: "bs = bs' @ [b]" "list_all2 could_unify as bs'" "could_unify a b"
    by (auto simp: list_all2_append1 list_all2_Cons1)
  with snoc show ?case by (simp add: list_comb_def)
qed

text \<open>If the instances of two terms are equal, then \<open>could_unify\<close> holds.\<close>

lemma could_unify_complete:
  assumes \<sigma>: "rigid_subst \<sigma>"
  shows "proper t \<Longrightarrow> proper u \<Longrightarrow> mk_subst \<sigma> (tr (inst \<rho> t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> u)) \<Longrightarrow> could_unify t u"
proof (induction "size t + size u" arbitrary: t u rule: less_induct)
  case less
  define h where "h = head_of t"
  define as where "as = snd (strip_comb t)"
  define h' where "h' = head_of u"
  define bs where "bs = snd (strip_comb u)"
  have t: "t = list_comb h as" using head_of_list_comb[of t] by (simp add: h_def as_def)
  have u: "u = list_comb h' bs" using head_of_list_comb[of u] by (simp add: bs_def h'_def)
  have ph: "proper h" "proper h'" and pas: "\<forall>a\<in>set as. proper a" "\<forall>b\<in>set bs. proper b"
    using less.prems(1,2) t u by (simp_all add: proper_list_comb)
  have cu: "could_unify t u = (case (h, h') of
      (_, Var _ _) \<Rightarrow> True
    | (Var _ _, _) \<Rightarrow> True
    | (Const a _, Const b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Free a _, Free b _) \<Rightarrow> a = b \<and> matchrands t u
    | (Bound i, Bound j) \<Rightarrow> i = j \<and> matchrands t u
    | (Abs _ _ _, _) \<Rightarrow> True
    | (_, Abs _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
    by (subst could_unify.simps) (simp add: h_def h'_def)
  show ?case
  proof (cases "is_rigid h \<and> is_rigid h'")
    case False
    have "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
      using head_of_not_App h_def h'_def by metis+
    with False ph show ?thesis unfolding cu by (cases h; cases h') (auto simp: is_rigid_def)
  next
    case True
    then have rig: "is_rigid h" "is_rigid h'" by simp_all
    have rigi: "is_rigid (inst \<rho> h)" "is_rigid (inst \<rho> h')" using rig by simp_all
    have ti: "inst \<rho> t = list_comb (inst \<rho> h) (map (inst \<rho>) as)" using t by (simp add: inst_list_comb)
    have ui: "inst \<rho> u = list_comb (inst \<rho> h') (map (inst \<rho>) bs)" using u by (simp add: inst_list_comb)
    note at = conjunct2[OF rigid_tr[OF rigi(1) \<sigma>]] conjunct2[OF rigid_tr[OF rigi(2) \<sigma>]]
    have "tr (inst \<rho> h) \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) (map (inst \<rho>) as) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        tr (inst \<rho> h') \<degree>\<degree> map (\<lambda>b. mk_subst \<sigma> (tr b)) (map (inst \<rho>) bs)"
      using less.prems(3) rigid_tr[OF rigi(1) \<sigma>] rigid_tr[OF rigi(2) \<sigma>] ti ui
      by (simp add: tr_list_comb comp_def)
    from atom_apps_equiv[OF at this] have trh: "tr (inst \<rho> h) = tr (inst \<rho> h')"
      and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma> (tr a)) (map (inst \<rho>) as))
        (map (\<lambda>b. mk_subst \<sigma> (tr b)) (map (inst \<rho>) bs))"
      by simp_all
    have hh: "inst \<rho> h = inst \<rho> h'" by (rule tr_rigid_inj[OF rigi trh])
    have "list_all2 could_unify as bs"
    proof -
      have l: "list_all2 (\<lambda>a b. mk_subst \<sigma> (tr (inst \<rho> a)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> b))) as bs"
        using args by (simp add: list_all2_map1 list_all2_map2)
      have "list_all2 (\<lambda>a b. a \<in> set as \<and> b \<in> set bs \<and>
          mk_subst \<sigma> (tr (inst \<rho> a)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> b))) as bs"
        using l by (auto simp: list_all2_conv_all_nth)
      then show ?thesis
      proof (rule list_all2_mono, elim conjE)
        fix a b assume a: "a \<in> set as" and b: "b \<in> set bs"
          and e: "mk_subst \<sigma> (tr (inst \<rho> a)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> b))"
        have "size a + size b < size t + size u"
          using size_list_comb_arg[OF a, of h] size_list_comb_arg[OF b, of h'] t u by simp
        from less.hyps[OF this _ _ e] pas a b show "could_unify a b" by blast
      qed
    qed
    then have "matchrands t u"
      using t u head_of_not_App h_def by (metis matchrands_list_comb)
    with rig hh show ?thesis unfolding cu by (cases h; cases h') (auto simp: is_rigid_def)
  qed
qed

text \<open>The problems of a call, whether or not \<open>could_unify\<close> holds.\<close>

definition probs :: "bspec \<Rightarrow> pterm option \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "probs sp A tus \<longleftrightarrow> (\<not> bs_eres sp \<and> A = None \<and> tus = bc_dpairs (bs_ctx sp)) \<or>
    (bs_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> tus = eres_prob sp asm))"

lemma er_concl'_eq: "er_concl' (eres_of sp) = rlist_abs (er_params (eres_of sp)) (er_concl (eres_of sp))"
  by (simp add: eres_of_def split: list.splits prod.splits)

lemma probs_probok:
  assumes "probs sp A tus" and \<sigma>: "rigid_subst \<sigma>"
    and ds: "\<forall>dp\<in>set (dps_of tus). dsolved \<sigma> (instd \<rho> dp)" and sw: "\<forall>dp\<in>set (dps_of tus). swf_dp ar dp"
  shows "probok sp A tus"
  using assms(1) unfolding probs_def probok_def
proof (elim disjE exE conjE)
  fix n asm assume er: "bs_eres sp" and A: "A = Some (er_A1 (eres_of sp))" and n: "1 \<le> n"
    "nat_of_integer n \<le> length (asms_of sp)" and asm: "asm = asms_of sp ! (nat_of_integer n - 1)"
    and tus: "tus = eres_prob sp asm"
  let ?ps = "er_params (eres_of sp)" and ?c = "er_concl (eres_of sp)"
  have dp: "([], rlist_abs ?ps asm, rlist_abs ?ps ?c) \<in> set (dps_of tus)"
    using tus by (simp add: eres_prob_def er_concl'_eq)
  from ds dp have "dsolved \<sigma> (instd \<rho> ([], rlist_abs ?ps asm, rlist_abs ?ps ?c))" by blast
  then have "mk_subst \<sigma> (tr (inst \<rho> (rlist_abs ?ps asm))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (rlist_abs ?ps ?c)))"
    by (simp add: dsolved_def instb_def)
  then have e: "mk_subst \<sigma> (tr (inst \<rho> asm)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> ?c))"
    by (simp add: inst_rlist_abs tr_rlist_abs mk_subst_Abs_m Abs_m_equiv_reflect)
  from sw dp have "proper asm" "proper ?c"
    by (auto simp: swf_dp_def swf_tm_def proper_rlist_abs)
  from could_unify_complete[OF \<sigma> this e] er A n asm tus
  show "\<not> bs_eres sp \<and> A = None \<and> tus = bc_dpairs (bs_ctx sp) \<or>
    bs_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> could_unify asm (er_concl (eres_of sp)) \<and>
      tus = eres_prob sp asm)"
    by blast
qed blast


subsection \<open>Every solution is an instance of a result\<close>

text \<open>
  A solution \<open>\<sigma>\<close> (with types \<open>\<rho>\<close>) of a problem of a call that the search bound admits is an
  instance of the unifier of a result: the unifier has an instance that satisfies its
  environment and flex-flex pairs and agrees with \<open>\<sigma>\<close> and \<open>\<rho>\<close> on the variables of the call.
\<close>

lemma bicompose_body_complete:
  assumes cfg: "cfg_alg (bs_cfg sp) = alg" and finA: "finite (bs_A sp)" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and rok: "results_ok sp" and nm: "\<not> bc_match (bs_ctx sp)"
    and b: "okT (bicompose_body (unify_ops (bs_cfg sp) (bs_vl sp)) (bs_ctx sp) (bs_env sp) (bs_eres sp)
      (bs_rAs sp)) s"
    and ev: "bevals (unify_ops (bs_cfg sp) (bs_vl sp)) s rs" and pr: "probs sp A tus"
    and k: "k = nat_of_integer (cfg_arity_bound (bs_cfg sp))"
    and sol: "pcinv alg ar (bs_A sp) W \<rho> \<tau>' \<sigma> (bs_env sp) (dps_of tus)"
    and kk: "kokA k \<rho> (tyenv (bs_env sp)) (bs_A sp)"
    and bound: "pmu \<tau>' \<sigma> \<rho> (bs_env sp) (dps_of tus) \<le> nat_of_integer (cfg_search_bound (bs_cfg sp))"
  shows "\<exists>r\<in>set rs. \<exists>na env' tps \<sigma>' \<rho>'. itsok sp A na tus \<and> okT (addth (bs_ctx sp) A na (env', tps)) r \<and>
    gsol alg ar (tyenv env') \<rho>' \<and> closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
    agree (maxidx (bs_env sp)) \<sigma> \<sigma>' \<and> tagree (maxidx (bs_env sp)) \<rho> \<rho>'"
proof -
  have pi: "pinv alg ar (bs_A sp) W (bs_env sp) (dps_of tus)" using sol by (simp add: pcinv_def)
  from unifiers_ops_ok[OF cfg finA pi] obtain us where un: "unifiers alg (bs_env sp) tus = Some (Ok us)"
    and ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us"
    by blast
  from ui obtain xs where es: "evals (bs_cfg sp) us xs" by (auto simp: uinv_def)
  from unifiers_pcomplete[OF cfg k finA sol kk bound un es] obtain env' tps \<sigma>' \<rho>' where
    el: "El_R env' tps \<in> set xs" and sol': "gsol alg ar (tyenv env') \<rho>'" "closed_on UNIV \<sigma>'"
      "sat \<sigma>' (instE \<rho>' env')" "tsolved \<sigma>' (itps \<rho>' tps)" "agree (maxidx (bs_env sp)) \<sigma> \<sigma>'"
      "tagree (maxidx (bs_env sp)) \<rho> \<rho>'"
    by blast
  have ue: "uelem alg (bs_cfg sp) (bs_env sp) tus (El_R env' tps)" using un es el by (auto simp: uelem_def)
  have "probok sp A tus"
  proof (rule probs_probok[OF pr])
    show "rigid_subst \<sigma>" using sol by (simp add: pcinv_def solution_def)
    show "\<forall>dp\<in>set (dps_of tus). dsolved \<sigma> (instd \<rho> dp)" using sol by (simp add: pcinv_def)
    show "\<forall>dp\<in>set (dps_of tus). swf_dp ar dp" using pinvD(4)[OF pi] by blast
  qed
  from bicompose_body_cover[OF cfg finA pa nok rok nm b ev this ue] sol' show ?thesis by blast
qed

text \<open>
  The main theorem on completeness: for a well-typed proof state and a well-typed rule (as for
  termination, @{thm [source] bicompose_aux_terminates}), if instantiations of the proof state
  are allowed, then for the environment \<open>env\<close> after the unification of the types of the
  variables, every solution of a problem of the call that the search bound admits is an instance
  of the unifier of one of the finitely many results.
\<close>

theorem bicompose_aux_complete:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
    and inc: "incremented \<Longrightarrow>
      \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<inter> vars_thm rtpairs rprop. Ws x = Wr x"
    and ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and nm: "\<not> match_flg" and k: "k = nat_of_integer (cfg_arity_bound cfg)"
  shows "\<exists>s rs. okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s \<and>
    bevals (unify_ops cfg vl) s rs \<and>
    (\<forall>rAs B env. ok (strip_prems nsubgoal [] rprop) (rAs, B) \<longrightarrow>
      (incremented \<longrightarrow> env = empty_env (max rmax smax)) \<longrightarrow>
      (\<not> incremented \<longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
        (empty_env (max rmax smax))) (Some env)) \<longrightarrow>
      (\<forall>Ao tus W \<rho> \<tau>' \<sigma>.
        probs (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) Ao tus \<longrightarrow>
        pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dps_of tus) \<longrightarrow> kokA k \<rho> (tyenv env) A \<longrightarrow>
        pmu \<tau>' \<sigma> \<rho> env (dps_of tus) \<le> nat_of_integer (cfg_search_bound cfg) \<longrightarrow>
        (\<exists>r\<in>set rs. \<exists>na env' tps \<sigma>' \<rho>'.
          itsok (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) Ao na tus \<and>
          okT (addth (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B))
            Ao na (env', tps)) r \<and>
          gsol alg ar (tyenv env') \<rho>' \<and> closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
          agree (maxidx env) \<sigma> \<sigma>' \<and> tagree (maxidx env) \<rho> \<rho>')))"
proof (rule bicompose_aux_call[where lifted = lifted and incremented = incremented and eres_flg = eres_flg
      and flatten = flatten and match_flg = match_flg, OF cfg finA state rule A inc ns er fl vl],
    (assumption+)?, goal_cases types call)
  case types
  have "bpull (unify_ops cfg vl) BS_Empty = returnT None" by (subst bpull.simps) simp
  then have "bevals (unify_ops cfg vl) BS_Empty []" by (auto intro: bevals.Nil)
  moreover have "\<not> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
      (empty_env (max rmax smax))) (Some env)" for env
    using types(2) by auto
  ultimately show ?thesis using types(1,3) by blast
next
  case (call rAs B env s W0)
  let ?sp = "call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have sel: "bs_cfg ?sp = cfg" "bs_vl ?sp = vl" "bs_A ?sp = A" "bs_env ?sp = env" "bs_eres ?sp = eres_flg"
    "bs_rAs ?sp = rAs" "bc_match (bs_ctx ?sp) = match_flg"
    by (simp_all add: call_spec_def Let_def)
  have pa: "pinv_all ?sp" by (rule pinv_allW_pinv_all[OF call(6)])
  have b: "okT (bicompose_body (unify_ops (bs_cfg ?sp) (bs_vl ?sp)) (bs_ctx ?sp) (bs_env ?sp) (bs_eres ?sp)
      (bs_rAs ?sp)) s"
    using call(5) sel by simp
  have "binv ?sp s" by (rule bicompose_body_binv) (use call(5) cfg finA pa sel in simp_all)
  from bpull_bevals[OF _ _ pa call(7,8) _ this] cfg finA sel obtain rs where
    ev: "bevals (unify_ops cfg vl) s rs"
    by auto
  have comp: "\<exists>r\<in>set rs. \<exists>na env' tps \<sigma>' \<rho>'. itsok ?sp Ao na tus \<and> okT (addth (bs_ctx ?sp) Ao na (env', tps)) r \<and>
      gsol alg ar (tyenv env') \<rho>' \<and> closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
      agree (maxidx env) \<sigma> \<sigma>' \<and> tagree (maxidx env) \<rho> \<rho>'"
    if "probs ?sp Ao tus" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env (dps_of tus)" "kokA k \<rho> (tyenv env) A"
      "pmu \<tau>' \<sigma> \<rho> env (dps_of tus) \<le> nat_of_integer (cfg_search_bound cfg)" for Ao tus W \<rho> \<tau>' \<sigma>
    using bicompose_body_complete[of ?sp, OF _ _ pa call(7,8) _ b _ that(1)]
      that(2-4) cfg finA nm ev k sel by simp
  have uniq: "rAs' = rAs \<and> B' = B \<and> env' = env"
    if "ok (strip_prems nsubgoal [] rprop) (rAs', B')" "incremented \<Longrightarrow> env' = empty_env (max rmax smax)"
      "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
        (empty_env (max rmax smax))) (Some env')" for rAs' B' env'
    using that call(1-3) by (cases incremented) auto
  show ?thesis
  proof (intro exI[of _ s] exI[of _ rs] conjI allI impI)
    show "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop)
      nsubgoal) s" by (fact call(4))
    show "bevals (unify_ops cfg vl) s rs" by (fact ev)
    fix rAs' B' env' Ao tus W \<rho> \<tau>' \<sigma>
    assume "ok (strip_prems nsubgoal [] rprop) (rAs', B')" "incremented \<longrightarrow> env' = empty_env (max rmax smax)"
      "\<not> incremented \<longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
        (empty_env (max rmax smax))) (Some env')"
    with uniq have e: "rAs' = rAs" "B' = B" "env' = env" by blast+
    assume "probs (call_spec cfg A vl env' flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B')
        Ao tus" "pcinv alg ar A W \<rho> \<tau>' \<sigma> env' (dps_of tus)" "kokA k \<rho> (tyenv env') A"
      "pmu \<tau>' \<sigma> \<rho> env' (dps_of tus) \<le> nat_of_integer (cfg_search_bound cfg)"
    from comp[OF this[unfolded e]] show "\<exists>r\<in>set rs. \<exists>na env'' tps \<sigma>' \<rho>'.
        itsok (call_spec cfg A vl env' flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B') Ao na tus \<and>
        okT (addth (bs_ctx (call_spec cfg A vl env' flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B'))
          Ao na (env'', tps)) r \<and>
        gsol alg ar (tyenv env'') \<rho>' \<and> closed_on UNIV \<sigma>' \<and> sat \<sigma>' (instE \<rho>' env'') \<and> tsolved \<sigma>' (itps \<rho>' tps) \<and>
        agree (maxidx env') \<sigma> \<sigma>' \<and> tagree (maxidx env') \<rho> \<rho>'"
      unfolding e .
  qed
qed

end

end
