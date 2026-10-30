section \<open>The Results of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Seq
  imports Bicompose_Unifiers
begin

text \<open>
  An invariant of the lazy sequences of results characterizes every result that pulling
  (\<^const>\<open>bpull\<close>) produces: it is the new theorem (\<^const>\<open>addth\<close>) for a unifier of the problem
  of resolution or of elim-resolution with one of the assumptions of the subgoal, and for the new
  premises computed by \<^const>\<open>newAs\<close>.
\<close>

subsection \<open>The data of a call\<close>

text \<open>
  The data that determine the results of a call of \<^const>\<open>bicompose_aux\<close>: the configuration, a set
  \<open>A\<close> of type variables for the invariant of the unifier, \<open>Name.variant_list []\<close>, the environment
  after the unification of the types of variables, the static data of the closures, the stripped
  premises of the rule (in reverse order), and the flag of elim-resolution.
\<close>

datatype bspec = BSpec
  (bs_cfg: cfg) (bs_A: "(indexname \<times> psort) set") (bs_vl: "name list \<Rightarrow> name list") (bs_env: env)
  (bs_ctx: bctx) (bs_rAs: "pterm list") (bs_eres: bool)

text \<open>The data of elim-resolution, as computed by \<^const>\<open>bicompose_aux\<close>.\<close>

definition eres_of :: "bspec \<Rightarrow> eres_data" where
  "eres_of sp =
    (case rev (bs_rAs sp) of
      A1 # As \<Rightarrow>
        (case assum_problems (bc_nlift (bs_ctx sp) + 1) A1 of (params, asms, concl) \<Rightarrow>
          ER (bs_env sp) params concl (rlist_abs params concl) A1 As)
    | [] \<Rightarrow> ER (bs_env sp) [] (Bound 0) (Bound 0) (Bound 0) [])"

definition asms_of :: "bspec \<Rightarrow> pterm list" where
  "asms_of sp =
    (case rev (bs_rAs sp) of
      A1 # As \<Rightarrow> fst (snd (assum_problems (bc_nlift (bs_ctx sp) + 1) A1))
    | [] \<Rightarrow> [])"

text \<open>
  The problems that are unified: resolution unifies the disagreement pairs of the context;
  elim-resolution with the \<open>n\<close>-th assumption \<open>asm\<close> adds the pair of \<open>asm\<close> and the conclusion of
  the first premise, both closed over the parameters.
\<close>

definition eres_prob :: "bspec \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list" where
  "eres_prob sp asm =
    (rlist_abs (er_params (eres_of sp)) asm, er_concl' (eres_of sp)) # bc_dpairs (bs_ctx sp)"

text \<open>An \<open>A\<close>, new premises \<open>na\<close> and a problem \<open>tus\<close> of a closure \<^const>\<open>BS_Its\<close>.\<close>

definition itsok :: "bspec \<Rightarrow> pterm option \<Rightarrow> newas \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "itsok sp A na tus \<longleftrightarrow>
    (\<not> bs_eres sp \<and> A = None \<and> tus = bc_dpairs (bs_ctx sp) \<and>
      (\<exists>tps1. okT (newAs (bs_vl sp) (bs_ctx sp) (rev (bs_rAs sp)) 0 [bc_BBi (bs_ctx sp)] tps1) na)) \<or>
    (bs_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> tus = eres_prob sp asm \<and>
      (\<exists>tps1. okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na)))"

context wf_algebra
begin

text \<open>A position in a sequence of unifiers of a problem.\<close>

definition uqinv :: "bspec \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> seq uq \<Rightarrow> bool" where
  "uqinv sp tus xq \<longleftrightarrow>
    (case xq of
      UQ_Cell ((env', tps), us') \<Rightarrow> punifier (bs_env sp) (dps_of tus) env' tps \<and>
        prres alg ar (bs_A sp) env' tps \<and> uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us'
    | UQ_Seq us \<Rightarrow> uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us)"

text \<open>The results: a new theorem for a unifier of a problem.\<close>

definition rchar :: "bspec \<Rightarrow> bres \<Rightarrow> bool" where
  "rchar sp r \<longleftrightarrow> (\<exists>A na tus env' tps. itsok sp A na tus \<and>
    punifier (bs_env sp) (dps_of tus) env' tps \<and> prres alg ar (bs_A sp) env' tps \<and>
    okT (addth (bs_ctx sp) A na (env', tps)) r)"

inductive binv :: "bspec \<Rightarrow> seq bseq \<Rightarrow> bool" for sp where
  Empty: "binv sp BS_Empty"
| Its: "itsok sp A na tus \<Longrightarrow> uqinv sp tus xq \<Longrightarrow> binv sp yq \<Longrightarrow>
    binv sp (BS_Its (bs_ctx sp) A na xq yq)"
| Tryasms: "bs_eres sp \<Longrightarrow> 1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    binv sp (BS_Tryasms (bs_ctx sp) (eres_of sp) asms n)"

text \<open>The problems of a call are well-typed.\<close>

definition pinv_all :: "bspec \<Rightarrow> bool" where
  "pinv_all sp \<longleftrightarrow>
    (\<not> bs_eres sp \<longrightarrow> (\<exists>W. pinv alg ar (bs_A sp) W (bs_env sp) (dps_of (bc_dpairs (bs_ctx sp))))) \<and>
    (bs_eres sp \<longrightarrow> (\<forall>asm\<in>set (asms_of sp). \<exists>W. pinv alg ar (bs_A sp) W (bs_env sp) (dps_of (eres_prob sp asm))))"

lemma okT_of: "m = Some r \<Longrightarrow> snd r = TOk x \<Longrightarrow> okT m x"
  by (cases r) auto

lemma okT_handle_COMPOSE:
  assumes "okT (handleT M (\<lambda>e. case e of COMPOSE \<Rightarrow> N | _ \<Rightarrow> raiseT e)) z"
  shows "okT M z \<or> okT N z"
proof -
  from assms consider "okT M z" | evs e where "M = Some (evs, TErr e)"
    "okT (case e of COMPOSE \<Rightarrow> N | _ \<Rightarrow> raiseT e) z"
    by (auto simp: okT_handleT)
  then show ?thesis by cases (auto split: texn.splits)
qed

lemma uinv_unifiers_ops:
  assumes "cfg_alg cfg = alg" "finite A" "pinv alg ar A W env (dps_of tus)"
    "okT (bo_unifiers (unify_ops cfg vl) env tus) us"
  shows "uinv cfg A env tus us"
proof -
  from unifiers_uinv[OF assms(1-3)] obtain s where
    "liftMT (unifiers alg env tus) = returnT s" "uinv cfg A env tus s" by blast
  with assms(1,4) show ?thesis by (auto simp: unify_ops_def returnT_def)
qed

lemma asms_of_nth:
  assumes "asms = drop (nat_of_integer n - 1) (asms_of sp)" "1 \<le> n" "asms = asm # rest"
  shows "asm = asms_of sp ! (nat_of_integer n - 1)" "nat_of_integer n \<le> length (asms_of sp)"
    "rest = drop (nat_of_integer (n + 1) - 1) (asms_of sp)"
proof -
  let ?k = "nat_of_integer n - 1"
  have d: "drop ?k (asms_of sp) = asm # rest" using assms(1,3) by simp
  then show "asm = asms_of sp ! ?k" by (simp add: nth_via_drop)
  have "?k < length (asms_of sp)" using d by (metis drop_all list.distinct(1) not_le_imp_less)
  then show "nat_of_integer n \<le> length (asms_of sp)" using assms(2) by (simp add: integer_reps)
  have "nat_of_integer (n + 1) - 1 = Suc ?k" using assms(2) by (simp add: integer_reps)
  moreover have "drop (Suc ?k) (asms_of sp) = rest"
    using d by (metis drop_Suc list.sel(3) tl_drop)
  ultimately show "rest = drop (nat_of_integer (n + 1) - 1) (asms_of sp)" by simp
qed

lemma tryasms_binv:
  assumes "cfg_alg (bs_cfg sp) = alg" "finite (bs_A sp)" "pinv_all sp" "bs_eres sp"
  shows "ops = unify_ops (bs_cfg sp) (bs_vl sp) \<Longrightarrow> ctx = bs_ctx sp \<Longrightarrow> er = eres_of sp \<Longrightarrow>
    1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    okT (tryasms ops ctx er asms n) s \<Longrightarrow> binv sp s"
proof (induction ops ctx er asms n arbitrary: s rule: tryasms.induct)
  case 1
  then show ?case by (simp add: binv.Empty)
next
  case (2 ops ctx er asm rest n)
  note eqs = "2.prems"(1-3)
  note prems = "2.prems"(4-6)
  note nth = asms_of_nth[OF prems(2,1) refl]
  have n1: "1 \<le> n + 1" using prems(1) by simp
  show ?case
  proof (cases "could_unify asm (er_concl er)")
    case False
    with prems(3) have "okT (tryasms ops ctx er rest (n + 1)) s" by simp
    from "2.IH"(2)[OF False eqs n1 nth(3) this] show ?thesis .
  next
    case True
    let ?asm' = "rlist_abs (er_params er) asm"
    let ?tus = "(?asm', er_concl' er) # bc_dpairs ctx"
    from prems(3) True obtain us r where
      us: "okT (bo_unifiers ops (er_env er) ?tus) us" and
      r: "okT (bo_pull ops us) r" and
      rest: "okT (case r of None \<Rightarrow> tryasms ops ctx er rest (n + 1)
        | Some ((env, tpairs), us') \<Rightarrow> do {
            na \<leftarrow> newAs (bo_variants ops) ctx (er_As er) n [bc_BBi ctx, (er_concl' er, ?asm')] tpairs;
            returnT (BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env, tpairs), us'))
              (BS_Tryasms ctx er rest (n + 1)))}) s"
      by (auto simp: Let_def)
    have tus: "?tus = eres_prob sp asm" using eqs by (simp add: eres_prob_def)
    have env: "er_env er = bs_env sp" using eqs by (simp add: eres_of_def split: list.splits prod.splits)
    from prems(2) have "asm \<in> set (asms_of sp)" by (metis in_set_dropD list.set_intros(1))
    with assms(3,4) obtain W where pi: "pinv alg ar (bs_A sp) W (bs_env sp) (dps_of (eres_prob sp asm))"
      by (auto simp: pinv_all_def)
    have ui: "uinv (bs_cfg sp) (bs_A sp) (bs_env sp) (eres_prob sp asm) us"
      using uinv_unifiers_ops[OF assms(1,2) pi] us env tus eqs by simp
    show ?thesis
    proof (cases r)
      case None
      with rest have "okT (tryasms ops ctx er rest (n + 1)) s" by simp
      from "2.IH"(1)[OF True refl us r None eqs n1 nth(3) this] show ?thesis .
    next
      case (Some c)
      then obtain env' tps us' where c: "r = Some ((env', tps), us')" by (cases c) auto
      from rest c obtain na where
        na: "okT (newAs (bs_vl sp) (bs_ctx sp) (er_As (eres_of sp)) n
          [bc_BBi (bs_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps) na"
        and s: "s = BS_Its (bs_ctx sp) (Some (er_A1 (eres_of sp))) na (UQ_Cell ((env', tps), us'))
          (BS_Tryasms (bs_ctx sp) (eres_of sp) rest (n + 1))"
        using eqs by (auto simp: unify_ops_def)
      have pu: "okT (upull (bs_cfg sp) us) (Some ((env', tps), us'))" using r c eqs by (simp add: unify_ops_def)
      note u = upull_uinv_Some[OF ui pu]
      have "itsok sp (Some (er_A1 (eres_of sp))) na (eres_prob sp asm)"
        unfolding itsok_def using assms(4) prems(1) nth(1,2) na by blast
      moreover have "uqinv sp (eres_prob sp asm) (UQ_Cell ((env', tps), us'))"
        using u by (simp add: uqinv_def)
      moreover have "binv sp (BS_Tryasms (bs_ctx sp) (eres_of sp) rest (n + 1))"
        by (rule binv.Tryasms[OF assms(4) n1 nth(3)])
      ultimately show ?thesis unfolding s by (rule binv.Its)
    qed
  qed
qed

inductive_cases binv_ItsE: "binv sp (BS_Its ctx A na xq yq)"
inductive_cases binv_TryasmsE: "binv sp (BS_Tryasms ctx er asms n)"

text \<open>Pulling the sequence of results preserves the invariant and yields results as characterized.\<close>

lemma bpull_binv:
  assumes "cfg_alg (bs_cfg sp) = alg" "finite (bs_A sp)" "pinv_all sp"
  shows "bpull ops s = Some r0 \<Longrightarrow> ops = unify_ops (bs_cfg sp) (bs_vl sp) \<Longrightarrow>
    snd r0 = TOk (Some (r, s')) \<Longrightarrow> binv sp s \<Longrightarrow> rchar sp r \<and> binv sp s'"
proof (induction ops s r0 arbitrary: r s' rule: bpull.raw_induct[rotated, consumes 1])
  case (1 P ops s r0)
  note ops = "1.prems"(1)
  have IH: "rchar sp r1 \<and> binv sp s1'" if "okT (P ops s1) (Some (r1, s1'))" "binv sp s1" for s1 r1 s1'
  proof -
    from that(1) obtain evs where "P ops s1 = Some (evs, TOk (Some (r1, s1')))" by blast
    from "1.IH"[OF this ops _ that(2)] show ?thesis by simp
  qed
  note hyps = okT_of[OF "1.hyps" "1.prems"(2)]
  note bi = "1.prems"(3)
  show ?case
  proof (cases s)
    case BS_Empty
    with hyps show ?thesis by simp
  next
    case (BS_Its ctx A na xq yq)
    from bi[unfolded BS_Its] obtain tus where ctx: "ctx = bs_ctx sp" and its: "itsok sp A na tus"
      and uq: "uqinv sp tus xq" and byq: "binv sp yq"
      by (auto elim: binv_ItsE)
    from hyps[unfolded BS_Its] obtain rr where
      rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and cont: "okT (case rr of None \<Rightarrow> P ops yq
        | Some (et, us') \<Rightarrow>
            handleT (do {th \<leftarrow> addth ctx A na et; returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> P ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e))
        (Some (r, s'))"
      by auto
    have elem: "punifier (bs_env sp) (dps_of tus) env' tps \<and> prres alg ar (bs_A sp) env' tps \<and>
        uinv (bs_cfg sp) (bs_A sp) (bs_env sp) tus us'"
      if "rr = Some ((env', tps), us')" for env' tps us'
    proof (cases xq)
      case (UQ_Cell c)
      with rr that uq show ?thesis by (auto simp: uqinv_def)
    next
      case (UQ_Seq us)
      with rr that ops have "okT (upull (bs_cfg sp) us) (Some ((env', tps), us'))"
        by (simp add: unify_ops_def)
      from upull_uinv_Some[OF _ this] uq UQ_Seq show ?thesis by (simp add: uqinv_def)
    qed
    show ?thesis
    proof (cases rr)
      case None
      with cont have "okT (P ops yq) (Some (r, s'))" by simp
      from IH[OF this byq] show ?thesis .
    next
      case (Some c)
      then obtain env' tps us' where c: "rr = Some ((env', tps), us')" by (cases c) auto
      note el = elem[OF c]
      have bi': "binv sp (BS_Its ctx A na (UQ_Seq us') yq)"
        unfolding ctx by (rule binv.Its[OF its _ byq]) (use el in \<open>simp add: uqinv_def\<close>)
      from cont c have h: "okT (handleT (do {th \<leftarrow> addth ctx A na (env', tps);
          returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
        (\<lambda>e. case e of COMPOSE \<Rightarrow> P ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseT e)) (Some (r, s'))"
        by simp
      from okT_handle_COMPOSE[OF h] consider "okT (do {th \<leftarrow> addth ctx A na (env', tps);
          returnT (Some (th, BS_Its ctx A na (UQ_Seq us') yq))}) (Some (r, s'))"
        | "okT (P ops (BS_Its ctx A na (UQ_Seq us') yq)) (Some (r, s'))"
        by blast
      then show ?thesis
      proof cases
        case 1
        then have th: "okT (addth ctx A na (env', tps)) r" and s': "s' = BS_Its ctx A na (UQ_Seq us') yq"
          by auto
        have "rchar sp r" unfolding rchar_def using its el th ctx by blast
        with bi' s' show ?thesis by simp
      next
        case 2
        from IH[OF this bi'] show ?thesis .
      qed
    qed
  next
    case (BS_Tryasms ctx er asms n)
    from bi[unfolded BS_Tryasms] have er: "bs_eres sp" "1 \<le> n" "asms = drop (nat_of_integer n - 1) (asms_of sp)"
      "ctx = bs_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from hyps[unfolded BS_Tryasms] obtain s'' where t: "okT (tryasms ops ctx er asms n) s''"
      and p: "okT (P ops s'') (Some (r, s'))"
      by auto
    from tryasms_binv[OF assms er(1) ops er(4,5,2,3) t] have "binv sp s''" .
    from IH[OF p this] show ?thesis .
  qed
qed

end

end
