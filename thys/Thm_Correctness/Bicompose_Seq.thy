section \<open>The Results of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Seq
  imports Thm_Semantics
begin

text \<open>
  An invariant of the lazy sequences of results characterizes every result that pulling
  (\<^const>\<open>bpull\<close>) produces: it is the new theorem (\<^const>\<open>addth\<close>) for a unifier of the problem
  of resolution, or of elim-resolution with one of the assumptions of the subgoal, and for the
  new premises computed by \<^const>\<open>newAs\<close>. A unifier is an element of the enumeration of
  \<^const>\<open>unifiers\<close>; for a well-formed problem, it is a result in the sense of
  \<^const>\<open>pure_sig.uresult\<close> (theorem @{thm [source] pure_sig.unifiers_uresult}).
\<close>


subsection \<open>Sequences of unifiers\<close>

context pure_sig
begin

text \<open>A problem is well-formed if it satisfies the invariant \<^const>\<open>sinv\<close> of unification:\<close>

definition pwf :: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "pwf env tus \<longleftrightarrow> (\<exists>A K X. finite X \<and> finite K \<and> sinv A K X env (tdps tus))"

text \<open>
  The unifiers of a problem: they satisfy the invariant of the results for every witness of the
  well-formedness of the problem.
\<close>

definition ures :: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> elem \<Rightarrow> bool" where
  "ures env tus x \<longleftrightarrow> (\<forall>A K X. finite X \<longrightarrow> finite K \<longrightarrow> sinv A K X env (tdps tus) \<longrightarrow> uresult A env tus x)"

lemma uresD: "ures env tus x \<Longrightarrow> finite X \<Longrightarrow> finite K \<Longrightarrow> sinv A K X env (tdps tus) \<Longrightarrow> uresult A env tus x"
  unfolding ures_def by blast

lemma ures_pwf:
  assumes "ures env tus x" "pwf env tus"
  obtains A where "uresult A env tus x"
  using assms unfolding ures_def pwf_def by blast

lemma fin_pull:
  assumes "fin cfg s P"
  obtains (none) evs where "pull cfg s = Some (evs, UOk None)"
  | (some) evs x s' where "pull cfg s = Some (evs, UOk (Some (x, s')))" "P x" "fin cfg s' P"
proof -
  from assms obtain xs where es: "evals cfg s xs" and P: "\<forall>x\<in>set xs. P x" by (auto simp: fin_def)
  from es show thesis
  proof cases
    case (Nil evs)
    show thesis by (rule none[OF Nil(2)])
  next
    case (Cons evs x s' xs')
    with P show thesis by (intro some[of evs x s']) (auto simp: fin_def)
  qed
qed

lemma upull_fin:
  assumes "fin cfg s (ures env tus)" "okT (upull cfg s) (Some ((env', tps), s'))"
  shows "ures env tus (El_R env' tps) \<and> fin cfg s' (ures env tus)"
  using assms(1)
proof (cases rule: fin_pull)
  case (none evs)
  with assms(2) show ?thesis by (simp add: upull_def bindW_def returnW_def liftWT_def)
next
  case (some evs x s'')
  with assms(2) show ?thesis
    by (cases x) (auto simp: upull_def bindW_def returnW_def raiseW_def liftWT_def)
qed

lemma unifiers_ures:
  assumes "cfg_alg cfg = alg" "pwf env tus" "okT (bo_unifiers (unify_ops cfg vl) env tus) s"
  shows "fin cfg s (ures env tus)"
proof -
  from assms(2) obtain A K X where fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    by (auto simp: pwf_def)
  from unifiers_fin[OF assms(1) fin si] obtain s0 where u: "unifiers alg env tus = Some (Ok s0)"
    and f: "fin cfg s0 (uresult A env tus)" by blast
  from assms(1,3) u have s: "s = s0" by (simp add: unify_ops_def liftMT_def liftWT_def liftM_def)
  from f obtain xs where es: "evals cfg s0 xs" by (auto simp: fin_def)
  have "ures env tus x" if "x \<in> set xs" for x
    unfolding ures_def using unifiers_uresult[OF assms(1) _ _ _ u es that] by blast
  with es s show ?thesis by (auto simp: fin_def)
qed

end


subsection \<open>The data of a call\<close>

text \<open>
  The data that determine the results of a call of \<^const>\<open>bicompose_aux\<close>: the configuration,
  \<open>Name.variant_list []\<close>, the environment after the unification of the types of variables, the
  static data of the closures, the stripped premises of the rule (in reverse order), and the flag
  of elim-resolution.
\<close>

datatype bspec = BSpec
  (sp_cfg: cfg) (sp_vl: "name list \<Rightarrow> name list") (sp_env: env)
  (sp_ctx: bctx) (sp_rAs: "pterm list") (sp_eres: bool)

text \<open>The data of elim-resolution, as computed by \<^const>\<open>bicompose_aux\<close>.\<close>

definition eres_of :: "bspec \<Rightarrow> eres_data" where
  "eres_of sp =
    (case rev (sp_rAs sp) of
      A1 # As \<Rightarrow>
        (case assum_problems (bc_nlift (sp_ctx sp) + 1) A1 of (params, asms, concl) \<Rightarrow>
          ER (sp_env sp) params concl (rlist_abs params concl) A1 As)
    | [] \<Rightarrow> ER (sp_env sp) [] (Bound 0) (Bound 0) (Bound 0) [])"

definition asms_of :: "bspec \<Rightarrow> pterm list" where
  "asms_of sp =
    (case rev (sp_rAs sp) of
      A1 # As \<Rightarrow> fst (snd (assum_problems (bc_nlift (sp_ctx sp) + 1) A1))
    | [] \<Rightarrow> [])"

text \<open>
  The problems that are unified: resolution unifies the disagreement pairs of the context;
  elim-resolution with the assumption \<open>asm\<close> adds the pair of \<open>asm\<close> and the conclusion of the
  first premise, both closed over the parameters.
\<close>

definition eres_prob :: "bspec \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list" where
  "eres_prob sp asm =
    (rlist_abs (er_params (eres_of sp)) asm, er_concl' (eres_of sp)) # bc_dpairs (sp_ctx sp)"

text \<open>An \<open>A\<close>, new premises \<open>na\<close> and a problem \<open>tus\<close> of a closure \<^const>\<open>BS_Its\<close>.\<close>

definition itsok :: "bspec \<Rightarrow> pterm option \<Rightarrow> newas \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "itsok sp A na tus \<longleftrightarrow>
    (\<not> sp_eres sp \<and> A = None \<and> tus = bc_dpairs (sp_ctx sp) \<and>
      (\<exists>tps1. okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps1) na)) \<or>
    (sp_eres sp \<and> (\<exists>n asm. A = Some (er_A1 (eres_of sp)) \<and> 1 \<le> n \<and> nat_of_integer n \<le> length (asms_of sp) \<and>
      asm = asms_of sp ! (nat_of_integer n - 1) \<and> tus = eres_prob sp asm \<and>
      (\<exists>tps1. okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na)))"

context pure_sig
begin

text \<open>A position in a sequence of unifiers of a problem.\<close>

definition uqinv :: "bspec \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> seq uq \<Rightarrow> bool" where
  "uqinv sp tus xq \<longleftrightarrow>
    (case xq of
      UQ_Cell ((env', tps), us') \<Rightarrow> ures (sp_env sp) tus (El_R env' tps) \<and> fin (sp_cfg sp) us' (ures (sp_env sp) tus)
    | UQ_Seq us \<Rightarrow> fin (sp_cfg sp) us (ures (sp_env sp) tus))"

text \<open>The results: a new theorem for a unifier of a problem.\<close>

definition rchar :: "bspec \<Rightarrow> bres \<Rightarrow> bool" where
  "rchar sp r \<longleftrightarrow> (\<exists>A na tus env' tps. itsok sp A na tus \<and> ures (sp_env sp) tus (El_R env' tps) \<and>
    okT (addth (sp_ctx sp) A na (env', tps)) r)"

inductive binv :: "bspec \<Rightarrow> seq bseq \<Rightarrow> bool" for sp where
  Empty: "binv sp BS_Empty"
| Its: "itsok sp A na tus \<Longrightarrow> uqinv sp tus xq \<Longrightarrow> binv sp yq \<Longrightarrow>
    binv sp (BS_Its (sp_ctx sp) A na xq yq)"
| Tryasms: "sp_eres sp \<Longrightarrow> 1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    binv sp (BS_Tryasms (sp_ctx sp) (eres_of sp) asms n)"

text \<open>The problems of a call are well-formed.\<close>

definition pinv_all :: "bspec \<Rightarrow> bool" where
  "pinv_all sp \<longleftrightarrow>
    (\<not> sp_eres sp \<longrightarrow> pwf (sp_env sp) (bc_dpairs (sp_ctx sp))) \<and>
    (sp_eres sp \<longrightarrow> (\<forall>asm\<in>set (asms_of sp). pwf (sp_env sp) (eres_prob sp asm)))"

lemma okT_handle_COMPOSE:
  assumes "okT (handleT m1 (\<lambda>e. case e of COMPOSE \<Rightarrow> m2 | _ \<Rightarrow> raiseT e)) z"
  shows "okT m1 z \<or> okT m2 z"
proof -
  from assms consider "okT m1 z" | evs e where "m1 = Some (evs, TErr e)"
    "okT (case e of COMPOSE \<Rightarrow> m2 | _ \<Rightarrow> raiseT e) z"
    by (auto simp: okT_handleT)
  then show ?thesis by cases (auto split: texn.splits)
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
  assumes "cfg_alg (sp_cfg sp) = alg" "pinv_all sp" "sp_eres sp"
  shows "ops = unify_ops (sp_cfg sp) (sp_vl sp) \<Longrightarrow> ctx = sp_ctx sp \<Longrightarrow> er = eres_of sp \<Longrightarrow>
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
    have env: "er_env er = sp_env sp" using eqs by (simp add: eres_of_def split: list.splits prod.splits)
    from prems(2) have "asm \<in> set (asms_of sp)" by (metis in_set_dropD list.set_intros(1))
    with assms(2,3) have pw: "pwf (sp_env sp) (eres_prob sp asm)" by (auto simp: pinv_all_def)
    have ui: "fin (sp_cfg sp) us (ures (sp_env sp) (eres_prob sp asm))"
      using unifiers_ures[OF assms(1) pw] us env tus eqs by simp
    show ?thesis
    proof (cases r)
      case None
      with rest have "okT (tryasms ops ctx er rest (n + 1)) s" by simp
      from "2.IH"(1)[OF True refl us r None eqs n1 nth(3) this] show ?thesis .
    next
      case (Some c)
      then obtain env' tps us' where c: "r = Some ((env', tps), us')" by (cases c) auto
      from rest c obtain na where
        na: "okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
          [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps) na"
        and s: "s = BS_Its (sp_ctx sp) (Some (er_A1 (eres_of sp))) na (UQ_Cell ((env', tps), us'))
          (BS_Tryasms (sp_ctx sp) (eres_of sp) rest (n + 1))"
        using eqs by (auto simp: unify_ops_def)
      have pu: "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))" using r c eqs by (simp add: unify_ops_def)
      note u = upull_fin[OF ui pu]
      have "itsok sp (Some (er_A1 (eres_of sp))) na (eres_prob sp asm)"
        unfolding itsok_def using assms(3) prems(1) nth(1,2) na by blast
      moreover have "uqinv sp (eres_prob sp asm) (UQ_Cell ((env', tps), us'))"
        using u by (simp add: uqinv_def)
      moreover have "binv sp (BS_Tryasms (sp_ctx sp) (eres_of sp) rest (n + 1))"
        by (rule binv.Tryasms[OF assms(3) n1 nth(3)])
      ultimately show ?thesis unfolding s by (rule binv.Its)
    qed
  qed
qed

inductive_cases binv_ItsE: "binv sp (BS_Its ctx A na xq yq)"
inductive_cases binv_TryasmsE: "binv sp (BS_Tryasms ctx er asms n)"

text \<open>Pulling the sequence of results preserves the invariant and yields results as characterized.\<close>

lemma bpull_binv:
  assumes "cfg_alg (sp_cfg sp) = alg" "pinv_all sp"
  shows "bpull ops s = Some r0 \<Longrightarrow> ops = unify_ops (sp_cfg sp) (sp_vl sp) \<Longrightarrow>
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
    from bi[unfolded BS_Its] obtain tus where ctx: "ctx = sp_ctx sp" and its: "itsok sp A na tus"
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
    have elem: "ures (sp_env sp) tus (El_R env' tps) \<and> fin (sp_cfg sp) us' (ures (sp_env sp) tus)"
      if "rr = Some ((env', tps), us')" for env' tps us'
    proof (cases xq)
      case (UQ_Cell c)
      with rr that uq show ?thesis by (auto simp: uqinv_def)
    next
      case (UQ_Seq us)
      with rr that ops have "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))"
        by (simp add: unify_ops_def)
      from upull_fin[OF _ this] uq UQ_Seq show ?thesis by (simp add: uqinv_def)
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
    from bi[unfolded BS_Tryasms] have er: "sp_eres sp" "1 \<le> n" "asms = drop (nat_of_integer n - 1) (asms_of sp)"
      "ctx = sp_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from hyps[unfolded BS_Tryasms] obtain s'' where t: "okT (tryasms ops ctx er asms n) s''"
      and p: "okT (P ops s'') (Some (r, s'))"
      by auto
    from tryasms_binv[OF assms er(1) ops er(4,5,2,3) t] have "binv sp s''" .
    from IH[OF p this] show ?thesis .
  qed
qed

text \<open>The data of a call of \<^const>\<open>bicompose_aux\<close>.\<close>

definition call_spec :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bspec" where
  "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B =
    (let
      nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0);
      BBi = (if lifted then strip_assums2 B Bi else (B, Bi));
      ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)
    in BSpec cfg vl env ctx rAs eres_flg)"

lemma bicompose_body_binv:
  assumes "okT (bicompose_body (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_ctx sp) (sp_env sp) (sp_eres sp)
    (sp_rAs sp)) s"
    "cfg_alg (sp_cfg sp) = alg" "pinv_all sp"
  shows "binv sp s"
proof (cases "sp_eres sp")
  case True
  then obtain A1 As where rA: "rev (sp_rAs sp) = A1 # As"
    using assms(1) by (cases "rev (sp_rAs sp)") (auto simp: bicompose_body_def)
  obtain params asms concl where ap: "assum_problems (bc_nlift (sp_ctx sp) + 1) A1 = (params, asms, concl)"
    by (cases "assum_problems (bc_nlift (sp_ctx sp) + 1) A1")
  have er: "ER (sp_env sp) params concl (rlist_abs params concl) A1 As = eres_of sp"
    using rA ap by (simp add: eres_of_def)
  have asms: "asms = drop (nat_of_integer 1 - 1) (asms_of sp)" using rA ap by (simp add: asms_of_def)
  from assms(1) True rA ap er have "okT (tryasms (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_ctx sp) (eres_of sp) asms 1) s"
    by (simp add: bicompose_body_def)
  from tryasms_binv[OF assms(2,3) True refl refl refl _ asms this] show ?thesis by simp
next
  case False
  let ?ops = "unify_ops (sp_cfg sp) (sp_vl sp)"
  from assms(1) False obtain us r where us: "okT (bo_unifiers ?ops (sp_env sp) (bc_dpairs (sp_ctx sp))) us"
    and r: "okT (bo_pull ?ops us) r"
    and rest: "okT (case r of None \<Rightarrow> returnT BS_Empty
      | Some ((env', tpairs), us') \<Rightarrow> do {
          na \<leftarrow> newAs (bo_variants ?ops) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tpairs;
          returnT (BS_Its (sp_ctx sp) None na (UQ_Cell ((env', tpairs), us')) BS_Empty)}) s"
    by (auto simp: bicompose_body_def)
  from assms(3) False have pw: "pwf (sp_env sp) (bc_dpairs (sp_ctx sp))" by (auto simp: pinv_all_def)
  have ui: "fin (sp_cfg sp) us (ures (sp_env sp) (bc_dpairs (sp_ctx sp)))"
    by (rule unifiers_ures[OF assms(2) pw us])
  show ?thesis
  proof (cases r)
    case None
    with rest show ?thesis by (simp add: binv.Empty)
  next
    case (Some c)
    then obtain env' tps us' where c: "r = Some ((env', tps), us')" by (cases c) auto
    from rest c obtain na where
      na: "okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps) na"
      and s: "s = BS_Its (sp_ctx sp) None na (UQ_Cell ((env', tps), us')) BS_Empty"
      by (auto simp: unify_ops_def)
    have pu: "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))" using r c by (simp add: unify_ops_def)
    note u = upull_fin[OF ui pu]
    have "itsok sp None na (bc_dpairs (sp_ctx sp))" unfolding itsok_def using False na by blast
    moreover have "uqinv sp (bc_dpairs (sp_ctx sp)) (UQ_Cell ((env', tps), us'))"
      using u by (simp add: uqinv_def)
    ultimately show ?thesis unfolding s by (rule binv.Its) (rule binv.Empty)
  qed
qed

lemma okT_handle_raise:
  assumes "okT (handleT (liftMT m) (\<lambda>e. case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT e' | _ \<Rightarrow> raiseT e)) x"
  shows "ok m x"
proof -
  from assms consider "okT (liftMT m) x" | evs e where "liftMT m = Some (evs, TErr e)"
      "okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT e' | _ \<Rightarrow> raiseT e) x"
    by (auto simp: okT_handleT)
  then show ?thesis
    by cases (auto split: texn.splits uexn.splits exn.splits)
qed

text \<open>
  The results of \<^const>\<open>bicompose_aux\<close>: the premises of the rule are stripped, the types of the
  variables are unified unless the rule is incremented, and the result sequence is in the
  invariant if the problems are well-formed.
\<close>

lemma bicompose_aux_binv:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (smax, stps0, sprop)
      (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s"
    and cfg: "cfg_alg cfg = alg"
  obtains (empty) "s = BS_Empty"
  | (spec) rAs B env where "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
      "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
      "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stps0, sprop) (rtpairs, rprop) (empty_env (max rmax smax)))
        (Some env)"
      "pinv_all (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) \<Longrightarrow>
        binv (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) s"
proof -
  let ?nlift = "count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  let ?ctx = "\<lambda>B. BCtx flatten match_flg lifted smax Bs Bi C rtpairs ?nlift
    (if lifted then strip_assums2 B Bi else (B, Bi))
    ((if lifted then strip_assums2 B Bi else (B, Bi)) # rtpairs @ stpairs)"
  have eq: "bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (smax, stps0, sprop)
      (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal =
    bindT (handleT (liftMT (strip_prems nsubgoal [] rprop))
      (\<lambda>e. case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: rule'') 0 Orule_State)
        | _ \<Rightarrow> raiseT e))
      (\<lambda>(rAs, B). bindT (if incremented then returnT (Some (empty_env (max rmax smax)))
          else unify_var_types alg (stps0, sprop) (rtpairs, rprop) (empty_env (max rmax smax)))
        (\<lambda>r. case r of None \<Rightarrow> returnT BS_Empty
          | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs))"
    by (simp add: bicompose_aux_def Let_def)
  from ok[unfolded eq] obtain rAsB where
    sp0: "okT (handleT (liftMT (strip_prems nsubgoal [] rprop))
      (\<lambda>e. case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: rule'') 0 Orule_State)
        | _ \<Rightarrow> raiseT e)) rAsB"
    and rest0: "okT ((\<lambda>(rAs, B). bindT (if incremented then returnT (Some (empty_env (max rmax smax)))
          else unify_var_types alg (stps0, sprop) (rtpairs, rprop) (empty_env (max rmax smax)))
        (\<lambda>r. case r of None \<Rightarrow> returnT BS_Empty
          | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs)) rAsB) s"
    by (simp only: okT_bindT) blast
  obtain rAs B where rAsB: "rAsB = (rAs, B)" by (cases rAsB)
  from sp0 rAsB have sp: "okT (handleT (liftMT (strip_prems nsubgoal [] rprop))
      (\<lambda>e. case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: rule'') 0 Orule_State)
        | _ \<Rightarrow> raiseT e)) (rAs, B)" by simp
  from rest0 rAsB obtain r where
    r: "okT (if incremented then returnT (Some (empty_env (max rmax smax)))
      else unify_var_types alg (stps0, sprop) (rtpairs, rprop) (empty_env (max rmax smax))) r"
    and rest: "okT (case r of None \<Rightarrow> returnT BS_Empty
      | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs) s"
    by (simp only: prod.case okT_bindT) blast
  have ok1: "ok (strip_prems nsubgoal [] rprop) (rAs, B)" by (rule okT_handle_raise[OF sp])
  show thesis
  proof (cases r)
    case None
    with rest show thesis by (intro empty) simp
  next
    case (Some env)
    let ?sp = "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    from rest Some have b: "okT (bicompose_body (unify_ops (sp_cfg ?sp) (sp_vl ?sp)) (sp_ctx ?sp) (sp_env ?sp)
        (sp_eres ?sp) (sp_rAs ?sp)) s"
      by (simp add: call_spec_def Let_def)
    have "binv ?sp s" if "pinv_all ?sp"
      by (rule bicompose_body_binv[OF b _ that]) (simp_all add: call_spec_def Let_def cfg)
    moreover have "incremented \<Longrightarrow> env = empty_env (max rmax smax)" using r Some by auto
    moreover have "\<not> incremented \<Longrightarrow>
        okT (unify_var_types alg (stps0, sprop) (rtpairs, rprop) (empty_env (max rmax smax))) (Some env)"
      using r Some by auto
    ultimately show thesis using ok1 by (intro spec) auto
  qed
qed

text \<open>
  The results of \<open>bicompose_aux\<close> are the theorems obtained by pulling its lazy sequence
  (\<^const>\<open>bpull\<close>), one after the other.
\<close>

inductive bresult :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> bres \<Rightarrow> bool" for ops where
  First: "okT (bpull ops s) (Some (r, s')) \<Longrightarrow> bresult ops s r"
| Next: "okT (bpull ops s) (Some (r', s')) \<Longrightarrow> bresult ops s' r \<Longrightarrow> bresult ops s r"

lemma bresult_rchar:
  assumes "bresult (unify_ops (sp_cfg sp) (sp_vl sp)) s r" "binv sp s"
    "cfg_alg (sp_cfg sp) = alg" "pinv_all sp"
  shows "rchar sp r"
  using assms(1,2)
proof (induction rule: bresult.induct)
  case (First s r s')
  then obtain r0 where "bpull (unify_ops (sp_cfg sp) (sp_vl sp)) s = Some r0" "snd r0 = TOk (Some (r, s'))"
    by (cases "bpull (unify_ops (sp_cfg sp) (sp_vl sp)) s") auto
  from bpull_binv[OF assms(3,4) this(1) refl this(2) First.prems] show ?case by simp
next
  case (Next s r' s' r)
  then obtain r0 where "bpull (unify_ops (sp_cfg sp) (sp_vl sp)) s = Some r0" "snd r0 = TOk (Some (r', s'))"
    by (cases "bpull (unify_ops (sp_cfg sp) (sp_vl sp)) s") auto
  from bpull_binv[OF assms(3,4) this(1) refl this(2) Next.prems] Next.IH show ?case by simp
qed

end

end
