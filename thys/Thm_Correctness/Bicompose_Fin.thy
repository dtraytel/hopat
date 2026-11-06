section \<open>Termination of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Fin
  imports Bicompose_Correct
begin

text \<open>
  For a well-typed proof state and rule, \<open>bicompose_aux\<close> terminates without an exception, and
  pulling its sequence of results yields finitely many results and then the end of the sequence.
  The argument has two parts. Generically, the sequence of results of a call is finite if the
  new premises can be computed for every unifier (\<open>newas_ok\<close>) and the new theorem can be built
  for every unifier unless \<open>match\<close> forbids it (\<open>results_ok\<close>): the unifiers of a problem are
  finitely many (theorem \<open>unifiers_fin\<close>). For the calls of \<open>bicompose_aux\<close>, both hold: the
  components of the new theorem are well-typed in the environment of the unifier, so their
  normalization terminates (theorem \<open>norm_term_term\<close>).
\<close>


subsection \<open>Finite enumerations of results\<close>

context pure_sig
begin

text \<open>Pulling the sequence of results repeatedly yields \<open>rs\<close> and then the end of the sequence.\<close>

inductive bevals :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> bres list \<Rightarrow> bool" for ops where
  Nil: "okT (bpull ops s) None \<Longrightarrow> bevals ops s []"
| Cons: "okT (bpull ops s) (Some (r, s')) \<Longrightarrow> bevals ops s' rs \<Longrightarrow> bevals ops s (r # rs)"

lemma bevals_cong:
  assumes "\<And>x. okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops s') x" "bevals ops s' rs"
  shows "bevals ops s rs"
  using assms(2) by cases (auto intro: bevals.intros simp: assms(1))

lemma bevals_results: "bevals ops s rs \<Longrightarrow> r \<in> set rs \<Longrightarrow> bresult ops s r"
  by (induction rule: bevals.induct) (auto intro: bresult.intros)

text \<open>The length of the enumeration of a sequence of unifiers.\<close>

definition elen :: "cfg \<Rightarrow> seq \<Rightarrow> nat" where
  "elen cfg s = length (THE xs. evals cfg s xs)"

lemma elen: "evals cfg s xs \<Longrightarrow> elen cfg s = length xs"
  unfolding elen_def by (rule arg_cong[of _ _ length], rule the_equality) (auto dest: evals_det)

text \<open>Pulling a finite sequence of unifiers of a problem terminates without an exception.\<close>

lemma upull_fin_cases:
  assumes "fin cfg us (ures env tus)" "pwf env tus"
  obtains (none) "okT (upull cfg us) None"
  | (some) env' tps us' where "okT (upull cfg us) (Some ((env', tps), us'))"
      "ures env tus (El_R env' tps)" "fin cfg us' (ures env tus)" "elen cfg us = Suc (elen cfg us')"
  using assms(1)
proof (cases rule: fin_pull)
  case (none evs)
  then show thesis by (intro that(1)) (simp add: upull_def bindW_def returnW_def liftWT_def)
next
  case (some evs x us')
  from ures_pwf[OF some(2) assms(2)] obtain A where "uresult A env tus x" .
  then obtain env' tps where x: "x = El_R env' tps" by (auto simp: uresult_def)
  from assms obtain xs where es: "evals cfg us xs" by (auto simp: fin_def)
  from es some(1) obtain xs' where "xs = x # xs'" "evals cfg us' xs'"
    by cases auto
  with es have "elen cfg us = Suc (elen cfg us')" by (simp add: elen)
  with some x show thesis
    by (intro that(2)[of env' tps us']) (simp_all add: upull_def bindW_def returnW_def liftWT_def)
qed

text \<open>The unifiers of a well-formed problem:\<close>

lemma unifiers_ops_ok:
  assumes "cfg_alg cfg = alg" "pwf env tus"
  obtains us where "okT (bo_unifiers (unify_ops cfg vl) env tus) us" "fin cfg us (ures env tus)"
    "unifiers alg env tus = Some (Ok us)"
proof -
  from assms(2) obtain A K X where fin: "finite X" "finite K" and si: "sinv A K X env (tdps tus)"
    by (auto simp: pwf_def)
  from unifiers_fin[OF assms(1) fin si] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (uresult A env tus)" by blast
  have ok: "okT (bo_unifiers (unify_ops cfg vl) env tus) s"
    using assms(1) u by (simp add: unify_ops_def liftMT_def liftWT_def liftM_def)
  from ok unifiers_ures[OF assms ok] u show thesis by (rule that)
qed

definition ulen :: "bspec \<Rightarrow> pterm \<Rightarrow> nat" where
  "ulen sp asm = (case unifiers alg (sp_env sp) (eres_prob sp asm) of Some (Ok s) \<Rightarrow> elen (sp_cfg sp) s | _ \<Rightarrow> 0)"

text \<open>A measure of the remaining work in a sequence of results.\<close>

fun bmu :: "bspec \<Rightarrow> seq bseq \<Rightarrow> nat" where
  "bmu sp BS_Empty = 0"
| "bmu sp (BS_Its ctx A na xq yq) =
    (case xq of UQ_Cell (_, us) \<Rightarrow> Suc (elen (sp_cfg sp) us) | UQ_Seq us \<Rightarrow> elen (sp_cfg sp) us) + 1 + bmu sp yq"
| "bmu sp (BS_Tryasms ctx er asms n) = (\<Sum>asm\<leftarrow>asms. 3 + ulen sp asm) + 1"

text \<open>
  The assumptions on a call: the new premises can be computed for every unifier of each
  problem, and the new theorem can be built for each unifier unless \<open>match\<close> forbids it.
\<close>

definition newas_ok :: "bspec \<Rightarrow> bool" where
  "newas_ok sp \<longleftrightarrow>
    (\<not> sp_eres sp \<longrightarrow> (\<forall>tps1. \<exists>na. okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps1) na)) \<and>
    (sp_eres sp \<longrightarrow> (\<forall>n asm tps1. 1 \<le> n \<longrightarrow> nat_of_integer n \<le> length (asms_of sp) \<longrightarrow>
      asm = asms_of sp ! (nat_of_integer n - 1) \<longrightarrow>
      (\<exists>na. okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na)))"

definition results_ok :: "bspec \<Rightarrow> bool" where
  "results_ok sp \<longleftrightarrow> (\<forall>A na tus env' tps. itsok sp A na tus \<longrightarrow> ures (sp_env sp) tus (El_R env' tps) \<longrightarrow>
    (\<exists>r. okT (addth (sp_ctx sp) A na (env', tps)) r) \<or>
    (bc_match (sp_ctx sp) \<and> (\<exists>evs. addth (sp_ctx sp) A na (env', tps) = Some (evs, TErr COMPOSE))))"

text \<open>Elim-resolution with the remaining assumptions terminates.\<close>

lemma tryasms_ok:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp" and er: "sp_eres sp" and nok: "newas_ok sp"
  shows "ops = unify_ops (sp_cfg sp) (sp_vl sp) \<Longrightarrow> ctx = sp_ctx sp \<Longrightarrow> er = eres_of sp \<Longrightarrow>
    1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    \<exists>s. okT (tryasms ops ctx er asms n) s \<and> bmu sp s < bmu sp (BS_Tryasms ctx er asms n)"
proof (induction ops ctx er asms n rule: tryasms.induct)
  case 1
  then show ?case by (simp add: returnT_def)
next
  case (2 ops ctx er asm rest n)
  note eqs = "2.prems"(1-3)
  note prems = "2.prems"(4-5)
  note nth = asms_of_nth[OF prems(2,1) refl]
  have n1: "1 \<le> n + 1" using prems(1) by simp
  have mono: "bmu sp (BS_Tryasms ctx er rest (n + 1)) < bmu sp (BS_Tryasms ctx er (asm # rest) n)" by simp
  show ?case
  proof (cases "could_unify asm (er_concl er)")
    case False
    from "2.IH"(2)[OF False eqs n1 nth(3)] False mono show ?thesis by auto
  next
    case True
    let ?asm' = "rlist_abs (er_params er) asm"
    let ?tus = "(?asm', er_concl' er) # bc_dpairs ctx"
    have tus: "?tus = eres_prob sp asm" using eqs by (simp add: eres_prob_def)
    have env: "er_env er = sp_env sp" using eqs by (simp add: eres_of_def split: list.splits prod.splits)
    from prems(2) have "asm \<in> set (asms_of sp)" by (metis in_set_dropD list.set_intros(1))
    with pa er have pw: "pwf (sp_env sp) (eres_prob sp asm)" by (auto simp: pinv_all_def)
    obtain us where us: "okT (bo_unifiers ops (er_env er) ?tus) us"
      and ui: "fin (sp_cfg sp) us (ures (sp_env sp) (eres_prob sp asm))"
      and un: "unifiers alg (sp_env sp) (eres_prob sp asm) = Some (Ok us)"
      by (rule unifiers_ops_ok[OF cfg pw]) (use eqs env tus in auto)
    show ?thesis
    proof (rule upull_fin_cases[OF ui pw])
      assume "okT (upull (sp_cfg sp) us) None"
      then have r: "okT (bo_pull ops us) None" using eqs by (simp add: unify_ops_def)
      from "2.IH"(1)[OF True refl us r refl eqs n1 nth(3)] obtain s where
        "okT (tryasms ops ctx er rest (n + 1)) s" "bmu sp s < bmu sp (BS_Tryasms ctx er rest (n + 1))"
        by blast
      with True us r mono show ?thesis by (auto simp: Let_def)
    next
      fix env' tps us' assume pu: "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))"
        and el: "elen (sp_cfg sp) us = Suc (elen (sp_cfg sp) us')"
      have r: "okT (bo_pull ops us) (Some ((env', tps), us'))" using pu eqs by (simp add: unify_ops_def)
      from nok er prems(1) nth(2,1) obtain na where
        na: "okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
          [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps) na"
        unfolding newas_ok_def by blast
      let ?s = "BS_Its ctx (Some (er_A1 er)) na (UQ_Cell ((env', tps), us')) (BS_Tryasms ctx er rest (n + 1))"
      have "okT (tryasms ops ctx er (asm # rest) n) ?s"
        using True us r na eqs by (auto simp: Let_def unify_ops_def okT_bindT returnT_def)
      moreover have "bmu sp ?s < bmu sp (BS_Tryasms ctx er (asm # rest) n)"
        using un el by (simp add: ulen_def)
      ultimately show ?thesis by blast
    qed
  qed
qed

text \<open>Pulling a sequence of results in the invariant yields finitely many results.\<close>

lemma bpull_bevals:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and rok: "results_ok sp" and ops: "ops = unify_ops (sp_cfg sp) (sp_vl sp)"
  shows "binv sp s \<Longrightarrow> \<exists>rs. bevals ops s rs"
proof (induction "bmu sp s" arbitrary: s rule: less_induct)
  case less
  show ?case
  proof (cases s)
    case BS_Empty
    have "bpull ops BS_Empty = returnT None" by (subst bpull.simps) simp
    with BS_Empty show ?thesis by (intro exI[of _ "[]"] bevals.Nil) (simp add: returnT_def)
  next
    case (BS_Its ctx A na xq yq)
    from less.prems[unfolded BS_Its] obtain tus where ctx: "ctx = sp_ctx sp" and its: "itsok sp A na tus"
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
    text \<open>The next unifier, if any.\<close>
    obtain rr where rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnT (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and el: "\<And>env' tps us'. rr = Some ((env', tps), us') \<Longrightarrow>
        fin (sp_cfg sp) us' (ures (sp_env sp) tus) \<and> ures (sp_env sp) tus (El_R env' tps) \<and>
        bmu sp (BS_Its ctx A na (UQ_Seq us') yq) < bmu sp s"
      and nn: "rr = None \<Longrightarrow> bmu sp yq < bmu sp s"
    proof (cases xq)
      case (UQ_Cell c)
      obtain env' tps us' where c: "c = ((env', tps), us')" by (cases c) auto
      show thesis
        by (rule that[of "Some c"]) (use uq UQ_Cell c BS_Its in \<open>auto simp: uqinv_def returnT_def\<close>)
    next
      case (UQ_Seq us)
      have ui: "fin (sp_cfg sp) us (ures (sp_env sp) tus)" using uq UQ_Seq by (simp add: uqinv_def)
      show thesis
      proof (rule upull_fin_cases[OF ui itsok_pwf[OF its pa]])
        assume "okT (upull (sp_cfg sp) us) None"
        then have "okT (bo_pull ops us) None" using ops by (simp add: unify_ops_def)
        then show thesis by (intro that[of None]) (use UQ_Seq BS_Its in auto)
      next
        fix env' tps us' assume "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))"
          "ures (sp_env sp) tus (El_R env' tps)" "fin (sp_cfg sp) us' (ures (sp_env sp) tus)"
          "elen (sp_cfg sp) us = Suc (elen (sp_cfg sp) us')"
        then show thesis
          by (intro that[of "Some ((env', tps), us')"]) (use UQ_Seq BS_Its ops in \<open>auto simp: unify_ops_def\<close>)
      qed
    qed
    show ?thesis
    proof (cases rr)
      case None
      have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops yq) x" for x
        using rr None unfolding bp by (auto simp: okT_bindT)
      from less.hyps[OF nn[OF None] byq] obtain rs where "bevals ops yq rs" by blast
      from bevals_cong[OF eqv this] show ?thesis by blast
    next
      case (Some c)
      then obtain env' tps us' where c: "rr = Some ((env', tps), us')" by (cases c) auto
      note e = el[OF c]
      let ?s' = "BS_Its ctx A na (UQ_Seq us') yq"
      have bi': "binv sp ?s'" unfolding ctx by (rule binv.Its[OF its _ byq]) (use e in \<open>simp add: uqinv_def\<close>)
      from less.hyps[OF conjunct2[OF conjunct2[OF e]] bi'] obtain rs where rs: "bevals ops ?s' rs" by blast
      from rok its conjunct1[OF conjunct2[OF e]] ctx
      consider th where "okT (addth ctx A na (env', tps)) th"
        | evs where "addth ctx A na (env', tps) = Some (evs, TErr COMPOSE)"
        unfolding results_ok_def by blast
      then show ?thesis
      proof cases
        case 1
        have "okT (bpull ops s) (Some (th, ?s'))"
          using rr c 1 unfolding bp by (auto simp: okT_bindT okT_handleT returnT_def)
        from bevals.Cons[OF this rs] show ?thesis by blast
      next
        case 2
        have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops ?s') x" for x
          using rr c 2 unfolding bp
          by (auto simp: okT_bindT okT_handleT bindT_def map_option_eq_Some split: option.splits tres.splits)
        from bevals_cong[OF eqv rs] show ?thesis by blast
      qed
    qed
  next
    case (BS_Tryasms ctx er asms n)
    from less.prems[unfolded BS_Tryasms] have er: "sp_eres sp" "1 \<le> n"
      "asms = drop (nat_of_integer n - 1) (asms_of sp)" "ctx = sp_ctx sp" "er = eres_of sp"
      by (auto elim: binv_TryasmsE)
    from tryasms_ok[OF cfg pa er(1) nok ops er(4,5,2,3)] obtain s'' where
      t: "okT (tryasms ops ctx er asms n) s''" and m: "bmu sp s'' < bmu sp (BS_Tryasms ctx er asms n)"
      by blast
    have b'': "binv sp s''" by (rule tryasms_binv[OF cfg pa er(1) ops er(4,5,2,3) t])
    have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops s'') x" for x
      using t unfolding BS_Tryasms by (subst bpull.simps) (auto simp: okT_bindT)
    from less.hyps[OF _ b''] m BS_Tryasms obtain rs where "bevals ops s'' rs" by auto
    from bevals_cong[OF eqv this] show ?thesis by blast
  qed
qed



subsection \<open>The new premises can be computed\<close>

text \<open>Removing the parameters succeeds if the deleted assumption exists:\<close>

lemma remove_params_exists:
  "ilength (strip_params A) = j \<Longrightarrow> n \<le> ilength (spine_hyps A) \<Longrightarrow> \<exists>A'. ok (remove_params j n A) A'"
proof (induction j n A rule: remove_params.induct)
  case (1 j n A)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    then show ?thesis by (subst remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      have spB: "ilength (strip_params B) = j" using "1.prems"(1) HB by (simp add: strip_params_imp)
      have sh: "spine_hyps A = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
      have n1: "n - 1 \<le> ilength (spine_hyps B)" using "1.prems"(2) sh by simp
      show ?thesis
      proof (cases "n = 1")
        case True
        from "1.IH"(2)[OF False HB refl True spB n1] obtain B' where "ok (remove_params j (n - 1) B) B'"
          by blast
        with False HB True show ?thesis by (subst remove_params.simps) simp
      next
        case n1': False
        from "1.IH"(3)[OF False HB refl n1' spB n1] obtain B' where "ok (remove_params j (n - 1) B) B'"
          by blast
        with False HB n1' show ?thesis by (subst remove_params.simps) (simp add: bindM_def)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        have sp: "ilength (strip_params b) = j - 1"
          using "1.prems"(1) None aTb by (simp add: strip_params_all)
        have sh: "spine_hyps A = spine_hyps b" using None aTb by (subst spine_hyps.simps) simp
        from "1.IH"(1)[OF False None aTb refl refl sp] "1.prems"(2) sh obtain A' where
          "ok (remove_params (j - 1) n b) A'" by auto
        with False None aTb show ?thesis by (subst remove_params.simps) simp
      next
        case None': None
        have "spine_hyps A = []" using None None' by (subst spine_hyps.simps) simp
        with "1.prems"(2) have "\<not> 0 < n" by simp
        with False None None' show ?thesis by (subst remove_params.simps) simp
      qed
    qed
  qed
qed

lemma flatten_params_exists:
  assumes "\<And>xs. length (vl xs) = length xs" "n \<le> ilength (spine_hyps A)"
  shows "\<exists>A'. ok (flatten_params vl n A) A'"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have "ilength ?ps = ilength ?vars" using assms(1)[of "map fst ?ps"] by (simp add: ilength_eq)
  from remove_params_exists[OF this assms(2)] show ?thesis
    by (auto simp: flatten_params_def Let_def)
qed

lemma ok_mapM_exI: "\<forall>x\<in>set xs. \<exists>y. ok (f x) y \<Longrightarrow> \<exists>ys. ok (mapM f xs) ys"
  by (induction xs) (auto simp: return_def bindM_def)

lemma okT_mapT_exI: "\<forall>x\<in>set xs. \<exists>y. okT (f x) y \<Longrightarrow> \<exists>ys. okT (mapT f xs) ys"
  by (induction xs) (auto simp: returnT_def)

text \<open>
  The new premises can be computed: flattening finds the assumption deleted by elim-resolution,
  if the rule is lifted.
\<close>

lemma call_newas_ok:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted" and vl: "\<And>xs. length (vl xs) = length xs"
  shows "newas_ok sp"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  text \<open>The new premises for a list \<open>As0\<close> of premises of the rule.\<close>
  have ex: "\<exists>na. okT (newAs vl ctx As0 n dps tps1) na"
    if n: "flatten \<Longrightarrow> 0 < n \<Longrightarrow> lifted \<and> n \<le> count_prems (strip_all_body Bi)"
      and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B" for As0 n dps tps1
  proof -
    define ro where "ro = (if lifted then rename_bvars dps (rtpairs @ tps1) Bi As0 else None)"
    define As1 where "As1 = (case ro of Some r \<Rightarrow> map (strip_apply (ren_term r) Bi) As0 | None \<Rightarrow> As0)"
    have fp: "\<exists>A'. ok (flatten_params vl n A1) A'" if "flatten" "A1 \<in> set As1" for A1
    proof -
      have "n \<le> ilength (spine_hyps A1)"
      proof (cases "0 < n")
        case True
        with n that(1) have lf: "lifted" and nc: "n \<le> count_prems (strip_all_body Bi)" by blast+
        from lr0[OF lf] obtain p Bi0 As0' where Bi: "Bi = lift_pre p Bi0"
          and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0': "As0 = map (lift_pre p) As0'"
          by (rule lifted_rule_lift_pre)
        from that(2) obtain Y where A1: "A1 = lift_pre p Y"
          by (auto simp: As1_def As0' Bi strip_apply_lift_pre[OF ok at] split: option.splits)
        note nc
        also have "count_prems (strip_all_body Bi) \<le> ilength (phyps p)"
          using count_prems_lift_pre[OF ok at] Bi by simp
        also have "\<dots> \<le> ilength (spine_hyps A1)"
          by (simp add: A1 spine_hyps_lift_pre[OF ok] ilength_eq integer_reps integer_of_nat.rep_eq)
        finally show ?thesis .
      qed (simp add: not_less order_trans[OF _ ilength_nonneg])
      then show ?thesis by (rule flatten_params_exists[OF vl])
    qed
    obtain As2 where As2: "if flatten then ok (mapM (flatten_params vl n) As1) As2 else As2 = As1"
      using ok_mapM_exI[of As1 "flatten_params vl n"] fp by (cases flatten) auto
    have "okT (newAs vl ctx As0 n dps tps1) (NewAs As2 As1 ro n)"
      using As2 by (auto simp: newAs_def ctx_def As1_def ro_def okT_handleT split: if_splits option.splits)
    then show ?thesis by blast
  qed
  show ?thesis
    unfolding newas_ok_def
  proof (intro conjI impI allI)
    assume "\<not> sp_eres sp"
    show "\<exists>na. okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps1) na" for tps1
      using ex[of 0 "rev rAs"] lr by (simp add: sp')
  next
    fix n asm tps1 assume er: "sp_eres sp" and n: "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
      and asm: "asm = asms_of sp ! (nat_of_integer n - 1)"
    have n1: "1 \<le> nat_of_integer n" using n(1) by (simp add: integer_reps)
    obtain A1 As where rA: "rev rAs = A1 # As"
      using n(2) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
      using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_def)
    have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using er by (simp add: nlift_def sp')
    have "ilength asms \<le> nlift + 1"
      by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
    moreover have "n \<le> ilength asms" using n e(2) by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
    ultimately have "n \<le> count_prems (strip_all_body Bi)" using cnt by simp
    with fl er have nn: "flatten \<Longrightarrow> 0 < n \<Longrightarrow> lifted \<and> n \<le> count_prems (strip_all_body Bi)"
      by (simp add: sp')
    have lrA: "lifted_rule smax Bi As B" if "lifted" using lr[OF that] rA by (auto dest: lifted_rule_Cons)
    show "\<exists>na. okT (newAs (sp_vl sp) (sp_ctx sp) (er_As (eres_of sp)) n
        [bc_BBi (sp_ctx sp), (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding e using ex[OF nn lrA] by (simp add: sp')
  qed
qed



subsection \<open>The new theorem can be built\<close>

text \<open>
  A term whose variables are consistent with the environment (\<^const>\<open>winv\<close>) and that is
  well-typed in the most general solution of the type environment is normalized without an
  exception, also when skipping assumptions.
\<close>

lemma norm_term_ok:
  assumes ei: "einv A K env" and wi: "winv env Y" and vY: "vtvars Y \<subseteq> tvars_env (tyenv env) \<union> A"
    and vt: "vars t \<subseteq> Y \<union> evars env" and tt: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and ty: "e \<turnstile> inst (rho0 env) t : T"
  shows "\<exists>t'. ok (norm_term env t) t'"
proof -
  note r0 = einv_rho0[OF ei]
  have wv: "wt_env (rho0 env) env" "vinv (rho0 env) env Y" using winvD[OF wi r0] by blast+
  have vk: "vok env (vars t \<union> evars env)"
    by (rule vok_mono[OF vok_winv[OF ei wi vY]]) (use vt in blast)
  have vc: "vcons (rho0 env) (vars t \<union> evars env)"
    by (rule vcons_mono[of _ "Y \<union> evars env"]) (use wv(2) vt in \<open>auto simp: vinv_def\<close>)
  from norm_term_term[OF ei vk tt wv(1) vc ty] show ?thesis by (auto simp: return_def)
qed

lemma norm_term_skip_ok:
  assumes ei: "einv A K env" and wi: "winv env Y" and vY: "vtvars Y \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "vars t \<subseteq> Y \<union> evars env \<Longrightarrow> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow>
    e \<turnstile> inst (rho0 env) t : propT \<Longrightarrow> 0 \<le> n \<Longrightarrow> n \<le> ilength (spine_hyps t) \<Longrightarrow>
    \<exists>t'. okT (norm_term_skip env n t) t'"
proof (induction t arbitrary: n e rule: measure_induct_rule[of size])
  case (less t)
  note e = einvD[OF ei]
  show ?case
  proof (cases "n = 0")
    case True
    from norm_term_ok[OF ei wi vY less.prems(1-3)] obtain t' where "ok (norm_term env t) t'" by blast
    with True show ?thesis by (subst norm_term_skip.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      then obtain U where t: "t = Const STR ''Pure.all'' U $ Abs a T b" by (auto simp: dest_all_Some)
      have di: "dest_all (inst (rho0 env) t) = Some (a, tsubst (rho0 env) T, inst (rho0 env) b)"
        by (simp add: t)
      have tb: "e\<langle>0:tsubst (rho0 env) T\<rangle> \<turnstile> inst (rho0 env) b : propT"
        by (rule typing_dest_all(5)[OF less.prems(3) di])
      have "dest_imp t = None" using t by simp
      with aTb have sh: "spine_hyps t = spine_hyps b" by (subst spine_hyps.simps) simp
      have "\<exists>b'. okT (norm_term_skip env n b) b'"
        by (rule less.IH[OF _ _ _ tb less.prems(4)]) (use less.prems(1,2,5) sh t in auto)
      then obtain b' where b': "okT (norm_term_skip env n b) b'" by blast
      have "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" using less.prems(2) t by (auto simp: ttvars_def)
      then have "norm_type (tyenv env) T = return (tnorm (tyenv env) T)"
        by (intro norm_type_ok e(6,7) tinv_tcons[OF e(2)])
      with False aTb b' show ?thesis by (subst norm_term_skip.simps) (auto simp: return_def)
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case (Some HB)
        then obtain H B where HB: "dest_imp t = Some (H, B)" by (cases HB) auto
        then obtain U where t: "t = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
        have di: "dest_imp (inst (rho0 env) t) = Some (inst (rho0 env) H, inst (rho0 env) B)"
          by (simp add: t)
        have tB: "e \<turnstile> inst (rho0 env) B : propT" by (rule typing_dest_imp(5)[OF less.prems(3) di])
        have sh: "spine_hyps t = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
        have n1: "0 \<le> n - 1" "n - 1 \<le> ilength (spine_hyps B)"
          using less.prems(4,5) False sh by (auto simp: integer_reps)
        have "\<exists>B'. okT (norm_term_skip env (n - 1) B) B'"
          by (rule less.IH[OF _ _ _ tB n1]) (use less.prems(1,2) t in auto)
        then obtain B' where "okT (norm_term_skip env (n - 1) B) B'" by blast
        with False None HB show ?thesis by (subst norm_term_skip.simps) auto
      next
        case None': None
        then have "spine_hyps t = []" using None by (subst spine_hyps.simps) simp
        with less.prems(4,5) False show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  \<^const>\<open>addth\<close> succeeds, or raises \<open>COMPOSE\<close> if instantiations of the proof state are forbidden,
  if the terms it normalizes can be normalized.
\<close>

lemma addth_ok:
  assumes tps: "\<forall>(t, u)\<in>set tps. (\<exists>t'. ok (norm_term env t) t') \<and> (\<exists>u'. ok (norm_term env u) u')"
    and BC: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). \<exists>X'. ok (norm_term env X) X'"
    and As: "\<forall>X\<in>set (na_As na). \<exists>X'. ok (norm_term env X) X'"
    and sk: "bc_lifted ctx \<Longrightarrow> above env (bc_smax ctx) \<Longrightarrow>
      \<forall>X\<in>set (na_As na). \<exists>X'. okT (norm_term_skip env (bc_nlift ctx) X) X'"
  shows "(\<exists>r. okT (addth ctx A1o na (env, tps)) r) \<or>
    (bc_match ctx \<and> (\<exists>evs. addth ctx A1o na (env, tps) = Some (evs, TErr COMPOSE)))"
proof -
  have "\<exists>tps'. ok (mapM (norm_tpair env) tps) tps'"
  proof (rule ok_mapM_exI, intro ballI)
    fix tu assume "tu \<in> set tps"
    with tps obtain t u where "tu = (t, u)" "\<exists>t'. ok (norm_term env t) t'" "\<exists>u'. ok (norm_term env u) u'"
      by (cases tu) blast
    then show "\<exists>y. ok (norm_tpair env tu) y" by (auto simp: norm_tpair_def)
  qed
  then obtain tps' where tps': "ok (mapM (norm_tpair env) tps) tps'" by blast
  show ?thesis
  proof (cases "env_is_empty env")
    case True
    then show ?thesis by (simp add: addth_def)
  next
    case False
    show ?thesis
    proof (cases "above env (bc_smax ctx)")
      case ab: True
      show ?thesis
      proof (cases "bc_lifted ctx")
        case True
        from okT_mapT_exI[OF sk[OF True ab]] obtain As' where
          "okT (mapT (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'" by blast
        then show ?thesis using False ab True tps' by (auto simp: addth_def)
      next
        case nl: False
        from ok_mapM_exI[OF As] obtain As' where "ok (mapM (norm_term env) (na_As na)) As'" by blast
        then show ?thesis using False ab nl tps' by (auto simp: addth_def)
      qed
    next
      case nab: False
      show ?thesis
      proof (cases "bc_match ctx")
        case True
        then show ?thesis using False nab tps'
          by (auto simp: addth_def raiseT_def bindT_def liftMT_def liftWT_def liftM_def)
      next
        case nm: False
        have "\<forall>X\<in>set (bc_Bs ctx @ na_As na). \<exists>X'. ok (norm_term env X) X'" using As BC by auto
        from ok_mapM_exI[OF this] obtain Hs where "ok (mapM (norm_term env) (bc_Bs ctx @ na_As na)) Hs"
          by blast
        moreover from BC obtain C' where "ok (norm_term env (bc_C ctx)) C'" by blast
        ultimately show ?thesis using False nab nm tps' by (auto simp: addth_def)
      qed
    qed
  qed
qed

end

end
