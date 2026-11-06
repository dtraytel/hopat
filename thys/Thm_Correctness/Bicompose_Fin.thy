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

end

end
