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
    (bc_match (sp_ctx sp) \<and> (\<exists>evs. addth (sp_ctx sp) A na (env', tps) = Some (evs, Err COMPOSE))))"

text \<open>Elim-resolution with the remaining assumptions terminates.\<close>

lemma tryasms_ok:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp" and er: "sp_eres sp" and nok: "newas_ok sp"
  shows "ops = unify_ops (sp_cfg sp) (sp_vl sp) \<Longrightarrow> ctx = sp_ctx sp \<Longrightarrow> er = eres_of sp \<Longrightarrow>
    1 \<le> n \<Longrightarrow> asms = drop (nat_of_integer n - 1) (asms_of sp) \<Longrightarrow>
    \<exists>s. okT (tryasms ops ctx er asms n) s \<and> bmu sp s < bmu sp (BS_Tryasms ctx er asms n)"
proof (induction ops ctx er asms n rule: tryasms.induct)
  case 1
  then show ?case by (simp add: returnW_def)
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
        using True us r na eqs by (auto simp: Let_def unify_ops_def returnW_def)
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
    have "bpull ops BS_Empty = returnW None" by (subst bpull.simps) simp
    with BS_Empty show ?thesis by (intro exI[of _ "[]"] bevals.Nil) (simp add: returnW_def)
  next
    case (BS_Its ctx A na xq yq)
    from less.prems[unfolded BS_Its] obtain tus where ctx: "ctx = sp_ctx sp" and its: "itsok sp A na tus"
      and uq: "uqinv sp tus xq" and byq: "binv sp yq"
      by (auto elim: binv_ItsE)
    have bp: "bpull ops s = do {
        r \<leftarrow> (case xq of UQ_Cell c \<Rightarrow> returnW (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us);
        case r of
          None \<Rightarrow> bpull ops yq
        | Some (et, us') \<Rightarrow>
            handleW
              (do {th \<leftarrow> addth ctx A na et; returnW (Some (th, BS_Its ctx A na (UQ_Seq us') yq))})
              (\<lambda>e. case e of COMPOSE \<Rightarrow> bpull ops (BS_Its ctx A na (UQ_Seq us') yq) | _ \<Rightarrow> raiseW e)}"
      unfolding BS_Its by (subst bpull.simps) simp
    text \<open>The next unifier, if any.\<close>
    obtain rr where rr: "okT (case xq of UQ_Cell c \<Rightarrow> returnW (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) rr"
      and el: "\<And>env' tps us'. rr = Some ((env', tps), us') \<Longrightarrow>
        fin (sp_cfg sp) us' (ures (sp_env sp) tus) \<and> ures (sp_env sp) tus (El_R env' tps) \<and>
        bmu sp (BS_Its ctx A na (UQ_Seq us') yq) < bmu sp s"
      and nn: "rr = None \<Longrightarrow> bmu sp yq < bmu sp s"
    proof (cases xq)
      case (UQ_Cell c)
      obtain env' tps us' where c: "c = ((env', tps), us')" by (cases c) auto
      show thesis
        by (rule that[of "Some c"]) (use uq UQ_Cell c BS_Its in \<open>auto simp: uqinv_def returnW_def\<close>)
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
        using rr None unfolding bp by auto
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
        | evs where "addth ctx A na (env', tps) = Some (evs, Err COMPOSE)"
        unfolding results_ok_def by blast
      then show ?thesis
      proof cases
        case 1
        have "okT (bpull ops s) (Some (th, ?s'))"
          using rr c 1 unfolding bp by (auto simp: okW_handleW returnW_def)
        from bevals.Cons[OF this rs] show ?thesis by blast
      next
        case 2
        have eqv: "okT (bpull ops s) x \<longleftrightarrow> okT (bpull ops ?s') x" for x
          using rr c 2 unfolding bp
          by (auto simp: okW_handleW bindW_def split: option.splits xres.splits)
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
      using t unfolding BS_Tryasms by (subst bpull.simps) auto
    from less.hyps[OF _ b''] m BS_Tryasms obtain rs where "bevals ops s'' rs" by auto
    from bevals_cong[OF eqv this] show ?thesis by blast
  qed
qed



subsection \<open>The renaming of the new premises\<close>

text \<open>
  \<^const>\<open>del_clashing\<close> keeps renamings whose targets are distinct and differ from the unchanged
  names, which include the sources of the dropped renamings.
\<close>

lemma del_round_clash: "del_round xs ys ps qs clash = (c, xs', qs') \<Longrightarrow> clash \<Longrightarrow> c"
  by (induction xs ys ps qs clash rule: del_round.induct) (auto split: if_splits)

lemma del_round_noclash:
  "del_round xs ys ps qs clash = (False, xs', qs') \<Longrightarrow>
    xs' = xs \<and> qs' = rev ps @ qs \<and> (\<forall>(x, y)\<in>set ps. y \<notin> set ys) \<and> distinct (map snd ps)"
proof (induction xs ys ps qs clash rule: del_round.induct)
  case (2 xs ys x y ps qs clash)
  show ?case
  proof (cases "y \<in> set ys")
    case True
    with "2.prems" have "del_round (x # xs) (x # ys) ps qs True = (False, xs', qs')" by simp
    from del_round_clash[OF this] show ?thesis by simp
  next
    case False
    with "2.prems" have "del_round xs (y # ys) ps ((x, y) # qs) clash = (False, xs', qs')" by simp
    from "2.IH"(2)[OF False this] False show ?thesis by auto
  qed
qed simp

lemma del_round_cover:
  "del_round xs ys ps qs clash = (c, xs', qs') \<Longrightarrow>
    set xs \<subseteq> set xs' \<and> set qs \<subseteq> set qs' \<and> (\<forall>(x, y)\<in>set ps. (x, y) \<in> set qs' \<or> x \<in> set xs')"
proof (induction xs ys ps qs clash rule: del_round.induct)
  case (2 xs ys x y ps qs clash)
  show ?case
  proof (cases "y \<in> set ys")
    case True
    with "2.prems" have "del_round (x # xs) (x # ys) ps qs True = (c, xs', qs')" by simp
    from "2.IH"(1)[OF True this] show ?thesis by auto
  next
    case False
    with "2.prems" have "del_round xs (y # ys) ps ((x, y) # qs) clash = (c, xs', qs')" by simp
    from "2.IH"(2)[OF False this] show ?thesis by auto
  qed
qed simp

lemma del_clashing_props:
  "\<exists>xs'. set xs \<subseteq> set xs' \<and> set (del_clashing xs ps) \<subseteq> set ps \<and>
    (\<forall>(x, y)\<in>set ps. (x, y) \<in> set (del_clashing xs ps) \<or> x \<in> set xs') \<and>
    (\<forall>(x, y)\<in>set (del_clashing xs ps). y \<notin> set xs') \<and> distinct (map snd (del_clashing xs ps))"
proof (induction xs ps rule: del_clashing.induct)
  case (1 xs ps)
  obtain c xs1 qs1 where r: "del_round xs xs ps [] False = (c, xs1, qs1)"
    by (cases "del_round xs xs ps [] False")
  show ?case
  proof (cases c)
    case True
    have d: "del_clashing xs ps = del_clashing xs1 qs1" using r True by (subst del_clashing.simps) simp
    from "1.IH"[OF r[symmetric] refl True] obtain xs' where
      ih: "set xs1 \<subseteq> set xs'" "set (del_clashing xs1 qs1) \<subseteq> set qs1"
        "\<forall>(x, y)\<in>set qs1. (x, y) \<in> set (del_clashing xs1 qs1) \<or> x \<in> set xs'"
        "\<forall>(x, y)\<in>set (del_clashing xs1 qs1). y \<notin> set xs'" "distinct (map snd (del_clashing xs1 qs1))"
      by blast
    note cv = del_round_cover[OF r]
    have "set qs1 \<subseteq> set ps" using set_del_round[OF r] by simp
    with ih cv show ?thesis unfolding d by (intro exI[of _ xs']) blast
  next
    case False
    have r': "del_round xs xs ps [] False = (False, xs1, qs1)" using r False by simp
    from del_round_noclash[OF r'] have
      nc: "xs1 = xs" "qs1 = rev ps" "\<forall>(x, y)\<in>set ps. y \<notin> set xs" "distinct (map snd ps)" by simp_all
    have d: "del_clashing xs ps = rev ps" using r False nc(2) by (subst del_clashing.simps) simp
    show ?thesis unfolding d using nc(3,4) by (intro exI[of _ xs]) (auto simp: rev_map[symmetric])
  qed
qed

lemma distinct_fst_functional:
  "(x, y1) \<in> set (distinct_fst ps) \<Longrightarrow> (x, y2) \<in> set (distinct_fst ps) \<Longrightarrow> y1 = y2"
proof (induction ps rule: distinct_fst.induct)
  case (2 x' y' ps)
  then show ?case using set_distinct_fst[of "filter (\<lambda>p. fst p \<noteq> x') ps"] by auto
qed simp

lemma fst_distinct_fst: "fst ` set (distinct_fst ps) = fst ` set ps"
proof (induction ps rule: distinct_fst.induct)
  case (2 x y ps)
  then show ?case by auto
qed simp

lemma ren_name_functional:
  assumes "\<forall>x y1 y2. (x, y1) \<in> set tab \<longrightarrow> (x, y2) \<in> set tab \<longrightarrow> y1 = y2" "(x, y) \<in> set tab"
  shows "ren_name tab x = y"
proof -
  from weak_map_of_SomeI[OF assms(2)] obtain y' where "map_of tab x = Some y'" by blast
  with assms show ?thesis by (auto simp: ren_name_def dest: map_of_SomeD)
qed

lemma ren_name_none:
  assumes "x \<notin> fst ` set tab"
  shows "ren_name tab x = x"
proof -
  from assms have "map_of tab x = None" by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: ren_name_def)
qed

lemma set_fold_add_var_names_pairs:
  "set (fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tps xs) =
    (\<Union>(t, u)\<in>set tps. vnames t \<union> vnames u) \<union> set xs"
proof (induction tps arbitrary: xs)
  case (Cons p tps)
  obtain t u where "p = (t, u)" by (cases p)
  with Cons show ?case by (simp add: set_add_var_names Un_ac)
qed simp

lemma set_fold_add_var_names_fst:
  "set (fold (add_var_names \<circ> fst) dps xs) = (\<Union>(t, u)\<in>set dps. vnames t) \<union> set xs"
proof (induction dps arbitrary: xs)
  case (Cons p dps)
  obtain t u where "p = (t, u)" by (cases p)
  with Cons show ?case by (simp add: set_add_var_names Un_ac)
qed simp

lemma set_fold_add_var_names_lifted:
  "set (fold (add_var_names \<circ> strip_lifted B) As xs) = (\<Union>A\<in>set As. vnames (strip_lifted B A)) \<union> set xs"
  by (induction As arbitrary: xs) (auto simp: set_add_var_names)

text \<open>
  The renaming of \<^const>\<open>rename_bvs\<close> is injective on the names of the variables of the premises,
  and its targets occur neither on the left of the disagreement pairs nor in the flex-flex pairs.
\<close>

lemma rename_bvs_inj:
  "inj_on (ren_name (fst (rename_bvs dpairs tpairs B As))) (\<Union>A\<in>set As. vnames (strip_lifted B A))"
    (is "inj_on (ren_name ?tab) ?N")
  and rename_bvs_target:
  "ren_name (fst (rename_bvs dpairs tpairs B As)) x \<noteq> x \<Longrightarrow>
    ren_name (fst (rename_bvs dpairs tpairs B As)) x \<notin>
      (\<Union>(t, u)\<in>set dpairs. vnames t) \<union> (\<Union>(t, u)\<in>set tpairs. vnames t \<union> vnames u)"
proof -
  let ?al = "foldr match_bvars dpairs []"
  let ?unknowns = "fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tpairs
    (fold (add_var_names \<circ> fst) dpairs [])"
  let ?unknowns' = "fold (add_var_names \<circ> strip_lifted B) As []"
  let ?al' = "distinct_fst (filter (\<lambda>(x, y). \<not> (x \<notin> set ?unknowns' \<or> x \<in> set ?unknowns \<or> y \<in> set ?unknowns)) ?al)"
  let ?unch = "filter (\<lambda>x. map_of ?al' x = None) ?unknowns'"
  let ?qs = "del_clashing ?unch ?al'"
  have U: "set ?unknowns = (\<Union>(t, u)\<in>set dpairs. vnames t) \<union> (\<Union>(t, u)\<in>set tpairs. vnames t \<union> vnames u)"
    by (simp add: set_fold_add_var_names_pairs set_fold_add_var_names_fst Un_ac)
  have N: "set ?unknowns' = ?N" by (simp add: set_fold_add_var_names_lifted)
  have "inj_on (ren_name ?tab) ?N \<and> (ren_name ?tab x \<noteq> x \<longrightarrow> ren_name ?tab x \<notin> set ?unknowns)"
  proof (cases "?al = []")
    case True
    then have "?tab = []" by (simp add: rename_bvs_def)
    moreover have "ren_name [] = (\<lambda>x. x)" by (simp add: ren_name_def fun_eq_iff)
    ultimately show ?thesis by simp
  next
    case False
    define al' where "al' = ?al'"
    define unch where "unch = filter (\<lambda>x. map_of al' x = None) ?unknowns'"
    define qs where "qs = del_clashing unch al'"
    have tab: "?tab = distinct_fst qs" using False by (simp add: rename_bvs_def Let_def al'_def unch_def qs_def)
    from del_clashing_props[of unch al', folded qs_def] obtain xs' where
      p: "set unch \<subseteq> set xs'" "set qs \<subseteq> set al'" "\<forall>(x, y)\<in>set al'. (x, y) \<in> set qs \<or> x \<in> set xs'"
        "\<forall>(x, y)\<in>set qs. y \<notin> set xs'" "distinct (map snd qs)"
      by blast
    have fq: "\<forall>x y1 y2. (x, y1) \<in> set qs \<longrightarrow> (x, y2) \<in> set qs \<longrightarrow> y1 = y2"
    proof (intro allI impI)
      fix x y1 y2 assume "(x, y1) \<in> set qs" "(x, y2) \<in> set qs"
      with p(2) have "(x, y1) \<in> set al'" "(x, y2) \<in> set al'" by auto
      then show "y1 = y2" unfolding al'_def by (rule distinct_fst_functional)
    qed
    have ft: "\<forall>x y1 y2. (x, y1) \<in> set ?tab \<longrightarrow> (x, y2) \<in> set ?tab \<longrightarrow> y1 = y2"
      unfolding tab by (blast intro: distinct_fst_functional)
    have ren_in: "ren_name ?tab x = y" if "(x, y) \<in> set qs" for x y
    proof -
      from that have "x \<in> fst ` set ?tab" unfolding tab fst_distinct_fst by force
      then obtain y' where y': "(x, y') \<in> set ?tab" by force
      then have "(x, y') \<in> set qs" unfolding tab using set_distinct_fst by blast
      with fq that have "y' = y" by blast
      with ren_name_functional[OF ft y'] show ?thesis by simp
    qed
    have ren_out: "ren_name ?tab x = x" if "x \<notin> fst ` set qs" for x
      using that by (intro ren_name_none) (simp add: tab fst_distinct_fst)
    have cov: "x \<in> set xs'" if "x \<in> ?N" "x \<notin> fst ` set qs" for x
    proof (cases "map_of al' x")
      case None
      with that(1) N have "x \<in> set unch" by (simp add: unch_def)
      with p(1) show ?thesis by blast
    next
      case (Some y)
      then have "(x, y) \<in> set al'" by (rule map_of_SomeD)
      with p(3) that(2) show ?thesis by force
    qed
    have "inj_on (ren_name ?tab) ?N"
    proof (rule inj_onI)
      fix x1 x2 assume x: "x1 \<in> ?N" "x2 \<in> ?N" and eq: "ren_name ?tab x1 = ren_name ?tab x2"
      show "x1 = x2"
      proof (cases "x1 \<in> fst ` set qs"; cases "x2 \<in> fst ` set qs")
        assume "x1 \<in> fst ` set qs" "x2 \<in> fst ` set qs"
        then obtain y1 y2 where q: "(x1, y1) \<in> set qs" "(x2, y2) \<in> set qs" by force
        with eq ren_in have "y1 = y2" by simp
        have "inj_on snd (set qs)" using p(5) by (simp add: distinct_map)
        from inj_onD[OF this _ q] \<open>y1 = y2\<close> show ?thesis by simp
      next
        assume a: "x1 \<in> fst ` set qs" "x2 \<notin> fst ` set qs"
        then obtain y1 where q: "(x1, y1) \<in> set qs" by force
        with eq ren_in ren_out a(2) have "y1 = x2" by simp
        with p(4) q cov[OF x(2) a(2)] show ?thesis by blast
      next
        assume a: "x1 \<notin> fst ` set qs" "x2 \<in> fst ` set qs"
        then obtain y2 where q: "(x2, y2) \<in> set qs" by force
        with eq ren_in ren_out a(1) have "y2 = x1" by simp
        with p(4) q cov[OF x(1) a(1)] show ?thesis by blast
      next
        assume "x1 \<notin> fst ` set qs" "x2 \<notin> fst ` set qs"
        with eq ren_out show ?thesis by simp
      qed
    qed
    moreover have "ren_name ?tab x \<notin> set ?unknowns" if "ren_name ?tab x \<noteq> x"
    proof -
      from ren_name_neq[OF that] obtain y where "(x, y) \<in> set ?tab" by blast
      then have xy: "(x, y) \<in> set al'" using p(2) set_distinct_fst unfolding tab by blast
      with ren_name_functional[OF ft] \<open>(x, y) \<in> set ?tab\<close> have "ren_name ?tab x = y" by blast
      moreover from xy have "y \<notin> set ?unknowns" unfolding al'_def using set_distinct_fst by fastforce
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
  then show "inj_on (ren_name ?tab) ?N"
    "ren_name ?tab x \<noteq> x \<Longrightarrow> ren_name ?tab x \<notin>
      (\<Union>(t, u)\<in>set dpairs. vnames t) \<union> (\<Union>(t, u)\<in>set tpairs. vnames t \<union> vnames u)"
    using U by blast+
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

lemma okT_mapT_exI: "\<forall>x\<in>set xs. \<exists>y. okT (f x) y \<Longrightarrow> \<exists>ys. okT (mapW f xs) ys"
  by (induction xs) (auto simp: returnW_def)

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
          by (simp add: A1 spine_hyps_lift_pre[OF ok] ilength_eq integer_reps)
        finally show ?thesis .
      qed (simp add: not_less order_trans[OF _ ilength_nonneg])
      then show ?thesis by (rule flatten_params_exists[OF vl])
    qed
    obtain As2 where As2: "if flatten then ok (mapM (flatten_params vl n) As1) As2 else As2 = As1"
      using ok_mapM_exI[of As1 "flatten_params vl n"] fp by (cases flatten) auto
    have "okT (newAs vl ctx As0 n dps tps1) (NewAs As2 As1 ro n)"
      using As2 by (auto simp: newAs_def ctx_def As1_def ro_def okW_handleW split: if_splits option.splits)
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
    moreover have "n \<le> ilength asms" using n e(2) by (simp add: ilength_eq integer_reps)
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
    (bc_match ctx \<and> (\<exists>evs. addth ctx A1o na (env, tps) = Some (evs, Err COMPOSE)))"
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
          "okT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'" by blast
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
          by (auto simp: addth_def raiseW_def bindW_def liftMT_def liftWT_def liftM_def)
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



subsection \<open>The new premises of a call\<close>

lemma ttvars_list_forall_eq: "ttvars (list_forall ps Y) = btvars ps \<union> ttvars Y"
  by (induction ps Y rule: list_forall.induct) (auto simp: btvars_def all_const_def all_type_def ttvars_def propT_def)

lemma strip_params_typs: "(a, T) \<in> set (strip_params A) \<Longrightarrow> T \<in> typs A"
proof (induction A rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    then obtain U where A: "A = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
    from less.prems have "(a, T) \<in> set (strip_params B)" by (simp add: strip_params_imp[OF HB])
    from less.IH[OF _ this] A show ?thesis by simp
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a' T' b where aTb: "dest_all A = Some (a', T', b)" by (cases aTb) auto
      then obtain U where A: "A = Const STR ''Pure.all'' U $ Abs a' T' b" by (auto simp: dest_all_Some)
      from less.prems have "(a, T) = (a', T') \<or> (a, T) \<in> set (strip_params b)"
        by (simp add: strip_params_all[OF None aTb])
      with less.IH[of b] A show ?thesis by auto
    next
      case None': None
      with less.prems None show ?thesis by (simp add: strip_params_other)
    qed
  qed
qed

lemma flatten_params_vars:
  assumes "ok (flatten_params vl n A) A'" "\<And>xs. length (vl xs) = length xs"
  shows "vars A' \<subseteq> vars A" "ttvars A' \<subseteq> ttvars A"
proof -
  have l: "length (vl (map fst (strip_params A))) = length (strip_params A)"
    using assms(2)[of "map fst (strip_params A)"] by simp
  obtain A'' where r: "ok (remove_params (ilength (strip_params A)) n A) A''"
    and A': "A' = list_forall (zip (vl (map fst (strip_params A))) (map snd (strip_params A))) A''"
    and sv: "map snd (zip (vl (map fst (strip_params A))) (map snd (strip_params A))) = map snd (strip_params A)"
    by (rule flatten_params_ok[OF assms(1) l])
  note rv = remove_params_vars[OF r]
  show "vars A' \<subseteq> vars A" using rv by (simp add: A')
  have "btvars (zip (vl (map fst (strip_params A))) (map snd (strip_params A))) \<subseteq> ttvars A"
  proof
    fix v assume "v \<in> btvars (zip (vl (map fst (strip_params A))) (map snd (strip_params A)))"
    then obtain a T where aT: "(a, T) \<in> set (zip (vl (map fst (strip_params A))) (map snd (strip_params A)))"
      and v: "v \<in> tvars T" by (auto simp: btvars_def)
    from set_zip_rightD[OF aT] obtain a' where "(a', T) \<in> set (strip_params A)" by auto
    with v have "(a', T) \<in> set (strip_params A)" "v \<in> tvars T" by blast+
    with strip_params_typs show "v \<in> ttvars A" by (auto simp: ttvars_def)
  qed
  moreover have "ttvars A'' \<subseteq> ttvars A"
    using rv by (auto simp: ttvars_def implies_def imp_type_def propT_def)
  ultimately show "ttvars A' \<subseteq> ttvars A" by (simp add: A' ttvars_list_forall_eq)
qed

lemma remove_params_spine_len:
  "ok (remove_params j n A) A' \<Longrightarrow> length (spine_hyps A) \<le> length (spine_hyps A') + (if 0 < n then 1 else 0)"
proof (induction j n A arbitrary: A' rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp show ?thesis by (subst (asm) remove_params.simps) simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      have sh: "spine_hyps A = H # spine_hyps B" using HB by (subst spine_hyps.simps) simp
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True this] True sh show ?thesis by simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits xres.splits)
        have sh': "spine_hyps A' = incr_boundvars j H # spine_hyps B'"
          using A' by (subst spine_hyps.simps) (simp add: implies_def)
        from "1.IH"(3)[OF False HB refl n1 B'] sh sh' n1 show ?thesis
          by (auto split: if_splits)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        with rp False None have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have "spine_hyps A = spine_hyps b" using None aTb by (subst spine_hyps.simps) simp
        with "1.IH"(1)[OF False None aTb refl refl r] show ?thesis by simp
      next
        case None': None
        with rp False None show ?thesis by (subst (asm) remove_params.simps) (auto split: if_splits)
      qed
    qed
  qed
qed

lemma flatten_params_spine_len:
  "ok (flatten_params vl n A) A' \<Longrightarrow> length (spine_hyps A) \<le> length (spine_hyps A') + (if 0 < n then 1 else 0)"
  by (auto simp: flatten_params_def Let_def spine_hyps_list_forall dest!: remove_params_spine_len)

lemma typs_lift_pre_ren: "typs (lift_pre p (ren_term r X)) = typs (lift_pre p X)"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) auto
qed simp

lemma vars_lift_pre_ren:
  "vars (lift_pre p (ren_term r X)) = pvars p \<union> (\<lambda>v. ((ren_name (fst r) (fst (fst v)), snd (fst v)), snd v)) ` vars X"
  by (simp add: vars_lift_pre vars_ren_term)

text \<open>The structure of the new premises: the renamed premises are flattened.\<close>

lemma newAs_struct:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
  shows "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    "na_oldAs na = As0 \<or> (bc_lifted ctx \<and> na_oldAs na =
      map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0)) (bc_Bi ctx)) As0)"
proof -
  have h: "\<not> okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseW (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseW e) y" for e and y :: newas
    by (auto simp: raiseW_def split: texn.splits uexn.splits exn.splits)
  from assms show "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    "na_oldAs na = As0 \<or> (bc_lifted ctx \<and> na_oldAs na =
      map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0)) (bc_Bi ctx)) As0)"
    unfolding newAs_def
    by (auto simp: okW_handleW h ok_mapM list.rel_eq rename_bvars_def Let_def split: if_splits option.splits)
qed


text \<open>
  The new premises are well-typed, their type variables are those of the premises \<open>As0\<close> of the
  rule, and an index-preserving map \<open>h\<close> (undoing the renaming) maps their variables to variables
  of \<open>As0\<close>. It is the identity on the variables of the proof state, on the left of the
  disagreement pairs and in the flex-flex pairs. If the rule is lifted, the new premises have
  the assumptions of the subgoal, but one if it is deleted.
\<close>

lemma newAs_props:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" and wf: "\<forall>A\<in>set As0. wtp A"
    and vl: "\<And>xs. length (vl xs) = length xs"
  obtains h where
    "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
    "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> h x = x"
    "\<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x"
    "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
    "bc_lifted ctx \<Longrightarrow> \<forall>X\<in>set (na_As na).
      count_prems (strip_all_body (bc_Bi ctx)) \<le> ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)"
    "\<not> bc_lifted ctx \<Longrightarrow> \<forall>x. h x = x"
proof -
  let ?m = "bc_smax ctx" and ?d = "if 0 < n \<and> bc_flatten ctx then 1 else 0 :: nat"
  note st = newAs_struct[OF na]
  text \<open>Flattening:\<close>
  have step: "vars A' \<subseteq> vars A1 \<and> ttvars A' \<subseteq> ttvars A1 \<and> (wtp A1 \<longrightarrow> wtp A') \<and>
      length (spine_hyps A1) \<le> length (spine_hyps A') + ?d"
    if f: "if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A'" for A1 A'
  proof (cases "bc_flatten ctx")
    case True
    with f have fp: "ok (flatten_params vl n A1) A'" by simp
    have l: "length (vl (map fst (strip_params A1))) = length (strip_params A1)"
      using vl[of "map fst (strip_params A1)"] by simp
    have "wtp A'" if w1: "wtp A1"
      by (rule wtpI[OF _ flatten_params_typing[OF fp l wtpD(2)[OF w1]]])
        (use flatten_params_loose[OF fp l] wtpD(1)[OF w1] in \<open>simp add: closed_def\<close>)
    with flatten_params_vars[OF fp vl] flatten_params_spine_len[OF fp] True show ?thesis by simp
  next
    case False
    with f show ?thesis by simp
  qed
  have bk: "\<exists>A1\<in>set (na_oldAs na). vars A' \<subseteq> vars A1 \<and> ttvars A' \<subseteq> ttvars A1 \<and> (wtp A1 \<longrightarrow> wtp A') \<and>
      length (spine_hyps A1) \<le> length (spine_hyps A') + ?d" if "A' \<in> set (na_As na)" for A'
    using list_all2_ex2[OF st(1) that] step by blast
  text \<open>The spine of the premises before flattening:\<close>
  have sp_old: "count_prems (strip_all_body (bc_Bi ctx)) \<le> ilength (spine_hyps A1)"
    if lf: "bc_lifted ctx" and A1: "A1 \<in> set (na_oldAs na)" for A1
  proof -
    from lr[OF lf] obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      by (rule lifted_rule_lift_pre)
    have "\<exists>Y. A1 = lift_pre p Y"
      using st(2) A1 by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
    then have "length (phyps p) \<le> length (spine_hyps A1)" by (auto simp: spine_hyps_lift_pre[OF ok])
    then have "ilength (phyps p) \<le> ilength (spine_hyps A1)"
      by (simp add: ilength_eq integer_reps)
    with count_prems_lift_pre[OF ok at] Bi show ?thesis by simp
  qed
  text \<open>The premises before flattening, and the map \<open>h\<close>:\<close>
  obtain h where
    o1: "\<forall>A1\<in>set (na_oldAs na). wtp A1 \<and> ttvars A1 \<subseteq> (\<Union>A\<in>set As0. ttvars A)" and
    o2: "\<forall>A1\<in>set (na_oldAs na). \<forall>(x, T)\<in>vars A1. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x" and
    o3: "\<forall>x. snd x \<le> ?m \<longrightarrow> h x = x" and
    o4: "\<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x" and
    o5: "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" and
    o6: "\<not> bc_lifted ctx \<longrightarrow> (\<forall>x. h x = x)"
  proof (cases "na_oldAs na = As0")
    case True
    show thesis by (rule that[of "\<lambda>x. x"]) (use True wf in auto)
  next
    case False
    with st(2) have lf: "bc_lifted ctx" and
      old: "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0))
        (bc_Bi ctx)) As0" by blast+
    let ?r = "rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0"
    let ?ren = "ren_name (fst ?r)"
    let ?N = "\<Union>A\<in>set As0. vnames (strip_lifted (bc_Bi ctx) A)"
    let ?U = "(\<Union>(t, u)\<in>set dps. vnames t) \<union> (\<Union>(t, u)\<in>set (bc_rtpairs ctx @ tps1). vnames t \<union> vnames u)"
    from lr[OF lf] obtain p Bi0 As0' B0 where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      and above: "\<forall>X\<in>insert B0 (set As0'). \<forall>v\<in>vars X. ?m < snd (fst v)"
      by (rule lifted_rule_lift_pre)
    have N: "?N = (\<Union>X\<in>set As0'. vnames X)"
      by (simp add: As0 Bi strip_lifted_lift_pre[OF ok at])
    have inj: "inj_on ?ren ?N" by (rule rename_bvs_inj)
    note tgt = rename_bvs_target[of dps "bc_rtpairs ctx @ tps1" "bc_Bi ctx" As0]
    have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> ?m"
      using ib Bi by (auto simp: ibelow_def vars_lift_pre)
    have old': "na_oldAs na = map (\<lambda>X. lift_pre p (ren_term ?r X)) As0'"
      using old As0 Bi strip_apply_lift_pre[OF ok at] by simp
    define h where "h = (\<lambda>(nm, i). if ?m < i \<and> nm \<in> ?ren ` ?N then (the_inv_into ?N ?ren nm, i) else (nm, i))"
    have h_snd: "snd (h x) = snd x" for x by (cases x) (simp add: h_def)
    have h_id: "h x = x" if "snd x \<le> ?m \<or> fst x \<in> ?U" for x
    proof -
      obtain nm i where x: "x = (nm, i)" by (cases x)
      show ?thesis
      proof (cases "?m < i \<and> nm \<in> ?ren ` ?N")
        case True
        then obtain y where y: "y \<in> ?N" "nm = ?ren y" by blast
        with that True x have "?ren y \<in> ?U" by auto
        with tgt have "?ren y = y" by blast
        with y the_inv_into_f_f[OF inj y(1)] True show ?thesis by (simp add: h_def x)
      next
        case False
        show ?thesis unfolding x h_def case_prod_conv if_not_P[OF False] by (rule refl)
      qed
    qed
    have h_ren: "h (?ren y, i) = (y, i)" if "y \<in> ?N" "?m < i" for y i
      using that by (auto simp: h_def the_inv_into_f_f[OF inj])
    show thesis
    proof (rule that[of h])
      show "\<forall>A1\<in>set (na_oldAs na). wtp A1 \<and> ttvars A1 \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
        using wf by (auto simp: old' As0 wtp_lift_pre_ren ttvars_def typs_lift_pre_ren)
      show "\<forall>A1\<in>set (na_oldAs na). \<forall>(x, T)\<in>vars A1. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
      proof (intro ballI, clarify)
        fix A1 x T assume A1: "A1 \<in> set (na_oldAs na)" and xT: "(x, T) \<in> vars A1"
        from A1 obtain X where X: "X \<in> set As0'" "A1 = lift_pre p (ren_term ?r X)" by (auto simp: old')
        have sh: "snd (h x) = snd x" by (rule h_snd)
        from xT X(2) consider "(x, T) \<in> pvars p" | y i where "((y, i), T) \<in> vars X" "x = (?ren y, i)"
          by (auto simp: vars_lift_pre_ren)
        then show "(h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
        proof cases
          case 1
          with pv have "h x = x" by (intro h_id) auto
          with 1 X(1) sh show ?thesis by (auto simp: As0 vars_lift_pre)
        next
          case 2
          have yN: "y \<in> ?N" using 2(1) X(1) N by force
          have "?m < i" using above X(1) 2(1) by fastforce
          with 2(2) yN have "h x = (y, i)" by (simp add: h_ren)
          with 2(1) X(1) sh show ?thesis by (auto simp: As0 vars_lift_pre)
        qed
      qed
      show "\<forall>x. snd x \<le> ?m \<longrightarrow> h x = x" using h_id by blast
      show "\<not> bc_lifted ctx \<longrightarrow> (\<forall>x. h x = x)" using lf by blast
      show "\<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x"
      proof (intro ballI, clarify)
        fix t u x T assume tu: "(t, u) \<in> set dps" and xT: "(x, T) \<in> vars t"
        have "fst x \<in> vnames t" using xT by (rule rev_image_eqI) simp
        then have "fst x \<in> (\<Union>(t, u)\<in>set dps. vnames t)" using tu by (intro UN_I[of "(t, u)"]) simp_all
        then show "h x = x" by (intro h_id disjI2 UnI1)
      qed
      show "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
      proof (intro ballI, clarify)
        fix t u x T assume tu: "(t, u) \<in> set (bc_rtpairs ctx @ tps1)" and xT: "(x, T) \<in> vars t \<union> vars u"
        have "fst x \<in> vnames t \<union> vnames u" using xT by (auto intro: rev_image_eqI)
        then have "fst x \<in> (\<Union>(t, u)\<in>set (bc_rtpairs ctx @ tps1). vnames t \<union> vnames u)"
          using tu by (intro UN_I[of "(t, u)"]) simp_all
        then show "h x = x" by (intro h_id disjI2 UnI2)
      qed
    qed
  qed
  show thesis
  proof (rule that[OF _ _ o3 o4 o5])
    show "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    proof
      fix X assume X: "X \<in> set (na_As na)"
      from bk[OF X] obtain A1 where "A1 \<in> set (na_oldAs na)" "ttvars X \<subseteq> ttvars A1" "wtp A1 \<longrightarrow> wtp X"
        by blast
      with o1 show "wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)" by blast
    qed
    show "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
    proof
      fix X assume X: "X \<in> set (na_As na)"
      from bk[OF X] obtain A1 where A1: "A1 \<in> set (na_oldAs na)" and sub: "vars X \<subseteq> vars A1" by blast
      have o: "\<forall>(x, T)\<in>vars A1. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
        by (rule bspec[OF o2 A1])
      show "\<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x"
      proof (intro ballI, clarify)
        fix x T assume "(x, T) \<in> vars X"
        with sub have "(x, T) \<in> vars A1" by blast
        with o show "(h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x" by blast
      qed
    qed
    show "\<forall>X\<in>set (na_As na). count_prems (strip_all_body (bc_Bi ctx)) \<le> ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)"
      if lf: "bc_lifted ctx"
    proof
      fix X assume X: "X \<in> set (na_As na)"
      from bk[OF X] obtain A1 where A1: "A1 \<in> set (na_oldAs na)"
        and l: "length (spine_hyps A1) \<le> length (spine_hyps X) + ?d" by blast
      have "ilength (spine_hyps A1) \<le> ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)"
        using l by (simp add: ilength_eq integer_reps split: if_splits)
      with sp_old[OF lf A1] show "count_prems (strip_all_body (bc_Bi ctx)) \<le>
        ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)" by simp
    qed
    show "\<forall>x. h x = x" if "\<not> bc_lifted ctx" using o6 that by blast
  qed
qed

lemma newAs_oldAs_wtp:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and wf: "\<forall>A\<in>set As0. wtp A"
  shows "\<forall>A1\<in>set (na_oldAs na). wtp A1"
proof (cases "na_oldAs na = As0")
  case True
  with wf show ?thesis by simp
next
  case False
  with newAs_struct(2)[OF na] have lf: "bc_lifted ctx" and
    old: "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0))
      (bc_Bi ctx)) As0" by blast+
  from lr[OF lf] obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
    and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
    by (rule lifted_rule_lift_pre)
  have old': "na_oldAs na = map (\<lambda>X. lift_pre p (ren_term (rename_bvs dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0) X)) As0'"
    using old As0 Bi strip_apply_lift_pre[OF ok at] by simp
  show ?thesis using wf by (auto simp: old' As0 wtp_lift_pre_ren)
qed


subsection \<open>The new theorem of a call can be built\<close>

text \<open>
  Variables that are mapped to consistent variables by an index-preserving map are consistent in
  an environment without term bindings:
\<close>


lemma winv_reindex:
  assumes te: "vt_is_empty (tenv env)"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> vcons \<rho> X" and bl: "below (maxidx env) X"
    and h: "\<And>x T. (x, T) \<in> Z \<Longrightarrow> (h x, T) \<in> X \<and> snd (h x) = snd x"
  shows "winv env Z"
proof -
  have ev: "evars env = {}" using te by (simp add: evars_def bnds_def vt_is_empty_lookup)
  show ?thesis unfolding winv_def
  proof (intro allI impI conjI)
    fix \<rho> assume t: "tsol (tyenv env) \<rho>" and c: "cert_inst \<rho>"
    show "wt_env \<rho> env" using te by (simp add: wt_env_def vt_is_empty_lookup)
    have "vcons \<rho> Z" unfolding vcons_def
    proof (intro allI impI)
      fix x T U assume "(x, T) \<in> Z" "(x, U) \<in> Z"
      with h have "(h x, T) \<in> X" "(h x, U) \<in> X" by blast+
      from vconsD[OF vc[OF t c] this] show "tsubst \<rho> T = tsubst \<rho> U" .
    qed
    moreover have "below (maxidx env) Z" unfolding below_def
    proof
      fix q assume q: "q \<in> Z"
      obtain x T where xT: "q = (x, T)" by (cases q)
      with q h have hx: "(h x, T) \<in> X" "snd (h x) = snd x" by blast+
      have "snd (h x) \<le> maxidx env" by (rule belowD[OF bl hx(1)])
      with hx(2) xT show "snd (fst q) \<le> maxidx env" by simp
    qed
    ultimately show "vinv \<rho> env Z" by (simp add: vinv_def ev)
  qed
qed

lemma ibelow_var: "ibelow m t \<Longrightarrow> (x, T) \<in> vars t \<Longrightarrow> snd x \<le> m"
  unfolding ibelow_def by fastforce

text \<open>Consistent variables stay consistent in the environment of a unifier:\<close>

lemma uresult_winv:
  assumes ur: "uresult A0 env tus (El_R env' tps)" and si: "sinv A K X env (tdps tus)"
    and wy: "winv env (Y \<union> dvars (tdps tus))"
  shows "winv env' Y"
proof -
  have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1)[OF ur])
  have "winv env' (Y \<union> dvars (tdps tps))"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume t': "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
    have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
    from winvD[OF wy t c] have w: "wt_env \<rho> env" "vinv \<rho> env (Y \<union> dvars (tdps tus))" by blast+
    from dstepD(2)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t c] w(2)]
    show "wt_env \<rho> env' \<and> vinv \<rho> env' (Y \<union> dvars (tdps tps))" by blast
  qed
  then show ?thesis by (rule ur_winv_sub) blast
qed

lemma itsok_sinv: "itsok sp A na tus \<Longrightarrow> sinv_all A' K X sp \<Longrightarrow> sinv A' K X (sp_env sp) (tdps tus)"
proof (unfold itsok_def, elim disjE exE conjE)
  assume "\<not> sp_eres sp" "tus = bc_dpairs (sp_ctx sp)" "sinv_all A' K X sp"
  then show "sinv A' K X (sp_env sp) (tdps tus)" by (simp add: sinv_all_def)
next
  fix n asm assume er: "sp_eres sp" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
    "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm" "sinv_all A' K X sp"
  have "nat_of_integer n - 1 < length (asms_of sp)" using er(2,3) by (simp add: integer_reps)
  then have "asm \<in> set (asms_of sp)" using er(4) by simp
  with er show "sinv A' K X (sp_env sp) (tdps tus)" by (simp add: sinv_all_def)
qed

text \<open>
  The call of \<^const>\<open>newAs\<close> of a result: the premises \<open>As0\<close> of the rule that are kept, and the
  pairs \<open>dps\<close> whose variables a renaming of the new premises fixes.
\<close>

lemma itsok_newAs_data:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and its: "itsok sp A1o na tus" and ibBi: "ibelow smax Bi"
    and ibst: "\<forall>(t, u)\<in>set stpairs. ibelow smax t \<and> ibelow smax u"
    and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and nlift_def: "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
    and BBi_def: "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
    and ctx_def: "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  obtains As0 n dps tps1 where "okT (newAs vl ctx As0 n dps tps1) na" "set As0 \<subseteq> set (rev rAs)"
    "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    "\<And>h. \<forall>x. snd x \<le> smax \<longrightarrow> h x = x \<Longrightarrow> \<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x \<Longrightarrow>
      \<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x \<Longrightarrow>
      (\<not> lifted \<Longrightarrow> \<forall>x. h x = x) \<Longrightarrow> \<forall>(x, T)\<in>dvars (tdps tus). h x = x"
    "0 \<le> nlift" "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
proof -
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have cs: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bi ctx = Bi"
    "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi" "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have spe: "sp_eres sp = eres_flg" "sp_vl sp = vl" "sp_ctx sp = ctx" "sp_rAs sp = rAs" by (simp_all add: sp')
  have cnt0: "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
  have vBBi: "vars (snd BBi) \<subseteq> vars Bi"
  proof (cases lifted)
    case True
    from lr[OF True] obtain p Bi0 As0' B0 where Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" and B: "B = lift_pre p B0" by (rule lifted_rule_lift_pre)
    have "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    then show ?thesis by (simp add: Bi vars_lift_pre)
  qed (simp add: BBi_def)
  text \<open>A map that fixes the variables of the proof state and those of the problem of the rule:\<close>
  have h_tps: "\<forall>(x, T)\<in>dvars (tdps (BBi # rtpairs @ stpairs)). h x = x"
    if h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" and h4: "\<forall>(x, T)\<in>vars (fst BBi). h x = x"
      and h5: "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" for h
  proof (clarify)
    fix x T assume "(x, T) \<in> dvars (tdps (BBi # rtpairs @ stpairs))"
    then consider "(x, T) \<in> vars (fst BBi)" | "(x, T) \<in> vars (snd BBi)"
      | t u where "(t, u) \<in> set rtpairs" "(x, T) \<in> vars t \<union> vars u"
      | t u where "(t, u) \<in> set stpairs" "(x, T) \<in> vars t \<union> vars u"
      by (cases BBi) (auto simp: dvars_def)
    then show "h x = x"
    proof cases
      case 1
      with h4 show ?thesis by blast
    next
      case 2
      with vBBi have "(x, T) \<in> vars Bi" by blast
      with ibBi have "snd x \<le> smax" by (rule ibelow_var)
      with h3 show ?thesis by blast
    next
      case 3
      with h5 show ?thesis by blast
    next
      case 4
      with ibst have "ibelow smax t" "ibelow smax u" by blast+
      with 4(2) have "snd x \<le> smax" by (auto intro: ibelow_var)
      with h3 show ?thesis by blast
    qed
  qed
  show thesis
  proof (cases eres_flg)
    case False
    from its False obtain tps1 where res: "tus = BBi # rtpairs @ stpairs"
      "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      unfolding itsok_def spe by (auto simp: cs)
    show thesis
    proof (rule that[OF res(2) _ lr])
      fix h assume h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x" and h4: "\<forall>(t, u)\<in>set [BBi]. \<forall>(x, T)\<in>vars t. h x = x"
        and h5: "\<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
      have "\<forall>(x, T)\<in>vars (fst BBi). h x = x" using h4 by (cases BBi) auto
      moreover have "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" using h5 by auto
      ultimately show "\<forall>(x, T)\<in>dvars (tdps tus). h x = x" using h_tps[OF h3] res(1) by blast
    next
      show "0 \<le> nlift" using False cnt0 by (simp add: nlift_def)
    next
      show "nlift + (if 0 < (0::integer) \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
        using False cnt0 by (simp add: nlift_def)
    qed simp
  next
    case True
    from its True obtain n asm tps1 where eres: "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
      "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
      "okT (newAs vl ctx (er_As (eres_of sp)) n
        [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      unfolding itsok_def spe cs[symmetric] by blast
    have n1: "1 \<le> nat_of_integer n" using eres(1) by (simp add: integer_reps)
    obtain A1 As where rA: "rev rAs = A1 # As"
      using eres(2) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
      using rA ap by (simp_all add: eres_of_def asms_of_def sp' cs)
    have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using True by (simp add: nlift_def)
    have "ilength asms \<le> nlift + 1" by (rule assum_problems_length[OF ap]) (use cnt cnt0 in simp)
    moreover have "n \<le> ilength asms" using eres(2) e(2) by (simp add: ilength_eq integer_reps)
    ultimately have nc: "1 \<le> count_prems (strip_all_body Bi)" using cnt eres(1) by simp
    have asm: "asm \<in> set asms"
    proof -
      have "nat_of_integer n - 1 < length asms" using eres(2) n1 e(2) by simp
      then show ?thesis using eres(3) e(2) by simp
    qed
    have tus: "tus = (rlist_abs params asm, rlist_abs params concl) # BBi # rtpairs @ stpairs"
      using eres(4) e by (simp add: eres_prob_def sp' cs)
    have lrA: "lifted_rule smax Bi As B" if "lifted" using lr[OF that] rA by (auto dest: lifted_rule_Cons)
    have na: "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
      using eres(5) e by simp
    show thesis
    proof (rule that[OF na _ lrA])
      show "set As \<subseteq> set (rev rAs)" using rA by auto
      fix h assume h3: "\<forall>x. snd x \<le> smax \<longrightarrow> h x = x"
        and h4: "\<forall>(t, u)\<in>set [BBi, (rlist_abs params concl, rlist_abs params asm)]. \<forall>(x, T)\<in>vars t. h x = x"
        and h5: "\<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x"
        and h7: "\<not> lifted \<Longrightarrow> \<forall>x. h x = x"
      have a: "\<forall>(x, T)\<in>vars asm. h x = x"
      proof (cases lifted)
        case True
        from lr[OF True] obtain p Bi0 As0' and B0 :: pterm where Bi: "Bi = lift_pre p Bi0"
          and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "rev rAs = map (lift_pre p) As0'"
          by (rule lifted_rule_lift_pre)
        from rA As0 obtain A1' where A1: "A1 = lift_pre p A1'" by (cases As0') auto
        have "set asms \<subseteq> set (phyps p)"
          by (rule assum_problems_lift_pre[OF ok at _ ap[unfolded A1]]) (use cnt cnt0 Bi in simp_all)
        with asm have va: "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        have "\<forall>(x, T)\<in>vars asm. snd x \<le> smax"
        proof (clarify)
          fix x T assume "(x, T) \<in> vars asm"
          with va have "(x, T) \<in> vars Bi" by (auto simp: Bi vars_lift_pre)
          with ibBi show "snd x \<le> smax" by (rule ibelow_var)
        qed
        with h3 show ?thesis by blast
      qed (use h7 in blast)
      have "\<forall>(x, T)\<in>vars (fst BBi). h x = x" using h4 by (cases BBi) auto
      moreover have "\<forall>(t, u)\<in>set rtpairs. \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" using h5 by auto
      ultimately have "\<forall>(x, T)\<in>dvars (tdps (BBi # rtpairs @ stpairs)). h x = x" by (rule h_tps[OF h3])
      moreover have "\<forall>(x, T)\<in>vars (rlist_abs params concl). h x = x" using h4 by auto
      ultimately show "\<forall>(x, T)\<in>dvars (tdps tus). h x = x" using a by (auto simp: tus dvars_def)
    next
      show "0 \<le> nlift" using cnt nc by auto
    next
      show "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
        using cnt nc by auto
    qed
  qed
qed

text \<open>
  The new theorem can be built for every unifier of a call with a well-typed proof state and
  rule, unless \<open>match\<close> forbids it.
\<close>

lemma call_results_ok:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)"
    and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and ei: "einv A K env" "finite K" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
    and A: "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> A"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow>
      vcons \<rho> (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "results_ok sp"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?R = "list_implies (rev rAs) B"
  let ?X = "vars_thm stpairs ?S \<union> vars_thm rtpairs ?R"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have cs: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs" "bc_match ctx = match_flg"
    by (simp_all add: ctx_def)
  have wS: "wtp ?S" "ibelow smax ?S" and wR: "wtp ?R" "ibelow rmax ?R"
    using state rule by (simp_all add: wt_thm_def)
  have wBs: "\<forall>X\<in>set Bs. wtp X" "wtp C" using wtp_list_implies[OF wS(1)] by simp_all
  have wAs: "\<forall>X\<in>set (rev rAs). wtp X" using wtp_list_implies[OF wR(1)] by simp
  have ibBi: "ibelow smax Bi" using wS(2) by simp
  have ibst: "\<forall>(t, u)\<in>set stpairs. ibelow smax t \<and> ibelow smax u" using state by (auto simp: wt_thm_def)
  have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
    using lr[OF that] by (auto simp: lifted_rule_def)
  have fX: "finite ?X" by (intro finite_UnI finite_vars_thm)
  have sa: "sinv_all A K ?X sp" unfolding sp by (rule sinv_all_call_spec[OF state rule lift ei A vc])
  have bX: "below (maxidx env) ?X"
    using wS(2) wR(2) ei(4) state rule by (fastforce simp: below_def vars_thm_def ibelow_def wt_thm_def)
  have tX: "tvars T \<subseteq> A" if "(x, T) \<in> ?X" for x T
  proof -
    from that have "tvars T \<subseteq> tvars_thm stpairs ?S \<union> tvars_thm rtpairs ?R"
      by (auto simp: vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
    with A show ?thesis by blast
  qed
  have XS: "vars ?S \<subseteq> ?X" "vars ?R \<subseteq> ?X" using vars_tvars_thm(1) by blast+
  have AS: "ttvars ?S \<subseteq> A" "ttvars ?R \<subseteq> A" using A vars_tvars_thm(2) by blast+
  have ty: "(\<lambda>j. tsubst \<rho> (e j)) \<turnstile> inst \<rho> X : propT" if "wtp X" "cert_inst \<rho>" for e \<rho> X
    using typing_inst[OF wtpD(2)[OF that(1)] cert_inst_inst_ok[OF that(2)]] by simp
  have vBBi: "vars (fst BBi) \<subseteq> vars B" "vars (snd BBi) \<subseteq> vars Bi"
  proof -
    have "vars (fst BBi) \<subseteq> vars B \<and> vars (snd BBi) \<subseteq> vars Bi"
    proof (cases lifted)
      case True
      from lift[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0" by blast
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      then show ?thesis by (simp add: B Bi vars_lift_pre)
    qed (simp add: BBi_def)
    then show "vars (fst BBi) \<subseteq> vars B" "vars (snd BBi) \<subseteq> vars Bi" by blast+
  qed
  show ?thesis unfolding results_ok_def
  proof (intro allI impI)
    fix A1o na tus env' tps
    assume its: "itsok sp A1o na tus" and ur: "ures (sp_env sp) tus (El_R env' tps)"
    have si: "sinv A K ?X env (tdps tus)" using itsok_sinv[OF its sa] by (simp add: sp')
    have urs: "uresult A env tus (El_R env' tps)" using uresD[OF ur fX ei(2)] si by (simp add: sp')
    from uresultD(3)[OF urs] obtain A' K' X' and e0 :: env where AA: "A \<subseteq> A'" and ff: "ffres A' K' X' env' tps" by blast
    have ei': "einv A' K' env'" and wi': "winv env' X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env' [] X' t u"
      using ff by (simp_all add: ffres_def)
    note r0 = einv_rho0[OF ei']
    have ev: "evars env = {}" using ei(3) by (simp add: evars_def bnds_def vt_is_empty_lookup)
    have wiX: "winv env ?X" using si by (simp add: sinv_def)
    have dX: "dvars (tdps tus) \<subseteq> ?X" using sinv_dvars[OF si] ev by simp
    have tw: "winv env' Y" if "winv env (Y \<union> dvars (tdps tus))" for Y by (rule uresult_winv[OF urs si that])
    text \<open>The flex-flex pairs:\<close>
    have n_tps: "\<forall>(t, u)\<in>set tps. (\<exists>t'. ok (norm_term env' t) t') \<and> (\<exists>u'. ok (norm_term env' u) u')"
    proof (intro ballI, clarify)
      fix t u assume "(t, u) \<in> set tps"
      with tpok have p: "upok A' env' [] X' t u" by blast
      from upokD(9)[OF p r0] obtain e T where "e \<turnstile> inst (rho0 env') t : T" "e \<turnstile> inst (rho0 env') u : T" by blast
      with norm_term_ok[OF ei' wi' upokD(6)[OF p] upokD(1)[OF p] upokD(3)[OF p]]
        norm_term_ok[OF ei' wi' upokD(6)[OF p] upokD(2)[OF p] upokD(4)[OF p]]
      show "(\<exists>t'. ok (norm_term env' t) t') \<and> (\<exists>u'. ok (norm_term env' u) u')" by blast
    qed
    text \<open>The other subgoals and the conclusion of the proof state:\<close>
    have "winv env (?X \<union> dvars (tdps tus))" by (rule ur_winv_sub[OF wiX]) (use dX in blast)
    then have wX': "winv env' ?X" by (rule tw)
    have vX': "vtvars ?X \<subseteq> tvars_env (tyenv env') \<union> A'"
    proof -
      have "tvars T \<subseteq> A'" if "(x, T) \<in> ?X" for x T using tX[OF that] AA by blast
      then show ?thesis by (auto simp: vtvars_def)
    qed
    have n_BC: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). \<exists>X'. ok (norm_term env' X) X'"
    proof
      fix X assume "X \<in> insert (bc_C ctx) (set (bc_Bs ctx))"
      then have X: "X \<in> insert C (set Bs)" by (simp add: cs)
      then have v: "vars X \<subseteq> ?X" using XS(1) by (auto simp: vars_list_implies)
      have "ttvars X \<subseteq> ttvars ?S"
        using X ttvars_list_implies(1)[of X "Bs @ [Bi]" C] ttvars_list_implies(2)[of C "Bs @ [Bi]"] by auto
      then have t: "ttvars X \<subseteq> tvars_env (tyenv env') \<union> A'" using AS(1) AA by blast
      have w: "wtp X" using X wBs by auto
      from norm_term_ok[OF ei' wX' vX' _ t ty[OF w r0(2)]] v show "\<exists>X'. ok (norm_term env' X) X'" by blast
    qed
    text \<open>The new premises, for the premises \<open>As0\<close> of the rule that are kept:\<close>
    have n_new: "(\<forall>X\<in>set (na_As na). \<exists>X'. ok (norm_term env' X) X') \<and>
        (lifted \<longrightarrow> (\<forall>X\<in>set (na_As na). \<exists>X'. okT (norm_term_skip env' nlift X) X'))"
      if na: "okT (newAs vl ctx As0 n dps tps1) na" and As0: "set As0 \<subseteq> set (rev rAs)"
        and lr0: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
        and hid: "\<And>h. \<forall>x. snd x \<le> smax \<longrightarrow> h x = x \<Longrightarrow> \<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x \<Longrightarrow>
          \<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x \<Longrightarrow>
          (\<not> lifted \<Longrightarrow> \<forall>x. h x = x) \<Longrightarrow> \<forall>(x, T)\<in>dvars (tdps tus). h x = x"
        and nl: "lifted \<Longrightarrow> 0 \<le> nlift \<and>
          (\<forall>k. count_prems (strip_all_body Bi) \<le> k + (if 0 < n \<and> flatten then 1 else 0) \<longrightarrow> nlift \<le> k)"
      for As0 n dps tps1
    proof -
      obtain h where
        p1: "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)" and
        p2: "\<forall>X\<in>set (na_As na). \<forall>(x, T)\<in>vars X. (h x, T) \<in> (\<Union>A\<in>set As0. vars A) \<and> snd (h x) = snd x" and
        p3: "\<forall>x. snd x \<le> bc_smax ctx \<longrightarrow> h x = x" and
        p4: "\<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x" and
        p5: "\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x" and
        p6: "bc_lifted ctx \<Longrightarrow> \<forall>X\<in>set (na_As na).
          count_prems (strip_all_body (bc_Bi ctx)) \<le> ilength (spine_hyps X) + (if 0 < n \<and> bc_flatten ctx then 1 else 0)" and
        p7: "\<not> bc_lifted ctx \<Longrightarrow> \<forall>x. h x = x"
      proof (rule newAs_props[OF na])
        show "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" using lr0 by (simp add: cs)
        show "ibelow (bc_smax ctx) (bc_Bi ctx)" using ibBi by (simp add: cs)
        show "\<forall>A\<in>set As0. wtp A" using As0 wAs by blast
      qed (rule vl, blast)
      note p = p3[unfolded cs] p5[unfolded cs] p6[unfolded cs] p7[unfolded cs]
      let ?V = "\<Union>X\<in>set (na_As na). vars X"
      have As0X: "(\<Union>A\<in>set As0. vars A) \<subseteq> ?X" using As0 XS(2) by (auto simp: vars_list_implies)
      have As0A: "(\<Union>A\<in>set As0. ttvars A) \<subseteq> A" using As0 AS(2) ttvars_list_implies(1)[of _ "rev rAs" B] by blast
      have hV: "(h x, T) \<in> ?X \<and> snd (h x) = snd x" if "(x, T) \<in> ?V" for x T
        using that p2 As0X by blast
      have hd: "\<forall>(x, T)\<in>dvars (tdps tus). h x = x" by (rule hid[OF p(1) p4 p(2) p(4)])
      have wV: "winv env (?V \<union> dvars (tdps tus))"
      proof (rule winv_reindex[OF ei(3) vc bX])
        fix x T assume "(x, T) \<in> ?V \<union> dvars (tdps tus)"
        then show "(h x, T) \<in> ?X \<and> snd (h x) = snd x"
        proof
          assume "(x, T) \<in> ?V"
          then show ?thesis by (rule hV)
        next
          assume d: "(x, T) \<in> dvars (tdps tus)"
          with hd have "h x = x" by blast
          with d dX show ?thesis by auto
        qed
      qed
      have wV': "winv env' ?V" by (rule tw[OF wV])
      have vV: "vtvars ?V \<subseteq> tvars_env (tyenv env') \<union> A'"
      proof -
        have "tvars T \<subseteq> A'" if "(x, T) \<in> ?V" for x T using hV[OF that] tX AA by blast
        then show ?thesis by (auto simp: vtvars_def)
      qed
      have props: "vars X \<subseteq> ?V \<union> evars env'" "ttvars X \<subseteq> tvars_env (tyenv env') \<union> A'"
        "(\<lambda>j. tsubst (rho0 env') (e j)) \<turnstile> inst (rho0 env') X : propT"
        if "X \<in> set (na_As na)" for X e
      proof -
        show "vars X \<subseteq> ?V \<union> evars env'" using that by blast
        show "ttvars X \<subseteq> tvars_env (tyenv env') \<union> A'" using that p1 As0A AA by blast
        show "(\<lambda>j. tsubst (rho0 env') (e j)) \<turnstile> inst (rho0 env') X : propT" using that p1 ty r0(2) by blast
      qed
      have "\<exists>X'. ok (norm_term env' X) X'" if "X \<in> set (na_As na)" for X
        by (rule norm_term_ok[OF ei' wV' vV props[OF that]])
      moreover have "\<exists>X'. okT (norm_term_skip env' nlift X) X'" if lf: lifted and X: "X \<in> set (na_As na)" for X
      proof (rule norm_term_skip_ok[OF ei' wV' vV props[OF X]])
        show "0 \<le> nlift" using nl[OF lf] by blast
        show "nlift \<le> ilength (spine_hyps X)" using nl[OF lf] p(3)[OF lf] X by blast
      qed
      ultimately show ?thesis by blast
    qed
    have n_As: "(\<forall>X\<in>set (na_As na). \<exists>X'. ok (norm_term env' X) X') \<and>
        (lifted \<longrightarrow> (\<forall>X\<in>set (na_As na). \<exists>X'. okT (norm_term_skip env' nlift X) X'))"
    proof (rule itsok_newAs_data[OF sp its ibBi ibst lr nlift_def BBi_def ctx_def])
      fix As0 n dps tps1
      assume d: "okT (newAs vl ctx As0 n dps tps1) na" "set As0 \<subseteq> set (rev rAs)"
          "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
          "\<And>h. \<forall>x. snd x \<le> smax \<longrightarrow> h x = x \<Longrightarrow> \<forall>(t, u)\<in>set dps. \<forall>(x, T)\<in>vars t. h x = x \<Longrightarrow>
            \<forall>(t, u)\<in>set (rtpairs @ tps1). \<forall>(x, T)\<in>vars t \<union> vars u. h x = x \<Longrightarrow>
            (\<not> lifted \<Longrightarrow> \<forall>x. h x = x) \<Longrightarrow> \<forall>(x, T)\<in>dvars (tdps tus). h x = x"
          "0 \<le> nlift" "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)"
      show ?thesis by (rule n_new[OF d(1-4)]) (use d(5,6) in auto)
    qed
    show "(\<exists>r. okT (addth (sp_ctx sp) A1o na (env', tps)) r) \<or>
        (bc_match (sp_ctx sp) \<and> (\<exists>evs. addth (sp_ctx sp) A1o na (env', tps) = Some (evs, Err COMPOSE)))"
      unfolding sp' bspec.sel by (rule addth_ok[OF n_tps n_BC]) (use n_As in \<open>simp_all add: cs\<close>)
  qed
qed



subsection \<open>Termination\<close>

lemma strip_prems_exists: "0 \<le> i \<Longrightarrow> i \<le> count_prems B \<Longrightarrow> \<exists>r. ok (strip_prems i As B) r"
proof (induction i As B rule: strip_prems.induct)
  case (1 i As B)
  show ?case
  proof (cases "i = 0")
    case False
    then obtain A B' where AB: "dest_imp B = Some (A, B')"
      using "1.prems" by (cases "dest_imp B") (auto simp: count_prems.simps[of B])
    have "i - 1 \<le> count_prems B'" using "1.prems"(2) AB by (subst (asm) count_prems.simps) simp
    moreover have "0 \<le> i - 1" using "1.prems"(1) False by (simp add: integer_reps)
    ultimately obtain r where "ok (strip_prems (i - 1) (A # As) B') r" using "1.IH"[OF False AB refl] by blast
    with False show ?thesis by (subst strip_prems.simps) (simp add: AB)
  qed (subst strip_prems.simps; simp)
qed

text \<open>The unification of the types of variables terminates, possibly with a failure to unify:\<close>

lemma foldM_unify_types_term:
  assumes "einv A K env" "finite K" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar T"
    "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar U"
  shows "(\<exists>env'. foldM (\<lambda>U env. unify_types alg T U env) Us env = return env' \<and> einv A K env' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')) \<or>
    (\<exists>u. foldM (\<lambda>U env. unify_types alg T U env) Us env = raise (Unif u))"
  using assms
proof (induction Us arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons U Us)
  have tU: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "wft ar U" "sorts_ok alg U"
    and tT: "wft ar T" "sorts_ok alg T"
    using Cons.prems(4,5) by (auto simp: cert_typ_def)
  from unify_types_term[OF Cons.prems(1,2,3) tT tU]
  consider (ok) env1 where "unify_types alg T U env = return env1" "einv A K env1"
      "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    | (err) u where "unify_types alg T U env = raise (Unif u)"
    by blast
  then show ?case
  proof cases
    case ok
    have "(\<exists>env'. foldM (\<lambda>U env. unify_types alg T U env) Us env1 = return env' \<and> einv A K env' \<and>
        tvars_env (tyenv env1) \<subseteq> tvars_env (tyenv env')) \<or>
      (\<exists>u. foldM (\<lambda>U env. unify_types alg T U env) Us env1 = raise (Unif u))"
    proof (rule Cons.IH[OF ok(2) Cons.prems(2)])
      show "tvars T \<subseteq> tvars_env (tyenv env1) \<union> A" using Cons.prems(3) ok(3) by blast
      show "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env1) \<union> A \<and> cert_typ alg ar U"
        using Cons.prems(5) ok(3) by fastforce
    qed (rule Cons.prems(4))
    with ok(1,3) show ?thesis by (auto simp: bindM_def return_def)
  next
    case err
    then show ?thesis by (simp add: bindM_def raise_def)
  qed
qed

lemma foldM_unify_vars_term:
  assumes "einv A K env" "finite K"
    "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar T"
  shows "(\<exists>env'. foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env = return env') \<or>
    (\<exists>u. foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env = raise (Unif u))"
  using assms
proof (induction tab arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons xTs tab)
  obtain x Ts where xTs: "xTs = (x, Ts)" by (cases xTs)
  have u: "(\<exists>env1. unify_vars alg Ts env = return env1 \<and> einv A K env1 \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)) \<or> (\<exists>u. unify_vars alg Ts env = raise (Unif u))"
  proof (cases Ts)
    case Nil
    with Cons.prems(1) show ?thesis by (simp add: return_def)
  next
    case (Cons T Us)
    with foldM_unify_types_term[OF Cons.prems(1,2), of T Us] Cons.prems(3) xTs
    show ?thesis by simp
  qed
  then show ?case
  proof (elim disjE exE conjE)
    fix env1 assume u1: "unify_vars alg Ts env = return env1" and e1: "einv A K env1"
      and t1: "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)"
    have "(\<exists>env'. foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env1 = return env') \<or>
      (\<exists>u. foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env1 = raise (Unif u))"
      by (rule Cons.IH[OF e1 Cons.prems(2)]) (use Cons.prems(3) t1 in fastforce)
    with u1 xTs show ?thesis by (auto simp: bindM_def return_def)
  next
    fix u assume "unify_vars alg Ts env = raise (Unif u)"
    with xTs show ?thesis by (simp add: bindM_def raise_def)
  qed
qed

lemma unify_var_types_exists:
  assumes ei: "einv A K (empty_env m)" "finite K"
    and ty: "\<forall>(x, T)\<in>vars_thm tps1 P1 \<union> vars_thm tps2 P2. tvars T \<subseteq> A \<and> cert_typ alg ar T"
    and w1: "wt_thm m1 h1 tps1 P1" and w2: "wt_thm m2 h2 tps2 P2"
  shows "\<exists>r. okT (unify_var_types alg (tps1, P1) (tps2, P2) (empty_env m)) r"
proof -
  have fp: "\<exists>p. ok (full_prop_of tps P) p" if "wt_thm mt ht tps P" for mt ht tps P
  proof -
    have "\<exists>e. ok (mk_equals tu) e" if "tu \<in> set tps" for tu
    proof -
      obtain t u where tu: "tu = (t, u)" by (cases tu)
      from \<open>wt_thm mt ht tps P\<close> that tu have c: "closed t" and "\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T"
        by (auto simp: wt_thm_def)
      then obtain T where "\<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T" by blast
      then have "fastype_of t = return T" using fastype_of_closed c by blast
      then show ?thesis by (auto simp: mk_equals_def tu return_def bindM_def)
    qed
    from ok_mapM_exI[of tps mk_equals] this obtain eqs where "ok (mapM mk_equals tps) eqs" by blast
    then show ?thesis by (auto simp: full_prop_of_def bindM_def return_def)
  qed
  from fp[OF w1] obtain p1 where p1: "ok (full_prop_of tps1 P1) p1" by blast
  from fp[OF w2] obtain p2 where p2: "ok (full_prop_of tps2 P2) p2" by blast
  let ?tab = "sort_keys (add_vars p2 (add_vars p1 []))"
  have vt: "vtab ?tab = vars_thm tps1 P1 \<union> vars_thm tps2 P2"
    using vars_full_prop_of[OF p1] vars_full_prop_of[OF p2]
    by (auto simp: vtab_def set_sort_keys vtab_add_vars[unfolded vtab_def] split: prod.splits)
  have "\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv (empty_env m)) \<union> A \<and> cert_typ alg ar T"
  proof (intro ballI, clarify)
    fix x Ts T assume "(x, Ts) \<in> set ?tab" "T \<in> set Ts"
    then have "(x, T) \<in> vtab ?tab" unfolding vtab_def by blast
    with vt ty have "tvars T \<subseteq> A \<and> cert_typ alg ar T" by blast
    then show "tvars T \<subseteq> tvars_env (tyenv (empty_env m)) \<union> A \<and> cert_typ alg ar T" by auto
  qed
  from foldM_unify_vars_term[OF ei this]
  consider env where "foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) ?tab (empty_env m) = return env"
    | u where "foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) ?tab (empty_env m) = raise (Unif u)"
    by blast
  then show ?thesis
  proof cases
    case 1
    with p1 p2 show ?thesis
      by (auto simp: unify_var_types_def Let_def bindM_def return_def liftMT_def liftWT_def liftM_def returnW_def)
  next
    case 2
    with p1 p2 show ?thesis
      by (auto simp: unify_var_types_def Let_def bindM_def return_def raise_def emit_def returnW_def bindW_def)
  qed
qed

text \<open>The body of a call terminates if its problems are well-formed and the new premises can be computed:\<close>

lemma bicompose_body_ok:
  assumes cfg: "cfg_alg (sp_cfg sp) = alg" and pa: "pinv_all sp"
    and nok: "newas_ok sp" and ne: "sp_eres sp \<Longrightarrow> sp_rAs sp \<noteq> []"
  shows "\<exists>s. okT (bicompose_body (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_ctx sp) (sp_env sp) (sp_eres sp) (sp_rAs sp)) s"
proof (cases "sp_eres sp")
  case True
  then obtain A1 As where rA: "rev (sp_rAs sp) = A1 # As" using ne by (cases "rev (sp_rAs sp)") auto
  obtain params asms concl where ap: "assum_problems (bc_nlift (sp_ctx sp) + 1) A1 = (params, asms, concl)"
    by (cases "assum_problems (bc_nlift (sp_ctx sp) + 1) A1")
  have er: "ER (sp_env sp) params concl (rlist_abs params concl) A1 As = eres_of sp"
    using rA ap by (simp add: eres_of_def)
  have asms: "asms = drop (nat_of_integer 1 - 1) (asms_of sp)" using rA ap by (simp add: asms_of_def)
  from tryasms_ok[OF cfg pa True nok refl refl refl _ asms] obtain s where
    "okT (tryasms (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_ctx sp) (eres_of sp) asms 1) s" by auto
  with True rA ap er show ?thesis by (auto simp: bicompose_body_def)
next
  case False
  from pa False have pw: "pwf (sp_env sp) (bc_dpairs (sp_ctx sp))" by (simp add: pinv_all_def)
  obtain us where us: "okT (bo_unifiers (unify_ops (sp_cfg sp) (sp_vl sp)) (sp_env sp) (bc_dpairs (sp_ctx sp))) us"
    and ui: "fin (sp_cfg sp) us (ures (sp_env sp) (bc_dpairs (sp_ctx sp)))"
    by (rule unifiers_ops_ok[OF cfg pw])
  show ?thesis
  proof (rule upull_fin_cases[OF ui pw])
    assume "okT (upull (sp_cfg sp) us) None"
    with us False show ?thesis by (auto simp: bicompose_body_def unify_ops_def)
  next
    fix env' tps us' assume "okT (upull (sp_cfg sp) us) (Some ((env', tps), us'))"
    moreover from nok False obtain na where
      "okT (newAs (sp_vl sp) (sp_ctx sp) (rev (sp_rAs sp)) 0 [bc_BBi (sp_ctx sp)] tps) na"
      unfolding newas_ok_def by blast
    ultimately show ?thesis using us False by (auto simp: bicompose_body_def unify_ops_def)
  qed
qed

lemma bindT_Some_TOk: "bindW (Some ([], Ok x)) f = f x"
  by (simp add: bindW_def option.map_id)

lemma handleT_Some_TOk: "handleW (Some (evs, Ok x)) h = Some (evs, Ok x)"
  by (simp add: handleW_def)

end

text \<open>
  The main theorem on termination: a call terminates without an exception, and pulling its
  sequence of results yields finitely many results and then its end, if the rule has at least
  \<open>nsubgoal\<close> premises, one at least for elim-resolution, which flattens parameters only for
  lifted rules.
\<close>

context bicompose_call
begin

theorem bicompose_aux_terminates:
  assumes ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
  shows "\<exists>s rs. okT bcall s \<and> bevals (unify_ops cfg vl) s rs"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  let ?A = "tvars_thm stpairs ?S \<union> tvars_thm rtpairs rprop"
  let ?nlift = "count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  let ?ctx = "\<lambda>B. BCtx flatten match_flg lifted smax Bs Bi C rtpairs ?nlift
    (if lifted then strip_assums2 B Bi else (B, Bi))
    ((if lifted then strip_assums2 B Bi else (B, Bi)) # rtpairs @ stpairs)"
  from strip_prems_exists[OF ns] obtain rAsB where sp0: "ok (strip_prems nsubgoal [] rprop) rAsB" by blast
  obtain rAs B where rAsB: "rAsB = (rAs, B)" by (cases rAsB)
  note sp1 = sp0[unfolded rAsB]
  have eq: "bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented (smax, stpairs, ?S)
      (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal =
    bindW (if incremented then returnW (Some (empty_env ?m))
        else unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m))
      (\<lambda>r. case r of None \<Rightarrow> returnW BS_Empty
        | Some env \<Rightarrow> bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs)"
    using sp1 by (simp add: bicompose_aux_def Let_def liftMT_def liftWT_def liftM_def bindT_Some_TOk handleT_Some_TOk)
  have wR: "wtp rprop" using rule(1) by (simp add: wt_thm_def)
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF sp1 wtpD(2)[OF wR, of "\<lambda>_. propT"]])
  note e0 = call_env0[OF state rule(1) tv]
  obtain r where r: "okT (if incremented then returnW (Some (empty_env ?m))
      else unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m)) r"
    using unify_var_types_exists[OF e0(1) _ e0(2) state rule(1)] by (cases incremented) auto
  show ?thesis
  proof (cases r)
    case None
    with r have "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) BS_Empty"
      unfolding eq by (auto simp: returnW_def)
    moreover have "bpull (unify_ops cfg vl) BS_Empty = returnW None" by (subst bpull.simps) simp
    then have "bevals (unify_ops cfg vl) BS_Empty []" by (auto intro: bevals.Nil)
    ultimately show ?thesis by blast
  next
    case (Some env)
    let ?sp = "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    have e1: "incremented \<Longrightarrow> env = empty_env ?m" and
      e2: "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, ?S) (rtpairs, rprop) (empty_env ?m)) (Some env)"
      using r Some by (auto split: if_splits)
    have env: "einv ?A ?A env \<and> vt_is_empty (tenv env) \<and> ?m \<le> maxidx env \<and>
        (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow>
          vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs rprop))"
      by (rule call_env[OF state rule(1) tv inc e1 e2])
    have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
      using lifted_over_lifted_rule[OF rule(2) sp1] by simp
    have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
      using lr[OF that] by (auto simp: lifted_rule_def)
    have fA: "finite ?A" by (intro finite_UnI finite_tvars_thm)
    have pa: "pinv_all ?sp"
    proof (rule pinv_all_call_spec[OF state rule(1)[unfolded P] lift])
      show "einv ?A ?A env" "finite ?A" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
        using env fA by simp_all
      show "tvars_thm stpairs ?S \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> ?A" using P by simp
      show "vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
        if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
        using env that P by simp
    qed
    have nok: "newas_ok ?sp" by (rule call_newas_ok[OF refl lr fl vl])
    have rok: "results_ok ?sp"
    proof (rule call_results_ok[OF refl state rule(1)[unfolded P] lr _ fA])
      show "einv ?A ?A env" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
        using env by simp_all
      show "tvars_thm stpairs ?S \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> ?A" using P by simp
      show "vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
        if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
        using env that P by simp
    qed (simp_all add: vl)
    have sel: "sp_cfg ?sp = cfg" "sp_vl ?sp = vl" "sp_env ?sp = env" "sp_eres ?sp = eres_flg"
      "sp_rAs ?sp = rAs" "sp_ctx ?sp = ?ctx B"
      by (simp_all add: call_spec_def Let_def)
    have ne: "eres_flg \<Longrightarrow> rAs \<noteq> []"
      using strip_prems_ok[OF sp1] er by (auto simp: integer_reps)
    from bicompose_body_ok[of ?sp] cfg pa nok ne sel obtain s where
      b: "okT (bicompose_body (unify_ops cfg vl) (?ctx B) env eres_flg rAs) s" by auto
    have ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s"
      using r Some b unfolding eq by (auto simp: returnW_def)
    have "binv ?sp s" by (rule bicompose_body_binv) (use b cfg pa sel in simp_all)
    from bpull_bevals[OF _ pa nok rok _ this] cfg sel obtain rs where "bevals (unify_ops cfg vl) s rs"
      by auto
    with ok show ?thesis by blast
  qed
qed

end

end
