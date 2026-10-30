section \<open>Renaming Schematic Variables\<close>

theory Bicompose_Rename
  imports Bicompose_Holds
begin

text \<open>
  When a rule is lifted over a subgoal, \<open>bicompose_aux\<close> renames the bound variables and some
  schematic variables of the new subgoals after the bound variables of the subgoal
  (\<^const>\<open>rename_bvars\<close>). On de Bruijn terms, the renaming of bound variables is invisible, and
  the renaming of schematic variables is a substitution of variables for variables. It never
  renames a variable that occurs in the conclusion of the rule (as stripped) or in its flex-flex
  pairs, so the new subgoals, together with the conclusion and the flex-flex pairs of the rule, are
  an instance of the rule. Variables of the subgoal (and of the proof state) are not renamed
  either, since their indices are at most the maximal index of the proof state, and the variables of
  the lifted rule are above it.
\<close>

subsection \<open>Renaming as a substitution\<close>

text \<open>Rename the variables with index above \<open>m\<close> according to the table \<open>tab\<close>.\<close>

definition rsub :: "integer \<Rightarrow> (name \<times> name) list \<Rightarrow> nat \<Rightarrow> dB" where
  "rsub m tab n =
    (case atom_of n of
      AVar (x, i) \<Rightarrow> if m < i then dB.Var (code (AVar (ren_name tab x, i))) else dB.Var n
    | _ \<Rightarrow> dB.Var n)"

lemma rsub_rigid: "rigid_code n \<Longrightarrow> rsub m tab n = dB.Var n"
  by (auto simp: rsub_def rigid_code_def)

lemma closed_rsub: "closed_on UNIV (rsub m tab)"
  by (auto simp: closed_on_def rsub_def split: atom.splits prod.splits)

lemma rigid_subst_comp_rsub: "rigid_subst \<sigma> \<Longrightarrow> rigid_subst (\<sigma> \<circ>\<^sub>s rsub m tab)"
  by (simp add: rigid_subst_def rsub_rigid)

lemma closed_comp_rsub: "closed_on UNIV \<sigma> \<Longrightarrow> closed_on UNIV (\<sigma> \<circ>\<^sub>s rsub m tab)"
  by (rule closed_on_comp[OF closed_rsub]) (auto intro: closed_on_mono)

lemma tr_ren_term:
  "\<forall>v\<in>vars t. m < snd v \<Longrightarrow> tr (ren_term r t) = mk_subst (rsub m (fst r)) (tr t)"
  by (induction r t rule: ren_term.induct) (auto simp: rsub_def)

lemma mk_subst_rsub_id:
  "\<forall>v\<in>vars t. snd v \<le> m \<or> ren_name tab (fst v) = fst v \<Longrightarrow> mk_subst (rsub m tab) (tr t) = tr t"
  by (induction t) (auto simp: rsub_def)

lemma inst_ren_term: "inst \<rho> (ren_term r t) = ren_term r (inst \<rho> t)"
  by (induction r t rule: ren_term.induct) auto

lemma vars_ren_term: "vars (ren_term r t) = (\<lambda>(x, i). (ren_name (fst r) x, i)) ` vars t"
  by (induction r t rule: ren_term.induct) auto

lemma sm_ren_term:
  "\<forall>v\<in>vars t. m < snd v \<Longrightarrow> sm \<rho> \<sigma> (ren_term r t) = sm \<rho> (\<sigma> \<circ>\<^sub>s rsub m (fst r)) t"
  by (simp add: sm_def inst_ren_term tr_ren_term)

lemma sm_rsub_id:
  "\<forall>v\<in>vars t. snd v \<le> m \<or> ren_name tab (fst v) = fst v \<Longrightarrow> sm \<rho> (\<sigma> \<circ>\<^sub>s rsub m tab) t = sm \<rho> \<sigma> t"
  by (simp add: sm_def mk_subst_comp[symmetric] mk_subst_rsub_id del: mk_subst_comp)

lemma proper_ren_term[simp]: "proper (ren_term r t) \<longleftrightarrow> proper t"
  by (induction r t rule: ren_term.induct) auto

lemma tr_ren_term_nlb: "no_loose_bound (tr (ren_term r t)) k \<longleftrightarrow> no_loose_bound (tr t) k"
  by (induction r t arbitrary: k rule: ren_term.induct) auto

lemma cok_ren_term[simp]: "cok (ren_term r t) \<longleftrightarrow> cok t"
proof (induction t)
  case (App s t)
  then show ?case by (cases s; cases t) auto
qed auto


subsection \<open>What \<^const>\<open>rename_bvs\<close> leaves unchanged\<close>

lemma set_add_var_names: "set (add_var_names t xs) = fst ` vars t \<union> set xs"
  by (induction t xs rule: add_var_names.induct) auto

lemma set_distinct_fst: "set (distinct_fst ps) \<subseteq> set ps"
  by (induction ps rule: distinct_fst.induct) auto

lemma set_del_round: "del_round xs ys ps qs clash = (c, xs', qs') \<Longrightarrow> set qs' \<subseteq> set ps \<union> set qs"
  by (induction xs ys ps qs clash rule: del_round.induct) (fastforce split: if_splits)+

lemma set_del_clashing: "set (del_clashing xs ps) \<subseteq> set ps"
proof (induction xs ps rule: del_clashing.induct)
  case (1 xs ps)
  obtain c xs' qs where r: "del_round xs xs ps [] False = (c, xs', qs)"
    by (cases "del_round xs xs ps [] False")
  from set_del_round[OF r] have "set qs \<subseteq> set ps" by simp
  with "1.IH"[OF r[symmetric] refl] r show ?case
    by (subst del_clashing.simps) auto
qed

lemma ren_name_neq: "ren_name tab x \<noteq> x \<Longrightarrow> \<exists>y. (x, y) \<in> set tab \<and> y \<noteq> x"
  by (auto simp: ren_name_def split: option.splits dest: map_of_SomeD)

text \<open>
  A renamed variable occurs neither on the left of the disagreement pairs nor in the flex-flex
  pairs given to \<^const>\<open>rename_bvs\<close>.
\<close>

lemma rename_bvs_unknowns:
  assumes "ren_name (fst (rename_bvs dpairs tpairs B As)) x \<noteq> x"
  shows "\<forall>(t, u)\<in>set dpairs. x \<notin> fst ` vars t"
    "\<forall>(t, u)\<in>set tpairs. x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u"
proof -
  let ?al = "foldr match_bvars dpairs []"
  let ?unknowns = "fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tpairs
    (fold (add_var_names \<circ> fst) dpairs [])"
  let ?unknowns' = "fold (add_var_names \<circ> strip_lifted B) As []"
  let ?al' = "distinct_fst (filter (\<lambda>(x, y). \<not> (x \<notin> set ?unknowns' \<or> x \<in> set ?unknowns \<or> y \<in> set ?unknowns)) ?al)"
  have "x \<notin> set ?unknowns"
  proof (cases "?al = []")
    case True
    with assms show ?thesis by (simp add: rename_bvs_def ren_name_def)
  next
    case False
    with assms have "ren_name (distinct_fst (del_clashing (filter (\<lambda>x. map_of ?al' x = None) ?unknowns') ?al')) x \<noteq> x"
      by (simp add: rename_bvs_def Let_def)
    then obtain y where "(x, y) \<in> set ?al'"
      using set_distinct_fst set_del_clashing by (fastforce dest: ren_name_neq)
    then show ?thesis using set_distinct_fst by fastforce
  qed
  moreover have "set (fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tps xs) =
      (\<Union>(t, u)\<in>set tps. fst ` vars t \<union> fst ` vars u) \<union> set xs" for tps xs
  proof (induction tps arbitrary: xs)
    case (Cons p tps)
    obtain t u where "p = (t, u)" by (cases p)
    with Cons show ?case by (simp add: set_add_var_names Un_ac)
  qed simp
  moreover have "set (fold (add_var_names \<circ> fst) dps xs) = (\<Union>(t, u)\<in>set dps. fst ` vars t) \<union> set xs"
    for dps :: "(pterm \<times> pterm) list" and xs
  proof (induction dps arbitrary: xs)
    case (Cons p dps)
    obtain t u where "p = (t, u)" by (cases p)
    with Cons show ?case by (simp add: set_add_var_names Un_ac)
  qed simp
  ultimately show "\<forall>(t, u)\<in>set dpairs. x \<notin> fst ` vars t"
    "\<forall>(t, u)\<in>set tpairs. x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u"
    by auto
qed

lemma rename_bvars_unknowns:
  assumes "rename_bvars dpairs tpairs B As = Some r" "ren_name (fst r) x \<noteq> x"
  shows "\<forall>(t, u)\<in>set dpairs. x \<notin> fst ` vars t"
    "\<forall>(t, u)\<in>set tpairs. x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u"
  using assms rename_bvs_unknowns[of dpairs tpairs B As x]
  by (auto simp: rename_bvars_def Let_def split: if_splits)

lemma ren_name_SomeD: "ren_name tab x \<noteq> x \<Longrightarrow> (x, ren_name tab x) \<in> set tab"
  by (auto simp: ren_name_def split: option.splits dest: map_of_SomeD)

lemma rename_bvs_target:
  assumes "ren_name (fst (rename_bvs dpairs tpairs B As)) x \<noteq> x"
  shows "\<forall>(t, u)\<in>set dpairs. ren_name (fst (rename_bvs dpairs tpairs B As)) x \<notin> fst ` vars t"
    "\<forall>(t, u)\<in>set tpairs. ren_name (fst (rename_bvs dpairs tpairs B As)) x \<notin> fst ` vars t \<and>
      ren_name (fst (rename_bvs dpairs tpairs B As)) x \<notin> fst ` vars u"
proof -
  let ?y = "ren_name (fst (rename_bvs dpairs tpairs B As)) x"
  let ?al = "foldr match_bvars dpairs []"
  let ?unknowns = "fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tpairs
    (fold (add_var_names \<circ> fst) dpairs [])"
  let ?unknowns' = "fold (add_var_names \<circ> strip_lifted B) As []"
  let ?al' = "distinct_fst (filter (\<lambda>(x, y). \<not> (x \<notin> set ?unknowns' \<or> x \<in> set ?unknowns \<or> y \<in> set ?unknowns)) ?al)"
  have "?y \<notin> set ?unknowns"
  proof (cases "?al = []")
    case True
    with assms show ?thesis by (simp add: rename_bvs_def ren_name_def)
  next
    case False
    then have "fst (rename_bvs dpairs tpairs B As) =
        distinct_fst (del_clashing (filter (\<lambda>x. map_of ?al' x = None) ?unknowns') ?al')"
      by (simp add: rename_bvs_def Let_def)
    moreover have "(x, ?y) \<in> set (fst (rename_bvs dpairs tpairs B As))" by (rule ren_name_SomeD[OF assms])
    ultimately have "(x, ?y) \<in> set (distinct_fst (del_clashing (filter (\<lambda>x. map_of ?al' x = None) ?unknowns') ?al'))"
      by (simp only:)
    then have "(x, ?y) \<in> set ?al'"
      using set_distinct_fst set_del_clashing by blast
    then show ?thesis using set_distinct_fst by fastforce
  qed
  moreover have "set (fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tps xs) =
      (\<Union>(t, u)\<in>set tps. fst ` vars t \<union> fst ` vars u) \<union> set xs" for tps xs
  proof (induction tps arbitrary: xs)
    case (Cons p tps)
    obtain t u where "p = (t, u)" by (cases p)
    with Cons show ?case by (simp add: set_add_var_names Un_ac)
  qed simp
  moreover have "set (fold (add_var_names \<circ> fst) dps xs) = (\<Union>(t, u)\<in>set dps. fst ` vars t) \<union> set xs"
    for dps :: "(pterm \<times> pterm) list" and xs
  proof (induction dps arbitrary: xs)
    case (Cons p dps)
    obtain t u where "p = (t, u)" by (cases p)
    with Cons show ?case by (simp add: set_add_var_names Un_ac)
  qed simp
  ultimately show "\<forall>(t, u)\<in>set dpairs. ?y \<notin> fst ` vars t"
    "\<forall>(t, u)\<in>set tpairs. ?y \<notin> fst ` vars t \<and> ?y \<notin> fst ` vars u"
    by auto
qed

subsection \<open>The renaming is injective\<close>

text \<open>
  One pass of \<^const>\<open>del_clashing\<close> keeps or drops each renaming; a dropped source joins the
  unchanged names. If nothing is dropped, the targets are distinct and differ from the names
  seen before.
\<close>

lemma del_round_props:
  "del_round xs ys ps qs c = (c', xs', qs') \<Longrightarrow>
    set xs \<subseteq> set xs' \<and> fst ` set ps \<union> fst ` set qs \<subseteq> set xs' \<union> fst ` set qs' \<and> (c \<longrightarrow> c') \<and>
    (\<not> c' \<longrightarrow> xs' = xs \<and> qs' = rev ps @ qs \<and> distinct (map snd ps) \<and> (\<forall>(x, y)\<in>set ps. y \<notin> set ys))"
proof (induction xs ys ps qs c rule: del_round.induct)
  case (2 xs ys x y ps qs clash)
  show ?case
  proof (cases "y \<in> set ys")
    case True
    with "2.prems" have "del_round (x # xs) (x # ys) ps qs True = (c', xs', qs')" by simp
    from "2.IH"(1)[OF True this] show ?thesis by auto
  next
    case False
    with "2.prems" have "del_round xs (y # ys) ps ((x, y) # qs) clash = (c', xs', qs')" by simp
    from "2.IH"(2)[OF False this] False show ?thesis by (auto simp: image_iff)
  qed
qed simp

lemma del_clashing_props:
  "del_clashing xs ps = qs \<Longrightarrow> \<exists>xs'. set xs \<subseteq> set xs' \<and> fst ` set ps \<subseteq> set xs' \<union> fst ` set qs \<and>
    distinct (map snd qs) \<and> (\<forall>(x, y)\<in>set qs. y \<notin> set xs')"
proof (induction xs ps arbitrary: qs rule: del_clashing.induct)
  case (1 xs ps)
  obtain c xs1 qs1 where r: "del_round xs xs ps [] False = (c, xs1, qs1)"
    by (cases "del_round xs xs ps [] False")
  note dr = del_round_props[OF r]
  show ?case
  proof (cases c)
    case False
    with "1.prems" r have "qs = qs1" by (subst (asm) del_clashing.simps) simp
    with dr False show ?thesis by (intro exI[of _ xs]) (auto simp: rev_map[symmetric])
  next
    case True
    with "1.prems" r have "del_clashing xs1 qs1 = qs" by (subst (asm) del_clashing.simps) simp
    from "1.IH"[OF r[symmetric] refl True this] obtain xs' where
      "set xs1 \<subseteq> set xs'" "fst ` set qs1 \<subseteq> set xs' \<union> fst ` set qs" "distinct (map snd qs)"
      "\<forall>(x, y)\<in>set qs. y \<notin> set xs'"
      by blast
    moreover have "fst ` set ps \<subseteq> set xs' \<union> fst ` set qs" using dr calculation(1,2) by blast
    ultimately show ?thesis using dr by (intro exI[of _ xs']) auto
  qed
qed

lemma map_of_filter_fst: "map_of (filter (\<lambda>p. fst p \<noteq> x) ps) y = (if y = x then None else map_of ps y)"
  by (induction ps) auto

lemma map_of_distinct_fst: "map_of (distinct_fst ps) = map_of ps"
  by (induction ps rule: distinct_fst.induct) (auto simp: map_of_filter_fst fun_eq_iff)

text \<open>
  The renaming of the variables is injective on the names of the variables of the new premises,
  and its targets occur neither on the left of the disagreement pairs nor in the flex-flex pairs.
\<close>

lemma rename_bvs_inj:
  assumes "\<forall>x\<in>{x1, x2}. \<exists>A\<in>set As. x \<in> fst ` vars (strip_lifted B A)"
    "ren_name (fst (rename_bvs dpairs tpairs B As)) x1 = ren_name (fst (rename_bvs dpairs tpairs B As)) x2"
  shows "x1 = x2"
proof -
  let ?al = "foldr match_bvars dpairs []"
  let ?unknowns = "fold (\<lambda>(t, u). add_var_names u \<circ> add_var_names t) tpairs
    (fold (add_var_names \<circ> fst) dpairs [])"
  let ?unknowns' = "fold (add_var_names \<circ> strip_lifted B) As []"
  let ?al' = "distinct_fst (filter (\<lambda>(x, y). \<not> (x \<notin> set ?unknowns' \<or> x \<in> set ?unknowns \<or> y \<in> set ?unknowns)) ?al)"
  let ?unchanged = "filter (\<lambda>x. map_of ?al' x = None) ?unknowns'"
  let ?al'' = "del_clashing ?unchanged ?al'"
  have su: "set (fold (add_var_names \<circ> f) Xs ys) = (\<Union>X\<in>set Xs. fst ` vars (f X)) \<union> set ys"
    for f :: "pterm \<Rightarrow> pterm" and Xs ys
    by (induction Xs arbitrary: ys) (auto simp: set_add_var_names)
  have xu: "x1 \<in> set ?unknowns'" "x2 \<in> set ?unknowns'" using assms(1) su[of "strip_lifted B" As "[]"] by auto
  show ?thesis
  proof (cases "?al = []")
    case True
    with assms(2) show ?thesis by (simp add: rename_bvs_def ren_name_def)
  next
    case False
    then have ren: "ren_name (fst (rename_bvs dpairs tpairs B As)) x = ren_name ?al'' x" for x
      by (simp add: rename_bvs_def Let_def ren_name_def map_of_distinct_fst)
    from del_clashing_props[OF refl, of ?unchanged ?al'] obtain xs' where
      xs': "set ?unchanged \<subseteq> set xs'" "fst ` set ?al' \<subseteq> set xs' \<union> fst ` set ?al''"
      and ds: "distinct (map snd ?al'')" and tg: "\<forall>(x, y)\<in>set ?al''. y \<notin> set xs'"
      by blast
    have kept: "x \<in> set xs'" if "x \<in> set ?unknowns'" "map_of ?al'' x = None" for x
    proof (cases "map_of ?al' x")
      case None
      with that(1) xs'(1) show ?thesis by auto
    next
      case (Some y)
      then have "x \<in> fst ` set ?al'" by (force dest: map_of_SomeD)
      with xs'(2) that(2) show ?thesis by (auto simp: map_of_eq_None_iff)
    qed
    have e: "ren_name ?al'' x1 = ren_name ?al'' x2" using assms(2) by (simp only: ren)
    then have rn: "(case map_of ?al'' x1 of Some y \<Rightarrow> y | None \<Rightarrow> x1) =
        (case map_of ?al'' x2 of Some y \<Rightarrow> y | None \<Rightarrow> x2)"
      by (simp only: ren_name_def)
    show ?thesis
    proof (cases "map_of ?al'' x1"; cases "map_of ?al'' x2")
      fix y1 y2 assume m: "map_of ?al'' x1 = Some y1" "map_of ?al'' x2 = Some y2"
      then have "(x1, y1) \<in> set ?al''" "(x2, y2) \<in> set ?al''" by (auto dest: map_of_SomeD)
      moreover have "y1 = y2" using rn by (simp only: m option.case)
      moreover have "inj_on snd (set ?al'')" using ds by (simp add: distinct_map)
      ultimately show ?thesis using inj_onD[of snd "set ?al''" "(x1, y1)" "(x2, y2)"] by simp
    next
      fix y1 assume m: "map_of ?al'' x1 = Some y1" "map_of ?al'' x2 = None"
      then have "(x1, y1) \<in> set ?al''" by (auto dest: map_of_SomeD)
      moreover have "y1 = x2" using rn by (simp only: m option.case)
      ultimately show ?thesis using tg kept[OF xu(2) m(2)] by auto
    next
      fix y2 assume m: "map_of ?al'' x1 = None" "map_of ?al'' x2 = Some y2"
      then have "(x2, y2) \<in> set ?al''" by (auto dest: map_of_SomeD)
      moreover have "y2 = x1" using rn by (simp only: m option.case)
      ultimately show ?thesis using tg kept[OF xu(1) m(1)] by auto
    next
      assume m: "map_of ?al'' x1 = None" "map_of ?al'' x2 = None"
      from rn show ?thesis by (simp only: m option.case)
    qed
  qed
qed


end
