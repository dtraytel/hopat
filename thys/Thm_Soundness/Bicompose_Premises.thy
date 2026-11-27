section \<open>The New Premises of a Composition\<close>

theory Bicompose_Premises
  imports Bicompose_Sound
begin

text \<open>
  The renaming of the variables of the new premises of a composition, the properties of the new
  premises of a call of \<open>bicompose_aux\<close>, and the invariants of a unifier at a call. The
  theorems on the results of \<open>bicompose_aux\<close> (theory \<open>Bicompose_Theorems\<close>) and its
  termination (session \<open>Thm_Complete\<close>) use them.
\<close>

lemma okT_det: "okT m x \<Longrightarrow> okT m y \<Longrightarrow> x = y"
  by auto

context pure_sig_gen
begin

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

end

context pure_sig_gen
begin

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
    and hl: "\<And>x. x \<notin> loose \<Longrightarrow> h x \<notin> loose"
  shows "winv env Z"
proof -
  have ev: "evars env = {}" using te by (simp add: evars_def bnds_def vt_is_empty_lookup)
  show ?thesis unfolding winv_def
  proof (intro allI impI conjI)
    fix \<rho> assume t: "tsol (tyenv env) \<rho>" and c: "cert_inst \<rho>"
    show "wt_env \<rho> env" using te by (simp add: wt_env_def vt_is_empty_lookup)
    have "vcons \<rho> Z" unfolding vcons_def
    proof (intro allI impI)
      fix x T U assume nl: "x \<notin> loose" and "(x, T) \<in> Z" "(x, U) \<in> Z"
      with h have "(h x, T) \<in> X" "(h x, U) \<in> X" by blast+
      from vconsD[OF vc[OF t c] hl[OF nl] this] show "tsubst \<rho> T = tsubst \<rho> U" .
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
    from dstepDg(1)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t c] w(2)]
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

end

end
