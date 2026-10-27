section \<open>Completeness of Pattern Unification\<close>

theory Pattern_Unif_Complete
  imports Pattern_Completeness
begin

text \<open>
  The occurs check of \<^const>\<open>flexrigid\<close> follows bindings in the environment and does not
  \<open>\<beta>\<close>-normalise: it is only complete for \<open>\<beta>\<close>-normal patterns in environments whose bindings are
  \<open>\<beta>\<close>-normal patterns. We therefore state completeness for such inputs.
\<close>

subsection \<open>\<open>\<beta>\<close>-normal patterns\<close>

definition is_rigid :: "pterm \<Rightarrow> bool" where
  "is_rigid h \<longleftrightarrow> (\<exists>c T. h = Const c T) \<or> (\<exists>c T. h = Free c T) \<or> (\<exists>i. h = Bound i \<and> 0 \<le> i)"

inductive ppat :: "pterm \<Rightarrow> bool" where
  ppat_Abs: "ppat t \<Longrightarrow> ppat (Abs a T t)"
| ppat_rigid: "is_rigid h \<Longrightarrow> \<forall>t\<in>set ts. ppat t \<Longrightarrow> ppat (list_comb h ts)"
| ppat_flex: "distinct is \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> ppat (app (Var x T) is)"

definition env_ppat :: "env \<Rightarrow> bool" where
  "env_ppat env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ppat u)"

lemma env_ppatD: "env_ppat env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ppat u"
  by (cases x) (simp add: env_ppat_def)

lemma list_comb_Nil[simp]: "list_comb h [] = h"
  by (simp add: list_comb_def)

lemma list_comb_snoc: "list_comb h (ts @ [t]) = list_comb h ts $ t"
  by (simp add: list_comb_def)

lemma list_comb_Abs_iff:
  "list_comb h ts = Abs a T t \<longleftrightarrow> ts = [] \<and> h = Abs a T t"
  "Abs a T t = list_comb h ts \<longleftrightarrow> ts = [] \<and> h = Abs a T t"
  by (cases ts rule: rev_cases; auto simp: list_comb_snoc)+

lemma list_comb_eq_iff:
  assumes "\<not> (\<exists>f u. h = f $ u)" "\<not> (\<exists>f u. h' = f $ u)"
  shows "list_comb h ts = list_comb h' ts' \<longleftrightarrow> h = h' \<and> ts = ts'"
proof (induction ts arbitrary: ts' rule: rev_induct)
  case Nil
  show ?case using assms by (cases ts' rule: rev_cases) (auto simp: list_comb_snoc)
next
  case (snoc t ts)
  show ?case
  proof (cases ts' rule: rev_cases)
    case Nil
    then show ?thesis using assms by (auto simp: list_comb_snoc)
  next
    case (snoc ts'' t')
    with snoc.IH show ?thesis by (auto simp: list_comb_snoc)
  qed
qed

lemma is_rigid_not_App: "is_rigid h \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)"
  by (auto simp: is_rigid_def)

lemma integer_succ_pos: "0 \<le> (i :: integer) \<Longrightarrow> 0 < i + 1"
  by transfer simp

lemma ppat_AbsD: "ppat (Abs a T t) \<Longrightarrow> ppat t"
  by (cases rule: ppat.cases) (auto simp: list_comb_Abs_iff is_rigid_def app_list_comb)

lemma ppat_spine:
  assumes "ppat (list_comb h ts)" "\<not> (\<exists>f u. h = f $ u)" "\<not> is_Abs (list_comb h ts)"
  shows "is_rigid h \<and> (\<forall>t\<in>set ts. ppat t) \<or> (\<exists>x T. h = Var x T)"
  using assms(1)
proof (cases rule: ppat.cases)
  case (ppat_Abs t a T)
  with assms(3) show ?thesis by simp
next
  case (ppat_rigid h' ts')
  with list_comb_eq_iff[OF assms(2) is_rigid_not_App[OF ppat_rigid(2)]] show ?thesis by auto
next
  case (ppat_flex iss x T)
  with list_comb_eq_iff[OF assms(2), of "Var x T" ts "map Bound iss"] show ?thesis
    by (auto simp: app_list_comb)
qed

lemma ppat_proper: "ppat t \<Longrightarrow> proper t"
  by (induction rule: ppat.induct) (auto simp: proper_list_comb is_rigid_def app_list_comb)

lemma incr_aux_list_comb:
  "incr_aux d (list_comb h ts) = list_comb (incr_aux d h) (map (incr_aux d) ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma incr_aux_app:
  "incr_aux d (app (Var x T) is) = app (Var x T) (map (\<lambda>i. if i < d then i else i + 1) is)"
  by (simp add: app_list_comb incr_aux_list_comb comp_def if_distrib)

lemma ppat_incr_aux: "ppat t \<Longrightarrow> 0 \<le> d \<Longrightarrow> ppat (incr_aux d t)"
proof (induction arbitrary: d rule: ppat.induct)
  case (ppat_Abs t a T)
  then show ?case by (auto intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "is_rigid (incr_aux d h)" using ppat_rigid.hyps(1)
    by (auto simp: is_rigid_def less_imp_le integer_succ_pos split: if_splits)
  with ppat_rigid show ?case by (auto simp: incr_aux_list_comb intro!: ppat.ppat_rigid)
next
  case (ppat_flex iss x T)
  have "inj_on (\<lambda>i. if i < d then i else i + 1) (set iss)" by (auto simp: inj_on_def split: if_splits)
  with ppat_flex show ?case
    by (auto simp: incr_aux_app distinct_map less_imp_le integer_succ_pos intro!: ppat.ppat_flex)
qed

lemma ppat_incr_Bound0:
  assumes "ppat t" "\<not> is_Abs t"
  shows "ppat (incr t $ Bound 0)"
  using assms(1)
proof (cases rule: ppat.cases)
  case (ppat_Abs t a T)
  with assms(2) show ?thesis by simp
next
  case (ppat_rigid h ts)
  have "is_rigid (incr_aux 0 h)" using ppat_rigid(2)
    by (auto simp: is_rigid_def less_imp_le integer_succ_pos)
  moreover have "ppat (Bound 0)" using ppat.ppat_rigid[of "Bound 0" "[]"] by (simp add: is_rigid_def)
  moreover have "incr t $ Bound 0 = list_comb (incr_aux 0 h) (map (incr_aux 0) ts @ [Bound 0])"
    by (simp add: ppat_rigid(1) incr_def incr_aux_list_comb list_comb_snoc)
  ultimately show ?thesis using ppat_rigid(3) ppat_incr_aux[of _ 0]
    by (auto intro!: ppat.ppat_rigid)
next
  case (ppat_flex iss x T)
  have mm: "map (\<lambda>i. if i < 0 then i else i + 1) iss = map (\<lambda>i. i + 1) iss"
    using ppat_flex(3) by (auto intro: map_cong)
  have "incr t = app (Var x T) (map (\<lambda>i. i + 1) iss)"
    by (simp only: ppat_flex(1) incr_def incr_aux_app mm)
  then have "incr t $ Bound 0 = app (Var x T) (map (\<lambda>i. i + 1) iss @ [0])"
    by (simp add: app_def)
  moreover have "distinct (map (\<lambda>i. i + 1) iss @ [0])"
    using ppat_flex(2,3) integer_succ_pos by (fastforce simp: distinct_map inj_on_def)
  moreover have "\<forall>i\<in>set (map (\<lambda>i. i + 1) iss @ [0]). 0 \<le> i"
    using ppat_flex(3) integer_succ_pos by (fastforce intro: less_imp_le)
  ultimately show ?thesis by (auto intro!: ppat.ppat_flex)
qed

lemma subst_bound_aux_list_comb:
  "subst_bound_aux arg lev (list_comb h ts) = list_comb (subst_bound_aux arg lev h) (map (subst_bound_aux arg lev) ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma incr_boundvars_Bound: "0 \<le> y \<Longrightarrow> incr_boundvars lev (Bound y) = Bound (y + lev)"
  by (simp add: incr_boundvars_def)

lemma subst_bound_aux_Bound_Bound:
  "0 \<le> y \<Longrightarrow> 0 \<le> lev \<Longrightarrow> subst_bound_aux (Bound y) lev (Bound i) =
    Bound (if i < lev then i else if i = lev then y + lev else i - 1)"
  by (auto simp: incr_boundvars_def add.commute)

lemma subst_bound_aux_app:
  "0 \<le> y \<Longrightarrow> 0 \<le> lev \<Longrightarrow> subst_bound_aux (Bound y) lev (app (Var x T) is) =
    app (Var x T) (map (\<lambda>i. if i < lev then i else if i = lev then y + lev else i - 1) is)"
proof -
  assume "0 \<le> y" "0 \<le> lev"
  then have "map (subst_bound_aux (Bound y) lev) (map Bound is) =
      map Bound (map (\<lambda>i. if i < lev then i else if i = lev then y + lev else i - 1) is)"
    by (simp add: subst_bound_aux_Bound_Bound del: subst_bound_aux.simps)
  moreover have "subst_bound_aux (Bound y) lev (Var x T) = Var x T" by simp
  ultimately show ?thesis by (simp only: app_list_comb subst_bound_aux_list_comb)
qed

lemma integer_pred_nonneg: "0 \<le> lev \<Longrightarrow> \<not> i < lev \<Longrightarrow> i \<noteq> lev \<Longrightarrow> 0 \<le> (i :: integer) - 1"
  by (simp add: integer_eq_iff less_eq_integer.rep_eq less_integer.rep_eq)

lemma subst_ren_inj:
  fixes i j y lev :: integer
  assumes "0 \<le> y" "i \<noteq> y + lev + 1" "j \<noteq> y + lev + 1"
    "(if i < lev then i else if i = lev then y + lev else i - 1) =
     (if j < lev then j else if j = lev then y + lev else j - 1)"
  shows "i = j"
  using assms by (auto split: if_splits simp: integer_eq_iff less_eq_integer.rep_eq less_integer.rep_eq)

lemma subst_ren_nonneg:
  fixes i y lev :: integer
  assumes "0 \<le> y" "0 \<le> lev" "0 \<le> i"
  shows "0 \<le> (if i < lev then i else if i = lev then y + lev else i - 1)"
  using assms by (auto split: if_splits simp: integer_eq_iff less_eq_integer.rep_eq less_integer.rep_eq)

lemma loose_BVars_tr_app: "loose_BVars (tr (app (Var x T) is)) = set (nats is)"
  by (auto simp: tr_app')

lemma ppat_subst_bound_aux:
  assumes "ppat t" "0 \<le> lev" "0 \<le> y" "Suc (nat_of_integer y + nat_of_integer lev) \<notin> loose_BVars (tr t)"
  shows "ppat (subst_bound_aux (Bound y) lev t)"
  using assms
proof (induction arbitrary: lev rule: ppat.induct)
  case (ppat_Abs t a T)
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using ppat_Abs.prems(1)
    by (simp add: nat_of_integer_add)
  then have "Suc (nat_of_integer y + nat_of_integer (lev + 1)) \<notin> loose_BVars (tr t)"
    using ppat_Abs.prems(3) by simp
  with ppat_Abs show ?case by (auto intro: ppat.ppat_Abs)
next
  case (ppat_rigid h ts)
  have "is_rigid (subst_bound_aux (Bound y) lev h)"
  proof -
    from ppat_rigid.hyps(1) consider c U where "h = Const c U" | c U where "h = Free c U"
      | i where "h = Bound i" "0 \<le> i" by (auto simp: is_rigid_def)
    then show ?thesis
    proof cases
      case 3
      then show ?thesis using ppat_rigid.prems(1,2)
        by (simp add: subst_bound_aux_Bound_Bound subst_ren_nonneg is_rigid_def del: subst_bound_aux.simps)
    qed (simp_all add: is_rigid_def)
  qed
  moreover have "ppat (subst_bound_aux (Bound y) lev t)" if "t \<in> set ts" for t
    using ppat_rigid.IH that ppat_rigid.prems by (auto simp: tr_list_comb)
  ultimately show ?case by (auto simp: subst_bound_aux_list_comb intro!: ppat.ppat_rigid)
next
  case (ppat_flex iss x T)
  let ?g = "\<lambda>i. if i < lev then i else if i = lev then y + lev else i - 1"
  have nin: "y + lev + 1 \<notin> set iss"
  proof
    assume "y + lev + 1 \<in> set iss"
    then have "nat_of_integer (y + lev + 1) \<in> set (nats iss)" by simp
    moreover have "nat_of_integer (y + lev + 1) = Suc (nat_of_integer y + nat_of_integer lev)"
      using ppat_flex.prems(1,2) by (simp add: nat_of_integer_add)
    ultimately show False using ppat_flex.prems(3) by (simp add: loose_BVars_tr_app)
  qed
  have "inj_on ?g (set iss)"
  proof (rule inj_onI)
    fix i j assume "i \<in> set iss" "j \<in> set iss" "?g i = ?g j"
    with nin ppat_flex.prems(2) show "i = j" by (intro subst_ren_inj[of y i lev j]) auto
  qed
  moreover have "\<forall>i\<in>set iss. 0 \<le> ?g i" using ppat_flex.hyps(2) ppat_flex.prems(1,2) subst_ren_nonneg by blast
  moreover have "\<forall>j\<in>set (map ?g iss). 0 \<le> j" using calculation(2) by (simp only: set_map) blast
  ultimately have "ppat (app (Var x T) (map ?g iss))"
    using ppat_flex.hyps(1) by (intro ppat.ppat_flex) (simp_all add: distinct_map)
  then show ?case using ppat_flex.prems(1,2) by (simp add: subst_bound_aux_app)
qed

lemma ppat_subst_bound:
  "ppat t \<Longrightarrow> 0 \<le> y \<Longrightarrow> Suc (nat_of_integer y) \<notin> loose_BVars (tr t) \<Longrightarrow> ppat (subst_bound (Bound y) t)"
  using ppat_subst_bound_aux[of t 0 y] by (simp add: subst_bound_def)

lemma list_comb_eq_App:
  "list_comb h ts = f $ u \<Longrightarrow> \<not> (\<exists>f u. h = f $ u) \<Longrightarrow> \<exists>ts'. ts = ts' @ [u] \<and> f = list_comb h ts'"
  by (cases ts rule: rev_cases) (auto simp: list_comb_snoc)

lemma ppat_AppE:
  assumes "ppat (f $ u)"
  obtains (rigid) h ts where "is_rigid h" "f = list_comb h ts" "\<forall>t\<in>set ts. ppat t" "ppat u"
  | (flex) x T iss i where "f = app (Var x T) iss" "u = Bound i" "distinct (iss @ [i])"
      "\<forall>j\<in>set (iss @ [i]). 0 \<le> j"
  using assms
proof (cases rule: ppat.cases)
  case (ppat_rigid h ts)
  from list_comb_eq_App[OF ppat_rigid(1)[symmetric] is_rigid_not_App[OF ppat_rigid(2)]]
  obtain ts' where "ts = ts' @ [u]" "f = list_comb h ts'" by blast
  with ppat_rigid show ?thesis using rigid by auto
next
  case (ppat_flex iss x T)
  from list_comb_eq_App[OF ppat_flex(1)[symmetric, unfolded app_list_comb]]
  obtain ts' where "map Bound iss = ts' @ [u]" "f = list_comb (Var x T) ts'" by auto
  then obtain iss' i where "iss = iss' @ [i]" "u = Bound i" "ts' = map Bound iss'"
    by (cases iss rule: rev_cases) auto
  with ppat_flex \<open>f = list_comb (Var x T) ts'\<close> show ?thesis using flex by (auto simp: app_list_comb)
qed

definition rigid_head :: "pterm \<Rightarrow> bool" where
  "rigid_head t \<longleftrightarrow> (\<exists>h ts. t = list_comb h ts \<and> is_rigid h)"

lemma not_rigid_head_app: "\<not> rigid_head (app (Var x T) is)"
proof
  assume "rigid_head (app (Var x T) is)"
  then obtain h ts where "list_comb (Var x T) (map Bound is) = list_comb h ts" "is_rigid h"
    by (auto simp: rigid_head_def app_list_comb)
  with list_comb_eq_iff[of "Var x T" h] is_rigid_not_App show False
    by (auto simp: is_rigid_def)
qed

lemma rigid_head_cases: "rigid_head t \<Longrightarrow> is_rigid t \<or> (\<exists>f u. t = f $ u)"
  unfolding rigid_head_def by (metis list_comb_Nil list_comb_snoc rev_exhaust)

lemma ppat_nonAbsE:
  assumes "ppat t" "\<not> is_Abs t"
  obtains (rigid) h ts where "is_rigid h" "t = list_comb h ts" "\<forall>t\<in>set ts. ppat t"
  | (flex) x T iss where "t = app (Var x T) iss" "distinct iss" "\<forall>j\<in>set iss. 0 \<le> j"
  using assms by (cases rule: ppat.cases) auto

lemma head_norm_ppat_aux:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow>
    ppat t' \<and> loose_BVars (tr t') \<subseteq> loose_BVars (tr t) \<and> (rigid_head t \<longrightarrow> t' = t)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and epp: "env_ppat env" and pt: "ppat t" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  note IH = "1.IH"[OF _ refl wf epp]
  show ?case
  proof (cases t)
    case (Var xi U)
    have nr: "\<not> rigid_head t" using Var rigid_head_cases[of t] by (auto simp: is_rigid_def)
    from Var t' obtain r' where lk: "ok (lookup env xi U) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest pt show ?thesis by auto
    next
      case 2
      with rest have hu: "hn env u = Some (Ok t')" by simp
      have "loose_BVars (tr u) = {}"
        using wf_envD(2)[OF wf 2(2)] by (simp add: no_loose_bound_loose_BVars)
      with IH[OF hu env_ppatD[OF epp 2(2)]] nr show ?thesis by simp
    qed
  next
    case (Abs a U body)
    have nr: "\<not> rigid_head t" using Abs rigid_head_cases[of t] by (auto simp: is_rigid_def)
    with t' obtain b' where hb: "hn env body = Some (Ok b')" and tb: "t' = pterm.Abs a U b'"
      using Abs by auto
    from IH[OF hb ppat_AbsD[OF pt[unfolded Abs]]] have "ppat b'" "loose_BVars (tr b') \<subseteq> loose_BVars (tr body)"
      by simp_all
    with tb Abs nr show ?thesis by (auto intro: ppat.ppat_Abs)
  next
    case (App f u)
    from pt[unfolded App] show ?thesis
    proof (cases rule: ppat_AppE)
      case (rigid h ts)
      have nA: "\<not> is_Abs f" using rigid(1,2) by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_snoc)
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have "rigid_head f" using rigid(1,2) by (auto simp: rigid_head_def)
      with IH[OF nf] rigid have "nf = f" by (auto intro: ppat.ppat_rigid)
      with rest nA have "t' = t" using App by (cases f) auto
      with pt show ?thesis by simp
    next
      case (flex x T iss i)
      have nA: "\<not> is_Abs f" using flex(1) by (cases iss rule: rev_cases) (auto simp: app_def)
      have nr: "\<not> rigid_head t" using flex(1,2) App not_rigid_head_app[of x T "iss @ [i]"] by (simp add: app_def)
      have pf: "ppat f" using flex(1,3,4) by (auto intro: ppat.ppat_flex)
      with t' App nA obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF nf pf] have pnf: "ppat nf" and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
        using flex(1) by (simp_all add: loose_BVars_tr_app)
      have i0: "0 \<le> i" using flex(4) by simp
      have ni: "nat_of_integer i \<notin> set (nats iss)"
      proof
        assume "nat_of_integer i \<in> set (nats iss)"
        then obtain j where "j \<in> set iss" "nat_of_integer j = nat_of_integer i" by auto
        with flex(4) i0 have "i \<in> set iss" by (auto simp: nat_of_integer_eq_iff)
        with flex(3) show False by simp
      qed
      have lt: "loose_BVars (tr t) = insert (nat_of_integer i) (set (nats iss))"
        using App flex(1,2) by (auto simp: tr_app')
      note fl = flex
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a U body where Abs: "nf = pterm.Abs a U body" by (cases nf) auto
        with rest have hb: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have pb: "ppat body" using pnf Abs by (auto dest: ppat_AbsD)
        have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)"
          using lnf ni Abs by auto
        from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound u body)" using fl(2) by simp
        have "loose_BVars (tr (subst_bound u body)) \<subseteq> insert (nat_of_integer i) (loose_BVars (dB.Abs (tr body)))"
          using fl(2) ppat_proper[OF pb] i0 loose_BVars_subst_BVar0[of "tr body" "nat_of_integer i"]
          by (simp add: tr_subst_bound)
        with lnf Abs lt have "loose_BVars (tr (subst_bound u body)) \<subseteq> loose_BVars (tr t)" by auto
        with IH[OF hb ps] nr show ?thesis by auto
      next
        case False
        with rest have tt: "t' = nf $ u" by (cases nf) auto
        have lt': "loose_BVars (tr t') \<subseteq> loose_BVars (tr t)" using tt fl(2) lnf lt by auto
        from pnf False show ?thesis
        proof (cases rule: ppat_nonAbsE)
          case (rigid h ts)
          have "ppat (Bound i)" using ppat.ppat_rigid[of "Bound i" "[]"] i0 by (simp add: is_rigid_def)
          then have "ppat t'" using tt rigid fl(2) ppat.ppat_rigid[of h "ts @ [Bound i]"]
            by (auto simp: list_comb_snoc)
          with lt' nr show ?thesis by simp
        next
          case (flex y V jss)
          have "i \<notin> set jss"
          proof
            assume "i \<in> set jss"
            then have "nat_of_integer i \<in> loose_BVars (tr nf)" using flex(1) by (auto simp: tr_app')
            with lnf ni show False by auto
          qed
          then have "ppat (app (Var y V) (jss @ [i]))" using flex(2,3) i0 by (auto intro!: ppat.ppat_flex)
          then have "ppat t'" using tt flex(1) fl(2) by (simp add: app_def)
          with lt' nr show ?thesis by simp
        qed
      qed
    qed
  qed (use t' pt in auto)
qed

lemma head_norm_ppat:
  "head_norm env t = Some (Ok t') \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow> ppat t'"
  using head_norm_ppat_aux by blast


lemma occurs_complete:
  assumes "ok (occurs F t env) True" "ppat t" "t = list_comb h ts" "is_rigid h"
    "env_ppat env" "wf_env ar env" "env_typed V env" "has_type V Ts t T"
    "has_type V Ts (app (Var F Fty) is) T" "distinct is" "solution V \<tau>' \<sigma> env"
    "unifies \<sigma> (tr (app (Var F Fty) is)) (tr t)"
  shows False
  sorry

lemma env_ppat_update:
  assumes "ok (update (F, T) t env) env'" "env_ppat env" "ppat t"
  shows "env_ppat env'"
  unfolding env_ppat_def ok_update(2)[OF assms(1)]
proof (intro allI impI)
  fix x U u assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u)"
  then show "ppat u" using assms(2,3) env_ppatD by (auto split: if_splits)
qed

lemma env_ppat_genvar: "genvar a env T = (env', G) \<Longrightarrow> env_ppat env' \<longleftrightarrow> env_ppat env"
  by (simp add: env_ppat_def genvar_simps)

lemma ppat_mkabs: "ok (mkabs binders is b) u \<Longrightarrow> ppat b \<Longrightarrow> ppat u"
  by (induction "is" arbitrary: u) (auto split: prod.splits intro: ppat.ppat_Abs)

lemma integer_le_pred_iff: "(x :: integer) \<le> k - 1 \<longleftrightarrow> x < k"
  by (simp add: less_eq_integer.rep_eq less_integer.rep_eq)

lemma distinct_sorted_gt: "sorted_wrt (>) xs \<Longrightarrow> distinct (xs :: 'a :: linorder list)"
  by (induction xs) auto

lemma mk_ff_list_aux_sorted:
  "ok (mk_ff_list_aux is js k) ks \<Longrightarrow> sorted_wrt (>) ks \<and> (\<forall>x\<in>set ks. x \<le> k)"
proof (induction "is" js k arbitrary: ks rule: mk_ff_list_aux.induct)
  case (2 i "is" j js k)
  then show ?case by (cases "i = j") (fastforce simp: integer_le_pred_iff intro: less_imp_le)+
qed auto

lemma ok_mk_ff_list_ppat:
  assumes "ok (mk_ff_list is js) ks"
  shows "distinct ks" "\<forall>k\<in>set ks. 0 \<le> k"
  using mk_ff_list_aux_sorted[OF assms[unfolded mk_ff_list_def]] mk_ff_list_ren(2)[OF assms]
  by (auto intro: distinct_sorted_gt)

lemma flexflex1_ppat:
  assumes "flexflex1 env binders F Fty is js = Some (Ok env')" "env_ppat env"
  shows "env_ppat env'"
proof (cases "is = js")
  case True
  with assms show ?thesis by (simp add: flexflex1_def)
next
  case False
  with assms(1) obtain ks where ks: "ok (mk_ff_list is js) ks"
    and hnf: "ok (mk_new_hnf env binders is F Fty ks) env'"
    by (auto simp: flexflex1_def)
  from hnf obtain Gty env1 G t where G: "genvar (fst F) env Gty = (env1, G)"
    and t: "ok (mkabs binders is (app G ks)) t" and env': "ok (update (F, Fty) t env1) env'"
    by (rule ok_mk_new_hnf)
  note ppk = ok_mk_ff_list_ppat[OF ks]
  have "ppat t" using ppat_mkabs[OF t] genvar_simps(4)[OF G] ppk by (auto intro: ppat.ppat_flex)
  with env_ppat_update[OF env'] env_ppat_genvar[OF G] assms(2) show ?thesis by simp
qed

lemma ok_idx_inj:
  assumes "ok (idx xs y) k" "ok (idx xs y') k"
  shows "y = y'"
proof -
  from assms obtain n n' where n: "Unification.idx xs y = Some n" "k = integer_of_nat n"
    and n': "Unification.idx xs y' = Some n'" "k = integer_of_nat n'"
    by (auto simp: ok_idx)
  from n(2) n'(2) have "n = n'" by (metis nat_of_integer_integer_of_nat)
  with idx_SomeD[OF n(1)] idx_SomeD[OF n'(1)] show ?thesis by simp
qed

lemma ok_mapM_idx_distinct: "ok (mapM (idx xs) ys) ks \<Longrightarrow> distinct ys \<Longrightarrow> distinct ks"
proof -
  assume "ok (mapM (idx xs) ys) ks" "distinct ys"
  then have "list_all2 (\<lambda>y k. ok (idx xs y) k) ys ks" "distinct ys" by (simp_all add: ok_mapM)
  then show "distinct ks"
  proof (induction ys ks rule: list_all2_induct)
    case (Cons y ys k ks)
    have "k \<notin> set ks"
    proof
      assume "k \<in> set ks"
      then obtain p where p: "p < length ks" "ks ! p = k" by (auto simp: in_set_conv_nth)
      with Cons.hyps(2) have "ok (idx xs (ys ! p)) k" "ys ! p \<in> set ys"
        by (auto simp: list_all2_conv_all_nth)
      with ok_idx_inj[OF Cons.hyps(1)] Cons.prems show False by auto
    qed
    with Cons show ?case by simp
  qed simp
qed

lemma ff_ppat:
  assumes ff: "ff env binders F Fty is G Gty js = Some (Ok env')" and epp: "env_ppat env"
    and dist: "distinct is" "distinct js" and nonneg: "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j"
  shows "env_ppat env'"
proof (cases "subset js is")
  case True
  with ff obtain ks t where ks: "ok (mapM (idx is) js) ks"
    and t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
    and env': "ok (update (F, Fty) t env) env'"
    by (auto simp: ff_def)
  have "ppat t"
    using ppat_mkabs[OF t] ok_mapM_idx_distinct[OF ks dist(2)] ok_mapM_idx(1)[OF ks nonneg]
    by (auto intro: ppat.ppat_flex)
  with env_ppat_update[OF env' epp] show ?thesis .
next
  case False
  let ?ks = "inter js is"
  from False ff obtain Hty where
    rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
      (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) \<bind> (\<lambda>tG.
      (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) \<bind> (\<lambda>tF.
      update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
    by (auto simp: ff_def Let_def)
  obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
  with rest obtain ksG tG ksF tF env2 where
    ksG: "ok (mapM (idx js) ?ks) ksG" and tG: "ok (mkabs binders js (app H ksG)) tG"
    and ksF: "ok (mapM (idx is) ?ks) ksF" and tF: "ok (mkabs binders is (app H ksF)) tF"
    and env2: "ok (update (F, Fty) tF env1) env2" and env': "ok (update (G, Gty) tG env2) env'"
    by auto
  have dk: "distinct ?ks" using dist(1) by (simp add: inter_def)
  have nk: "\<forall>k\<in>set ?ks. 0 \<le> k" using nonneg(1) by (auto simp: inter_def)
  have HV: "\<exists>x T. H = pterm.Var x T" using genvar_simps(4)[OF H] by blast
  have "ppat tG"
    using ppat_mkabs[OF tG] ok_mapM_idx_distinct[OF ksG dk] ok_mapM_idx(1)[OF ksG nonneg(2) nk] HV
    by (auto intro: ppat.ppat_flex)
  moreover have "ppat tF"
    using ppat_mkabs[OF tF] ok_mapM_idx_distinct[OF ksF dk] ok_mapM_idx(1)[OF ksF nonneg(1) nk] HV
    by (auto intro: ppat.ppat_flex)
  ultimately show ?thesis
    using env_ppat_update[OF env'] env_ppat_update[OF env2] env_ppat_genvar[OF H] epp by simp
qed

lemma flexflex2_ppat:
  "flexflex2 env binders F Fty is G Gty js = Some (Ok env') \<Longrightarrow> env_ppat env \<Longrightarrow>
    distinct is \<Longrightarrow> distinct js \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> \<forall>j\<in>set js. 0 \<le> j \<Longrightarrow> env_ppat env'"
  by (auto simp: flexflex2_def split: if_splits intro: ff_ppat)

lemma mk_proj_list_aux_sorted:
  "sorted_wrt (>) (mk_proj_list_aux os j) \<and> (\<forall>x\<in>set (mk_proj_list_aux os j). x \<le> j)"
proof (induction os arbitrary: j)
  case (Cons opt os)
  from Cons.IH[of "j - 1"] have "sorted_wrt (>) (mk_proj_list_aux os (j - 1))"
    "\<forall>x\<in>set (mk_proj_list_aux os (j - 1)). x < j"
    by (auto simp: integer_le_pred_iff)
  then show ?case by (auto intro: less_imp_le)
qed simp

lemma distinct_map_filter_rel:
  assumes "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> f l = g j)) js os" "distinct (map g js)"
  shows "distinct (List.map_filter id os)"
  using assms
proof (induction js os rule: list_all2_induct)
  case (Cons j js opt os)
  have sub: "f ` set (List.map_filter id os) \<subseteq> g ` set js"
  proof
    fix z assume "z \<in> f ` set (List.map_filter id os)"
    then obtain l where l: "l \<in> set (List.map_filter id os)" "z = f l" by blast
    from l(1) have "Some l \<in> set os" by (simp add: set_map_filter_id)
    then obtain p where p: "p < length os" "os ! p = Some l" by (auto simp: in_set_conv_nth)
    have lp: "p < length js" using p(1) list_all2_lengthD[OF Cons.hyps(2)] by simp
    from list_all2_nthD[OF Cons.hyps(2) lp] p(2) have "f l = g (js ! p)" by simp
    with lp l(2) show "z \<in> g ` set js" by simp
  qed
  show ?case
  proof (cases opt)
    case None
    with Cons show ?thesis by simp
  next
    case (Some l)
    with Cons.hyps(1) have fl: "f l = g j" by simp
    have "l \<notin> set (List.map_filter id os)"
    proof
      assume l: "l \<in> set (List.map_filter id os)"
      have "g j \<in> g ` set js" using subsetD[OF sub imageI[OF l]] fl by simp
      with Cons.prems show False by simp
    qed
    with Some Cons show ?thesis by (simp add: id_def)
  qed
qed simp

lemma pr_ppat:
  assumes "pr xs s env d binders = Some r"
  shows "r = Ok (s', env') \<Longrightarrow> wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_ppat env \<Longrightarrow>
    ppat s \<Longrightarrow> typs_ok ar s \<Longrightarrow> 0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow>
    ppat s' \<and> env_ppat env' \<and> wf_env ar env'"
  using assms
proof (induction xs s env d binders r arbitrary: s' env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d binders r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and epp: "env_ppat env"
    and ps: "ppat s" "typs_ok ar s" and d: "0 \<le> d" and xs: "\<forall>x\<in>set xs. 0 \<le> x"
    using "1.prems" by simp_all
  define R where "R = (\<lambda>s0. if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))"
  from "1.hyps" "1.prems"(1) have "ok (head_norm env s \<bind> R) (s', env')"
    unfolding R_def by (simp only:)
  then obtain s0 where hn: "ok (head_norm env s) s0" and rest0: "ok (R s0) (s', env')"
    unfolding ok_bindM by blast
  note rest = rest0[unfolded R_def]
  from head_norm_sound[OF hn refl wf] ps ppat_proper[OF ps(1)]
  have s0: "proper s0" "typs_ok ar s0" by auto
  have pp0: "ppat s0" by (rule head_norm_ppat[OF hn wf epp ps(1)])
  show ?case
  proof (cases "is_Abs s0")
    case True
    then obtain a T t where s0a: "s0 = pterm.Abs a T t" by (cases s0) auto
    with rest True obtain t' where t': "ok (prr xs t env (d + 1) ((a, T) # binders)) (t', env')"
      and s': "s' = pterm.Abs a T t'"
      by (auto split: prod.splits)
    have bok': "binders_ok ar ((a, T) # binders)" using bok s0 s0a by (simp add: binders_ok_def)
    have "d + 1 \<ge> 0" using d by simp
    from "1.IH"[OF t' refl wf bok' epp _ _ this xs] pp0 s0 s0a
    have "ppat t'" "env_ppat env'" "wf_env ar env'" by (auto dest: ppat_AbsD)
    with s' show ?thesis by (auto intro: ppat.ppat_Abs)
  next
    case False
    obtain h ts where hts: "strip_comb s0 = (h, ts)" by force
    note s0_eq = strip_comb_list_comb[OF hts]
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
    note sp = ppat_spine[OF pp0[unfolded s0_eq] nApp False[unfolded s0_eq]]
    have ts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t" "typs_ok ar h"
      using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = pterm.Var F Fty" by (cases h) auto
      from rest False hts h obtain js js' Hty where js: "ok (ints_of' env ts) js"
        and js': "ok (mapM (try_trans xs d) js) js'"
        and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
        and rest2: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow>
          mk_hnf binders js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
            (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (s', env')"
        by (auto simp: Let_def)
      obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
      with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
        and env': "ok (update (F, Fty) t env1) env'" and s': "s' = app H (List.map_filter id js')"
        by (auto simp: mk_hnf_def)
      note ints = ints_of'_sound[OF js wf ts(1)]
      have js'2: "list_all2 (\<lambda>j opt. ok (try_trans xs d j) opt) js js'" using js' by (simp add: ok_mapM)
      then have len: "length js' = length js" by (simp add: list_all2_lengthD)
      have tt: "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> 0 \<le> l \<and>
          nat_of_integer l < nat_of_integer d + length xs \<and>
          bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer j)) js js'"
      proof -
        have "js' ! p = None \<or> (\<exists>l. js' ! p = Some l \<and> 0 \<le> l \<and>
          nat_of_integer l < nat_of_integer d + length xs \<and>
          bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer (js ! p))"
          if p: "p < length js" for p
        proof -
          from js'2 p have "ok (try_trans xs d (js ! p)) (js' ! p)" by (simp add: list_all2_conv_all_nth)
          from ok_try_trans[OF this d _ xs] ints(2) p show ?thesis by auto
        qed
        with len show ?thesis by (simp add: list_all2_conv_all_nth)
      qed
      have HV: "H = pterm.Var (fst F, maxidx env + 1) Hty" by (rule genvar_simps(4)[OF G])
      have dks: "distinct (mk_proj_list js')"
        using mk_proj_list_aux_sorted[of js' "ilength js' - 1"] by (auto simp: mk_proj_list_def intro: distinct_sorted_gt)
      have ks_b: "\<forall>k\<in>set (mk_proj_list js'). 0 \<le> k \<and> nat_of_integer k < length js"
        using mk_proj_list_ren(2)[of "nats js" js'] len by simp
      have "ppat t" using ppat_mkabs[OF t] HV dks ks_b by (auto intro: ppat.ppat_flex)
      then have epp': "env_ppat env'" using env_ppat_update[OF env'] env_ppat_genvar[OF G] epp by simp
      have gF: "ground ar Fty" using ts(2) h by simp
      have Hg: "ground ar Hty" by (rule type_of_G_ground[OF Hty wf_envD(1)[OF wf] gF])
      have wf': "wf_env ar env'"
        by (rule binding_sound(2)[OF t[unfolded HV] env' genvar_wf_env[OF G wf] gF Hg bok ks_b])
      have "distinct (map nat_of_integer js)"
        using ints(1,2) by (auto simp: distinct_map intro: inj_on_nat_of_integer)
      moreover have "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and>
          bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer j)) js js'"
        using tt by (rule list_all2_mono) auto
      ultimately have dls: "distinct (List.map_filter id js')"
        by (intro distinct_map_filter_rel) auto
      have "\<forall>l\<in>set (List.map_filter id js'). 0 \<le> l"
        using tt by (fastforce simp: set_map_filter_id list_all2_conv_all_nth in_set_conv_nth)
      with dls HV have "ppat s'" by (auto simp: s' intro: ppat.ppat_flex)
      with epp' wf' show ?thesis by simp
    next
      case notVar: False
      have rig: "is_rigid h" "\<forall>t\<in>set ts. ppat t" using sp notVar by auto
      have nAbs: "\<not> is_Abs h" using rig(1) by (auto simp: is_rigid_def)
      from rest False hts notVar nAbs obtain h' ts' where
        h': "ok (case h of Bound i \<Rightarrow> trans xs d i \<bind> (\<lambda>j. return (Bound j)) | _ \<Rightarrow> return h) h'"
        and mt: "ok (mapAccM (\<lambda>s env. prr xs s env d binders) ts env) (ts', env')"
        and s': "s' = list_comb h' ts'"
        by (auto split: prod.splits)
      have rh': "is_rigid h'"
      proof (cases h)
        case (Bound i)
        with h' obtain j where j: "ok (trans xs d i) j" "h' = Bound j" by auto
        from ok_trans[OF j(1) d _ xs] rig(1) Bound j(2) show ?thesis by (auto simp: is_rigid_def)
      qed (use h' rig(1) in \<open>auto simp: is_rigid_def\<close>)
      have m: "(wf_env ar env' \<and> env_ppat env') \<and> True \<and> list_all2 (\<lambda>x y. ppat y) ts ts'"
      proof (rule mapAccM_ok[OF mt, where P = "\<lambda>e. wf_env ar e \<and> env_ppat e" and R = "\<lambda>_ _. True"
          and Q = "\<lambda>_ y _. ppat y"])
        fix x e y e1
        assume x: "x \<in> set ts" and y: "ok (prr xs x e d binders) (y, e1)" and e: "wf_env ar e \<and> env_ppat e"
        from "1.IH"[OF y refl _ bok _ _ _ d xs] e rig(2) ts(1) x
        show "(wf_env ar e1 \<and> env_ppat e1) \<and> True \<and> ppat y" by auto
      qed (use wf epp in auto)
      then have "ppat s'" using rh' by (auto simp: s' list_all2_conv_all_nth in_set_conv_nth intro!: ppat.ppat_rigid)
      with m show ?thesis by simp
    qed
  qed
qed

lemma flexrigid_ppat:
  assumes frg: "flexrigid env binders F Fty is t = Some (Ok env')" and wf: "wf_env ar env"
    and bok: "binders_ok ar binders" and epp: "env_ppat env" and pt: "ppat t" "typs_ok ar t"
    and is0: "\<forall>i\<in>set is. 0 \<le> i"
  shows "env_ppat env'"
proof -
  have hnd: "\<not> ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e) y"
    for e and y :: env by (cases e) simp_all
  from frg obtain u env1 u' where pj: "ok (proj t env binders is) (u, env1)"
    and u': "ok (mkabs binders is u) u'" and env': "ok (update (F, Fty) u' env1) env'"
    by (auto simp: flexrigid_def ok_handle hnd split: if_splits prod.splits)
  have "ppat u \<and> env_ppat env1"
  proof (cases "downto0 is (ilength binders - 1)")
    case True
    with pj epp pt show ?thesis by (simp add: proj_def)
  next
    case False
    with pj have "pr is t env 0 binders = Some (Ok (u, env1))" by (simp add: proj_def)
    from pr_ppat[OF this refl wf bok epp pt _ is0] show ?thesis by simp
  qed
  with ppat_mkabs[OF u'] env_ppat_update[OF env'] show ?thesis by simp
qed


lemma vars_incr_aux: "vars (incr_aux d t) = vars t"
  by (induction d t rule: incr_aux.induct) auto

lemma vars_incr: "vars (incr t) = vars t"
  by (simp add: incr_def vars_incr_aux)

lemma zip_eq_return: "length xs = length ys \<Longrightarrow> zip_eq xs ys = return (zip xs ys)"
  by (induction xs ys rule: zip_eq.induct) auto

lemma ext_sol_sol_ext:
  "ext_sol V \<tau>' \<sigma> env env' \<Longrightarrow> wf_env ar env' \<Longrightarrow> \<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
  by (auto simp: ext_sol_def sol_ext_def)


subsection \<open>Folding\<close>

lemma foldM_complete:
  assumes "foldM f xs e = Some r" "P g e"
    and "\<And>x g e r. x \<in> set xs \<Longrightarrow> P g e \<Longrightarrow> f x e = Some r \<Longrightarrow>
      no_unif (Some r) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
  shows "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
  using assms
proof (induction xs arbitrary: g e r)
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons x xs)
  have step: "no_unif (Some r) \<and> (\<forall>e1. r = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
    if "x' \<in> set xs" "P g e" "f x' e = Some r" for x' g e r
    using Cons.prems(3)[OF _ that(2,3)] that(1) by simp
  from Cons.prems(1) have "f x e \<bind> (\<lambda>b'. foldM f xs b') = Some r" by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix ex assume "f x e = Some (Err ex)" "r = Err ex"
    with Cons.prems(3)[of x g e "Err ex"] Cons.prems(2) show ?thesis by simp
  next
    fix e1 assume fx: "f x e = Some (Ok e1)" and rest: "foldM f xs e1 = Some r"
    from Cons.prems(3)[of x g e, OF _ Cons.prems(2) fx] obtain g1 where "P g1 e1" by auto
    have "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
      by (rule Cons.IH[OF rest \<open>P g1 e1\<close>], rule step, assumption+)
    then show ?thesis .
  qed
qed


subsection \<open>Completeness\<close>

theorem unif_complete:
  assumes "unif alg binders s t env = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    env_ppat env \<Longrightarrow> wf_term ar (length binders) s \<Longrightarrow> wf_term ar (length binders) t \<Longrightarrow>
    ppat s \<Longrightarrow> ppat t \<Longrightarrow> has_type V (map snd binders) s T \<Longrightarrow> has_type V (map snd binders) t T \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    solution V \<tau>' \<sigma> env \<Longrightarrow> unifies \<sigma> (tr s) (tr t) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>env'. r = Ok env' \<longrightarrow> env_ppat env' \<and> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'))"
  using assms
proof (induction alg binders s t env r arbitrary: V \<sigma> T rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and epp: "env_ppat env"
    and ws: "wf_term ar (length binders) s" and wt: "wf_term ar (length binders) t"
    and pps: "ppat s" and ppt: "ppat t"
    and tys: "has_type V (map snd binders) s T" and tyt: "has_type V (map snd binders) t T"
    and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    and sol: "solution V \<tau>' \<sigma> env" and uni: "unifies \<sigma> (tr s) (tr t)"
    using "1.prems" by simp_all
  let ?Bs = "map snd binders" and ?n = "length binders"
  note \<sigma> = solutionD[OF sol]
  have vt: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  define R where "R = (\<lambda>s0 t0. if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht)))"
  from "1.hyps" have "head_norm env s \<bind> (\<lambda>s0. head_norm env t \<bind> (\<lambda>t0. R s0 t0)) = Some r"
    unfolding R_def by (simp only:)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env s = Some (Err e)" "r = Err e"
    with no_unif_head_norm[OF vt, of s] show ?thesis by simp
  next
    fix s0 assume hs: "head_norm env s = Some (Ok s0)"
      and rest1: "head_norm env t \<bind> (\<lambda>t0. R s0 t0) = Some r"
    from rest1 show ?thesis
    proof (rule bindM_SomeE)
      fix e assume "head_norm env t = Some (Err e)" "r = Err e"
      with no_unif_head_norm[OF vt, of t] show ?thesis by simp
    next
      fix t0 assume ht: "head_norm env t = Some (Ok t0)" and rest0: "R s0 t0 = Some r"
      note rest = rest0[unfolded R_def]
      from head_norm_sound[OF hs refl wf] ws
      have ws0: "wf_term ar ?n s0" and s0: "env \<Turnstile> s \<approx> s0" by (auto simp: wf_term_def)
      from head_norm_sound[OF ht refl wf] wt
      have wt0: "wf_term ar ?n t0" and t0: "env \<Turnstile> t \<approx> t0" by (auto simp: wf_term_def)
      have tys0: "has_type V ?Bs s0 T" by (rule head_norm_typed[OF hs refl wf ety tys])
      have tyt0: "has_type V ?Bs t0 T" by (rule head_norm_typed[OF ht refl wf ety tyt])
      have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hs refl wf fr bs])
      have bt0: "below (maxidx env) t0" by (rule below_head_norm[OF ht refl wf fr bt])
      have pps0: "ppat s0" by (rule head_norm_ppat[OF hs wf epp pps])
      have ppt0: "ppat t0" by (rule head_norm_ppat[OF ht wf epp ppt])
      have uni0: "unifies \<sigma> (tr s0) (tr t0)"
        using env_equivD[OF s0 \<sigma>(1,4)] env_equivD[OF t0 \<sigma>(1,4)] uni
        by (simp add: unifies_def) (meson equiv_sym equiv_trans)
      note IH = "1.IH"
      show ?thesis
      proof (cases "is_Abs s0")
        case sA: True
        then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
        have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
        from tys0 s0a obtain W where T: "T = Ts \<rightarrow>\<^sub>T W" and tyts: "has_type V (Ts # ?Bs) ts W"
          by (auto elim: has_type_elims)
        have pts: "ppat ts" using pps0 s0a by (auto dest: ppat_AbsD)
        have bts: "below (maxidx env) ts" using bs0 s0a by simp
        have wts: "wf_term ar (Suc ?n) ts" using ws0 s0a by (simp add: wf_term_def)
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          from tyt0 t0a T have Tt: "Tt = Ts" and tytt: "has_type V (Ts # ?Bs) tt W"
            by (auto elim: has_type_elims)
          define nm where "nm = (if ns = STR '''' then nt else ns)"
          from rest sA True s0a t0a have u: "uni alg ((nm, Ts) # binders) ts tt env = Some r"
            by (simp add: Let_def nm_def unify_types_ground[OF gTs gTs] Tt)
          have bok': "binders_ok ar ((nm, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have ptt: "ppat tt" using ppt0 t0a by (auto dest: ppat_AbsD)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have uni': "unifies \<sigma> (tr ts) (tr tt)" using uni0 s0a t0a by (simp add: unifies_def fact5[symmetric])
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pts ptt _ _ bts btt sol uni'] wts wtt tyts tytt by simp
        next
          case False
          from rest sA False s0a have u: "uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env = Some r"
            by simp
          have bok': "binders_ok ar ((ns, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
          have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
            using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Ts # ?Bs) (incr t0 $ Bound 0) W"
            using has_type_incr[OF tyt0, of Ts] T by (intro has_type.App[of _ _ _ Ts]) (auto simp: has_type_Bound_iff)
          have pi: "ppat (incr t0 $ Bound 0)" by (rule ppat_incr_Bound0[OF ppt0 False])
          have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr t0 $ Bound 0)) = lift (mk_subst \<sigma> (tr t0)) 0 \<degree> BVar 0"
            using wt0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          then have uni': "unifies \<sigma> (tr ts) (tr (incr t0 $ Bound 0))"
            using uni0 s0a by (simp add: unifies_def fact6)
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pts pi _ _ bts bi sol uni'] wts wi tyts tyi by simp
        qed
      next
        case nsA: False
        show ?thesis
        proof (cases "is_Abs t0")
          case True
          then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
          have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
          from tyt0 t0a obtain W where T: "T = Tt \<rightarrow>\<^sub>T W" and tytt: "has_type V (Tt # ?Bs) tt W"
            by (auto elim: has_type_elims)
          from rest nsA True t0a have u: "uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env = Some r"
            by simp
          have bok': "binders_ok ar ((nt, Tt) # binders)" using bok gTt by (simp add: binders_ok_def)
          have ptt: "ppat tt" using ppt0 t0a by (auto dest: ppat_AbsD)
          have btt: "below (maxidx env) tt" using bt0 t0a by simp
          have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
          have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
            using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
              intro: no_loose_bound_lift)
          have tyi: "has_type V (Tt # ?Bs) (incr s0 $ Bound 0) W"
            using has_type_incr[OF tys0, of Tt] T by (intro has_type.App[of _ _ _ Tt]) (auto simp: has_type_Bound_iff)
          have pi: "ppat (incr s0 $ Bound 0)" by (rule ppat_incr_Bound0[OF pps0 nsA])
          have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
          have "mk_subst \<sigma> (tr (incr s0 $ Bound 0)) = lift (mk_subst \<sigma> (tr s0)) 0 \<degree> BVar 0"
            using ws0 \<sigma>(1) by (simp add: wf_term_def incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
          moreover have "mk_subst \<sigma> (tr s0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr tt))"
            using uni0 t0a by (simp add: unifies_def)
          ultimately have uni': "unifies \<sigma> (tr (incr s0 $ Bound 0)) (tr tt)"
            using fact6[of "mk_subst \<sigma> (tr tt)" "mk_subst \<sigma> (tr s0)"] by (auto simp: unifies_def equiv_sym)
          show ?thesis
            using IH[OF u wf bok' ety fr epp _ _ pi ptt _ _ bi btt sol uni'] wi wtt tyi tytt by simp
        next
          case nAt: False
          obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
          obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
          note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
          have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
            using ws0 s0e by (simp_all add: wf_term_list_comb)
          have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
            using wt0 t0e by (simp_all add: wf_term_list_comb)
          have pss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
            using wss(2) wts(2) by (auto simp: wf_term_def)
          have wt0': "proper t0" "typs_ok ar t0" and ws0': "proper s0" "typs_ok ar s0"
            using wt0 ws0 by (simp_all add: wf_term_def)
          have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
            using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
          note sps = ppat_spine[OF pps0[unfolded s0e] nApp(1) nsA[unfolded s0e]]
          note spt = ppat_spine[OF ppt0[unfolded t0e] nApp(2) nAt[unfolded t0e]]
          have uni0': "mk_subst \<sigma> (tr (list_comb hs ss)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (list_comb ht ts))"
            using uni0 s0e t0e by (simp add: unifies_def)
          consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
            | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
            | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
            | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
            by (cases hs; cases ht) auto
          then show ?thesis
          proof cases
            case VV
            from rest nsA nAt shs sht VV have ff0: "ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js)) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ss] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and ff1: "ints_of' env ts \<bind> (\<lambda>js.
                if F = G then flexflex1 env binders F Fty is js else flexflex2 env binders F Fty is G Gty js) =
                Some r"
              from ff1 show ?thesis
              proof (rule bindM_SomeE)
                fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
                with no_unif_ints_of'[OF vt, of ts] show ?thesis by simp
              next
                fix js assume js: "ok (ints_of' env ts) js" and ff: "(if F = G then flexflex1 env binders F Fty is js
                  else flexflex2 env binders F Fty is G Gty js) = Some r"
                note iS = ints_of'_sound[OF iss wf pss] and jS = ints_of'_sound[OF js wf pts]
                have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                  using has_type_ints_of'[OF iss wf ety] tys0 s0e VV by simp
                have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                  using has_type_ints_of'[OF js wf ety] tyt0 t0e VV by simp
                have gF: "ground ar Fty" and gG: "ground ar Gty"
                  using wss(1) wts(1) VV by (simp_all add: wf_term_def)
                have Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
                  using bs0 bt0 s0e t0e VV by (simp_all add: below_list_comb)
                have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
                  using ints_of'_equiv[OF iss wf pss] s0e VV by simp
                have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
                  using ints_of'_equiv[OF js wf pts] t0e VV by simp
                have uniFG: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var G Gty) js))"
                  using uni0 env_equivD[OF eqs \<sigma>(1,4)] env_equivD[OF eqt \<sigma>(1,4)]
                  by (simp add: unifies_def) (meson equiv_sym equiv_trans)
                show ?thesis
                proof (cases "F = G")
                  case True
                  with ff have ff': "flexflex1 env binders F Fty is js = Some r" by simp
                  have GF: "Gty = Fty" using has_type_app_Var(2)[OF tyF] has_type_app_Var(2)[OF tyG] True by simp
                  then have tyG': "has_type V ?Bs (app (pterm.Var F Fty) js) T" using tyG True by simp
                  have uni': "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var F Fty) js))"
                    using uniFG True GF by simp
                  note c = flexflex1_complete[OF ff' wf ety fr Fm tyF tyG' iS(1) jS(1) sol uni']
                  show ?thesis
                  proof (intro conjI allI impI c(1))
                    fix env' assume r: "r = Ok env'"
                    show "env_ppat env'" using flexflex1_ppat[OF ff'[unfolded r] epp] .
                    show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
                      using ext_sol_sol_ext[OF c(2)[OF r] flexflex1_sound(2)[OF ff'[unfolded r] wf gF bok]] .
                  qed
                next
                  case False
                  with ff have ff': "flexflex2 env binders F Fty is G Gty js = Some r" by simp
                  note c = flexflex2_complete[OF ff' wf ety fr Fm Gm False tyF tyG iS(1) jS(1) sol uniFG]
                  show ?thesis
                  proof (intro conjI allI impI c(1))
                    fix env' assume r: "r = Ok env'"
                    show "env_ppat env'" using flexflex2_ppat[OF ff'[unfolded r] epp iS(1) jS(1) iS(2) jS(2)] .
                    show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
                      using ext_sol_sol_ext[OF c(2)[OF r]
                        flexflex2_sound(2)[OF ff'[unfolded r] wf gF gG bok iS(2) jS(2)]] .
                  qed
                qed
              qed
            qed
          next
            case VR
            from rest nsA nAt shs sht VR have fr0: "ints_of' env ss \<bind> (\<lambda>is. flexrigid env binders F Fty is t0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ss = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ss] show ?thesis by simp
            next
              fix "is" assume iss: "ok (ints_of' env ss) is" and frg: "flexrigid env binders F Fty is t0 = Some r"
              note iS = ints_of'_sound[OF iss wf pss]
              have tyF: "has_type V ?Bs (app (pterm.Var F Fty) is) T"
                using has_type_ints_of'[OF iss wf ety] tys0 s0e VR by simp
              have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
              have Fm: "snd F \<le> maxidx env" using bs0 s0e VR by (simp add: below_list_comb)
              have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
                using ints_of'_equiv[OF iss wf pss] s0e VR by simp
              have uniF: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr t0)"
                using uni0 env_equivD[OF eqs \<sigma>(1,4)] by (simp add: unifies_def) (meson equiv_sym equiv_trans)
              have rig: "is_rigid ht" using spt VR(2) by auto
              have occ: "\<not> ok (occurs F t0 env) True"
                using occurs_complete[OF _ ppt0 t0e rig epp wf ety tyt0 tyF iS(1) sol uniF] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Fm gF tyF tyt0 wt0' bt0 iS(1) sol uniF occ]
              show ?thesis
              proof (intro conjI allI impI c(1))
                fix env' assume r: "r = Ok env'"
                show "env_ppat env'" using flexrigid_ppat[OF frg[unfolded r] wf bok epp ppt0 wt0'(2) iS(2)] .
                show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'" using c(2)[OF r] .
              qed
            qed
          next
            case RV
            from rest nsA nAt shs sht RV have fr0: "ints_of' env ts \<bind> (\<lambda>js. flexrigid env binders G Gty js s0) =
              Some r"
              by simp
            then show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "ints_of' env ts = Some (Err e)" "r = Err e"
              with no_unif_ints_of'[OF vt, of ts] show ?thesis by simp
            next
              fix js assume js: "ok (ints_of' env ts) js" and frg: "flexrigid env binders G Gty js s0 = Some r"
              note jS = ints_of'_sound[OF js wf pts]
              have tyG: "has_type V ?Bs (app (pterm.Var G Gty) js) T"
                using has_type_ints_of'[OF js wf ety] tyt0 t0e RV by simp
              have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
              have Gm: "snd G \<le> maxidx env" using bt0 t0e RV by (simp add: below_list_comb)
              have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
                using ints_of'_equiv[OF js wf pts] t0e RV by simp
              have uniG: "unifies \<sigma> (tr (app (pterm.Var G Gty) js)) (tr s0)"
                using uni0 env_equivD[OF eqt \<sigma>(1,4)] by (simp add: unifies_def) (meson equiv_sym equiv_trans)
              have rig: "is_rigid hs" using sps RV(1) by auto
              have occ: "\<not> ok (occurs G s0 env) True"
                using occurs_complete[OF _ pps0 s0e rig epp wf ety tys0 tyG jS(1) sol uniG] by blast
              note c = flexrigid_complete[OF frg wf bok ety fr Gm gG tyG tys0 ws0' bs0 jS(1) sol uniG occ]
              show ?thesis
              proof (intro conjI allI impI c(1))
                fix env' assume r: "r = Ok env'"
                show "env_ppat env'" using flexrigid_ppat[OF frg[unfolded r] wf bok epp pps0 ws0'(2) jS(2)] .
                show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'" using c(2)[OF r] .
              qed
            qed
          next
            case RR
            have rs: "is_rigid hs" "\<forall>t\<in>set ss. ppat t" using sps RR by auto
            have rt: "is_rigid ht" "\<forall>t\<in>set ts. ppat t" using spt RR by auto
            have rigtr: "mk_subst \<sigma> (tr h) = tr h \<and> is_atom (tr h)" if "is_rigid h" for h
              using that by (auto simp: is_rigid_def rigid_substD[OF \<sigma>(3)])
            from uni0' have "tr hs \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ss \<equiv>\<^sub>\<beta>\<^sub>\<eta>
                tr ht \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
              using rigtr[OF rs(1)] rigtr[OF rt(1)] by (simp add: tr_list_comb comp_def)
            from atom_apps_equiv[OF conjunct2[OF rigtr[OF rs(1)]] conjunct2[OF rigtr[OF rt(1)]] this]
            have hh: "tr hs = tr ht"
              and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ss) (map (\<lambda>t. mk_subst \<sigma> (tr t)) ts)"
              by auto
            have hsht: "hs = ht" using hh rs(1) rt(1)
              by (auto simp: is_rigid_def integer_reps)
            have len: "length ss = length ts" using list_all2_lengthD[OF args] by simp
            have gh: "typs_ok ar hs" using wss(1) by (simp add: wf_term_def)
            have fo: "foldM (\<lambda>(s, t) env. uni alg binders s t env) (zip ss ts) env = Some r"
            proof -
              from rs(1) consider (C) c U where "hs = Const c U" | (Fr) c U where "hs = Free c U"
                | (B) i where "hs = Bound i" by (auto simp: is_rigid_def)
              then show ?thesis
              proof cases
                case C
                with gh have "ground ar U" by simp
                with rest nsA nAt shs sht C hsht len show ?thesis
                  by (simp add: unify_types_ground zip_eq_return)
              next
                case Fr
                with gh have "ground ar U" by simp
                with rest nsA nAt shs sht Fr hsht len show ?thesis
                  by (simp add: unify_types_ground zip_eq_return)
              next
                case B
                with hsht have hb: "hs = Bound i" "ht = Bound i" by simp_all
                from rest nsA nAt shs sht len show ?thesis by (simp add: hb zip_eq_return)
              qed
            qed
            from tys0 s0e obtain Us where tyhs: "has_type V ?Bs hs (foldr fun_type Us T)"
              and tyss: "list_all2 (has_type V ?Bs) ss Us"
              by (auto simp: has_type_list_comb)
            from tyt0 t0e obtain Us' where tyht: "has_type V ?Bs ht (foldr fun_type Us' T)"
              and tyts: "list_all2 (has_type V ?Bs) ts Us'"
              by (auto simp: has_type_list_comb)
            have "Us' = Us"
              using has_type_unique[OF tyhs tyht[folded hsht]] by (auto dest: foldr_fun_type_inj)
            note tyts = tyts[unfolded this]
            have bss: "\<forall>t\<in>set ss. below (maxidx env) t" using bs0 s0e by (simp add: below_list_comb)
            have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bt0 t0e by (simp add: below_list_comb)
            define P where "P = (\<lambda>(g :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e.
              sol_ext ar V \<tau>' \<sigma> env (fst g) (snd g) e \<and> env_ppat e)"
            have "no_unif (Some r) \<and> (\<forall>e'. r = Ok e' \<longrightarrow> (\<exists>g'. P g' e'))"
            proof (rule foldM_complete[OF fo, of P "(V, \<sigma>)"])
              show "P (V, \<sigma>) env" using sol ety fr wf epp by (simp add: P_def sol_ext_refl)
            next
              fix x g e r1
              assume x: "x \<in> set (zip ss ts)" and Pg: "P g e"
                and f: "(\<lambda>(s, t) env. uni alg binders s t env) x e = Some r1"
              from x obtain i where i: "i < length ss" "x = (ss ! i, ts ! i)"
                using len by (auto simp: in_set_zip)
              obtain V1 \<sigma>1 where g: "g = (V1, \<sigma>1)" by force
              from Pg have e1: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 e" and epp1: "env_ppat e" by (simp_all add: P_def g)
              have agV: "agreeV (maxidx env) V V1" and ag: "agree (maxidx env) \<sigma> \<sigma>1"
                and sol1: "solution V1 \<tau>' \<sigma>1 e" and ety1: "env_typed V1 e" and fr1: "fresh_env e"
                and wf1: "wf_env ar e" and mx: "maxidx env \<le> maxidx e"
                using e1 by (simp_all add: sol_ext_def)
              have ii: "i < length ts" using i(1) len by simp
              have u: "uni alg binders (ss ! i) (ts ! i) e = Some r1" using f i(2) by simp
              have ba: "below (maxidx env) (ss ! i)" and bb: "below (maxidx env) (ts ! i)"
                using bss bts i(1) ii by simp_all
              have tya: "has_type V1 ?Bs (ss ! i) (Us ! i)"
                using has_type_agreeV[OF _ ba agV] tyss i(1) by (simp add: list_all2_conv_all_nth)
              have tyb: "has_type V1 ?Bs (ts ! i) (Us ! i)"
                using has_type_agreeV[OF _ bb agV] tyts ii by (simp add: list_all2_conv_all_nth)
              have "mk_subst \<sigma> (tr (ss ! i)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (ts ! i))"
                using args i(1) len by (simp add: list_all2_conv_all_nth)
              then have uni1: "unifies \<sigma>1 (tr (ss ! i)) (tr (ts ! i))"
                using mk_subst_agree[OF ba ag] mk_subst_agree[OF bb ag] by (simp add: unifies_def)
              note IHi = IH[OF u wf1 bok ety1 fr1 epp1 _ _ _ _ tya tyb below_mono[OF ba mx] below_mono[OF bb mx]
                sol1 uni1]
              have "no_unif (Some r1) \<and> (\<forall>env'. r1 = Ok env' \<longrightarrow> env_ppat env' \<and>
                  (\<exists>V' \<sigma>'. sol_ext ar V1 \<tau>' \<sigma>1 e V' \<sigma>' env'))"
                using IHi wss(2) wts(2) rs(2) rt(2) i(1) ii by simp
              then show "no_unif (Some r1) \<and> (\<forall>e1. r1 = Ok e1 \<longrightarrow> (\<exists>g1. P g1 e1))"
                using sol_ext_trans[OF e1] by (fastforce simp: P_def)
            qed
            then show ?thesis by (auto simp: P_def)
          qed
        qed
      qed
    qed
  qed
qed

end
