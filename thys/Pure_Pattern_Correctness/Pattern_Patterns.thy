section \<open>\<open>\<beta>\<close>-Normal Patterns\<close>

theory Pattern_Patterns
  imports Pattern_Step_Completeness
begin

text \<open>
  \<open>\<beta>\<close>-normal patterns, and their preservation by head normalisation and by the binding steps of
  unification. Used for termination.
\<close>

subsection \<open>Rigid heads\<close>

definition is_rigid :: "pterm \<Rightarrow> bool" where
  "is_rigid h \<longleftrightarrow> (\<exists>c T. h = Const c T) \<or> (\<exists>c T. h = Free c T) \<or> (\<exists>i. h = Bound i \<and> 0 \<le> i)"

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

definition rigid_head :: "pterm \<Rightarrow> bool" where
  "rigid_head t \<longleftrightarrow> (\<exists>h ts. t = list_comb h ts \<and> is_rigid h)"

lemma rigid_head_cases: "rigid_head t \<Longrightarrow> is_rigid t \<or> (\<exists>f u. t = f $ u)"
  unfolding rigid_head_def by (metis list_comb_Nil list_comb_snoc rev_exhaust)

lemma vars_incr_aux: "vars (incr_aux d t) = vars t"
  by (induction d t rule: incr_aux.induct) auto

lemma vars_incr: "vars (incr t) = vars t"
  by (simp add: incr_def vars_incr_aux)

subsection \<open>Patterns\<close>

inductive ppat :: "pterm \<Rightarrow> bool" where
  ppat_Abs: "ppat t \<Longrightarrow> ppat (Abs a T t)"
| ppat_rigid: "is_rigid h \<Longrightarrow> \<forall>t\<in>set ts. ppat t \<Longrightarrow> ppat (list_comb h ts)"
| ppat_flex: "distinct is \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> ppat (app (Var x T) is)"

definition env_ppat :: "env \<Rightarrow> bool" where
  "env_ppat env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ppat u)"

lemma env_ppatD: "env_ppat env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ppat u"
  by (cases x) (simp add: env_ppat_def)

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

lemma not_rigid_head_app: "\<not> rigid_head (app (Var x T) is)"
proof
  assume "rigid_head (app (Var x T) is)"
  then obtain h ts where "list_comb (Var x T) (map Bound is) = list_comb h ts" "is_rigid h"
    by (auto simp: rigid_head_def app_list_comb)
  with list_comb_eq_iff[of "Var x T" h] is_rigid_not_App show False
    by (auto simp: is_rigid_def)
qed

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


subsection \<open>Completeness of the occurs check on patterns\<close>

lemma ld_closed: "no_loose_bound t 0 \<Longrightarrow> ld e \<tau> t T = ld e' \<tau> t T"
  using ld_map_BVars[of t e' "\<lambda>x. x" e \<tau> T] no_loose_bound_loose_BVars[of t] by (simp add: map_BVars_id)

lemma rigid_tr: "is_rigid h \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow> mk_subst \<sigma> (tr h) = tr h \<and> is_atom (tr h)"
  by (auto simp: is_rigid_def rigid_substD)

lemma nf_typed:
  assumes "(e, \<tau>) \<turnstile> t : T"
  obtains w where "\<beta>\<eta>cl t w" "normal w" "(e, \<tau>) \<turnstile> w : T"
  using normal_form_ex[OF assms] subject_reduction_\<beta>\<eta>[OF _ assms] by blast

lemma closed_nf: "\<beta>\<eta>cl t w \<Longrightarrow> no_loose_bound t 0 \<Longrightarrow> no_loose_bound w 0"
  using loose_BVars_\<beta>\<eta>cl[of t w] no_loose_bound_loose_BVars[of t]
  by (intro loose_BVars_no_loose_bound) auto

text \<open>
  An occurrence of \<open>F\<close> found by \<^const>\<open>occurs\<close> in a pattern survives in every
  \<open>\<beta>\<close>-normal instance: the measure \<^const>\<open>ld\<close> of the instance is at least that of the value
  of \<open>F\<close>, and strictly larger below a rigid head.
\<close>

lemma occurs_ld:
  assumes "occurs F t env = Some r"
  shows "r = Ok True \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> env_typed V env \<Longrightarrow>
    solution V \<tau>' \<sigma> env \<Longrightarrow> \<beta>\<eta>cl (\<sigma> (code (AVar F))) nF \<Longrightarrow> normal nF \<Longrightarrow>
    ppat t \<Longrightarrow> has_type V Ts t T \<Longrightarrow> v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t) \<Longrightarrow> no_redex v \<Longrightarrow>
    (bnd_env Ts, \<tau>') \<turnstile> v : trty T \<Longrightarrow>
    \<not> is_rigid t \<and> ld E \<tau>' nF (trty (V F)) \<le> ld (bnd_env Ts) \<tau>' v (trty T) \<and>
    (rigid_head t \<longrightarrow> ld E \<tau>' nF (trty (V F)) < ld (bnd_env Ts) \<tau>' v (trty T))"
  using assms
proof (induction F t env r arbitrary: Ts T v rule: occurs.raw_induct[rotated, consumes 1])
  case (1 occ F t env r)
  have rT: "r = Ok True" and wf: "wf_env ar env" and epp: "env_ppat env" and ety: "env_typed V env"
    and sol: "solution V \<tau>' \<sigma> env" and nF: "\<beta>\<eta>cl (\<sigma> (code (AVar F))) nF" "normal nF"
    and pt: "ppat t" and tyt: "has_type V Ts t T" and veq: "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
    and vnr: "no_redex v" and vty: "(bnd_env Ts, \<tau>') \<turnstile> v : trty T"
    using "1.prems" by blast+
  note \<sigma> = solutionD[OF sol]
  note IH = "1.IH"[OF _ refl wf epp ety sol nF]
  let ?L = "ld E \<tau>' nF (trty (V F))"
  have \<sigma>c: "no_loose_bound (\<sigma> n) 0" for n using closed_onD[OF \<sigma>(1)] by simp
  have \<sigma>ty: "(e, \<tau>') \<turnstile> \<sigma> (code a) : tau V (code a)" for e a using typed_onD[OF \<sigma>(2)] by simp
  from "1.hyps" rT have hyp: "(case t of
      pterm.Var G T \<Rightarrow> lookup env G T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G))
    | t1 $ t2 \<Rightarrow> occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env)
    | pterm.Abs _ _ u \<Rightarrow> occ F u env
    | _ \<Rightarrow> return False) = Some (Ok True)"
    by simp
  show ?case
  proof (cases t)
    case (Var G U)
    have nr: "\<not> rigid_head t" "\<not> is_rigid t" using Var rigid_head_cases[of t] by (auto simp: is_rigid_def)
    from tyt Var have T: "T = U" "V G = U" by (auto elim: has_type_elims)
    from hyp Var obtain r' where lk: "ok (lookup env G U) r'"
      and rest: "(case r' of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G)) = Some (Ok True)"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" "vt_lookup (tenv env) G = None" | u where "r' = Some u" "vt_lookup (tenv env) G = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest have G: "G = F" by (simp add: return_def)
      have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> nF" using veq nF(1) Var G by (auto intro: equiv_trans \<beta>\<eta>cl_into_equiv)
      moreover have "(bnd_env Ts, \<tau>') \<turnstile> nF : trty T"
        using subject_reduction_\<beta>\<eta>[OF nF(1) \<sigma>ty] T G by simp
      ultimately have "ld (bnd_env Ts) \<tau>' v (trty T) = ld (bnd_env Ts) \<tau>' nF (trty T)"
        using vty vnr normal_no_redex[OF nF(2)] by (intro ld_equiv)
      also have "\<dots> = ?L" using ld_closed[OF closed_nf[OF nF(1) \<sigma>c]] T G by simp
      finally show ?thesis using nr by simp
    next
      case 2
      with rest have ou: "occ F u env = Some (Ok True)" by simp
      have tyu: "has_type V [] u U" using env_typedD[OF ety 2(2)] by simp
      have cu: "no_loose_bound (tr u) 0" using wf_envD(2)[OF wf 2(2)] by simp
      have "(bnd_env [], \<tau>') \<turnstile> mk_subst \<sigma> (tr u) : trty U" by (rule has_type_subst[OF tyu \<sigma>(2)])
      then obtain w where w: "\<beta>\<eta>cl (mk_subst \<sigma> (tr u)) w" "normal w" "(bnd_env [], \<tau>') \<turnstile> w : trty U"
        by (rule nf_typed)
      have cw: "no_loose_bound w 0"
        using closed_nf[OF w(1)] mk_subst_no_loose_bound[OF cu closed_on_mono[OF \<sigma>(1)]] by simp
      from IH[OF ou env_ppatD[OF epp 2(2)] tyu equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]]
          normal_no_redex[OF w(2)] w(3)]
      have "?L \<le> ld (bnd_env []) \<tau>' w (trty U)" by simp
      also have "\<dots> = ld (bnd_env Ts) \<tau>' w (trty U)" by (rule ld_closed[OF cw])
      also have "\<dots> = ld (bnd_env Ts) \<tau>' v (trty T)"
        unfolding T(1)
      proof (rule ld_equiv)
        have "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]])
        also have "mk_subst \<sigma> (tr u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
          using equiv_sym[OF satD[OF \<sigma>(4) 2(2)]] Var by simp
        also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> v" by (rule equiv_sym[OF veq])
        finally show "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> v" .
        show "(bnd_env Ts, \<tau>') \<turnstile> w : trty U" using typing_closed[OF w(3) cw] .
      qed (use vty[unfolded T(1)] vnr normal_no_redex[OF w(2)] in auto)
      finally show ?thesis using nr by simp
    qed
  next
    case (Abs a U body)
    have nr: "\<not> rigid_head t" "\<not> is_rigid t" using Abs rigid_head_cases[of t] by (auto simp: is_rigid_def)
    from hyp Abs have ob: "occ F body env = Some (Ok True)" by simp
    from tyt Abs obtain W where T: "T = U \<rightarrow>\<^sub>T W" and tyb: "has_type V (U # Ts) body W"
      by (auto elim: has_type_elims)
    have "(bnd_env (U # Ts), \<tau>') \<turnstile> mk_subst \<sigma> (tr body) : trty W" by (rule has_type_subst[OF tyb \<sigma>(2)])
    then obtain w where w: "\<beta>\<eta>cl (mk_subst \<sigma> (tr body)) w" "normal w" "(bnd_env (U # Ts), \<tau>') \<turnstile> w : trty W"
      by (rule nf_typed)
    from IH[OF ob ppat_AbsD[OF pt[unfolded Abs]] tyb equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]]
        normal_no_redex[OF w(2)] w(3)]
    have "?L \<le> ld (bnd_env (U # Ts)) \<tau>' w (trty W)" by simp
    also have "\<dots> = ld (bnd_env Ts) \<tau>' (dB.Abs w) (trty T)" by (simp add: T bnd_env_Cons)
    also have "\<dots> = ld (bnd_env Ts) \<tau>' v (trty T)"
    proof (rule ld_equiv)
      have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs w" using w(1) Abs by (auto intro: equiv_Abs \<beta>\<eta>cl_into_equiv)
      then show "dB.Abs w \<equiv>\<^sub>\<beta>\<^sub>\<eta> v" using veq by (meson equiv_sym equiv_trans)
      show "(bnd_env Ts, \<tau>') \<turnstile> dB.Abs w : trty T" using w(3) T by (auto simp: bnd_env_Cons)
    qed (use vty vnr normal_no_redex[OF w(2)] in auto)
    finally show ?thesis using nr by simp
  next
    case (App t1 t2)
    from tyt App obtain U2 where ty1: "has_type V Ts t1 (U2 \<rightarrow>\<^sub>T T)" and ty2: "has_type V Ts t2 U2"
      by (auto elim: has_type_elims)
    from hyp App have hyp': "occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env) = Some (Ok True)"
      by simp
    from pt[unfolded App] show ?thesis
    proof (cases rule: ppat_AppE)
      case (rigid h ts)
      note ra = rigid_tr[OF rigid(1) \<sigma>(3)]
      have "t = list_comb h (ts @ [t2])" using App rigid(2) by (simp add: list_comb_snoc)
      then have rt: "rigid_head t" "\<not> is_rigid t" using App rigid(1) by (auto simp: rigid_head_def is_rigid_def)
      have p1: "ppat t1" using rigid by (auto intro: ppat.ppat_rigid)
      have "(bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t1) : trty (U2 \<rightarrow>\<^sub>T T)" by (rule has_type_subst[OF ty1 \<sigma>(2)])
      then obtain w1 where w1: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t1)) w1" "normal w1"
        "(bnd_env Ts, \<tau>') \<turnstile> w1 : trty U2 \<Rightarrow> trty T"
        by (auto elim: nf_typed)
      have "mk_subst \<sigma> (tr t1) = tr h \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
        using ra rigid(2) by (simp add: tr_list_comb comp_def)
      with atom_apps_\<beta>\<eta>cl[OF conjunct2[OF ra]] w1(1) have nA1: "\<not> Unif_Occurs.is_Abs w1"
        using is_Abs_atom_apps[OF conjunct2[OF ra]] by force
      have "(bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t2) : trty U2" by (rule has_type_subst[OF ty2 \<sigma>(2)])
      then obtain w2 where w2: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t2)) w2" "normal w2" "(bnd_env Ts, \<tau>') \<turnstile> w2 : trty U2"
        by (rule nf_typed)
      have nr12: "no_redex w1" "no_redex w2" using w1(2) w2(2) by (simp_all add: normal_no_redex)
      have sp: "spine_type (bnd_env Ts) \<tau>' w1 = trty U2 \<Rightarrow> trty T"
        by (rule spine_type_typing[OF w1(3) nr12(1) nA1])
      have ldv: "ld (bnd_env Ts) \<tau>' v (trty T) = ld (bnd_env Ts) \<tau>' (w1 \<degree> w2) (trty T)"
      proof (rule ld_equiv)
        have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> w1 \<degree> w2"
          using App w1(1) w2(1) by (auto intro: equiv_App \<beta>\<eta>cl_into_equiv)
        with veq show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> w1 \<degree> w2" by (rule equiv_trans)
        show "(bnd_env Ts, \<tau>') \<turnstile> w1 \<degree> w2 : trty T" using w1(3) w2(3) by auto
      qed (use vty vnr nr12 nA1 in auto)
      have ld12: "ld (bnd_env Ts) \<tau>' w1 (trty U2 \<Rightarrow> trty T) \<le> ld (bnd_env Ts) \<tau>' v (trty T)"
        "ld (bnd_env Ts) \<tau>' w2 (trty U2) < ld (bnd_env Ts) \<tau>' v (trty T)"
        using ldv sp by simp_all
      from hyp' show ?thesis
      proof (rule bindM_SomeE)
        fix e assume "occ F t1 env = Some (Err e)" "Ok True = Err e"
        then show ?thesis by simp
      next
        fix b assume o1: "occ F t1 env = Some (Ok b)"
          and o2: "(if b then return True else occ F t2 env) = Some (Ok True)"
        show ?thesis
        proof (cases b)
          case True
          from o1 True have "occ F t1 env = Some (Ok True)" by simp
          from IH[OF this p1 ty1 equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w1(1)]] nr12(1)]
            w1(3) rigid
          have "?L < ld (bnd_env Ts) \<tau>' w1 (trty U2 \<Rightarrow> trty T)" by (auto simp: rigid_head_def)
          with ld12 rt show ?thesis by simp
        next
          case False
          with o2 have o2': "occ F t2 env = Some (Ok True)" by simp
          from IH[OF o2' rigid(4) ty2 equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w2(1)]] nr12(2) w2(3)]
          have "?L \<le> ld (bnd_env Ts) \<tau>' w2 (trty U2)" by simp
          with ld12 rt show ?thesis by simp
        qed
      qed
    next
      case (flex x Ux iss i)
      have ta: "t = app (Var x Ux) (iss @ [i])" using App flex(1,2) by (simp add: app_def)
      have nr: "\<not> rigid_head t" "\<not> is_rigid t"
        using ta not_rigid_head_app[of x Ux "iss @ [i]"] App by (auto simp: is_rigid_def)
      have p1: "ppat t1" using flex(1,3,4) by (auto intro: ppat.ppat_flex)
      have \<sigma>x: "no_loose_bound (\<sigma> (code (AVar x))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar x)) : tau V (code (AVar x))"
        by (rule \<sigma>c, rule \<sigma>ty)
      obtain nFx where nFx: "\<beta>\<eta>cl (\<sigma> (code (AVar x))) nFx" "normal nFx"
        using normal_form_ex[OF \<sigma>x(2)] by blast
      from hyp' show ?thesis
      proof (rule bindM_SomeE)
        fix e assume "occ F t1 env = Some (Err e)" "Ok True = Err e"
        then show ?thesis by simp
      next
        fix b assume o1: "occ F t1 env = Some (Ok b)"
          and o2: "(if b then return True else occ F t2 env) = Some (Ok True)"
        show ?thesis
        proof (cases b)
          case False
          with o2 flex(2) have o2': "occ F (Bound i) env = Some (Ok True)" by simp
          have i0: "0 \<le> i" using flex(4) by simp
          have pB: "ppat (Bound i)" using ppat.ppat_rigid[of "Bound i" "[]"] i0 by (simp add: is_rigid_def)
          have tyB: "has_type V Ts (Bound i) U2" using ty2 flex(2) by simp
          from IH[OF o2' pB tyB equiv_refl _ has_type_subst[OF tyB \<sigma>(2)]] i0
          show ?thesis by (simp add: is_rigid_def)
        next
          case True
          with o1 have o1': "occ F t1 env = Some (Ok True)" by simp
          have "(bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t1) : trty (U2 \<rightarrow>\<^sub>T T)"
            by (rule has_type_subst[OF ty1 \<sigma>(2)])
          then obtain w1 where w1: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t1)) w1" "normal w1"
            "(bnd_env Ts, \<tau>') \<turnstile> w1 : trty (U2 \<rightarrow>\<^sub>T T)"
            by (rule nf_typed)
          from IH[OF o1' p1 ty1 equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w1(1)]] normal_no_redex[OF w1(2)] w1(3)]
          have "?L \<le> ld (bnd_env Ts) \<tau>' w1 (trty (U2 \<rightarrow>\<^sub>T T))" by simp
          also have "\<dots> = ld E \<tau>' nFx (tau V (code (AVar x)))"
          proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = "code (AVar x)" and \<tau> = "tau V", OF \<sigma>x nFx])
            show "distinct (nats iss)" using flex(3,4) by (auto intro: distinct_nats)
            show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar x)) \<degree>\<degree> map BVar (nats iss) : trty (U2 \<rightarrow>\<^sub>T T)"
              using has_type_tr[OF ty1] flex(1) by (simp add: tr_app')
            show "w1 \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar x)) \<degree>\<degree> map BVar (nats iss)"
              using equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w1(1)]] flex(1) by (simp add: tr_app' comp_def)
          qed (use w1 normal_no_redex in auto)
          also have "\<dots> = ld (bnd_env Ts) \<tau>' v (trty T)"
          proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = "code (AVar x)" and \<tau> = "tau V", OF \<sigma>x nFx, symmetric])
            show "distinct (nats (iss @ [i]))" using flex(3,4) by (intro distinct_nats) auto
            show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar x)) \<degree>\<degree> map BVar (nats (iss @ [i])) : trty T"
              using has_type_tr[OF tyt] ta by (simp add: tr_app')
            show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar x)) \<degree>\<degree> map BVar (nats (iss @ [i]))"
              using veq ta by (simp add: tr_app' comp_def)
          qed (use vnr vty in auto)
          finally show ?thesis using nr by simp
        qed
      qed
    qed
  qed (use hyp in \<open>simp_all add: return_def\<close>)
qed

lemma occurs_complete:
  assumes "ok (occurs F t env) True" "ppat t" "t = list_comb h ts" "is_rigid h"
    "env_ppat env" "wf_env ar env" "env_typed V env" "has_type V Ts t T"
    "has_type V Ts (app (Var F Fty) is) T" "distinct is" "solution V \<tau>' \<sigma> env"
    "unifies \<sigma> (tr (app (Var F Fty) is)) (tr t)"
  shows False
proof -
  note \<sigma> = solutionD[OF assms(11)]
  have \<sigma>F: "no_loose_bound (\<sigma> (code (AVar F))) 0" "\<And>e'. (e', \<tau>') \<turnstile> \<sigma> (code (AVar F)) : tau V (code (AVar F))"
    by (rule closed_onD[OF \<sigma>(1)], simp, rule typed_onD[OF \<sigma>(2)], simp)
  obtain nF where nF: "\<beta>\<eta>cl (\<sigma> (code (AVar F))) nF" "normal nF" using normal_form_ex[OF \<sigma>F(2)] by blast
  have "(bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t) : trty T" by (rule has_type_subst[OF assms(8) \<sigma>(2)])
  then obtain v where v: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t)) v" "normal v" "(bnd_env Ts, \<tau>') \<turnstile> v : trty T"
    by (rule nf_typed)
  have rh: "rigid_head t" using assms(3,4) by (auto simp: rigid_head_def)
  from occurs_ld[OF assms(1) refl assms(6,5,7,11) nF assms(2,8) equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF v(1)]]
      normal_no_redex[OF v(2)] v(3)] rh
  have lt: "ld E \<tau>' nF (trty (V F)) < ld (bnd_env Ts) \<tau>' v (trty T)" by simp
  note ti = has_type_app_Var[OF assms(9)]
  have "ld (bnd_env Ts) \<tau>' v (trty T) = ld E \<tau>' nF (tau V (code (AVar F)))"
  proof (rule ld_flex_occurrence[where \<sigma> = \<sigma> and F = "code (AVar F)" and \<tau> = "tau V", OF \<sigma>F nF])
    show "distinct (nats is)" using assms(10) ti(1) by (auto intro: distinct_nats)
    show "(bnd_env Ts, tau V) \<turnstile> dB.Var (code (AVar F)) \<degree>\<degree> map BVar (nats is) : trty T"
      using has_type_tr[OF assms(9)] by (simp add: tr_app')
    have "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" by (rule equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF v(1)]])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (Var F Fty) is))"
      using assms(12) by (simp add: unifies_def equiv_sym)
    finally show "v \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar F)) \<degree>\<degree> map BVar (nats is)"
      by (simp add: tr_app' comp_def)
  qed (use v normal_no_redex in auto)
  with lt ti(2) show False by simp
qed

end
