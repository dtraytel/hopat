section \<open>Termination of Pattern Unification\<close>

theory Pattern_Termination
  imports Pattern_Unif_Complete
begin

text \<open>
  The functions \<^const>\<open>head_norm\<close>, \<^const>\<open>occurs\<close>, \<^const>\<open>pr\<close> and \<^const>\<open>unif\<close> are partial:
  they diverge on cyclic environments. We show that \<^const>\<open>unify\<close> terminates (with a result or
  an exception) on \<open>\<beta>\<close>-normal patterns in acyclic environments whose bindings are \<open>\<beta>\<close>-normal
  patterns. No typing is needed.

  Variables are identified with their type, as in \<^const>\<open>lookup\<close>: a variable occurring with a
  type different from the one of its binding is stuck (\<^const>\<open>lookup\<close> raises an exception).
\<close>

subsection \<open>Head normalisation without exceptions\<close>

definition lk :: "env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm option" where
  "lk env x T = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> if U = T then Some u else None | None \<Rightarrow> None)"

partial_function (option) hn :: "env \<Rightarrow> pterm \<Rightarrow> pterm option" where
  "hn env t =
    (case t of
      Var x T \<Rightarrow> (case lk env x T of Some u \<Rightarrow> hn env u | None \<Rightarrow> Some t)
    | Abs a T body \<Rightarrow> Option.bind (hn env body) (\<lambda>body'. Some (Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> Option.bind (hn env f) (\<lambda>nf.
            case nf of
              Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
            | _ \<Rightarrow> Some (nf $ u)))
    | _ \<Rightarrow> Some t)"

lemma lookup_lk:
  assumes "vt_is_empty (tyenv env)"
  shows "lookup env x T = (case vt_lookup (tenv env) x of
      Some (U, u) \<Rightarrow> if U = T then return (lk env x T) else var_clash x T U
    | None \<Rightarrow> return None)"
  using assms by (auto simp: lookup_def lk_def unified_empty split: option.splits)

lemma head_norm_hn:
  assumes "head_norm env t = Some r" "vt_is_empty (tyenv env)"
  shows "r = Ok t' \<Longrightarrow> hn env t = Some t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 h env t r)
  show ?case
  proof (cases t)
    case (Var x T)
    with 1 show ?thesis
      by (subst hn.simps) (auto simp: lookup_lk lk_def var_clash_def split: option.splits if_splits)
  next
    case (Abs a T b)
    with 1 show ?thesis by (subst hn.simps) auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where "f = Abs a T b" by (cases f) auto
      with 1 App show ?thesis by (subst hn.simps) auto
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have hf: "hn env f = Some nf" using "1.IH"[OF nf refl] 1 by simp
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where "nf = Abs a T b" by (cases nf) auto
        with rest 1 App False hf show ?thesis by (subst hn.simps) (cases f; auto)
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with 1 App False hf nA show ?thesis by (subst hn.simps) (cases f; cases nf; auto)
      qed
    qed
  qed (use 1 in \<open>subst hn.simps; auto\<close>)+
qed

lemma lkD: "lk env x T = Some u \<Longrightarrow> vt_lookup (tenv env) x = Some (T, u)"
  by (auto simp: lk_def split: option.splits if_splits)


subsection \<open>Variables and dependencies\<close>

fun vps :: "pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps (Var x T) = {(x, T)}"
| "vps (Abs _ _ t) = vps t"
| "vps (s $ t) = vps s \<union> vps t"
| "vps _ = {}"

lemma finite_vps[simp]: "finite (vps t)"
  by (induction t) auto

lemma vps_incr_bv: "vps (incr_bv inc lev t) = vps t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma vps_subst_bound_aux: "vps (subst_bound_aux arg lev t) \<subseteq> vps arg \<union> vps t"
  by (induction arg lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_def vps_incr_bv)

lemma vps_subst_bound: "vps (subst_bound arg t) \<subseteq> vps arg \<union> vps t"
  using vps_subst_bound_aux[of arg 0 t] by (simp add: subst_bound_def)

lemma vps_list_comb: "vps (list_comb h ts) = vps h \<union> \<Union> (vps ` set ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma vps_app[simp]: "vps (app h is) = vps h"
  by (induction "is" arbitrary: h) (simp_all add: app_def)

text \<open>\<open>(y, x) \<in> dep env\<close>: the binding of \<open>x\<close> contains \<open>y\<close>.\<close>

definition dep :: "env \<Rightarrow> ((indexname \<times> ptyp) \<times> (indexname \<times> ptyp)) set" where
  "dep env = {(y, xT). \<exists>u. lk env (fst xT) (snd xT) = Some u \<and> y \<in> vps u}"

lemma dep_iff: "(y, (x, T)) \<in> dep env \<longleftrightarrow> (\<exists>u. lk env x T = Some u \<and> y \<in> vps u)"
  by (simp add: dep_def)

definition reach :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "reach env X = {y. \<exists>x\<in>X. (y, x) \<in> (dep env)\<^sup>*}"

lemma reach_incl: "X \<subseteq> reach env X"
  by (auto simp: reach_def)

lemma reach_mono: "X \<subseteq> reach env Y \<Longrightarrow> reach env X \<subseteq> reach env Y"
  by (auto simp: reach_def intro: rtrancl_trans)

lemma reach_subset: "X \<subseteq> Y \<Longrightarrow> reach env X \<subseteq> reach env Y"
  by (auto simp: reach_def)

lemma reach_Un: "reach env (X \<union> Y) = reach env X \<union> reach env Y"
  by (auto simp: reach_def)

lemma reach_lk: "lk env x T = Some u \<Longrightarrow> reach env (vps u) \<subseteq> reach env {(x, T)}"
proof
  fix y assume "y \<in> reach env (vps u)" and lu: "lk env x T = Some u"
  then obtain z where "z \<in> vps u" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  moreover from \<open>z \<in> vps u\<close> lu have "(z, (x, T)) \<in> dep env" by (auto simp: dep_iff)
  ultimately show "y \<in> reach env {(x, T)}" by (auto simp: reach_def intro: rtrancl_into_rtrancl)
qed

lemma hn_ppat_aux:
  assumes "hn env t = Some t'"
  shows "wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow>
    ppat t' \<and> loose_BVars (tr t') \<subseteq> loose_BVars (tr t) \<and> (rigid_head t \<longrightarrow> t' = t) \<and>
    vps t' \<subseteq> reach env (vps t)"
  using assms
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  have wf: "wf_env ar env" and epp: "env_ppat env" and pt: "ppat t" and t': "(case t of
      pterm.Var x T \<Rightarrow> (case lk env x T of Some u \<Rightarrow> h env u | None \<Rightarrow> Some t)
    | pterm.Abs a T body \<Rightarrow> Option.bind (h env body) (\<lambda>body'. Some (Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body)
        | _ \<Rightarrow> Option.bind (h env f) (\<lambda>nf.
            case nf of
              pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body)
            | _ \<Rightarrow> Some (nf $ u)))
    | _ \<Rightarrow> Some t) = Some t'"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf epp]
  show ?case
  proof (cases t)
    case (Var xi U)
    have nr: "\<not> rigid_head t" using Var rigid_head_cases[of t] by (auto simp: is_rigid_def)
    show ?thesis
    proof (cases "lk env xi U")
      case None
      with t' Var pt show ?thesis by (auto intro: reach_incl[THEN subsetD])
    next
      case (Some u)
      with t' Var have hu: "h env u = Some t'" by simp
      note lu = lkD[OF Some]
      have "loose_BVars (tr u) = {}"
        using wf_envD(2)[OF wf lu] by (simp add: no_loose_bound_loose_BVars)
      with IH[OF hu env_ppatD[OF epp lu]] nr reach_lk[OF Some] Var show ?thesis by auto
    qed
  next
    case (Abs a U body)
    have nr: "\<not> rigid_head t" using Abs rigid_head_cases[of t] by (auto simp: is_rigid_def)
    with t' obtain b' where hb: "h env body = Some b'" and tb: "t' = Abs a U b'"
      using Abs by (auto split: Option.bind_splits)
    from IH[OF hb ppat_AbsD[OF pt[unfolded Abs]]] have "ppat b'"
      "loose_BVars (tr b') \<subseteq> loose_BVars (tr body)" "vps b' \<subseteq> reach env (vps body)"
      by simp_all
    with tb Abs nr show ?thesis by (auto intro: ppat.ppat_Abs)
  next
    case (App f u)
    from pt[unfolded App] show ?thesis
    proof (cases rule: ppat_AppE)
      case (rigid hd ts)
      have nA: "\<not> is_Abs f" using rigid(1,2) by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_snoc)
      with t' App obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      have "rigid_head f" using rigid(1,2) by (auto simp: rigid_head_def)
      with IH[OF nf] rigid have "nf = f" by (auto intro: ppat.ppat_rigid)
      with rest nA have "t' = t" using App by (cases f) auto
      with pt show ?thesis by (auto intro: reach_incl[THEN subsetD])
    next
      case (flex x T iss i)
      have nA: "\<not> is_Abs f" using flex(1) by (cases iss rule: rev_cases) (auto simp: app_def)
      have nr: "\<not> rigid_head t" using flex(1,2) App not_rigid_head_app[of x T "iss @ [i]"] by (simp add: app_def)
      have pf: "ppat f" using flex(1,3,4) by (auto intro: ppat.ppat_flex)
      with t' App nA obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      from IH[OF nf pf] have pnf: "ppat nf" and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
        and vnf: "vps nf \<subseteq> reach env (vps f)"
        using flex(1) by (simp_all add: loose_BVars_tr_app)
      have vt: "vps t = vps f" using App flex(2) by simp
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
        then obtain a U body where Abs: "nf = Abs a U body" by (cases nf) auto
        with rest have hb: "h env (subst_bound u body) = Some t'" by simp
        have pb: "ppat body" using pnf Abs by (auto dest: ppat_AbsD)
        have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)"
          using lnf ni Abs by auto
        from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound u body)" using fl(2) by simp
        have "loose_BVars (tr (subst_bound u body)) \<subseteq> insert (nat_of_integer i) (loose_BVars (dB.Abs (tr body)))"
          using fl(2) ppat_proper[OF pb] i0 loose_BVars_subst_BVar0[of "tr body" "nat_of_integer i"]
          by (simp add: tr_subst_bound)
        with lnf Abs lt have lsub: "loose_BVars (tr (subst_bound u body)) \<subseteq> loose_BVars (tr t)" by auto
        have "vps (subst_bound u body) \<subseteq> reach env (vps t)"
          using vps_subst_bound[of u body] fl(2) vnf Abs vt by auto
        then have "reach env (vps (subst_bound u body)) \<subseteq> reach env (vps t)" by (rule reach_mono)
        with IH[OF hb ps] lsub nr show ?thesis by auto
      next
        case False
        with rest have tt: "t' = nf $ u" by (cases nf) auto
        have lt': "loose_BVars (tr t') \<subseteq> loose_BVars (tr t)" using tt fl(2) lnf lt by auto
        have vt': "vps t' \<subseteq> reach env (vps t)" using tt fl(2) vnf vt by simp
        from pnf False show ?thesis
        proof (cases rule: ppat_nonAbsE)
          case (rigid hd ts)
          have "ppat (Bound i)" using ppat.ppat_rigid[of "Bound i" "[]"] i0 by (simp add: is_rigid_def)
          then have "ppat t'" using tt rigid fl(2) ppat.ppat_rigid[of hd "ts @ [Bound i]"]
            by (auto simp: list_comb_snoc)
          with lt' vt' nr show ?thesis by simp
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
          with lt' vt' nr show ?thesis by simp
        qed
      qed
    qed
  qed (use t' pt in \<open>auto intro: reach_incl[THEN subsetD]\<close>)
qed


lemma hn_Var: "hn env (Var x T) = (case lk env x T of Some u \<Rightarrow> hn env u | None \<Rightarrow> Some (Var x T))"
  by (subst hn.simps) simp

lemma hn_Abs: "hn env (Abs a T b) = Option.bind (hn env b) (\<lambda>b'. Some (Abs a T b'))"
  by (subst hn.simps) simp

lemma hn_App_nonAbs:
  "\<not> is_Abs f \<Longrightarrow> hn env (f $ u) = Option.bind (hn env f) (\<lambda>nf.
    case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u))"
  by (subst hn.simps) (cases f; simp)

lemma hn_atoms: "hn env (Bound i) = Some (Bound i)" "hn env (Const c T) = Some (Const c T)"
  "hn env (Free c T) = Some (Free c T)"
  by (subst hn.simps; simp)+

lemma rigid_list_comb_not_Abs: "is_rigid h \<Longrightarrow> \<not> is_Abs (list_comb h ts)"
  by (cases ts rule: rev_cases) (auto simp: list_comb_snoc is_rigid_def)

lemma app_snoc: "app s (is @ [i]) = app s is $ Bound i"
  by (simp add: app_def)

lemma app_Var_not_Abs: "\<not> is_Abs (app (Var x T) is)"
  by (cases "is" rule: rev_cases) (auto simp: app_snoc app_def)

lemma reach_trans: "A \<subseteq> reach env B \<Longrightarrow> B \<subseteq> reach env C \<Longrightarrow> A \<subseteq> reach env C"
  using reach_mono by blast

lemma hn_vps:
  assumes "hn env t = Some t'"
  shows "vps t' \<subseteq> reach env (vps t)"
  using assms
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "lk env x T")
      case None
      with 1 Var show ?thesis by (auto intro: reach_incl[THEN subsetD])
    next
      case (Some u)
      with 1 Var have "h env u = Some t'" by simp
      from subset_trans[OF "1.IH"[OF this] reach_lk[OF Some]] Var show ?thesis by simp
    qed
  next
    case (Abs a T b)
    with 1 obtain b' where "h env b = Some b'" "t' = Abs a T b'" by (auto split: Option.bind_splits)
    with "1.IH" Abs show ?thesis by auto
  next
    case (App f u)
    have vt: "vps t = vps f \<union> vps u" using App by simp
    have sub: "reach env (vps (subst_bound u body)) \<subseteq> reach env (vps t)"
      if "vps body \<subseteq> reach env (vps t)" for body
      using vps_subst_bound[of u body] that vt
      by (intro reach_mono) (auto intro: reach_incl[THEN subsetD])
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with 1 App have "h env (subst_bound u b) = Some t'" by simp
      then have "vps t' \<subseteq> reach env (vps (subst_bound u b))" by (rule "1.IH")
      moreover have "vps b \<subseteq> reach env (vps t)" using f vt reach_incl[of "vps t" env] by auto
      ultimately show ?thesis using sub[of b] by blast
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      have vnf: "vps nf \<subseteq> reach env (vps t)"
        using "1.IH"[OF nf] vt reach_subset[of "vps f" "vps t" env] by auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
        with rest have "h env (subst_bound u b) = Some t'" by simp
        then have "vps t' \<subseteq> reach env (vps (subst_bound u b))" by (rule "1.IH")
        moreover have "vps b \<subseteq> reach env (vps t)" using vnf nfa by simp
        ultimately show ?thesis using sub[of b] by blast
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with vnf vt show ?thesis by (auto intro: reach_incl[THEN subsetD])
      qed
    qed
  qed (use 1 in auto)
qed

lemma hn_app_bound_vps:
  assumes "lk env x T = Some u" "hn env (app (Var x T) iss) = Some r"
  shows "vps r \<subseteq> reach env (vps u)"
  using assms(2)
proof (induction iss arbitrary: r rule: rev_induct)
  case Nil
  with assms(1) hn_vps show ?case by (simp add: app_def hn_Var)
next
  case (snoc i iss)
  from snoc.prems obtain nf where nf: "hn env (app (Var x T) iss) = Some nf"
    and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound (Bound i) body)
      | _ \<Rightarrow> Some (nf $ Bound i)) = Some r"
    by (auto simp: app_snoc hn_App_nonAbs app_Var_not_Abs split: Option.bind_splits)
  note vnf = snoc.IH[OF nf]
  show ?case
  proof (cases "is_Abs nf")
    case True
    then obtain a U b where nfa: "nf = Abs a U b" by (cases nf) auto
    with rest have "hn env (subst_bound (Bound i) b) = Some r" by simp
    from hn_vps[OF this] have "vps r \<subseteq> reach env (vps (subst_bound (Bound i) b))" .
    moreover have "vps (subst_bound (Bound i) b) \<subseteq> reach env (vps u)"
      using vps_subst_bound[of "Bound i" b] vnf nfa by auto
    ultimately show ?thesis by (rule reach_trans)
  next
    case False
    with rest vnf show ?thesis by (cases nf) auto
  qed
qed


subsection \<open>Acyclic environments\<close>

definition fin_env :: "env \<Rightarrow> bool" where
  "fin_env env \<longleftrightarrow> finite {x. vt_lookup (tenv env) x \<noteq> None}"

definition acyc :: "env \<Rightarrow> bool" where
  "acyc env \<longleftrightarrow> acyclic (dep env)"

lemma finite_dep:
  assumes "fin_env env"
  shows "finite (dep env)"
proof -
  let ?D = "{x. vt_lookup (tenv env) x \<noteq> None}"
  have "dep env \<subseteq> (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))"
  proof
    fix p assume "p \<in> dep env"
    then obtain y x T u where p: "p = (y, (x, T))" "lk env x T = Some u" "y \<in> vps u"
      by (auto simp: dep_def)
    from lkD[OF p(2)] p show "p \<in> (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))" by (intro UN_I[of x]) auto
  qed
  moreover have "finite (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))"
    using assms by (simp add: fin_env_def)
  ultimately show ?thesis by (rule finite_subset)
qed

lemma wf_dep: "fin_env env \<Longrightarrow> acyc env \<Longrightarrow> wf (dep env)"
  by (simp add: acyc_def finite_acyclic_wf finite_dep)

lemma reach_lk_trancl:
  assumes "lk env x T = Some u" "y \<in> reach env (vps u)"
  shows "(y, (x, T)) \<in> (dep env)\<^sup>+"
proof -
  from assms(2) obtain z where "z \<in> vps u" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  moreover from \<open>z \<in> vps u\<close> assms(1) have "(z, (x, T)) \<in> dep env" by (auto simp: dep_iff)
  ultimately show ?thesis by (blast intro: rtrancl_into_trancl1)
qed


subsection \<open>Termination of head normalisation\<close>

lemma hn_rigid: "is_rigid h \<Longrightarrow> hn env (list_comb h ts) = Some (list_comb h ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (subst hn.simps) (auto simp: is_rigid_def)
next
  case (snoc t ts)
  have nA: "\<not> is_Abs (list_comb h ts)" using snoc.prems
    by (cases ts rule: rev_cases) (auto simp: is_rigid_def list_comb_snoc)
  with snoc show ?case by (auto simp: list_comb_snoc hn_App_nonAbs split: pterm.splits)
qed

lemma hn_unbound: "lk env x T = None \<Longrightarrow> hn env (app (Var x T) is) = Some (app (Var x T) is)"
proof (induction "is" rule: rev_induct)
  case Nil
  then show ?case by (simp add: app_def hn_Var)
next
  case (snoc i "is")
  with app_Var_not_Abs[of x T "is"] show ?case
    by (auto simp: app_snoc hn_App_nonAbs split: pterm.splits)
qed

lemma hn_term:
  assumes fin: "fin_env env" and ac: "acyc env" and wf: "wf_env ar env" and epp: "env_ppat env"
    and pt: "ppat t"
  shows "\<exists>t'. hn env t = Some t'"
proof -
  define Q where "Q x \<longleftrightarrow> (\<forall>iss. distinct iss \<longrightarrow> (\<forall>i\<in>set iss. 0 \<le> i) \<longrightarrow>
    (\<exists>t'. hn env (app (Var (fst x) (snd x)) iss) = Some t'))" for x
  have L: "\<exists>t'. hn env t = Some t'" if "ppat t" "\<forall>y\<in>vps t. Q y" for t
    using that
  proof (induction rule: ppat.induct)
    case (ppat_Abs t a T)
    then show ?case by (auto simp: hn_Abs)
  next
    case (ppat_rigid h ts)
    then show ?case using hn_rigid by blast
  next
    case (ppat_flex iss x T)
    then show ?case by (auto simp: Q_def)
  qed
  have "Q x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_dep[OF fin ac]]])
    case (1 x)
    obtain xn T where x: "x = (xn, T)" by (cases x)
    show ?case
    proof (cases "lk env xn T")
      case None
      then show ?thesis using hn_unbound by (simp add: Q_def x)
    next
      case (Some u)
      note lu = lkD[OF Some]
      have pu: "ppat u" using env_ppatD[OF epp lu] .
      have Qy: "Q y" if "y \<in> reach env (vps u)" for y
        using 1 reach_lk_trancl[OF Some that] x by blast
      show ?thesis unfolding Q_def x fst_conv snd_conv
      proof (intro allI impI)
        fix iss :: "integer list" assume "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
        then show "\<exists>t'. hn env (app (Var xn T) iss) = Some t'"
        proof (induction iss rule: rev_induct)
          case Nil
          have "\<exists>t'. hn env u = Some t'" using L[OF pu] Qy reach_incl by blast
          then show ?case using Some by (simp add: app_def hn_Var)
        next
          case (snoc i iss)
          let ?f = "app (Var xn T) iss"
          from snoc obtain nf where nf: "hn env ?f = Some nf" by auto
          have pf: "ppat ?f" using snoc.prems by (auto intro: ppat.ppat_flex)
          from hn_ppat_aux[OF nf wf epp pf] have pnf: "ppat nf"
            and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
            by (simp_all add: loose_BVars_tr_app)
          have vnf: "vps nf \<subseteq> reach env (vps u)" by (rule hn_app_bound_vps[OF Some nf])
          have i0: "0 \<le> i" using snoc.prems by simp
          show ?case
          proof (cases "is_Abs nf")
            case True
            then obtain a U body where nfa: "nf = Abs a U body" by (cases nf) auto
            have ni: "nat_of_integer i \<notin> set (nats iss)"
            proof
              assume "nat_of_integer i \<in> set (nats iss)"
              then obtain j where "j \<in> set iss" "nat_of_integer j = nat_of_integer i" by auto
              with snoc.prems i0 have "i \<in> set iss" by (auto simp: nat_of_integer_eq_iff)
              with snoc.prems show False by simp
            qed
            have pb: "ppat body" using pnf nfa by (auto dest: ppat_AbsD)
            have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)" using lnf ni nfa by auto
            from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound (Bound i) body)" .
            have "vps (subst_bound (Bound i) body) \<subseteq> reach env (vps u)"
              using vps_subst_bound[of "Bound i" body] vnf nfa by auto
            with L[OF ps] Qy obtain r where "hn env (subst_bound (Bound i) body) = Some r" by blast
            with nf nfa show ?thesis
              by (simp add: app_snoc hn_App_nonAbs app_Var_not_Abs)
          next
            case False
            with nf show ?thesis
              by (cases nf) (simp_all add: app_snoc hn_App_nonAbs app_Var_not_Abs)
          qed
        qed
      qed
    qed
  qed
  then show ?thesis using L[OF pt] by blast
qed


subsection \<open>Renaming of loose bound variables\<close>

definition liftr :: "(integer \<Rightarrow> integer) \<Rightarrow> integer \<Rightarrow> integer" where
  "liftr f i = (if i = 0 then 0 else f (i - 1) + 1)"

fun rbv :: "(integer \<Rightarrow> integer) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "rbv f (Bound i) = Bound (f i)"
| "rbv f (Abs a T t) = Abs a T (rbv (liftr f) t)"
| "rbv f (s $ t) = rbv f s $ rbv f t"
| "rbv f (Const c T) = Const c T"
| "rbv f (Free c T) = Free c T"
| "rbv f (Var x T) = Var x T"

definition nonneg :: "(integer \<Rightarrow> integer) \<Rightarrow> bool" where
  "nonneg f \<longleftrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> 0 \<le> f i)"

lemma integer_one_le: "0 \<le> (i :: integer) \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> 1 \<le> i"
  by (simp add: integer_eq_iff less_eq_integer.rep_eq)

lemma nonneg_liftr:
  assumes "nonneg f"
  shows "nonneg (liftr f)"
  unfolding nonneg_def
proof (intro allI impI)
  fix i :: integer assume i: "0 \<le> i"
  show "0 \<le> liftr f i"
  proof (cases "i = 0")
    case False
    with i assms have "0 \<le> f (i - 1)" by (simp add: nonneg_def integer_one_le)
    then show ?thesis by (simp add: liftr_def)
  qed (simp add: liftr_def)
qed

lemma rbv_cong: "proper t \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> f i = g i) \<Longrightarrow> rbv f t = rbv g t"
proof (induction t arbitrary: f g)
  case (Abs a T t)
  have "rbv (liftr f) t = rbv (liftr g) t"
    using Abs.prems by (intro Abs.IH) (auto simp: liftr_def integer_one_le intro!: Abs.prems(2))
  then show ?case by simp
next
  case (App t1 t2)
  have "rbv f t1 = rbv g t1" "rbv f t2 = rbv g t2"
    using App.prems by (intro App.IH; simp)+
  then show ?case by simp
qed simp_all

lemma proper_rbv: "proper t \<Longrightarrow> nonneg f \<Longrightarrow> proper (rbv f t)"
proof (induction t arbitrary: f)
  case (Bound i)
  then show ?case by (simp add: nonneg_def)
qed (simp_all add: nonneg_liftr)

lemma is_Abs_rbv[simp]: "is_Abs (rbv f t) = is_Abs t"
  by (cases t) auto

lemma vps_rbv[simp]: "vps (rbv f t) = vps t"
  by (induction t arbitrary: f) auto

lemma rbv_comp: "proper t \<Longrightarrow> nonneg g \<Longrightarrow> rbv f (rbv g t) = rbv (f \<circ> g) t"
proof (induction t arbitrary: f g)
  case (Abs a T t)
  have "rbv (liftr f) (rbv (liftr g) t) = rbv (liftr f \<circ> liftr g) t"
    using Abs by (intro Abs.IH) (simp_all add: nonneg_liftr)
  also have "\<dots> = rbv (liftr (f \<circ> g)) t"
  proof (rule rbv_cong)
    show "proper t" using Abs.prems by simp
  next
    fix k :: integer assume k: "0 \<le> k"
    show "(liftr f \<circ> liftr g) k = liftr (f \<circ> g) k"
    proof (cases "k = 0")
      case False
      with k have "0 \<le> g (k - 1)" using Abs.prems(2) by (simp add: nonneg_def integer_one_le)
      with False show ?thesis by (simp add: liftr_def)
    qed (simp add: liftr_def)
  qed
  finally show ?case by (simp add: comp_def)
qed auto

lemma nat_of_integer_pos: "0 < i \<Longrightarrow> nat_of_integer i = Suc (nat_of_integer (i - 1))"
  by (simp add: nat_of_integer.rep_eq less_integer.rep_eq Suc_nat_eq_nat_zadd1)

lemma rbv_fix:
  "proper t \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> nat_of_integer i \<in> loose_BVars (tr t) \<Longrightarrow> f i = i) \<Longrightarrow> rbv f t = t"
proof (induction t arbitrary: f)
  case (Abs a T t)
  have "rbv (liftr f) t = t"
  proof (rule Abs.IH)
    show "proper t" using Abs.prems by simp
  next
    fix i :: integer assume i: "0 \<le> i" "nat_of_integer i \<in> loose_BVars (tr t)"
    show "liftr f i = i"
    proof (cases "i = 0")
      case False
      with i have "nat_of_integer (i - 1) \<in> loose_BVars (tr (Abs a T t))"
        using nat_of_integer_pos[of i] by simp
      with Abs.prems(2)[of "i - 1"] i False show ?thesis by (simp add: liftr_def integer_one_le)
    qed (simp add: liftr_def)
  qed
  then show ?case by simp
qed auto

lemma subst_bound_aux_ren:
  "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> 0 \<le> j \<Longrightarrow>
    subst_bound_aux (Bound j) lev t = rbv (\<lambda>i. if i < lev then i else if i = lev then j + lev else i - 1) t"
proof (induction t arbitrary: lev)
  case (Abs a T t)
  have "subst_bound_aux (Bound j) (lev + 1) t =
    rbv (\<lambda>i. if i < lev + 1 then i else if i = lev + 1 then j + (lev + 1) else i - 1) t"
    using Abs by (intro Abs.IH) simp_all
  also have "\<dots> = rbv (liftr (\<lambda>i. if i < lev then i else if i = lev then j + lev else i - 1)) t"
    using Abs.prems by (intro rbv_cong) (auto simp: liftr_def)
  finally show ?case by simp
qed (auto simp: incr_boundvars_Bound add.commute)

lemma subst_bound_ren:
  "proper t \<Longrightarrow> 0 \<le> j \<Longrightarrow> subst_bound (Bound j) t = rbv (\<lambda>i. if i = 0 then j else i - 1) t"
  unfolding subst_bound_def
  by (subst subst_bound_aux_ren) (auto intro: rbv_cong)

lemma incr_aux_ren: "proper t \<Longrightarrow> 0 \<le> d \<Longrightarrow> incr_aux d t = rbv (\<lambda>i. if i < d then i else i + 1) t"
proof (induction t arbitrary: d)
  case (Abs a T t)
  have "incr_aux (d + 1) t = rbv (\<lambda>i. if i < d + 1 then i else i + 1) t"
    using Abs by (intro Abs.IH) simp_all
  also have "\<dots> = rbv (liftr (\<lambda>i. if i < d then i else i + 1)) t"
    using Abs.prems by (intro rbv_cong) (auto simp: liftr_def)
  finally show ?case by simp
qed auto

lemma incr_ren: "proper t \<Longrightarrow> incr t = rbv (\<lambda>i. i + 1) t"
  unfolding incr_def by (subst incr_aux_ren) (auto intro: rbv_cong)


lemma liftr_id: "liftr (\<lambda>i. i) = (\<lambda>i. i)"
  by (auto simp: liftr_def fun_eq_iff)

lemma rbv_id[simp]: "rbv (\<lambda>i. i) t = t"
  by (induction t) (simp_all add: liftr_id)

lemma nonneg_id: "nonneg (\<lambda>i. i)"
  by (simp add: nonneg_def)

definition sb :: "integer \<Rightarrow> integer \<Rightarrow> integer" where
  "sb j i = (if i = 0 then j else i - 1)"

lemma nonneg_sb: "0 \<le> j \<Longrightarrow> nonneg (sb j)"
  by (auto simp: nonneg_def sb_def integer_one_le)

lemma subst_bound_rbv: "proper t \<Longrightarrow> 0 \<le> j \<Longrightarrow> subst_bound (Bound j) t = rbv (sb j) t"
  unfolding sb_def by (rule subst_bound_ren)

lemma subst_bound_rbv_liftr:
  assumes "proper b" "nonneg f" "0 \<le> i"
  shows "subst_bound (Bound (f i)) (rbv (liftr f) b) = rbv f (subst_bound (Bound i) b)"
proof -
  have fi: "0 \<le> f i" using assms(2,3) by (simp add: nonneg_def)
  have "subst_bound (Bound (f i)) (rbv (liftr f) b) = rbv (sb (f i)) (rbv (liftr f) b)"
    using assms fi by (intro subst_bound_rbv proper_rbv nonneg_liftr)
  also have "\<dots> = rbv (sb (f i) \<circ> liftr f) b"
    using assms by (intro rbv_comp nonneg_liftr)
  also have "\<dots> = rbv (f \<circ> sb i) b"
  proof (rule rbv_cong[OF assms(1)])
    fix k :: integer assume "0 \<le> k"
    show "(sb (f i) \<circ> liftr f) k = (f \<circ> sb i) k"
    proof (cases "k = 0")
      case False
      with \<open>0 \<le> k\<close> assms(2) have "0 \<le> f (k - 1)" by (simp add: nonneg_def integer_one_le)
      with False show ?thesis by (simp add: sb_def liftr_def)
    qed (simp add: sb_def liftr_def)
  qed
  also have "\<dots> = rbv f (rbv (sb i) b)"
    using assms by (intro rbv_comp[symmetric] nonneg_sb)
  also have "\<dots> = rbv f (subst_bound (Bound i) b)"
    using assms by (simp add: subst_bound_rbv)
  finally show ?thesis .
qed

lemma hn_rbv:
  assumes "hn env t = Some t'"
  shows "wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow> nonneg f \<Longrightarrow> hn env (rbv f t) = Some (rbv f t')"
  using assms
proof (induction env t t' arbitrary: f rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  have wf: "wf_env ar env" and epp: "env_ppat env" and pt: "ppat t" and nn: "nonneg f"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf epp]
  have real: "hn env s = Some s'" if "h env s = Some s'" "ppat s" for s s'
    using IH[OF that nonneg_id] by simp
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "lk env x T")
      case None
      with 1 Var have "t' = t" by simp
      with Var None show ?thesis by (simp add: hn_Var)
    next
      case (Some u)
      with 1 Var have hu: "h env u = Some t'" by simp
      note lu = lkD[OF Some]
      have pu: "ppat u" by (rule env_ppatD[OF epp lu])
      have hu': "hn env u = Some t'" by (rule real[OF hu pu])
      have "loose_BVars (tr u) = {}"
        using wf_envD(2)[OF wf lu] by (simp add: no_loose_bound_loose_BVars)
      with hn_ppat_aux[OF hu' wf epp pu] have "ppat t'" "loose_BVars (tr t') = {}" by auto
      then have "rbv f t' = t'" by (intro rbv_fix ppat_proper) auto
      with hu' Some Var show ?thesis by (simp add: hn_Var)
    qed
  next
    case (Abs a U b)
    with 1 obtain b' where hb: "h env b = Some b'" and tb: "t' = Abs a U b'"
      by (auto split: Option.bind_splits)
    have "hn env (rbv (liftr f) b) = Some (rbv (liftr f) b')"
      using IH[OF hb] pt Abs nn by (auto dest: ppat_AbsD intro: nonneg_liftr)
    with Abs tb show ?thesis by (simp add: hn_Abs)
  next
    case (App f0 u)
    have nA: "\<not> is_Abs f0" "\<not> is_Abs (rbv f f0)"
      using pt App by (auto elim!: ppat_AppE simp: app_Var_not_Abs rigid_list_comb_not_Abs)
    with 1 App obtain nf where nf: "h env f0 = Some nf"
      and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
      by (cases f0) (auto split: Option.bind_splits)
    from pt[unfolded App] have pf: "ppat f0"
      by (cases rule: ppat_AppE) (auto intro: ppat.ppat_rigid ppat.ppat_flex)
    have hf: "hn env (rbv f f0) = Some (rbv f nf)" by (rule IH[OF nf pf nn])
    have hf': "hn env f0 = Some nf" by (rule real[OF nf pf])
    show ?thesis
    proof (cases "is_Abs nf")
      case False
      with rest have "t' = nf $ u" by (cases nf) auto
      moreover have "\<not> is_Abs (rbv f nf)" using False by simp
      ultimately show ?thesis using hf nA App by (cases "rbv f nf") (simp_all add: hn_App_nonAbs)
    next
      case True
      then obtain a U body where nfa: "nf = Abs a U body" by (cases nf) auto
      with rest have hb: "h env (subst_bound u body) = Some t'" by simp
      from pt[unfolded App] show ?thesis
      proof (cases rule: ppat_AppE)
        case (rigid hd ts)
        have "rigid_head f0" using rigid by (auto simp: rigid_head_def)
        with hn_ppat_aux[OF hf' wf epp pf] have "nf = f0" by simp
        with nfa nA show ?thesis by simp
      next
        case (flex x T iss i)
        from hn_ppat_aux[OF hf' wf epp pf] have pnf: "ppat nf"
          and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
          using flex(1) by (simp_all add: loose_BVars_tr_app)
        have i0: "0 \<le> i" using flex(4) by simp
        have ni: "nat_of_integer i \<notin> set (nats iss)"
        proof
          assume "nat_of_integer i \<in> set (nats iss)"
          then obtain j where "j \<in> set iss" "nat_of_integer j = nat_of_integer i" by auto
          with flex(4) i0 have "i \<in> set iss" by (auto simp: nat_of_integer_eq_iff)
          with flex(3) show False by simp
        qed
        have pb: "ppat body" using pnf nfa by (auto dest: ppat_AbsD)
        have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)" using lnf ni nfa by auto
        from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound u body)" using flex(2) by simp
        have hs: "hn env (rbv f (subst_bound u body)) = Some (rbv f t')" by (rule IH[OF hb ps nn])
        have "subst_bound (Bound (f i)) (rbv (liftr f) body) = rbv f (subst_bound u body)"
          using flex(2) subst_bound_rbv_liftr[OF ppat_proper[OF pb] nn i0] by simp
        with hs hf nfa nA App flex(2) show ?thesis by (simp add: hn_App_nonAbs)
      qed
    qed
  qed (use 1 in \<open>auto simp: hn_atoms\<close>)
qed

lemma hn_idem: "hn env t = Some t' \<Longrightarrow> hn env t' = Some t'"
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  show ?case
  proof (cases t)
    case (Var x T)
    with 1 show ?thesis by (cases "lk env x T") (auto simp: hn_Var)
  next
    case (Abs a U b)
    with 1 show ?thesis by (auto simp: hn_Abs split: Option.bind_splits)
  next
    case (App f0 u)
    show ?thesis
    proof (cases "is_Abs f0")
      case True
      with 1 App show ?thesis by (cases f0) auto
    next
      case False
      with 1 App obtain nf where nf: "h env f0 = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f0) (auto split: Option.bind_splits)
      have hnf: "hn env nf = Some nf" by (rule "1.IH"[OF nf])
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a U b where "nf = Abs a U b" by (cases nf) auto
        with rest "1.IH" show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with hnf nA show ?thesis by (cases nf) (simp_all add: hn_App_nonAbs)
      qed
    qed
  qed (use 1 in \<open>auto simp: hn_atoms\<close>)
qed


subsection \<open>A size measure\<close>

text \<open>
  The size of the instance of a term under the environment, where an uninstantiated flexible
  term \<open>F t\<^sub>1 \<dots> t\<^sub>m\<close> counts as its \<open>\<eta>\<close>-expansion \<open>\<lambda>x\<^sub>m\<^sub>+\<^sub>1 \<dots> x\<^sub>n. F t\<^sub>1 \<dots> t\<^sub>m x\<^sub>m\<^sub>+\<^sub>1 \<dots> x\<^sub>n\<close>
  without the arguments. Abstractions count twice, so that \<open>\<eta>\<close>-expansion in \<^const>\<open>unif\<close>
  decreases the size. Bindings that only prune arguments do not change the size.
\<close>

fun arity :: "ptyp \<Rightarrow> nat" where
  "arity (Type a [T, U]) = (if a = STR ''fun'' then Suc (arity U) else 0)"
| "arity _ = 0"

lemma arity_foldr: "arity (foldr fun_type Us U) = length Us + arity U"
  by (induction Us) auto

fun hd_of :: "pterm \<Rightarrow> pterm" where
  "hd_of (s $ t) = hd_of s"
| "hd_of t = t"

fun nargs :: "pterm \<Rightarrow> nat" where
  "nargs (s $ t) = Suc (nargs s)"
| "nargs t = 0"

lemma hd_of_list_comb[simp]: "hd_of (list_comb h ts) = hd_of h"
  by (induction ts rule: rev_induct) (simp_all add: list_comb_snoc)

lemma nargs_list_comb[simp]: "nargs (list_comb h ts) = nargs h + length ts"
  by (induction ts rule: rev_induct) (simp_all add: list_comb_snoc)

lemma hd_of_app[simp]: "hd_of (app h is) = hd_of h"
  by (simp add: app_list_comb)

lemma nargs_app[simp]: "nargs (app h is) = nargs h + length is"
  by (simp add: app_list_comb)

lemma hd_of_rbv[simp]: "hd_of (rbv f t) = rbv f (hd_of t)"
  by (induction t) auto

lemma nargs_rbv[simp]: "nargs (rbv f t) = nargs t"
  by (induction t) auto

definition is_flex :: "pterm \<Rightarrow> bool" where
  "is_flex t \<longleftrightarrow> is_Var (hd_of t)"

definition fsz :: "pterm \<Rightarrow> nat" where
  "fsz t = (case hd_of t of Var x T \<Rightarrow> 2 * (arity T - nargs t) + 1 | _ \<Rightarrow> 0)"

lemma is_flex_rbv[simp]: "is_flex (rbv f t) = is_flex t"
  by (cases "hd_of t") (auto simp: is_flex_def)

lemma fsz_rbv[simp]: "fsz (rbv f t) = fsz t"
  by (cases "hd_of t") (auto simp: fsz_def)

partial_function (option) psz :: "env \<Rightarrow> pterm \<Rightarrow> nat option" where
  "psz env t =
    (case t of
      Abs a T b \<Rightarrow> Option.bind (psz env b) (\<lambda>n. Some (n + 2))
    | _ \<Rightarrow>
      if is_flex t then
        Option.bind (hn env t) (\<lambda>t'. if is_flex t' then Some (fsz t') else psz env t')
      else
        (case t of
          f $ u \<Rightarrow> Option.bind (psz env f) (\<lambda>m. Option.bind (psz env u) (\<lambda>n. Some (m + n)))
        | _ \<Rightarrow> Some 1))"

lemma psz_Abs: "psz env (Abs a T b) = Option.bind (psz env b) (\<lambda>n. Some (n + 2))"
  by (subst psz.simps) simp

lemma psz_flex: "is_flex t \<Longrightarrow>
    psz env t = Option.bind (hn env t) (\<lambda>t'. if is_flex t' then Some (fsz t') else psz env t')"
  by (subst psz.simps) (cases t; simp add: is_flex_def)

lemma psz_App: "\<not> is_flex (f $ u) \<Longrightarrow>
    psz env (f $ u) = Option.bind (psz env f) (\<lambda>m. Option.bind (psz env u) (\<lambda>n. Some (m + n)))"
  by (subst psz.simps) simp

lemma psz_atoms: "psz env (Bound i) = Some 1" "psz env (Const c T) = Some 1" "psz env (Free c T) = Some 1"
  by (subst psz.simps; simp add: is_flex_def)+

lemma ppat_Bound: "0 \<le> i \<Longrightarrow> ppat (Bound i)"
  using ppat.ppat_rigid[of "Bound i" "[]"] by (simp add: is_rigid_def)

lemma is_flex_app_Var[simp]: "is_flex (app (Var x T) is)"
  by (simp add: is_flex_def)

lemma is_rigid_not_flex: "is_rigid h \<Longrightarrow> \<not> is_flex (list_comb h ts)"
  by (auto simp: is_flex_def is_rigid_def)

lemma psz_rigid_atom: "is_rigid h \<Longrightarrow> psz env h = Some 1"
  by (auto simp: is_rigid_def psz_atoms)

lemma psz_rigid_snoc:
  assumes "is_rigid h"
  shows "psz env (list_comb h (ts @ [t])) =
    Option.bind (psz env (list_comb h ts)) (\<lambda>m. Option.bind (psz env t) (\<lambda>n. Some (m + n)))"
proof -
  have "\<not> is_flex (list_comb h ts $ t)"
    using is_rigid_not_flex[OF assms, of "ts @ [t]"] by (simp add: list_comb_snoc)
  then show ?thesis by (simp add: list_comb_snoc psz_App)
qed

lemma psz_term:
  assumes fin: "fin_env env" and ac: "acyc env" and wf: "wf_env ar env" and epp: "env_ppat env"
    and pt: "ppat t"
  shows "\<exists>n. psz env t = Some n"
proof -
  define Q where "Q x \<longleftrightarrow> (\<forall>iss. distinct iss \<longrightarrow> (\<forall>i\<in>set iss. 0 \<le> i) \<longrightarrow>
    (\<exists>n. psz env (app (Var (fst x) (snd x)) iss) = Some n))" for x
  have L: "\<exists>n. psz env t = Some n" if "ppat t" "\<forall>y\<in>vps t. Q y" for t
    using that
  proof (induction rule: ppat.induct)
    case (ppat_Abs t a T)
    then show ?case by (auto simp: psz_Abs)
  next
    case (ppat_rigid h ts)
    then have IH: "\<exists>n. psz env t = Some n" if "t \<in> set ts" for t using that by (auto simp: vps_list_comb)
    have "\<exists>n. psz env (list_comb h ts') = Some n" if "set ts' \<subseteq> set ts" for ts'
      using that
    proof (induction ts' rule: rev_induct)
      case Nil
      then show ?case using psz_rigid_atom[OF ppat_rigid.hyps(1)] by simp
    next
      case (snoc t ts')
      with IH[of t] show ?case by (auto simp: psz_rigid_snoc[OF ppat_rigid.hyps(1)])
    qed
    then show ?case by blast
  next
    case (ppat_flex iss x T)
    then show ?case by (auto simp: Q_def)
  qed
  have "Q x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_dep[OF fin ac]]])
    case (1 x)
    obtain xn T where x: "x = (xn, T)" by (cases x)
    show ?case unfolding Q_def x fst_conv snd_conv
    proof (intro allI impI)
      fix iss :: "integer list" assume d: "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
      then have pf: "ppat (app (Var xn T) iss)" by (auto intro: ppat.ppat_flex)
      from hn_term[OF fin ac wf epp pf] obtain t' where ht: "hn env (app (Var xn T) iss) = Some t'"
        by blast
      show "\<exists>n. psz env (app (Var xn T) iss) = Some n"
      proof (cases "is_flex t'")
        case False
        then obtain u where Some: "lk env xn T = Some u"
          using ht hn_unbound[of env xn T iss] by (cases "lk env xn T") auto
        have "vps t' \<subseteq> reach env (vps u)" by (rule hn_app_bound_vps[OF Some ht])
        then have "\<forall>y\<in>vps t'. Q y" using 1 reach_lk_trancl[OF Some] x by blast
        with L[OF hn_ppat_aux[OF ht wf epp pf, THEN conjunct1]] ht False show ?thesis
          by (auto simp: psz_flex)
      qed (use ht in \<open>simp add: psz_flex\<close>)
    qed
  qed
  then show ?thesis using L[OF pt] by blast
qed

lemma psz_hn:
  assumes "hn env t = Some t'" "ppat t" "wf_env ar env" "env_ppat env"
  shows "psz env t' = psz env t"
  using assms(2,1)
proof (induction arbitrary: t' rule: ppat.induct)
  case (ppat_Abs t a T)
  then obtain b' where "hn env t = Some b'" "t' = Abs a T b'" by (auto simp: hn_Abs split: Option.bind_splits)
  with ppat_Abs show ?case by (simp add: psz_Abs)
next
  case (ppat_rigid h ts)
  with hn_rigid show ?case by simp
next
  case (ppat_flex iss x T)
  have "hn env t' = Some t'" by (rule hn_idem[OF ppat_flex.prems])
  with ppat_flex.prems show ?case by (cases "is_flex t'") (simp_all add: psz_flex)
qed

lemma psz_rbv:
  assumes "psz env t = Some n"
  shows "wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> ppat t \<Longrightarrow> nonneg f \<Longrightarrow> psz env (rbv f t) = Some n"
  using assms
proof (induction env t n arbitrary: f rule: psz.raw_induct[rotated, consumes 1])
  case (1 p env t n)
  have wf: "wf_env ar env" and epp: "env_ppat env" and pt: "ppat t" and nn: "nonneg f"
    using 1 by simp_all
  note IH = "1.IH"[OF _ wf epp]
  show ?case
  proof (cases "is_Abs t")
    case True
    then obtain a T b where t: "t = Abs a T b" by (cases t) auto
    with 1 obtain m where m: "p env b = Some m" and n: "n = m + 2" by (auto split: Option.bind_splits)
    have "psz env (rbv (liftr f) b) = Some m"
      using IH[OF m] pt t nn by (auto dest: ppat_AbsD intro: nonneg_liftr)
    with t n show ?thesis by (simp add: psz_Abs)
  next
    case nA: False
    show ?thesis
    proof (cases "is_flex t")
      case True
      with 1 nA obtain t' where ht: "hn env t = Some t'"
        and rest: "(if is_flex t' then Some (fsz t') else p env t') = Some n"
        by (cases t) (auto split: Option.bind_splits)
      have hr: "hn env (rbv f t) = Some (rbv f t')" by (rule hn_rbv[OF ht wf epp pt nn])
      have pt': "ppat t'" using hn_ppat_aux[OF ht wf epp pt] by simp
      show ?thesis
      proof (cases "is_flex t'")
        case True
        with rest hr \<open>is_flex t\<close> show ?thesis by (simp add: psz_flex)
      next
        case False
        with rest have "p env t' = Some n" by simp
        from IH[OF this pt' nn] hr False \<open>is_flex t\<close> show ?thesis by (simp add: psz_flex)
      qed
    next
      case False
      show ?thesis
      proof (cases t)
        case (App f0 u)
        with 1 nA False obtain m k where m: "p env f0 = Some m" and k: "p env u = Some k" and n: "n = m + k"
          by (auto split: Option.bind_splits)
        from pt App have pf: "ppat f0" and pu: "ppat u"
          by (auto elim!: ppat_AppE intro: ppat.ppat_rigid ppat.ppat_flex ppat_Bound)
        have "is_flex (rbv f (f0 $ u)) = is_flex (f0 $ u)" by (rule is_flex_rbv)
        with False App have "\<not> is_flex (rbv f f0 $ rbv f u)" by simp
        with IH[OF m pf nn] IH[OF k pu nn] App n show ?thesis by (simp add: psz_App)
      qed (use 1 False nA in \<open>auto simp: psz_atoms is_flex_def\<close>)
    qed
  qed
qed


subsection \<open>Extending environments\<close>

definition tinv :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> bool" where
  "tinv ar env \<longleftrightarrow> fin_env env \<and> acyc env \<and> wf_env ar env \<and> env_ppat env"

lemma tinvD:
  assumes "tinv ar env"
  shows "fin_env env" "acyc env" "wf_env ar env" "env_ppat env"
  using assms by (simp_all add: tinv_def)

lemma extends_lk:
  assumes "extends env' env" "lk env x T = Some u"
  shows "lk env' x T = Some u"
proof -
  have "vt_lookup (tenv env') x = Some (T, u)" using assms(1) lkD[OF assms(2)] unfolding extends_def by blast
  then show ?thesis by (simp add: lk_def)
qed

lemma dep_extends: "extends env' env \<Longrightarrow> dep env \<subseteq> dep env'"
  by (auto simp: dep_def dest: extends_lk)

lemma reach_extends: "extends env' env \<Longrightarrow> reach env X \<subseteq> reach env' X"
  unfolding reach_def using rtrancl_mono[OF dep_extends] by blast

lemma hn_ext:
  assumes "hn env t = Some t1"
  shows "ppat t \<Longrightarrow> extends env' env \<Longrightarrow> wf_env ar env \<Longrightarrow> env_ppat env \<Longrightarrow> tinv ar env' \<Longrightarrow>
    hn env t = Some t1 \<and> hn env' t = hn env' t1"
  using assms
proof (induction env t t1 rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t1)
  have pt: "ppat t" and ext: "extends env' env" and wf: "wf_env ar env" and epp: "env_ppat env"
    and ti: "tinv ar env'"
    using 1 by simp_all
  note IH = "1.IH"[OF _ _ ext wf epp ti]
  note ti' = tinvD[OF ti]
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "lk env x T")
      case None
      with 1 Var have "t1 = t" by simp
      with Var None show ?thesis by (simp add: hn_Var)
    next
      case (Some u)
      with 1 Var have hu: "h env u = Some t1" by simp
      note lu = lkD[OF Some]
      from IH[OF hu env_ppatD[OF epp lu]] Some extends_lk[OF ext Some] Var show ?thesis
        by (simp add: hn_Var)
    qed
  next
    case (Abs a U b)
    with 1 obtain b1 where hb: "h env b = Some b1" and tb: "t1 = Abs a U b1"
      by (auto split: Option.bind_splits)
    from IH[OF hb] pt Abs have "hn env b = Some b1" "hn env' b = hn env' b1"
      by (auto dest: ppat_AbsD)
    with Abs tb show ?thesis by (simp add: hn_Abs)
  next
    case (App f0 u)
    have nA: "\<not> is_Abs f0"
      using pt App by (auto elim!: ppat_AppE simp: app_Var_not_Abs rigid_list_comb_not_Abs)
    with 1 App obtain nf where nf: "h env f0 = Some nf"
      and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t1"
      by (cases f0) (auto split: Option.bind_splits)
    from pt[unfolded App] have pf: "ppat f0"
      by (cases rule: ppat_AppE) (auto intro: ppat.ppat_rigid ppat.ppat_flex)
    from IH[OF nf pf] have hf: "hn env f0 = Some nf" and hf': "hn env' f0 = hn env' nf" by simp_all
    show ?thesis
    proof (cases "is_Abs nf")
      case False
      with rest have t1: "t1 = nf $ u" by (cases nf) auto
      have "hn env t = Some t1" using hf nA False t1 App by (cases nf) (simp_all add: hn_App_nonAbs)
      moreover have "hn env' t = hn env' t1"
        using hf' nA False t1 App by (simp add: hn_App_nonAbs)
      ultimately show ?thesis by simp
    next
      case True
      then obtain a U body where nfa: "nf = Abs a U body" by (cases nf) auto
      with rest have hb: "h env (subst_bound u body) = Some t1" by simp
      from pt[unfolded App] show ?thesis
      proof (cases rule: ppat_AppE)
        case (rigid hd ts)
        have "rigid_head f0" using rigid by (auto simp: rigid_head_def)
        with hn_ppat_aux[OF hf wf epp pf] have "nf = f0" by simp
        with nfa nA show ?thesis by simp
      next
        case (flex x T iss i)
        from hn_ppat_aux[OF hf wf epp pf] have pnf: "ppat nf"
          and lnf: "loose_BVars (tr nf) \<subseteq> set (nats iss)"
          using flex(1) by (simp_all add: loose_BVars_tr_app)
        have i0: "0 \<le> i" using flex(4) by simp
        have ni: "nat_of_integer i \<notin> set (nats iss)"
        proof
          assume "nat_of_integer i \<in> set (nats iss)"
          then obtain j where "j \<in> set iss" "nat_of_integer j = nat_of_integer i" by auto
          with flex(4) i0 have "i \<in> set iss" by (auto simp: nat_of_integer_eq_iff)
          with flex(3) show False by simp
        qed
        have pb: "ppat body" using pnf nfa by (auto dest: ppat_AbsD)
        have "Suc (nat_of_integer i) \<notin> loose_BVars (tr body)" using lnf ni nfa by auto
        from ppat_subst_bound[OF pb i0 this] have ps: "ppat (subst_bound u body)" using flex(2) by simp
        from IH[OF hb ps] have hs: "hn env (subst_bound u body) = Some t1"
          and hs': "hn env' (subst_bound u body) = hn env' t1" by simp_all
        have "hn env t = Some t1" using hf nfa hs nA App by (simp add: hn_App_nonAbs)
        moreover have "hn env' t = hn env' t1"
        proof -
          from hn_term[OF ti'(1,2,3,4) pb] obtain b' where hb': "hn env' body = Some b'" by blast
          have pb': "ppat b'" using hn_ppat_aux[OF hb' ti'(3,4) pb] by simp
          have "hn env' t = hn env' (subst_bound (Bound i) b')"
            using hf' nfa hb' nA App flex(2) by (simp add: hn_App_nonAbs hn_Abs)
          also have "\<dots> = hn env' (rbv (sb i) b')"
            using subst_bound_rbv[OF ppat_proper[OF pb'] i0] by simp
          also have "\<dots> = Some (rbv (sb i) b')"
            using hn_rbv[OF hn_idem[OF hb'] ti'(3,4) pb' nonneg_sb[OF i0]] .
          also have "\<dots> = hn env' (rbv (sb i) body)"
            using hn_rbv[OF hb' ti'(3,4) pb nonneg_sb[OF i0]] by simp
          also have "\<dots> = hn env' (subst_bound u body)"
            using subst_bound_rbv[OF ppat_proper[OF pb] i0] flex(2) by simp
          finally show ?thesis using hs' by simp
        qed
        ultimately show ?thesis by simp
      qed
    qed
  qed (use 1 in \<open>auto simp: hn_atoms\<close>)
qed

lemma psz_ext:
  assumes ti: "tinv ar env" and ti': "tinv ar env'" and ext: "extends env' env"
    and new: "\<And>x X u. lk env' x X = Some u \<Longrightarrow> (x, X) \<noteq> (F, T) \<Longrightarrow> lk env x X = Some u"
    and Fnew: "vt_lookup (tenv env) F = None"
    and prune: "\<And>iss. distinct iss \<Longrightarrow> \<forall>i\<in>set iss. 0 \<le> i \<Longrightarrow>
      psz env' (app (Var F T) iss) = Some (fsz (app (Var F T) iss))"
    and pt: "ppat t"
  shows "psz env' t = psz env t"
proof -
  note t0 = tinvD[OF ti] and t1 = tinvD[OF ti']
  define Q where "Q x \<longleftrightarrow> (\<forall>iss. distinct iss \<longrightarrow> (\<forall>i\<in>set iss. 0 \<le> i) \<longrightarrow>
    psz env' (app (Var (fst x) (snd x)) iss) = psz env (app (Var (fst x) (snd x)) iss))" for x
  have L: "psz env' t = psz env t" if "ppat t" "\<forall>y\<in>vps t. Q y" for t
    using that
  proof (induction rule: ppat.induct)
    case (ppat_Abs t a T)
    then show ?case by (simp add: psz_Abs)
  next
    case (ppat_rigid h ts)
    then have IH: "psz env' t = psz env t" if "t \<in> set ts" for t using that by (auto simp: vps_list_comb)
    have "psz env' (list_comb h ts') = psz env (list_comb h ts')" if "set ts' \<subseteq> set ts" for ts'
      using that
    proof (induction ts' rule: rev_induct)
      case Nil
      then show ?case using psz_rigid_atom[OF ppat_rigid.hyps(1)] by simp
    next
      case (snoc t ts')
      with IH[of t] show ?case by (simp add: psz_rigid_snoc[OF ppat_rigid.hyps(1)])
    qed
    then show ?case by blast
  next
    case (ppat_flex iss x T)
    then show ?case by (auto simp: Q_def)
  qed
  have lkF: "lk env F X = None" for X using Fnew by (simp add: lk_def)
  have "Q x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_dep[OF t1(1,2)]]])
    case (1 x)
    obtain xn X where x: "x = (xn, X)" by (cases x)
    show ?case unfolding Q_def x fst_conv snd_conv
    proof (intro allI impI)
      fix iss :: "integer list" assume d: "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
      then have pf: "ppat (app (Var xn X) iss)" by (auto intro: ppat.ppat_flex)
      show "psz env' (app (Var xn X) iss) = psz env (app (Var xn X) iss)"
      proof (cases "(xn, X) = (F, T)")
        case True
        with prune[OF d] lkF hn_unbound[of env F T iss] show ?thesis by (simp add: psz_flex)
      next
        case False
        show ?thesis
        proof (cases "lk env' xn X")
          case None
          then have "lk env xn X = None" using extends_lk[OF ext, of xn X] by (cases "lk env xn X") auto
          with None hn_unbound[of env' xn X iss] hn_unbound[of env xn X iss] show ?thesis
            by (simp add: psz_flex)
        next
          case (Some u)
          have lu: "lk env xn X = Some u" by (rule new[OF Some False])
          from hn_term[OF t0 pf] obtain s1 where hs: "hn env (app (Var xn X) iss) = Some s1" by blast
          have ps1: "ppat s1" using hn_ppat_aux[OF hs t0(3,4) pf] by simp
          from hn_ext[OF hs pf ext t0(3,4) ti'] have e: "hn env' (app (Var xn X) iss) = hn env' s1"
            by simp
          from hn_term[OF t1 ps1] obtain s1' where hs': "hn env' s1 = Some s1'" by blast
          have "psz env' (app (Var xn X) iss) = psz env' s1"
            using psz_hn[OF e[unfolded hs'] pf t1(3,4)] psz_hn[OF hs' ps1 t1(3,4)] by simp
          moreover have "psz env (app (Var xn X) iss) = psz env s1"
            using psz_hn[OF hs pf t0(3,4)] by simp
          moreover have "psz env' s1 = psz env s1"
          proof (rule L[OF ps1], intro ballI)
            fix y assume "y \<in> vps s1"
            with hn_app_bound_vps[OF lu hs] reach_extends[OF ext] have "y \<in> reach env' (vps u)" by blast
            from reach_lk_trancl[OF Some this] 1 x show "Q y" by blast
          qed
          ultimately show ?thesis by simp
        qed
      qed
    qed
  qed
  then show ?thesis using L[OF pt] by blast
qed


end
