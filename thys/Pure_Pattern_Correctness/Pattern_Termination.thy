section \<open>Termination of Pattern Unification\<close>

theory Pattern_Termination
  imports Pattern_Patterns
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

lemma hn_App_nonAbs_res:
  "\<not> is_Abs nf \<Longrightarrow> hn env f = Some nf \<Longrightarrow> \<not> is_Abs f \<Longrightarrow> hn env (f $ u) = Some (nf $ u)"
  by (cases nf) (simp_all add: hn_App_nonAbs)

lemma app_Nil[simp]: "app s [] = s"
  by (simp add: app_def)

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


subsection \<open>Bindings that prune arguments\<close>

definition absl :: "(name \<times> ptyp) list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "absl bs t = foldr (\<lambda>(a, T) b. Abs a T b) bs t"

lemma absl_simps[simp]: "absl [] t = t" "absl ((a, T) # bs) t = Abs a T (absl bs t)"
  by (simp_all add: absl_def)

lemma ok_mkabs_absl: "ok (mkabs binders is t) u \<Longrightarrow> \<exists>bs. length bs = length is \<and> u = absl bs t"
proof (induction "is" arbitrary: u)
  case (Cons i "is")
  then obtain a T u' where "ok (nth binders i) (a, T)" "ok (mkabs binders is t) u'" "u = Abs a T u'"
    by (auto split: prod.splits)
  with Cons.IH[of u'] obtain bs where "length bs = length is" "u' = absl bs t" by blast
  with \<open>u = Abs a T u'\<close> show ?case by (intro exI[of _ "(a, T) # bs"]) simp
qed simp

lemma rbv_app_Var: "rbv f (app (Var H T) js) = app (Var H T) (map f js)"
  by (induction js rule: rev_induct) (simp_all add: app_snoc app_def)

lemma rbv_absl_app:
  "\<exists>js'. rbv f (absl bs (app (Var H T) js)) = absl bs (app (Var H T) js') \<and> length js' = length js \<and>
    (nonneg f \<longrightarrow> (\<forall>j\<in>set js. 0 \<le> j) \<longrightarrow> (\<forall>j\<in>set js'. 0 \<le> j))"
proof (induction bs arbitrary: f)
  case Nil
  show ?case by (intro exI[of _ "map f js"]) (auto simp: rbv_app_Var nonneg_def)
next
  case (Cons b bs)
  obtain a U where b: "b = (a, U)" by force
  from Cons.IH[of "liftr f"] obtain js' where "rbv (liftr f) (absl bs (app (Var H T) js)) = absl bs (app (Var H T) js')"
    "length js' = length js" "nonneg (liftr f) \<longrightarrow> (\<forall>j\<in>set js. 0 \<le> j) \<longrightarrow> (\<forall>j\<in>set js'. 0 \<le> j)" by blast
  with b show ?case by (auto intro: nonneg_liftr)
qed

lemma proper_absl_app: "(\<forall>j\<in>set js. 0 \<le> j) \<Longrightarrow> proper (absl bs (app (Var H T) js))"
  by (induction bs) (auto simp: app_list_comb proper_list_comb)

lemma hn_absl_app: "lk env H T = None \<Longrightarrow> hn env (absl bs (app (Var H T) js)) = Some (absl bs (app (Var H T) js))"
  by (induction bs) (auto simp: hn_Abs hn_unbound)

lemma psz_absl_app: "lk env H T = None \<Longrightarrow>
    psz env (absl bs (app (Var H T) js)) = Some (2 * length bs + fsz (app (Var H T) js))"
proof (induction bs)
  case Nil
  then show ?case by (simp add: psz_flex hn_unbound)
next
  case (Cons b bs)
  then show ?case by (cases b) (simp add: psz_Abs)
qed

lemma ok_split_type:
  "ok (split_type T n Acc) (Ts, U) \<Longrightarrow>
    0 \<le> n \<and> (\<exists>Us. T = foldr fun_type Us U \<and> Ts = rev Us @ Acc \<and> length Us = nat_of_integer n)"
proof (induction T arbitrary: n Acc)
  case (Type a Ts0)
  show ?case
  proof (cases "n = 0")
    case True
    with Type.prems show ?thesis by (subst (asm) split_type.simps) (auto simp: integer_reps)
  next
    case False
    with Type.prems obtain T1 T2 where T: "a = STR ''fun''" "Ts0 = [T1, T2]"
      and r: "ok (split_type T2 (n - 1) (T1 # Acc)) (Ts, U)"
      by (subst (asm) split_type.simps) (auto split: list.splits if_splits)
    from Type.IH[OF _ r] T obtain Us where
      "0 \<le> n - 1" "T2 = foldr fun_type Us U" "Ts = rev Us @ T1 # Acc" "length Us = nat_of_integer (n - 1)"
      by auto
    moreover from \<open>0 \<le> n - 1\<close> have "0 < n" by (simp add: integer_reps)
    ultimately show ?thesis using T
      by (intro conjI exI[of _ "T1 # Us"]) (auto simp: nat_of_integer_pos)
  qed
next
  case (TFree b S)
  then show ?case by (subst (asm) split_type.simps) (auto simp: integer_reps split: if_splits)
next
  case (TVar v S)
  then show ?case by (subst (asm) split_type.simps) (auto simp: integer_reps split: if_splits)
qed

lemma ok_type_of_G:
  assumes "ok (type_of_G env T n ks) Hty" "vt_is_empty (tyenv env)"
  obtains Us U Vs where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    "Hty = foldr fun_type Vs U" "length Vs = length ks"
proof -
  from assms obtain Ts U Vs where st: "ok (split_type T n []) (Ts, U)"
    and Vs: "list_all2 (\<lambda>i U. ok (nth Ts i) U) ks Vs" and H: "Hty = foldr fun_type Vs U"
    by (auto simp: type_of_G_def norm_type_def ok_mapM)
  from ok_split_type[OF st] obtain Us where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    by auto
  moreover have "length Vs = length ks" using Vs by (simp add: list_all2_lengthD)
  ultimately show ?thesis using H that by blast
qed

lemma psz_prune:
  assumes lF: "lk env F T = Some u" and u: "ok (mkabs binders is (app (Var H Hty) ks)) u"
    and lH: "lk env H Hty = None" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
    and T: "T = foldr fun_type Us U" "length Us = length is"
    and Hty: "Hty = foldr fun_type Vs U" "length Vs = length ks"
    and iss: "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
  shows "psz env (app (Var F T) iss) = Some (fsz (app (Var F T) iss))"
proof -
  have C: "\<exists>bs js. hn env (app (Var F T) jss) = Some (absl bs (app (Var H Hty) js)) \<and>
      length bs = length is - length jss \<and> length js = length ks + (length jss - length is) \<and>
      (\<forall>j\<in>set js. 0 \<le> j)" if "\<forall>i\<in>set jss. 0 \<le> i" for jss
    using that
  proof (induction jss rule: rev_induct)
    case Nil
    from ok_mkabs_absl[OF u] obtain bs where "length bs = length is" "u = absl bs (app (Var H Hty) ks)"
      by blast
    with lF lH ks show ?case by (intro exI[of _ bs] exI[of _ ks]) (simp add: hn_Var hn_absl_app)
  next
    case (snoc i jss)
    then obtain bs js where r: "hn env (app (Var F T) jss) = Some (absl bs (app (Var H Hty) js))"
      and l: "length bs = length is - length jss" "length js = length ks + (length jss - length is)"
      and js: "\<forall>j\<in>set js. 0 \<le> j"
      by auto
    have i0: "0 \<le> i" using snoc.prems by simp
    show ?case
    proof (cases bs)
      case Nil
      then have "hn env (app (Var F T) (jss @ [i])) = Some (app (Var H Hty) (js @ [i]))"
        using r hn_App_nonAbs_res[of "app (Var H Hty) js" env "app (Var F T) jss" "Bound i"]
        by (simp add: app_snoc app_Var_not_Abs)
      with Nil l js i0 show ?thesis by (intro exI[of _ "[]"] exI[of _ "js @ [i]"]) auto
    next
      case (Cons b bs')
      obtain a V where b: "b = (a, V)" by force
      have pb: "proper (absl bs' (app (Var H Hty) js))" by (rule proper_absl_app[OF js])
      from rbv_absl_app[of "sb i" bs' H Hty js] obtain js' where
        e: "rbv (sb i) (absl bs' (app (Var H Hty) js)) = absl bs' (app (Var H Hty) js')"
        and lj: "length js' = length js" and nj: "\<forall>j\<in>set js'. 0 \<le> j"
        using nonneg_sb[OF i0] js by blast
      have "hn env (app (Var F T) (jss @ [i])) = hn env (subst_bound (Bound i) (absl bs' (app (Var H Hty) js)))"
        using r Cons b by (simp add: app_snoc hn_App_nonAbs app_Var_not_Abs)
      also have "\<dots> = Some (absl bs' (app (Var H Hty) js'))"
        using subst_bound_rbv[OF pb i0] e hn_absl_app[OF lH] by simp
      finally show ?thesis using l lj nj Cons by (intro exI[of _ bs'] exI[of _ js']) auto
    qed
  qed
  from C[OF iss(2)] obtain bs js where r: "hn env (app (Var F T) iss) = Some (absl bs (app (Var H Hty) js))"
    and l: "length bs = length is - length iss" "length js = length ks + (length iss - length is)"
    by blast
  have p: "psz env (app (Var F T) iss) = Some (2 * length bs + fsz (app (Var H Hty) js))"
  proof (cases bs)
    case Nil
    with r show ?thesis by (simp add: psz_flex)
  next
    case (Cons b bs')
    then have "\<not> is_flex (absl bs (app (Var H Hty) js))" by (cases b) (simp add: is_flex_def)
    with r psz_absl_app[OF lH, of bs js] show ?thesis by (simp add: psz_flex)
  qed
  have "2 * length bs + fsz (app (Var H Hty) js) = fsz (app (Var F T) iss)"
    using l T Hty by (simp add: fsz_def arity_foldr)
  with p show ?thesis by simp
qed


subsection \<open>Unbound reachable variables\<close>

definition unb :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "unb env X = {y \<in> reach env X. lk env (fst y) (snd y) = None}"

lemma unb_subset: "X \<subseteq> Y \<Longrightarrow> unb env X \<subseteq> unb env Y"
  unfolding unb_def using reach_subset[of X Y env] by blast

lemma reach_pred: "(y, z) \<in> dep env \<Longrightarrow> z \<in> reach env X \<Longrightarrow> y \<in> reach env X"
  by (auto simp: reach_def intro: converse_rtrancl_into_rtrancl)

lemma reach_Domain: "reach env X \<subseteq> X \<union> Domain (dep env)"
proof
  fix y assume "y \<in> reach env X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  from x(2) have "y = x \<or> (\<exists>z. (y, z) \<in> dep env)" by (cases rule: converse_rtranclE) auto
  with x(1) show "y \<in> X \<union> Domain (dep env)" by auto
qed

lemma finite_reach:
  assumes "fin_env env" "finite X"
  shows "finite (reach env X)"
proof -
  have "finite (X \<union> Domain (dep env))" using assms finite_dep[OF assms(1)] by (simp add: finite_Domain)
  with reach_Domain[of env X] show ?thesis by (rule finite_subset)
qed

lemma finite_unb: "fin_env env \<Longrightarrow> finite X \<Longrightarrow> finite (unb env X)"
  using finite_reach[of env X] by (auto simp: unb_def)

lemma reach_unbound: "lk env x T = None \<Longrightarrow> reach env {(x, T)} = {(x, T)}"
proof -
  assume u: "lk env x T = None"
  have "y = (x, T)" if "(y, (x, T)) \<in> (dep env)\<^sup>*" for y
    using that by (cases rule: rtranclE) (auto simp: dep_def u)
  then show ?thesis by (auto simp: reach_def)
qed

lemma lk_update:
  "tenv env' = vt_update (F, (T, u)) (tenv env) \<Longrightarrow>
    lk env' x X = (if x = F then (if X = T then Some u else None) else lk env x X)"
  by (simp add: lk_def)

lemma dep_update:
  assumes "tenv env' = vt_update (F, (T, u)) (tenv env)" "vt_lookup (tenv env) F = None"
  shows "dep env' = dep env \<union> (\<lambda>y. (y, (F, T))) ` vps u"
proof -
  have "lk env F X = None" for X using assms(2) by (simp add: lk_def)
  then show ?thesis using lk_update[OF assms(1)] by (auto simp: dep_def)
qed

lemma dep_update_path:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
    and p: "(a, b) \<in> (dep env')\<^sup>*"
  shows "(a, b) \<in> (dep env)\<^sup>* \<or> (a \<in> reach env V \<and> (c, b) \<in> (dep env)\<^sup>*)"
  using p
proof (induction rule: rtrancl_induct)
  case (step b d')
  from step.hyps(2) d consider "(b, d') \<in> dep env" | "d' = c" "b \<in> V" by auto
  then show ?case
  proof cases
    case 1
    with step.IH show ?thesis by (auto intro: rtrancl_into_rtrancl)
  next
    case 2
    from step.IH 2 have "a \<in> reach env V" by (auto simp: reach_def)
    with 2 show ?thesis by simp
  qed
qed simp

lemma reach_update:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
  shows "reach env' X = reach env X \<union> (if c \<in> reach env X then reach env V else {})"
proof
  show "reach env' X \<subseteq> reach env X \<union> (if c \<in> reach env X then reach env V else {})"
  proof
    fix y assume "y \<in> reach env' X"
    then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env')\<^sup>*" by (auto simp: reach_def)
    from dep_update_path[OF d c x(2)] x(1)
    show "y \<in> reach env X \<union> (if c \<in> reach env X then reach env V else {})"
      by (auto simp: reach_def)
  qed
next
  have sub: "dep env \<subseteq> dep env'" using d by auto
  then have "reach env X \<subseteq> reach env' X" unfolding reach_def using rtrancl_mono by blast
  moreover have "reach env V \<subseteq> reach env' X" if "c \<in> reach env X"
  proof
    fix y assume "y \<in> reach env V"
    then obtain z where z: "z \<in> V" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
    from that obtain x where x: "x \<in> X" "(c, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
    have "(y, z) \<in> (dep env')\<^sup>*" "(c, x) \<in> (dep env')\<^sup>*" using z(2) x(2) rtrancl_mono[OF sub] by auto
    moreover have "(z, c) \<in> dep env'" using d z(1) by auto
    ultimately have "(y, x) \<in> (dep env')\<^sup>*" by (meson rtrancl_into_rtrancl rtrancl_trans)
    with x(1) show "y \<in> reach env' X" by (auto simp: reach_def)
  qed
  ultimately show "reach env X \<union> (if c \<in> reach env X then reach env V else {}) \<subseteq> reach env' X"
    by auto
qed

lemma acyclic_update:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
    and ac: "acyclic (dep env)"
  shows "acyclic (dep env')"
  unfolding acyclic_def
proof
  fix x
  show "(x, x) \<notin> (dep env')\<^sup>+"
  proof
    assume "(x, x) \<in> (dep env')\<^sup>+"
    then obtain z where xz: "(x, z) \<in> dep env'" and zx: "(z, x) \<in> (dep env')\<^sup>*"
      by (auto dest: tranclD)
    from xz d consider "(x, z) \<in> dep env" | "z = c" "x \<in> V" by auto
    then show False
    proof cases
      case 1
      from dep_update_path[OF d c zx] show False
      proof
        assume "(z, x) \<in> (dep env)\<^sup>*"
        with 1 have "(x, x) \<in> (dep env)\<^sup>+" by (rule rtrancl_into_trancl2)
        with ac show False unfolding acyclic_def by blast
      next
        assume "z \<in> reach env V \<and> (c, x) \<in> (dep env)\<^sup>*"
        then have "x \<in> reach env V" "(c, x) \<in> (dep env)\<^sup>*" using reach_pred[OF 1] by auto
        then have "c \<in> reach env V" by (auto simp: reach_def intro: rtrancl_trans)
        with c show False by simp
      qed
    next
      case 2
      from dep_update_path[OF d c zx[unfolded 2(1)]] 2(2) have "c \<in> reach env V"
        by (auto simp: reach_def)
      with c show False by simp
    qed
  qed
qed

lemma unb_update:
  assumes "tenv env' = vt_update (F, (T, u)) (tenv env)" "vt_lookup (tenv env) F = None"
    and c: "(F, T) \<notin> reach env (vps u)"
  shows "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
proof -
  note r = reach_update[OF dep_update[OF assms(1,2)] c]
  have l: "lk env' (fst y) (snd y) = None \<longleftrightarrow> y \<noteq> (F, T) \<and> lk env (fst y) (snd y) = None" for y
    using lk_update[OF assms(1)] assms(2) by (cases y) (auto simp: lk_def)
  have "(F, T) \<notin> unb env (vps u)" using c by (auto simp: unb_def)
  then show ?thesis unfolding unb_def r l by auto
qed

lemma fin_env_update: "tenv env' = vt_update (F, (T, u)) (tenv env) \<Longrightarrow> fin_env env \<Longrightarrow> fin_env env'"
  by (simp add: fin_env_def Collect_mono_iff[symmetric])
    (rule finite_subset[of _ "insert F {x. vt_lookup (tenv env) x \<noteq> None}"]; auto)


subsection \<open>Termination of the occurs check\<close>

lemma occurs_term:
  assumes fin: "fin_env env" and ac: "acyc env" and wf: "wf_env ar env"
  shows "\<exists>r. occurs F t env = Some r"
proof -
  define Q where "Q x \<longleftrightarrow> (\<exists>r. occurs F (Var (fst x) (snd x)) env = Some r)" for x
  have L: "\<exists>r. occurs F t env = Some r" if "\<forall>y\<in>vps t. Q y" for t
    using that
  proof (induction t)
    case (Var x T)
    then show ?case by (simp add: Q_def)
  next
    case (Abs a T t)
    then show ?case by (subst occurs.simps) simp
  next
    case (App t1 t2)
    then obtain r1 r2 where "occurs F t1 env = Some r1" "occurs F t2 env = Some r2" by auto
    then show ?case
      by (subst occurs.simps) (cases r1; auto simp: bindM_def return_def split: res.splits)
  qed (subst occurs.simps; simp add: return_def)+
  have "Q x" for x
  proof (induction x rule: wf_induct[OF wf_trancl[OF wf_dep[OF fin ac]]])
    case (1 x)
    obtain xn T where x: "x = (xn, T)" by (cases x)
    show ?case
    proof (cases "vt_lookup (tenv env) xn")
      case None
      then show ?thesis using wf_envD(1)[OF wf]
        by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk return_def bindM_def)
    next
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "U = T")
        case False
        with Some p wf_envD(1)[OF wf] show ?thesis
          by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk var_clash_def raise_def bindM_def)
      next
        case True
        with Some p have lu: "lk env xn T = Some u" by (simp add: lk_def)
        have "\<forall>y\<in>vps u. Q y"
          using 1 reach_lk_trancl[OF lu] reach_incl x by blast
        from L[OF this] lu Some p True wf_envD(1)[OF wf] show ?thesis
          by (simp add: Q_def x occurs.simps[of F "Var xn T"] lookup_lk)
      qed
    qed
  qed
  then show ?thesis using L by blast
qed

lemma occurs_False:
  assumes "occurs F t env = Some r"
  shows "r = Ok False \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> vt_lookup (tenv env) F = None \<Longrightarrow>
    \<forall>y\<in>reach env (vps t). fst y \<noteq> F"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  have e: "vt_is_empty (tyenv env)" and F: "vt_lookup (tenv env) F = None" using 1 by simp_all
  note IH = "1.IH"[OF _ refl e F]
  show ?case
  proof (cases t)
    case (Var G T)
    show ?thesis
    proof (cases "lk env G T")
      case None
      with 1 Var e have "G \<noteq> F"
        by (auto simp: lookup_lk lk_def var_clash_def split: option.splits if_splits)
      with None Var show ?thesis by (simp add: reach_unbound)
    next
      case (Some u)
      with 1 Var e have "oc F u env = Some (Ok False)"
        by (auto simp: lookup_lk lk_def split: option.splits if_splits)
      from IH[OF this] have "\<forall>y\<in>reach env (vps u). fst y \<noteq> F" .
      moreover have "G \<noteq> F" using F lkD[OF Some] by auto
      moreover have "reach env {(G, T)} \<subseteq> insert (G, T) (reach env (vps u))"
      proof
        fix y assume "y \<in> reach env {(G, T)}"
        then have "(y, (G, T)) \<in> (dep env)\<^sup>*" by (simp add: reach_def)
        then show "y \<in> insert (G, T) (reach env (vps u))"
        proof (cases rule: rtranclE)
          case (step w)
          then have "w \<in> vps u" using Some by (auto simp: dep_def)
          with step(1) show ?thesis by (auto simp: reach_def)
        qed simp
      qed
      ultimately show ?thesis using Var by auto
    qed
  next
    case (App t1 t2)
    with 1 obtain b1 where o1: "oc F t1 env = Some (Ok b1)"
      and rest: "(if b1 then return True else oc F t2 env) = Some (Ok False)"
      by (auto simp: bindM_def split: option.splits res.splits)
    then have "b1 = False" "oc F t2 env = Some (Ok False)" by (auto simp: return_def split: if_splits)
    with IH o1 App show ?thesis by (auto simp: reach_Un)
  next
    case (Abs a T b)
    with 1 IH show ?thesis by simp
  qed (use 1 in \<open>auto simp: reach_def\<close>)
qed



subsection \<open>Pruning steps\<close>

definition fr :: "env \<Rightarrow> (indexname \<times> ptyp) set" where
  "fr env = {y. maxidx env < snd (fst y)}"

text \<open>
  \<open>prunes ar env env' S\<close>: \<open>env'\<close> extends \<open>env\<close> by bindings that prune the arguments of variables
  in \<open>S\<close> or of new variables. This preserves the invariants, does not add unbound variables, and
  does not change the size measure.
\<close>

definition prunes :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "prunes ar env env' S \<longleftrightarrow> extends env' env \<and> maxidx env \<le> maxidx env' \<and> tinv ar env' \<and> fresh_env env' \<and>
    (\<forall>X. reach env' X \<subseteq> reach env X \<union> fr env) \<and>
    (\<forall>X. finite X \<longrightarrow> (\<forall>y\<in>X. snd (fst y) \<le> maxidx env) \<longrightarrow> card (unb env' X) \<le> card (unb env X)) \<and>
    (\<forall>t. ppat t \<longrightarrow> psz env' t = psz env t) \<and>
    (\<forall>x X. lk env x X = None \<longrightarrow> lk env' x X \<noteq> None \<longrightarrow> (x, X) \<in> S \<union> fr env)"

lemma prunes_refl: "tinv ar env \<Longrightarrow> fresh_env env \<Longrightarrow> prunes ar env env S"
  by (auto simp: prunes_def)

lemma fr_mono: "maxidx env \<le> maxidx env' \<Longrightarrow> fr env' \<subseteq> fr env"
  by (auto simp: fr_def)

lemma prunes_trans:
  assumes p1: "prunes ar env env1 S" and p2: "prunes ar env1 env2 S'" and S': "S' \<subseteq> S \<union> fr env"
  shows "prunes ar env env2 S"
proof -
  have m: "maxidx env \<le> maxidx env1" "maxidx env1 \<le> maxidx env2" using p1 p2 by (simp_all add: prunes_def)
  note f = fr_mono[OF m(1)]
  have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
  proof -
    have "reach env1 X \<subseteq> reach env X \<union> fr env" using p1 by (simp add: prunes_def)
    moreover have "reach env2 X \<subseteq> reach env1 X \<union> fr env1" using p2 by (simp add: prunes_def)
    ultimately show ?thesis using f by blast
  qed
  moreover have "card (unb env2 X) \<le> card (unb env X)"
    if "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have "\<forall>y\<in>X. snd (fst y) \<le> maxidx env1" using that(2) m(1) by force
    with p1 p2 that show ?thesis unfolding prunes_def by (meson order_trans)
  qed
  moreover have "(x, X) \<in> S \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
  proof (cases "lk env1 x X = None")
    case True
    have "\<forall>x X. lk env1 x X = None \<longrightarrow> lk env2 x X \<noteq> None \<longrightarrow> (x, X) \<in> S' \<union> fr env1"
      using p2 unfolding prunes_def by blast
    with True that have "(x, X) \<in> S' \<union> fr env1" by blast
    with S' f show ?thesis by blast
  next
    case False
    have "\<forall>x X. lk env x X = None \<longrightarrow> lk env1 x X \<noteq> None \<longrightarrow> (x, X) \<in> S \<union> fr env"
      using p1 unfolding prunes_def by blast
    with False that show ?thesis by blast
  qed
  ultimately show ?thesis using p1 p2 m unfolding prunes_def by (auto intro: extends_trans)
qed

lemma vps_vars: "y \<in> vps t \<Longrightarrow> fst y \<in> vars t"
  by (induction t) auto

lemma vps_mkabs: "ok (mkabs binders is t) u \<Longrightarrow> vps u = vps t"
  by (induction "is" arbitrary: u) (auto split: prod.splits)

lemma lk_tenv: "tenv env' = tenv env \<Longrightarrow> lk env' = lk env"
  by (simp add: lk_def fun_eq_iff)

lemma dep_tenv: assumes "tenv env' = tenv env" shows "dep env' = dep env"
  unfolding dep_def lk_tenv[OF assms] by (rule refl)

lemma reach_tenv: assumes "tenv env' = tenv env" shows "reach env' = reach env"
  unfolding reach_def dep_tenv[OF assms] by (rule refl)

lemma unb_tenv: assumes "tenv env' = tenv env" shows "unb env' = unb env"
  unfolding unb_def reach_tenv[OF assms] lk_tenv[OF assms] by (rule refl)

lemma reach_old:
  assumes "fresh_env env" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" "y \<in> reach env X"
  shows "snd (fst y) \<le> maxidx env"
proof -
  from assms(3) obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with x(1) assms(2) show ?case by simp
  next
    case (step y z)
    then obtain u where "lk env (fst z) (snd z) = Some u" "y \<in> vps u" by (auto simp: dep_def)
    with fresh_envD[OF assms(1) lkD] vps_vars[of y u] show ?case by (auto simp: below_def)
  qed
qed

lemma lk_fresh: "fresh_env env \<Longrightarrow> maxidx env < snd x \<Longrightarrow> lk env x T = None"
  using fresh_envD[of env x] by (cases "vt_lookup (tenv env) x") (auto simp: lk_def)

lemma ok_type_of_G':
  assumes "ok (type_of_G env T n ks) Hty" "vt_is_empty (tyenv env)"
  obtains Us U Vs where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    "Hty = foldr fun_type Vs U" "length Vs = length ks" "\<forall>k\<in>set ks. 0 \<le> k"
proof -
  from assms obtain Ts U Vs where st: "ok (split_type T n []) (Ts, U)"
    and Vs: "list_all2 (\<lambda>i U. ok (nth Ts i) U) ks Vs" and H: "Hty = foldr fun_type Vs U"
    by (auto simp: type_of_G_def norm_type_def ok_mapM)
  from ok_split_type[OF st] obtain Us where "T = foldr fun_type Us U" "length Us = nat_of_integer n"
    by auto
  moreover have "length Vs = length ks" using Vs by (simp add: list_all2_lengthD)
  moreover have "\<forall>k\<in>set ks. 0 \<le> k" using Vs
    by (induction ks Vs rule: list_all2_induct) (auto simp: ok_nth)
  ultimately show ?thesis using H that by blast
qed

lemma prune_step:
  assumes ti: "tinv ar env" and fr: "fresh_env env"
    and gv: "genvar a env Hty = (env1, H)" and upd: "ok (update (G, Gty) u env1) env2"
    and u: "ok (mkabs binders js (app H ks)) u" and ks: "\<forall>k\<in>set ks. 0 \<le> k"
    and T: "Gty = foldr fun_type Us U" "length Us = length js"
      "Hty = foldr fun_type Vs U" "length Vs = length ks"
    and G: "snd G \<le> maxidx env"
    and wf2: "wf_env ar env2" and epp2: "env_ppat env2"
  shows "prunes ar env env2 {(G, Gty)}"
proof -
  note t0 = tinvD[OF ti]
  define m where "m = maxidx env"
  define Hn where "Hn = (a, m + 1)"
  note g = genvar_simps[OF gv, folded m_def]
  note up = ok_update[OF upd]
  have H: "H = Var Hn Hty" using g(4) by (simp add: Hn_def)
  have lk1: "lk env1 = lk env" by (rule lk_tenv[OF g(1)])
  have G0: "vt_lookup (tenv env) G = None" using up(1) g(1) by simp
  have t2: "tenv env2 = vt_update (G, (Gty, u)) (tenv env)" using up(2) g(1) by simp
  have vu: "vps u = {(Hn, Hty)}" using vps_mkabs[OF u] H by simp
  have m1: "m < snd Hn" by (simp add: Hn_def)
  have lH: "lk env Hn Hty = None" using lk_fresh[OF fr] m1 by (simp add: m_def)
  have rH: "reach env (vps u) = {(Hn, Hty)}" using vu reach_unbound[OF lH] by simp
  have GH: "(G, Gty) \<notin> reach env (vps u)" using rH G m1 by (auto simp: m_def)
  have d2: "dep env2 = dep env \<union> (\<lambda>y. (y, (G, Gty))) ` vps u" by (rule dep_update[OF t2 G0])
  have fin2: "fin_env env2" by (rule fin_env_update[OF t2 t0(1)])
  have ac2: "acyc env2" using acyclic_update[OF d2 GH] t0(2) by (simp add: acyc_def)
  have ti2: "tinv ar env2" using fin2 ac2 wf2 epp2 by (simp add: tinv_def)
  have mx2: "maxidx env2 = m + 1" using up(4) g(3) by simp
  have fr2: "fresh_env env2"
    unfolding fresh_env_def
  proof (intro allI impI)
    fix x U' u' assume "vt_lookup (tenv env2) x = Some (U', u')"
    then consider "x = G" "u' = u" | "vt_lookup (tenv env) x = Some (U', u')"
      using t2 by (auto split: if_splits)
    then show "snd x \<le> maxidx env2 \<and> below (maxidx env2) u'"
    proof cases
      case 1
      have "vars u = {Hn}" using vars_mkabs[OF u] H by (simp add: vars_app)
      with 1 G show ?thesis by (simp add: mx2 below_def m_def Hn_def)
    next
      case 2
      from fresh_envD[OF fr 2] show ?thesis by (auto simp: mx2 m_def intro: below_mono)
    qed
  qed
  have ext: "extends env2 env"
    using ok_update_extends[OF upd] genvar_extends[OF gv] by (rule extends_trans)
  have lk2: "lk env2 x X = (if x = G then (if X = Gty then Some u else None) else lk env x X)" for x X
    by (simp add: lk_update[OF t2])
  have r2: "reach env2 X = reach env X \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})" for X
    using reach_update[OF d2 GH] rH by simp
  have u2: "unb env2 X = (unb env X - {(G, Gty)}) \<union> (if (G, Gty) \<in> reach env X then {(Hn, Hty)} else {})"
    for X
  proof -
    have "unb env (vps u) = {(Hn, Hty)}" using rH lH by (auto simp: unb_def)
    then show ?thesis using unb_update[OF t2 G0 GH] by simp
  qed
  have "card (unb env2 X) \<le> card (unb env X)"
    if X: "finite X" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" for X
  proof -
    have fu: "finite (unb env X)" by (rule finite_unb[OF t0(1) X(1)])
    have "(Hn, Hty) \<notin> unb env X"
    proof
      assume "(Hn, Hty) \<in> unb env X"
      then have "(Hn, Hty) \<in> reach env X" by (simp add: unb_def)
      from reach_old[OF fr X(2) this] m1 show False by (simp add: m_def)
    qed
    moreover have "(G, Gty) \<in> unb env X" if "(G, Gty) \<in> reach env X"
      using that G0 by (simp add: unb_def lk_def)
    ultimately show ?thesis using fu
    proof (cases "(G, Gty) \<in> reach env X")
      case True
      with \<open>(G, Gty) \<in> reach env X \<Longrightarrow> (G, Gty) \<in> unb env X\<close> have G1: "(G, Gty) \<in> unb env X" by simp
      have "card (unb env2 X) = card (insert (Hn, Hty) (unb env X - {(G, Gty)}))" using True by (simp add: u2)
      also have "\<dots> = Suc (card (unb env X - {(G, Gty)}))"
        using fu \<open>(Hn, Hty) \<notin> unb env X\<close> by simp
      also have "\<dots> = card (unb env X)" by (rule card_Suc_Diff1[OF fu G1])
      finally show ?thesis by simp
    next
      case False
      then show ?thesis using fu by (simp add: u2 card_Diff1_le)
    qed
  qed
  moreover have "psz env2 t = psz env t" if "ppat t" for t
  proof (rule psz_ext[OF ti ti2 ext _ G0 _ that])
    show "lk env x X = Some u'" if "lk env2 x X = Some u'" "(x, X) \<noteq> (G, Gty)" for x X u'
      using that lk2[of x X] by (auto split: if_splits)
  next
    fix iss :: "integer list" assume "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
    moreover have "lk env2 Hn Hty = None" using lk2[of Hn Hty] lH G m1 by (auto simp: m_def)
    ultimately show "psz env2 (app (Var G Gty) iss) = Some (fsz (app (Var G Gty) iss))"
      using psz_prune[of env2 G Gty u binders js Hn Hty ks Us U Vs iss] lk2 u H ks T by simp
  qed
  moreover have "reach env2 X \<subseteq> reach env X \<union> fr env" for X
    using r2 m1 by (auto simp: fr_def m_def)
  moreover have "(x, X) \<in> {(G, Gty)} \<union> fr env" if "lk env x X = None" "lk env2 x X \<noteq> None" for x X
    using that lk2[of x X] by (auto split: if_splits)
  ultimately show ?thesis using ext ti2 fr2 mx2 by (simp add: prunes_def m_def)
qed


subsection \<open>Terminating computations\<close>

lemma hn_head_norm:
  assumes "hn env t = Some t'"
  shows "vt_is_empty (tyenv env) \<Longrightarrow> head_norm env t = Some (Ok t') \<or> (\<exists>e. head_norm env t = Some (Err e))"
  using assms
proof (induction env t t' rule: hn.raw_induct[rotated, consumes 1])
  case (1 h env t t')
  have e: "vt_is_empty (tyenv env)" using 1 by simp
  note IH = "1.IH"[OF _ e]
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      with 1 Var have "t' = t" by (simp add: lk_def)
      with None Var show ?thesis by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e return_def bindM_def)
    next
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "U = T")
        case True
        with Some p 1 Var have hu: "h env u = Some t'" by (simp add: lk_def)
        from IH[OF hu] Some p True Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def bindM_def return_def)
      next
        case False
        with Some p Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def var_clash_def raise_def bindM_def)
      qed
    qed
  next
    case (Abs a T b)
    with 1 obtain b' where hb: "h env b = Some b'" and t': "t' = Abs a T b'"
      by (auto split: Option.bind_splits)
    from IH[OF hb] t' Abs show ?thesis
      by (auto simp: head_norm.simps[of env "Abs a T b"] bindM_def raise_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T b where f: "f = Abs a T b" by (cases f) auto
      with 1 App have "h env (subst_bound u b) = Some t'" by simp
      from IH[OF this] App f show ?thesis by (simp add: head_norm.simps[of env "Abs a T b $ u"])
    next
      case False
      with 1 App obtain nf where nf: "h env f = Some nf"
        and rest: "(case nf of pterm.Abs _ _ body \<Rightarrow> h env (subst_bound u body) | _ \<Rightarrow> Some (nf $ u)) = Some t'"
        by (cases f) (auto split: Option.bind_splits)
      have hn_eq: "head_norm env (f $ u) = bindM (head_norm env f) (\<lambda>nf. case nf of
          pterm.Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body) | _ \<Rightarrow> return (nf $ u))"
        using False by (subst head_norm.simps) (cases f; simp)
      from IH[OF nf] show ?thesis
      proof
        assume hf: "head_norm env f = Some (Ok nf)"
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain a T b where nfa: "nf = Abs a T b" by (cases nf) auto
          with rest have "h env (subst_bound u b) = Some t'" by simp
          from IH[OF this] hf nfa App hn_eq show ?thesis by (simp add: bindM_def)
        next
          case nA: False
          with rest have "t' = nf $ u" by (cases nf) auto
          with hf nA App hn_eq show ?thesis by (cases nf) (simp_all add: return_def bindM_def)
        qed
      next
        assume "\<exists>e. head_norm env f = Some (Err e)"
        with App hn_eq show ?thesis by (auto simp: bindM_def)
      qed
    qed
  next
    case (Const c T)
    with 1 have "t' = t" by simp
    with Const show ?thesis by (simp add: head_norm.simps[of env "Const c T"] return_def)
  next
    case (Free c T)
    with 1 have "t' = t" by simp
    with Free show ?thesis by (simp add: head_norm.simps[of env "Free c T"] return_def)
  next
    case (Bound i)
    with 1 have "t' = t" by simp
    with Bound show ?thesis by (simp add: head_norm.simps[of env "Bound i"] return_def)
  qed
qed

lemma head_norm_term:
  "tinv ar env \<Longrightarrow> ppat t \<Longrightarrow> \<exists>r. head_norm env t = Some r"
  using hn_term[OF tinvD(1-4)] hn_head_norm[OF _ wf_envD(1)[OF tinvD(3)]] by blast

lemma mapM_term: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. mapM f xs = Some r"
  by (induction xs) (auto simp: bindM_def return_def split: option.splits res.splits)

lemma bindM_term:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>x. m = Some (Ok x) \<Longrightarrow> \<exists>r. f x = Some r) \<Longrightarrow> \<exists>r. bindM m f = Some r"
  by (auto simp: bindM_def split: res.splits)

lemma handle_term:
  "\<exists>r. m = Some r \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> \<exists>r. h e = Some r) \<Longrightarrow> \<exists>r. handle m h = Some r"
  by (auto simp: handle_def split: res.splits)

lemma return_term[simp]: "\<exists>r. return x = Some r" and raise_term[simp]: "\<exists>r. raise e = Some r"
  by (simp_all add: return_def raise_def)

lemma nth_term: "\<exists>r. nth xs i = Some r"
  by (induction xs i rule: nth.induct) auto

lemma mkabs_term: "\<exists>r. mkabs binders is t = Some r"
  by (induction "is") (auto intro!: bindM_term nth_term split: prod.splits)

lemma update_term: "\<exists>r. update xT t env = Some r"
  by (auto simp: update_def update_new_def split: env.splits intro!: bindM_term)

lemma ints_of_term: "\<exists>r. ints_of ts = Some r"
  by (induction ts rule: ints_of.induct) (auto intro!: bindM_term)

lemma idx_term: "\<exists>r. idx is j = Some r"
  by (induction "is") auto

lemma split_type_term: "\<exists>r. split_type T n Ts = Some r"
  by (induction T n Ts rule: split_type.induct) (subst split_type.simps; auto split: ptyp.splits list.splits)

lemma type_of_G_term: "vt_is_empty (tyenv env) \<Longrightarrow> \<exists>r. type_of_G env T n ks = Some r"
  by (auto simp: type_of_G_def norm_type_def intro!: bindM_term split_type_term mapM_term nth_term
      split: prod.splits)

lemma ints_of'_term:
  "tinv ar env \<Longrightarrow> \<forall>t\<in>set ts. ppat t \<Longrightarrow> \<exists>r. ints_of' env ts = Some r"
  unfolding ints_of'_def by (auto intro!: bindM_term mapM_term head_norm_term ints_of_term)

lemma try_trans_term: "\<exists>r. try_trans xs d i = Some r"
  by (auto simp: try_trans_def intro!: handle_term bindM_term idx_term)

lemma trans_term: "\<exists>r. trans xs d i = Some r"
  by (auto simp: trans_def intro!: bindM_term idx_term)

lemma mapAccM_inv:
  assumes f: "\<And>x e. x \<in> set xs \<Longrightarrow> R e \<Longrightarrow>
      \<exists>r. f x e = Some r \<and> (\<forall>y e'. r = Ok (y, e') \<longrightarrow> R e' \<and> S e e' \<and> Q x y e')"
    and trans: "\<And>e1 e2 e3. S e1 e2 \<Longrightarrow> S e2 e3 \<Longrightarrow> S e1 e3" and refl: "\<And>e. S e e"
    and mono: "\<And>x y e1 e2. Q x y e1 \<Longrightarrow> S e1 e2 \<Longrightarrow> Q x y e2"
    and R: "R e"
  shows "\<exists>r. mapAccM f xs e = Some r \<and>
    (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow> R e' \<and> S e e' \<and> list_all2 (\<lambda>x y. Q x y e') xs ys)"
  using f R
proof (induction xs arbitrary: e)
  case Nil
  then show ?case by (auto simp: return_def refl)
next
  case (Cons x xs)
  from Cons.prems(1)[of x e] Cons.prems(2) obtain r where r: "f x e = Some r"
    and rp: "\<forall>y e'. r = Ok (y, e') \<longrightarrow> R e' \<and> S e e' \<and> Q x y e'" by auto
  show ?case
  proof (cases r)
    case (Ok p)
    obtain y e1 where p: "p = (y, e1)" by force
    with rp Ok have e1: "R e1" "S e e1" "Q x y e1" by auto
    from Cons.IH[OF _ e1(1)] Cons.prems(1) obtain r2 where r2: "mapAccM f xs e1 = Some r2"
      and rp2: "\<forall>ys e'. r2 = Ok (ys, e') \<longrightarrow> R e' \<and> S e1 e' \<and> list_all2 (\<lambda>x y. Q x y e') xs ys"
      by auto
    show ?thesis
    proof (cases r2)
      case (Ok q)
      obtain ys e' where q: "q = (ys, e')" by force
      with rp2 Ok have "R e'" "S e1 e'" "list_all2 (\<lambda>x y. Q x y e') xs ys" by auto
      with e1 have "R e' \<and> S e e' \<and> list_all2 (\<lambda>x y. Q x y e') (x # xs) (y # ys)"
        by (auto intro: trans mono)
      with r r2 \<open>r = Ok p\<close> p Ok q show ?thesis by (simp add: return_def bindM_def)
    next
      case (Err e')
      with r r2 \<open>r = Ok p\<close> p show ?thesis by (simp add: bindM_def)
    qed
  next
    case (Err e')
    with r show ?thesis by (simp add: bindM_def raise_def)
  qed
qed


subsection \<open>Termination of projection\<close>

lemma prunes_mono: "prunes ar env env' S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> prunes ar env env' S'"
  unfolding prunes_def by blast

lemma prunesD:
  assumes "prunes ar env env' S"
  shows "extends env' env" "maxidx env \<le> maxidx env'" "tinv ar env'" "fresh_env env'"
    "reach env' X \<subseteq> reach env X \<union> fr env"
    "finite X \<Longrightarrow> \<forall>y\<in>X. snd (fst y) \<le> maxidx env \<Longrightarrow> card (unb env' X) \<le> card (unb env X)"
    "ppat t \<Longrightarrow> psz env' t = psz env t"
  using assms unfolding prunes_def by blast+

lemma psz_rigid_pos:
  assumes "is_rigid h"
  shows "psz env (list_comb h ts) = Some n \<Longrightarrow> 0 < n"
  by (induction ts arbitrary: n rule: rev_induct)
    (auto simp: psz_rigid_atom[OF assms] psz_rigid_snoc[OF assms] split: Option.bind_splits)

lemma psz_rigid_arg:
  assumes "is_rigid h" "psz env (list_comb h ts) = Some n" "t \<in> set ts"
  shows "\<exists>m. psz env t = Some m \<and> m < n"
  using assms(2,3)
proof (induction ts arbitrary: n rule: rev_induct)
  case (snoc t' ts)
  from snoc.prems(1) obtain n1 n2 where n1: "psz env (list_comb h ts) = Some n1"
    and n2: "psz env t' = Some n2" and n: "n = n1 + n2"
    by (auto simp: psz_rigid_snoc[OF assms(1)] split: Option.bind_splits)
  have "0 < n1" by (rule psz_rigid_pos[OF assms(1) n1])
  with snoc n1 n2 n show ?case by (cases "t = t'") fastforce+
qed simp

lemma list_all2_set2': "list_all2 P xs ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. P x y"
  by (induction rule: list_all2_induct) auto

lemma vps_rigid: "is_rigid h \<Longrightarrow> vps h = {}"
  by (auto simp: is_rigid_def)

lemma pr_term:
  "psz env s = Some n \<Longrightarrow> tinv ar env \<Longrightarrow> fresh_env env \<Longrightarrow> ppat s \<Longrightarrow> typs_ok ar s \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> binders_ok ar binders \<Longrightarrow> 0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow>
    \<exists>r. pr xs s env d binders = Some r \<and>
      (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> prunes ar env env' (reach env (vps s)) \<and>
        vps s' \<subseteq> reach env' (vps s) \<and> below (maxidx env') s')"
proof (induction n arbitrary: s env d binders rule: less_induct)
  case (less n s env d binders)
  have pz: "psz env s = Some n" and ti: "tinv ar env" and fr: "fresh_env env" and ps: "ppat s"
    and ts: "typs_ok ar s" and bs: "below (maxidx env) s" and bok: "binders_ok ar binders"
    and d0: "0 \<le> d" and xs0: "\<forall>x\<in>set xs. 0 \<le> x"
    using less.prems by simp_all
  note t0 = tinvD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(3)])
  from hn_term[OF t0 ps] obtain s0 where hs: "hn env s = Some s0" by blast
  define R where "R = (\<lambda>s0. if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> pr xs t env (d + 1) ((a, T) # binders);
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
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. pr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))"
  define P where "P r \<longleftrightarrow> (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> prunes ar env env' (reach env (vps s)) \<and>
    vps s' \<subseteq> reach env' (vps s) \<and> below (maxidx env') s')" for r
  have pr_hn: "pr xs s env d binders = head_norm env s \<bind> R"
    unfolding R_def by (subst pr.simps) (rule refl)
  from hn_head_norm[OF hs e] consider (err) e' where "head_norm env s = Some (Err e')"
    | (ok) "head_norm env s = Some (Ok s0)" by blast
  then have "\<exists>r. pr xs s env d binders = Some r \<and> P r"
  proof cases
    case err
    then show ?thesis by (simp add: pr_hn bindM_def P_def)
  next
    case ok
    have hh: "head_norm env s = return s0" using ok by (simp add: return_def)
    have pr_eq: "pr xs s env d binders = R s0" by (simp add: pr_hn hh)
    have ps0: "ppat s0" and vs0: "vps s0 \<subseteq> reach env (vps s)" using hn_ppat_aux[OF hs t0(3,4) ps] by simp_all
    have pz0: "psz env s0 = Some n" using psz_hn[OF hs ps t0(3,4)] pz by simp
    from head_norm_sound[OF ok refl t0(3) ppat_proper[OF ps] ts] have ts0: "typs_ok ar s0" by simp
    have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF ok refl t0(3) fr bs])
    have vmono: "reach env' (vps s0) \<subseteq> reach env' (vps s)" if "extends env' env" for env'
      using vs0 reach_extends[OF that] by (intro reach_mono) blast
    have rmono: "reach env (vps x) \<subseteq> reach env (vps s)" if "vps x \<subseteq> vps s0" for x
      using that vs0 by (intro reach_mono) blast
    show ?thesis
    proof (cases "is_Abs s0")
      case True
      then obtain a T t where s0: "s0 = Abs a T t" by (cases s0) auto
      from pz0 s0 obtain m where m: "psz env t = Some m" "n = m + 2"
        by (auto simp: psz_Abs split: Option.bind_splits)
      have pt: "ppat t" using ps0 s0 by (auto dest: ppat_AbsD)
      have tt: "typs_ok ar t" "ground ar T" using ts0 s0 by simp_all
      have bt: "below (maxidx env) t" using bs0 s0 by simp
      have bok': "binders_ok ar ((a, T) # binders)" using bok tt(2) by (simp add: binders_ok_def)
      have "m < n" using m by simp
      moreover have "0 \<le> d + 1" using d0 by simp
      ultimately obtain r where r: "pr xs t env (d + 1) ((a, T) # binders) = Some r"
        and rP: "\<forall>s' env'. r = Ok (s', env') \<longrightarrow> prunes ar env env' (reach env (vps t)) \<and>
          vps s' \<subseteq> reach env' (vps t) \<and> below (maxidx env') s'"
        using less.IH[OF _ m(1) ti fr pt tt(1) bt bok' _ xs0] by blast
      show ?thesis
      proof (cases r)
        case (Ok p)
        obtain t' env' where p: "p = (t', env')" by force
        with rP Ok have pr1: "prunes ar env env' (reach env (vps t))" and v1: "vps t' \<subseteq> reach env' (vps t)"
          and b1: "below (maxidx env') t'" by auto
        have "prunes ar env env' (reach env (vps s))" using pr1 rmono[of t] s0 by (auto intro: prunes_mono)
        moreover have "vps (Abs a T t') \<subseteq> reach env' (vps s)"
          using v1 vmono[OF prunesD(1)[OF pr1]] s0 by auto
        ultimately have "P (Ok (Abs a T t', env'))" using b1 by (simp add: P_def)
        with pr_eq r Ok p s0 show ?thesis by (simp add: R_def return_def bindM_def)
      next
        case (Err e')
        with pr_eq r s0 show ?thesis by (simp add: R_def bindM_def P_def)
      qed
    next
      case nA: False
      obtain h ts where sc: "strip_comb s0 = (h, ts)" by force
      have s0e: "s0 = list_comb h ts" by (rule strip_comb_list_comb[OF sc])
      have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF sc])
      from ppat_spine[OF ps0[unfolded s0e] nApp nA[unfolded s0e]]
      consider (rigid) "is_rigid h" "\<forall>t\<in>set ts. ppat t" | (flex) F Fty where "h = Var F Fty" by blast
      then show ?thesis
      proof cases
        case flex
        have "\<exists>iss. ts = map Bound iss \<and> (\<forall>i\<in>set iss. 0 \<le> i)"
          using ps0 nA
        proof (cases rule: ppat_nonAbsE)
          case (rigid h' ts')
          have "list_comb h' ts' = list_comb (Var F Fty) ts" using rigid(2) s0e \<open>h = Var F Fty\<close> by simp
          then have "h' = Var F Fty"
            using list_comb_eq_iff[OF is_rigid_not_App[OF rigid(1)], of "Var F Fty" ts' ts] by simp
          with rigid(1) show ?thesis by (simp add: is_rigid_def)
        next
          case (flex x T jss)
          have "list_comb (Var x T) (map Bound jss) = list_comb (Var F Fty) ts"
            using flex(1) s0e \<open>h = Var F Fty\<close> by (simp add: app_list_comb)
          then have "ts = map Bound jss" using list_comb_eq_iff[of "Var x T" "Var F Fty" "map Bound jss" ts] by simp
          with flex(3) show ?thesis by blast
        qed
        then obtain iss where ts_eq: "ts = map Bound iss" and iss: "\<forall>i\<in>set iss. 0 \<le> i" by blast
        have pts: "\<forall>t\<in>set ts. ppat t" using ts_eq iss by (auto intro: ppat_Bound)
        have trm: "\<exists>r. R s0 = Some r"
          using nA sc flex unfolding R_def
          by (auto simp: Let_def mk_hnf_def split: prod.splits
              intro!: bindM_term ints_of'_term[OF ti pts] mapM_term try_trans_term type_of_G_term[OF e]
              mkabs_term update_term)
        then obtain r where r: "R s0 = Some r" by blast
        have "P r"
          unfolding P_def
        proof (intro allI impI)
          fix s' env'' assume rOk: "r = Ok (s', env'')"
          with r nA sc flex obtain js js' Hty where js: "ok (ints_of' env ts) js"
            and js': "ok (mapM (try_trans xs d) js) js'"
            and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
            and rest2: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow>
              mk_hnf binders js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
                (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (s', env'')"
            unfolding R_def by (auto simp: Let_def)
          obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
          with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
            and env'': "ok (update (F, Fty) t env1) env''" and s': "s' = app H (List.map_filter id js')"
            by (auto simp: mk_hnf_def)
          have prs: "pr xs s env d binders = Some (Ok (s', env''))" using pr_eq r rOk by simp
          have wf'': "wf_env ar env''"
            using pr_sound[OF prs refl t0(3) bok ppat_proper[OF ps] ts d0 xs0] by simp
          have epp'': "env_ppat env''"
            using pr_ppat[OF prs refl t0(3) bok t0(4) ps ts d0 xs0] by simp
          from ok_type_of_G'[OF Hty e] obtain Us U Vs where
            T: "Fty = foldr fun_type Us U" "length Us = length js"
              "Hty = foldr fun_type Vs U" "length Vs = length (mk_proj_list js')"
              and ks: "\<forall>k\<in>set (mk_proj_list js'). 0 \<le> k"
            by auto
          have Fm: "snd F \<le> maxidx env" using bs0 s0e flex by (simp add: below_list_comb)
          have p1: "prunes ar env env'' {(F, Fty)}"
            by (rule prune_step[OF ti fr G env'' t ks T Fm wf'' epp''])
          have Fr: "(F, Fty) \<in> reach env (vps s)" using vs0 s0e flex by (auto simp: vps_list_comb)
          have "prunes ar env env'' (reach env (vps s))" using p1 Fr by (auto intro: prunes_mono)
          moreover have "vps s' \<subseteq> reach env'' (vps s)"
          proof
            fix y assume "y \<in> vps s'"
            then have y: "y = ((fst F, maxidx env + 1), Hty)" using s' genvar_simps(4)[OF G] by simp
            have "lk env'' F Fty = Some t" using ok_update_lookup[OF env''] by (simp add: lk_def)
            moreover have "y \<in> vps t" using vps_mkabs[OF t] genvar_simps(4)[OF G] y by simp
            ultimately have "(y, (F, Fty)) \<in> dep env''" by (auto simp: dep_iff)
            moreover have "(F, Fty) \<in> reach env'' (vps s)"
              using Fr reach_extends[OF prunesD(1)[OF p1]] by blast
            ultimately show "y \<in> reach env'' (vps s)" by (rule reach_pred)
          qed
          moreover have "below (maxidx env'') s'"
            using s' genvar_simps(3,4)[OF G] ok_update(4)[OF env''] by (simp add: below_app)
          ultimately show "prunes ar env env'' (reach env (vps s)) \<and> vps s' \<subseteq> reach env'' (vps s) \<and>
            below (maxidx env'') s'" by simp
        qed
        with r pr_eq show ?thesis by simp
      next
        case rigid
        have nV: "\<not> is_Var h" "\<not> is_Abs h" using rigid(1) by (auto simp: is_rigid_def)
        define hc where "hc = (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h)"
        have hc: "\<exists>r. hc = Some r \<and> (\<forall>h'. r = Ok h' \<longrightarrow> vps h' = {} \<and> vars h' = {})"
          using rigid(1) trans_term[of xs d]
          by (auto simp: hc_def is_rigid_def return_def bindM_def split: option.splits res.splits)
        define R0 where "R0 e \<longleftrightarrow> prunes ar env e (reach env (vps s))" for e
        define S0 where "S0 e e' \<longleftrightarrow> extends e' e \<and> maxidx e \<le> maxidx e'" for e e'
        define Q0 where "Q0 x y e' \<longleftrightarrow> vps y \<subseteq> reach e' (vps x) \<and> below (maxidx e') y" for x y e'
        have tts: "\<forall>t\<in>set ts. typs_ok ar t" "\<forall>t\<in>set ts. below (maxidx env) t"
          using ts0 bs0 s0e by (simp_all add: typs_ok_list_comb below_list_comb)
        have vts: "vps x \<subseteq> vps s0" if "x \<in> set ts" for x using that s0e by (auto simp: vps_list_comb)
        have mp: "\<exists>r. mapAccM (\<lambda>s env. pr xs s env d binders) ts env = Some r \<and>
            (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow> R0 e' \<and> S0 env e' \<and> list_all2 (\<lambda>x y. Q0 x y e') ts ys)"
        proof (rule mapAccM_inv)
          fix x e assume x: "x \<in> set ts" and Re: "R0 e"
          note pe = Re[unfolded R0_def]
          from psz_rigid_arg[OF rigid(1) pz0[unfolded s0e] x] obtain m where m: "psz env x = Some m" "m < n"
            by blast
          have px: "ppat x" using rigid(2) x by simp
          have me: "psz e x = Some m" using prunesD(7)[OF pe px] m by simp
          have bx: "below (maxidx e) x" using tts(2) x prunesD(2)[OF pe] by (auto intro: below_mono)
          from less.IH[OF m(2) me prunesD(3,4)[OF pe] px _ bx bok d0 xs0] tts(1) x
          obtain r where r: "pr xs x e d binders = Some r"
            and rP: "\<forall>y e'. r = Ok (y, e') \<longrightarrow> prunes ar e e' (reach e (vps x)) \<and>
              vps y \<subseteq> reach e' (vps x) \<and> below (maxidx e') y"
            by blast
          have "R0 e' \<and> S0 e e' \<and> Q0 x y e'" if "r = Ok (y, e')" for y e'
          proof -
            from rP that have p2: "prunes ar e e' (reach e (vps x))" and q: "vps y \<subseteq> reach e' (vps x)"
              "below (maxidx e') y" by auto
            have "reach e (vps x) \<subseteq> reach env (vps s) \<union> fr env"
              using prunesD(5)[OF pe, of "vps x"] rmono[OF vts[OF x]] by blast
            with prunes_trans[OF pe p2] have "R0 e'" by (simp add: R0_def)
            moreover have "S0 e e'" using prunesD(1,2)[OF p2] by (simp add: S0_def)
            ultimately show ?thesis using q by (simp add: Q0_def)
          qed
          with r show "\<exists>r. pr xs x e d binders = Some r \<and>
            (\<forall>y e'. r = Ok (y, e') \<longrightarrow> R0 e' \<and> S0 e e' \<and> Q0 x y e')" by blast
        next
          show "S0 e1 e3" if "S0 e1 e2" "S0 e2 e3" for e1 e2 e3
            using that by (auto simp: S0_def intro: extends_trans)
        next
          show "S0 e e" for e by (simp add: S0_def)
        next
          show "Q0 x y e2" if "Q0 x y e1" "S0 e1 e2" for x y e1 e2
            using that reach_extends[of e2 e1] by (auto simp: Q0_def S0_def intro: below_mono)
        next
          show "R0 env" using prunes_refl[OF ti fr] by (simp add: R0_def)
        qed
        from hc obtain rh where rh: "hc = Some rh" and rhP: "\<forall>h'. rh = Ok h' \<longrightarrow> vps h' = {} \<and> vars h' = {}"
          by blast
        from mp obtain rm where rm: "mapAccM (\<lambda>s env. pr xs s env d binders) ts env = Some rm"
          and rmP: "\<forall>ys e'. rm = Ok (ys, e') \<longrightarrow> R0 e' \<and> S0 env e' \<and> list_all2 (\<lambda>x y. Q0 x y e') ts ys"
          by blast
        have R_eq: "R s0 = hc \<bind> (\<lambda>h'. mapAccM (\<lambda>s env. pr xs s env d binders) ts env \<bind>
            (\<lambda>(ts', env'). return (list_comb h' ts', env')))"
          using nA sc nV unfolding R_def hc_def by simp
        show ?thesis
        proof (cases rh)
          case (Err e')
          with R_eq rh pr_eq show ?thesis by (simp add: bindM_def P_def)
        next
          case (Ok h')
          note hv = rhP[rule_format, OF Ok]
          show ?thesis
          proof (cases rm)
            case (Err e')
            with R_eq rh rm Ok pr_eq show ?thesis by (simp add: bindM_def P_def)
          next
            case (Ok q)
            obtain ts' env' where q: "q = (ts', env')" by force
            with rmP Ok have R0': "R0 env'" and S0': "S0 env env'" and Q: "list_all2 (\<lambda>x y. Q0 x y env') ts ts'"
              by auto
            have "vps (list_comb h' ts') \<subseteq> reach env' (vps s)"
            proof -
              have "vps y \<subseteq> reach env' (vps s)" if "y \<in> set ts'" for y
              proof -
                from list_all2_set2'[OF Q] that obtain x where x: "x \<in> set ts" "Q0 x y env'"
                  by blast
                have e': "extends env' env" using S0' by (simp add: S0_def)
                have "reach env' (vps x) \<subseteq> reach env' (vps s)"
                  using reach_subset[OF vts[OF x(1)], of env'] vmono[OF e'] by (rule order_trans)
                with x(2) show ?thesis by (auto simp: Q0_def)
              qed
              with hv show ?thesis by (auto simp: vps_list_comb)
            qed
            moreover have "below (maxidx env') (list_comb h' ts')"
            proof -
              have "below (maxidx env') y" if "y \<in> set ts'" for y
                using list_all2_set2'[OF Q] that by (auto simp: Q0_def)
              moreover have "below (maxidx env') h'" using hv by (simp add: below_def)
              ultimately show ?thesis by (simp add: below_list_comb)
            qed
            ultimately have "P (Ok (list_comb h' ts', env'))" using R0' by (simp add: P_def R0_def)
            with R_eq rh rm \<open>rh = Ok h'\<close> Ok q pr_eq show ?thesis by (simp add: bindM_def return_def)
          qed
        qed
      qed
    qed
  qed
  then show ?case by (simp add: P_def)
qed


subsection \<open>Binding steps\<close>

lemma bind_step:
  assumes fin: "fin_env env" and ac: "acyc env" and fr: "fresh_env env"
    and upd: "ok (update (F, T) u env) env'" and nc: "(F, T) \<notin> reach env (vps u)"
    and Fm: "snd F \<le> maxidx env" and bu: "below (maxidx env) u"
  shows "fin_env env'" "acyc env'" "fresh_env env'" "extends env' env" "maxidx env' = maxidx env"
    "vt_lookup (tenv env) F = None"
    "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
    "reach env' X = reach env X \<union> (if (F, T) \<in> reach env X then reach env (vps u) else {})"
    "lk env' F T = Some u"
proof -
  note up = ok_update[OF upd]
  have d: "dep env' = dep env \<union> (\<lambda>y. (y, (F, T))) ` vps u" by (rule dep_update[OF up(2,1)])
  show "fin_env env'" by (rule fin_env_update[OF up(2) fin])
  show "acyc env'" using acyclic_update[OF d nc] ac by (simp add: acyc_def)
  show "fresh_env env'"
    unfolding fresh_env_def
  proof (intro allI impI)
    fix x U' u' assume "vt_lookup (tenv env') x = Some (U', u')"
    then consider "x = F" "u' = u" | "vt_lookup (tenv env) x = Some (U', u')"
      using up(2) by (auto split: if_splits)
    then show "snd x \<le> maxidx env' \<and> below (maxidx env') u'"
      using fresh_envD[OF fr] Fm bu up(4) by cases auto
  qed
  show "extends env' env" by (rule ok_update_extends[OF upd])
  show "maxidx env' = maxidx env" by (rule up(4))
  show "vt_lookup (tenv env) F = None" by (rule up(1))
  show "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
    by (rule unb_update[OF up(2,1) nc])
  show "reach env' X = reach env X \<union> (if (F, T) \<in> reach env X then reach env (vps u) else {})"
    by (rule reach_update[OF d nc])
  show "lk env' F T = Some u" using ok_update_lookup[OF upd] by (simp add: lk_def)
qed

lemma int_succ_not_le: "\<not> (m + 1 \<le> (m :: integer))"
  by (simp add: less_eq_integer.rep_eq)

lemma int_le_succ: "x \<le> m \<Longrightarrow> x \<le> (m :: integer) + 1"
  by (simp add: less_eq_integer.rep_eq)

lemma fresh_env_genvar:
  assumes "genvar a env T = (env', H)" "fresh_env env"
  shows "fresh_env env'"
  unfolding fresh_env_def
proof (intro allI impI)
  note g = genvar_simps[OF assms(1)]
  fix x U u assume "vt_lookup (tenv env') x = Some (U, u)"
  with fresh_envD[OF assms(2)] g(1) have "snd x \<le> maxidx env" "below (maxidx env) u" by auto
  then show "snd x \<le> maxidx env' \<and> below (maxidx env') u"
    using g(3) int_le_succ by (auto intro: below_mono)
qed

lemma hn_flex_unbound:
  assumes "hn env t = Some (app (Var G T) js)" "fin_env env" "acyc env"
  shows "lk env G T = None"
proof (rule ccontr)
  assume "lk env G T \<noteq> None"
  then obtain u where u: "lk env G T = Some u" by blast
  from hn_idem[OF assms(1)] have "hn env (app (Var G T) js) = Some (app (Var G T) js)" .
  from hn_app_bound_vps[OF u this] have "(G, T) \<in> reach env (vps u)" by simp
  from reach_lk_trancl[OF u this] have "((G, T), (G, T)) \<in> (dep env)\<^sup>+" .
  with assms(3) show False unfolding acyc_def acyclic_def by blast
qed

text \<open>A measure-decreasing step: the variables in \<open>D\<close> become bound, at most \<open>k\<close> new ones appear.\<close>

lemma card_unb_less:
  assumes "finite A" "unb' \<subseteq> (A - D) \<union> N" "D \<subseteq> A" "card N < card D" "finite N"
  shows "card unb' < card A"
proof -
  have "card unb' \<le> card ((A - D) \<union> N)" using assms by (intro card_mono) auto
  also have "\<dots> \<le> card (A - D) + card N" by (rule card_Un_le)
  also have "card (A - D) = card A - card D" using assms(1,3) by (simp add: card_Diff_subset finite_subset)
  also have "card D \<le> card A" using assms(1,3) by (rule card_mono)
  then have "card A - card D + card N < card A" using assms(4) by linarith
  finally show ?thesis .
qed


subsection \<open>Termination of the flexible cases\<close>

lemma proj_term:
  assumes ti: "tinv ar env" and fr: "fresh_env env" and pt: "ppat t" "typs_ok ar t"
    and bt: "below (maxidx env) t" and bok: "binders_ok ar binders" and is0: "\<forall>i\<in>set is. 0 \<le> i"
  shows "\<exists>r. proj t env binders is = Some r \<and>
    (\<forall>u env'. r = Ok (u, env') \<longrightarrow> prunes ar env env' (reach env (vps t)) \<and>
      vps u \<subseteq> reach env' (vps t) \<and> below (maxidx env') u)"
proof (cases "downto0 is (ilength binders - 1)")
  case True
  then show ?thesis using prunes_refl[OF ti fr] reach_incl[of "vps t" env] bt
    by (simp add: proj_def return_def)
next
  case False
  from psz_term[OF tinvD[OF ti] pt(1)] obtain n where "psz env t = Some n" by blast
  from pr_term[OF this ti fr pt bt bok _ is0] False show ?thesis by (simp add: proj_def)
qed

lemma psz_some: "tinv ar env \<Longrightarrow> ppat t \<Longrightarrow> psz env t = Some (the (psz env t))"
  using psz_term[OF tinvD] by fastforce

lemma psz_rigid_sum:
  assumes "is_rigid h" "\<forall>t\<in>set ts. \<exists>n. psz env t = Some n"
  shows "psz env (list_comb h ts) = Some (1 + sum_list (map (\<lambda>t. the (psz env t)) ts))"
  using assms(2)
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case using psz_rigid_atom[OF assms(1)] by simp
next
  case (snoc t ts)
  then show ?case by (auto simp: psz_rigid_snoc[OF assms(1)])
qed

lemma ppat_strip_flex:
  assumes "strip_comb t = (Var x T, ss)" "ppat t"
  obtains iss where "ss = map Bound iss" "distinct iss" "\<forall>i\<in>set iss. 0 \<le> i"
proof -
  have t: "t = list_comb (Var x T) ss" by (rule strip_comb_list_comb[OF assms(1)])
  have nv: "\<not> (\<exists>f u. Var x T = f $ u)" by simp
  from assms(2) show ?thesis
  proof (cases rule: ppat.cases)
    case (ppat_Abs u a U)
    with t show ?thesis by (simp add: list_comb_Abs_iff)
  next
    case (ppat_rigid h ts)
    from ppat_rigid t have "list_comb (Var x T) ss = list_comb h ts" by simp
    with list_comb_eq_iff[OF nv is_rigid_not_App[OF ppat_rigid(2)]] have "h = Var x T" by simp
    with ppat_rigid(2) show ?thesis by (simp add: is_rigid_def)
  next
    case (ppat_flex iss y U)
    from ppat_flex t have "list_comb (Var x T) ss = list_comb (Var y U) (map Bound iss)"
      by (simp add: app_list_comb)
    with list_comb_eq_iff[OF nv, of "Var y U"] have "ss = map Bound iss" by simp
    then show ?thesis by (rule that[OF _ ppat_flex(2,3)])
  qed
qed

lemma existsM_term: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>r. P x = Some r) \<Longrightarrow> \<exists>r. existsM P xs = Some r"
  by (induction xs) (auto intro!: bindM_term)

subsection \<open>Termination of the rigid occurs check\<close>

lemma rigid_occurs_term:
  assumes ti: "tinv ar env"
  shows "ppat t \<Longrightarrow> \<exists>r. rigid_occurs F t env = Some r"
proof (induction "the (psz env t)" arbitrary: t rule: less_induct)
  case less
  note t0 = tinvD[OF ti]
  from hn_term[OF t0 less.prems] obtain t' where hn: "hn env t = Some t'" by blast
  have pt': "ppat t'" using hn_ppat_aux[OF hn t0(3,4) less.prems] by simp
  have pz: "psz env t' = psz env t" by (rule psz_hn[OF hn less.prems t0(3,4)])
  have IH: "\<exists>r. rigid_occurs F u env = Some r" if "ppat u" "the (psz env u) < the (psz env t')" for u
    using less.hyps[OF _ that(1)] that(2) pz by simp
  define B where "B = (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> rigid_occurs F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)))"
  have ro: "rigid_occurs F t env = head_norm env t \<bind> B"
    by (subst rigid_occurs.simps) (simp add: B_def)
  have "\<exists>r. B t' = Some r"
  proof (cases "is_Abs t'")
    case True
    then obtain a T u where t'a: "t' = pterm.Abs a T u" by (cases t') auto
    have pu: "ppat u" using pt' t'a by (auto dest: ppat_AbsD)
    have "the (psz env t') = the (psz env u) + 2"
      unfolding t'a psz_Abs by (subst psz_some[OF ti pu]) simp
    with IH[OF pu] t'a show ?thesis by (simp add: B_def)
  next
    case nA: False
    obtain h ts where sc: "strip_comb t' = (h, ts)" by force
    note t'e = strip_comb_list_comb[OF sc]
    have B: "B t' = (case h of
        pterm.Var G _ \<Rightarrow>
          if G = F then
            handle (ints_of' env ts \<bind> (\<lambda>_. return True))
              (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
          else return False
      | pterm.Abs _ _ _ \<Rightarrow> return False
      | _ \<Rightarrow> existsM (\<lambda>u. rigid_occurs F u env) ts)"
      using sc nA unfolding B_def by (cases t') simp_all
    from ppat_spine[OF pt'[unfolded t'e] strip_comb_head[OF sc] nA[unfolded t'e]]
    consider (R) "is_rigid h" "\<forall>u\<in>set ts. ppat u" | (V) x T where "h = Var x T" by blast
    then show ?thesis
    proof cases
      case R
      have "\<forall>u\<in>set ts. \<exists>n. psz env u = Some n" using R(2) psz_some[OF ti] by blast
      from psz_rigid_sum[OF R(1) this] t'e
      have "the (psz env t') = 1 + sum_list (map (\<lambda>u. the (psz env u)) ts)" by simp
      then have "the (psz env u) < the (psz env t')" if "u \<in> set ts" for u
        using member_le_sum_list[of "the (psz env u)" "map (\<lambda>u. the (psz env u)) ts"] that by simp
      with IH R(2) have "\<exists>r. existsM (\<lambda>u. rigid_occurs F u env) ts = Some r"
        by (intro existsM_term) blast
      with B R(1) show ?thesis by (cases h) (simp_all add: is_rigid_def)
    next
      case V
      from ppat_strip_flex[OF sc[unfolded V] pt'] obtain iss
        where "ts = map Bound iss" "\<forall>i\<in>set iss. 0 \<le> i" by blast
      then have "\<forall>u\<in>set ts. ppat u" by (auto intro: ppat_Bound)
      from ints_of'_term[OF ti this] have "\<exists>r. handle (ints_of' env ts \<bind> (\<lambda>_. return True))
          (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e) = Some r"
        by (auto intro!: handle_term bindM_term split: exn.splits)
      with B V show ?thesis by simp
    qed
  qed
  then show ?case
    using hn_head_norm[OF hn wf_envD(1)[OF t0(3)]] ro by (auto intro!: bindM_term)
qed

lemma handler_term: "\<exists>r. (case e of Unif x \<Rightarrow> raise a | _ \<Rightarrow> raise e) = Some r"
  by (cases e) (simp_all add: raise_def)

lemma flexrigid_term:
  assumes ti: "tinv ar env" and fr: "fresh_env env" and pt: "ppat t" "typs_ok ar t"
    and bt: "below (maxidx env) t" and Fm: "snd F \<le> maxidx env" and bok: "binders_ok ar binders"
    and is0: "\<forall>i\<in>set is. 0 \<le> i" and gF: "ground ar Fty" and nlb: "no_loose_bound (tr t) (length binders)"
  shows "\<exists>r. flexrigid env binders F Fty is t = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      vps t \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof -
  note t0 = tinvD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(3)])
  have hnd: "\<not> ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e) y"
    for e and y :: env by (cases e) simp_all
  from occurs_term[OF t0(1-3)] obtain ro where ro: "occurs F t env = Some ro" by blast
  from proj_term[OF ti fr pt bt bok is0] obtain rp where rp: "proj t env binders is = Some rp"
    and rpP: "\<forall>u env'. rp = Ok (u, env') \<longrightarrow> prunes ar env env' (reach env (vps t)) \<and>
      vps u \<subseteq> reach env' (vps t) \<and> below (maxidx env') u" by blast
  from rigid_occurs_term[OF ti pt(1)] obtain rro where rro: "rigid_occurs F t env = Some rro" by blast
  have "\<exists>r. flexrigid env binders F Fty is t = Some r"
    unfolding flexrigid_def using ro rp rro
    by (auto intro!: bindM_term handle_term mkabs_term update_term handler_term split: prod.splits res.splits)
  then obtain r where r: "flexrigid env binders F Fty is t = Some r" by blast
  have "tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      vps t \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))" if rOk: "r = Ok env''" for env''
  proof -
    have frg: "flexrigid env binders F Fty is t = Some (Ok env'')" using r rOk by simp
    from frg obtain u env1 u' where occ: "occurs F t env = Some (Ok False)"
      and pj: "ok (proj t env binders is) (u, env1)"
      and u': "ok (mkabs binders is u) u'" and env'': "ok (update (F, Fty) u' env1) env''"
      by (auto simp: flexrigid_def ok_handle hnd split: if_splits prod.splits)
    from rpP pj rp have p1: "prunes ar env env1 (reach env (vps t))" and vu: "vps u \<subseteq> reach env1 (vps t)"
      and bu: "below (maxidx env1) u" by auto
    note pd = prunesD[OF p1]
    note t1 = tinvD[OF pd(3)]
    have F1: "vt_lookup (tenv env1) F = None" by (rule ok_update(1)[OF env''])
    have F0: "vt_lookup (tenv env) F = None"
    proof (rule ccontr)
      assume "vt_lookup (tenv env) F \<noteq> None"
      then obtain b where "vt_lookup (tenv env) F = Some b" by blast
      with pd(1) have "vt_lookup (tenv env1) F = Some b" unfolding extends_def by blast
      with F1 show False by simp
    qed
    have noF: "\<forall>y\<in>reach env (vps t). fst y \<noteq> F" by (rule occurs_False[OF occ refl e F0])
    have vu': "vps u' = vps u" by (rule vps_mkabs[OF u'])
    have ru: "reach env1 (vps u') \<subseteq> reach env1 (vps t)" using vu vu' by (intro reach_mono) simp
    have nc: "(F, Fty) \<notin> reach env1 (vps u')"
      using ru pd(5)[of "vps t"] noF Fm by (force simp: fr_def)
    have Fm1: "snd F \<le> maxidx env1" using Fm pd(2) by simp
    have bu': "below (maxidx env1) u'" using bu vars_mkabs[OF u'] by (simp add: below_def)
    note bs = bind_step[OF t1(1,2) pd(4) env'' nc Fm1 bu']
    have wf'': "wf_env ar env''"
      using flexrigid_sound(2)[OF frg t0(3) bok gF ppat_proper[OF pt(1)] pt(2) is0 nlb] .
    have epp'': "env_ppat env''" by (rule flexrigid_ppat[OF frg t0(3) bok t0(4) pt is0])
    have ti'': "tinv ar env''" using bs(1,2) wf'' epp'' by (simp add: tinv_def)
    have ext: "extends env'' env" by (rule extends_trans[OF bs(4) pd(1)])
    have mx: "maxidx env \<le> maxidx env''" using bs(5) pd(2) by simp
    have "card (unb env'' Y) < card (unb env Y)"
      if Y: "finite Y" "\<forall>y\<in>Y. snd (fst y) \<le> maxidx env" "(F, Fty) \<in> unb env Y" "vps t \<subseteq> reach env Y" for Y
    proof -
      have rY: "reach env Y \<subseteq> reach env1 Y" by (rule reach_extends[OF pd(1)])
      have "reach env1 (vps t) \<subseteq> reach env1 Y" using Y(4) rY by (intro reach_mono) blast
      with ru have uu: "unb env1 (vps u') \<subseteq> unb env1 Y" by (auto simp: unb_def)
      have e1: "unb env'' Y \<subseteq> (unb env1 Y - {(F, Fty)}) \<union> unb env1 (vps u')"
        using bs(7)[of Y] by (cases "(F, Fty) \<in> reach env1 Y") simp_all
      have e2: "(F, Fty) \<notin> unb env1 (vps u')" using nc by (simp add: unb_def)
      from e1 e2 uu have sub: "unb env'' Y \<subseteq> unb env1 Y - {(F, Fty)}" by blast
      have F1Y: "(F, Fty) \<in> unb env1 Y" using Y(3) rY F1 by (auto simp: unb_def lk_def)
      have fin1: "finite (unb env1 Y)" by (rule finite_unb[OF t1(1) Y(1)])
      have "card (unb env'' Y) \<le> card (unb env1 Y - {(F, Fty)})" using sub fin1 by (intro card_mono) auto
      also have "\<dots> < card (unb env1 Y)" by (rule card_Diff1_less[OF fin1 F1Y])
      also have "\<dots> \<le> card (unb env Y)" by (rule pd(6)[OF Y(1,2)])
      finally show ?thesis .
    qed
    with ti'' bs(3) ext mx show ?thesis by blast
  qed
  with r show ?thesis by blast
qed

lemma mk_ff_list_term: "\<exists>r. mk_ff_list is js = Some r"
proof -
  have "\<exists>r. mk_ff_list_aux is js k = Some r" for k
    by (induction "is" js k rule: mk_ff_list_aux.induct) (auto intro!: bindM_term)
  then show ?thesis by (simp add: mk_ff_list_def)
qed

lemma flexflex1_term:
  assumes ti: "tinv ar env" and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env"
    and gF: "ground ar Fty" and bok: "binders_ok ar binders"
  shows "\<exists>r. flexflex1 env binders F Fty is js = Some r \<and>
    (\<forall>env''. r = Ok env'' \<longrightarrow> prunes ar env env'' {(F, Fty)})"
proof -
  note t0 = tinvD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(3)])
  have "\<exists>r. flexflex1 env binders F Fty is js = Some r"
    unfolding flexflex1_def mk_new_hnf_def mk_hnf_def using mk_ff_list_term[of "is" js]
    by (auto intro!: bindM_term type_of_G_term[OF e] mkabs_term update_term split: prod.splits)
  then obtain r where r: "flexflex1 env binders F Fty is js = Some r" by blast
  have "prunes ar env env'' {(F, Fty)}" if rOk: "r = Ok env''" for env''
  proof (cases "is = js")
    case True
    with r rOk have "env'' = env" by (simp add: flexflex1_def return_def)
    with prunes_refl[OF ti fr] show ?thesis by simp
  next
    case False
    have f1: "flexflex1 env binders F Fty is js = Some (Ok env'')" using r rOk by simp
    with False obtain ks where ks: "ok (mk_ff_list is js) ks"
      and hnf: "ok (mk_new_hnf env binders is F Fty ks) env''"
      by (auto simp: flexflex1_def)
    from hnf obtain Gty env1 G t where Gty: "ok (type_of_G env Fty (ilength is) ks) Gty"
      and G: "genvar (fst F) env Gty = (env1, G)" and t: "ok (mkabs binders is (app G ks)) t"
      and env'': "ok (update (F, Fty) t env1) env''"
      by (rule ok_mk_new_hnf)
    from ok_type_of_G'[OF Gty e] obtain Us U Vs where
      T: "Fty = foldr fun_type Us U" "length Us = length is" "Gty = foldr fun_type Vs U" "length Vs = length ks"
      and ks0: "\<forall>k\<in>set ks. 0 \<le> k" by auto
    have wf'': "wf_env ar env''" by (rule flexflex1_sound(2)[OF f1 t0(3) gF bok])
    have epp'': "env_ppat env''" by (rule flexflex1_ppat[OF f1 t0(4)])
    show ?thesis by (rule prune_step[OF ti fr G env'' t ks0 T Fm wf'' epp''])
  qed
  with r show ?thesis by blast
qed

lemma idx_mapM_term: "\<exists>r. mapM (idx is) js = Some r"
  by (rule mapM_term) (rule idx_term)

lemma ff_term:
  assumes ti: "tinv ar env" and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
    and gF: "ground ar Fty" and gG: "ground ar Gty" and bok: "binders_ok ar binders"
    and dist: "distinct is" "distinct js" and nonneg: "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j"
    and FG: "F \<noteq> G" and lG: "lk env G Gty = None"
  shows "\<exists>r. ff env binders F Fty is G Gty js = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof -
  note t0 = tinvD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(3)])
  have "\<exists>r. ff env binders F Fty is G Gty js = Some r"
    unfolding ff_def Let_def
    by (auto intro!: bindM_term idx_mapM_term type_of_G_term[OF e] mkabs_term update_term
        split: prod.splits)
  then obtain r where r: "ff env binders F Fty is G Gty js = Some r" by blast
  have "tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))" if rOk: "r = Ok env''" for env''
  proof -
    have f: "ff env binders F Fty is G Gty js = Some (Ok env'')" using r rOk by simp
    have wf'': "wf_env ar env''" by (rule ff_sound(2)[OF f t0(3) gF gG bok nonneg])
    have epp'': "env_ppat env''" by (rule ff_ppat[OF f t0(4) dist nonneg])
    show ?thesis
    proof (cases "subset js is")
      case True
      with f obtain ks t where ks: "ok (mapM (idx is) js) ks"
        and t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
        and env'': "ok (update (F, Fty) t env) env''"
        by (auto simp: ff_def)
      have vt: "vps t = {(G, Gty)}" using vps_mkabs[OF t] by simp
      have nc: "(F, Fty) \<notin> reach env (vps t)" using vt reach_unbound[OF lG] FG by simp
      have bt: "below (maxidx env) t" using vars_mkabs[OF t] Gm by (simp add: below_def vars_app)
      note bs = bind_step[OF t0(1,2) fr env'' nc Fm bt]
      have "card (unb env'' Y) < card (unb env Y)"
        if Y: "finite Y" "(F, Fty) \<in> unb env Y" "(G, Gty) \<in> unb env Y" for Y
      proof -
        have "unb env (vps t) = {(G, Gty)}" using vt reach_unbound[OF lG] lG by (auto simp: unb_def)
        then have "unb env'' Y \<subseteq> unb env Y - {(F, Fty)}" using bs(7)[of Y] Y(3) FG by auto
        moreover have fu: "finite (unb env Y)" by (rule finite_unb[OF t0(1) Y(1)])
        ultimately have "card (unb env'' Y) \<le> card (unb env Y - {(F, Fty)})" by (intro card_mono) auto
        also have "\<dots> < card (unb env Y)" by (rule card_Diff1_less[OF fu Y(2)])
        finally show ?thesis .
      qed
      with bs wf'' epp'' show ?thesis by (simp add: tinv_def)
    next
      case False
      let ?ks = "inter js is"
      from False f obtain ks' Hty where
        Hty: "ok (type_of_G env Fty (ilength is) ks') Hty"
        and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
          (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) \<bind> (\<lambda>tG.
          (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) \<bind> (\<lambda>tF.
          update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env''"
        by (auto simp: ff_def Let_def)
      obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
      with rest obtain ksG tG ksF tF env2 where
        tG: "ok (mkabs binders js (app H ksG)) tG"
        and tF: "ok (mkabs binders is (app H ksF)) tF"
        and env2: "ok (update (F, Fty) tF env1) env2" and env'': "ok (update (G, Gty) tG env2) env''"
        by auto
      note g = genvar_simps[OF H]
      define Hn where "Hn = (fst G, maxidx env + 1)"
      have HV: "H = Var Hn Hty" using g(4) by (simp add: Hn_def)
      have fin1: "fin_env env1" "acyc env1"
        using t0(1,2) unfolding fin_env_def acyc_def g(1) dep_tenv[OF g(1)] by simp_all
      have fr1: "fresh_env env1" by (rule fresh_env_genvar[OF H fr])
      have lH1: "lk env1 Hn Hty = None" using lk_fresh[OF fr, of Hn Hty] lk_tenv[OF g(1)] by (simp add: Hn_def)
      have sH: "snd Hn = maxidx env + 1" by (simp add: Hn_def)
      have GH: "G \<noteq> Hn" "F \<noteq> Hn"
        using Gm Fm int_succ_not_le[of "maxidx env"] sH by metis+
      have vF: "vps tF = {(Hn, Hty)}" and vG: "vps tG = {(Hn, Hty)}"
        using vps_mkabs[OF tF] vps_mkabs[OF tG] HV by simp_all
      have nc1: "(F, Fty) \<notin> reach env1 (vps tF)" using vF reach_unbound[OF lH1] GH by auto
      have bF: "below (maxidx env1) tF" using vars_mkabs[OF tF] HV g(3) by (simp add: below_def vars_app Hn_def)
      have Fm1: "snd F \<le> maxidx env1" using Fm g(3) by simp
      note b1 = bind_step[OF fin1 fr1 env2 nc1 Fm1 bF]
      have lH2: "lk env2 Hn Hty = None"
        using lk_update[OF ok_update(2)[OF env2], of Hn Hty] lH1 GH by auto
      have nc2: "(G, Gty) \<notin> reach env2 (vps tG)" using vG reach_unbound[OF lH2] GH by auto
      have bG: "below (maxidx env2) tG" using vars_mkabs[OF tG] HV g(3) b1(5) by (simp add: below_def vars_app Hn_def)
      have Gm2: "snd G \<le> maxidx env2" using Gm g(3) b1(5) by simp
      note b2 = bind_step[OF b1(1-3) env'' nc2 Gm2 bG]
      have ext: "extends env'' env"
        using extends_trans[OF b2(4) extends_trans[OF b1(4) genvar_extends[OF H]]] .
      have mx: "maxidx env \<le> maxidx env''" using b2(5) b1(5) g(3) by simp
      have "card (unb env'' Y) < card (unb env Y)"
        if Y: "finite Y" "(F, Fty) \<in> unb env Y" "(G, Gty) \<in> unb env Y" for Y
      proof -
        have u1: "unb env1 = unb env" by (rule unb_tenv[OF g(1)])
        have "unb env1 (vps tF) \<subseteq> {(Hn, Hty)}" using vF by (auto simp: unb_def reach_unbound[OF lH1])
        moreover have "unb env2 (vps tG) \<subseteq> {(Hn, Hty)}" using vG by (auto simp: unb_def reach_unbound[OF lH2])
        ultimately have s1: "unb env2 Y \<subseteq> (unb env Y - {(F, Fty)}) \<union> {(Hn, Hty)}"
          and s2: "unb env'' Y \<subseteq> (unb env2 Y - {(G, Gty)}) \<union> {(Hn, Hty)}"
          using b2(7)[of Y] b1(7)[of Y] u1 by (auto split: if_splits)
        have sub: "unb env'' Y \<subseteq> (unb env Y - {(F, Fty), (G, Gty)}) \<union> {(Hn, Hty)}"
          using s1 s2 GH by blast
        have fu: "finite (unb env Y)" by (rule finite_unb[OF t0(1) Y(1)])
        have D: "{(F, Fty), (G, Gty)} \<subseteq> unb env Y" using Y(2,3) by simp
        have c: "card {(Hn, Hty)} < card {(F, Fty), (G, Gty)}" using FG by simp
        show ?thesis by (rule card_unb_less[OF fu sub D c]) simp
      qed
      with b2 wf'' epp'' ext mx show ?thesis by (simp add: tinv_def)
    qed
  qed
  with r show ?thesis by blast
qed

lemma flexflex2_term:
  assumes "tinv ar env" "fresh_env env" "snd F \<le> maxidx env" "snd G \<le> maxidx env"
    "ground ar Fty" "ground ar Gty" "binders_ok ar binders"
    "distinct is" "distinct js" "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j"
    "F \<noteq> G" "lk env F Fty = None" "lk env G Gty = None"
  shows "\<exists>r. flexflex2 env binders F Fty is G Gty js = Some r \<and> (\<forall>env''. r = Ok env'' \<longrightarrow>
    tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y)))"
proof (cases "indexname_less G F")
  case True
  with ff_term[OF assms(1-11,12,14)] show ?thesis by (simp add: flexflex2_def)
next
  case False
  from ff_term[OF assms(1,2,4,3,6,5,7,9,8,11,10) assms(12)[symmetric] assms(13)] False show ?thesis
    by (auto simp: flexflex2_def)
qed


subsection \<open>The measure of unification problems\<close>

text \<open>
  A unification problem is measured by the number of unbound variables reachable from its terms
  and, lexicographically, by its size. The context \<open>C\<close> contains the terms of the problems that
  are still to be solved.
\<close>

definition vsl :: "pterm list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vsl ts = \<Union> (vps ` set ts)"

definition mu :: "env \<Rightarrow> pterm list \<Rightarrow> nat \<times> nat" where
  "mu env ts = (card (unb env (vsl ts)), sum_list (map (\<lambda>t. the (psz env t)) ts))"

abbreviation lexr :: "((nat \<times> nat) \<times> (nat \<times> nat)) set" where
  "lexr \<equiv> less_than <*lex*> less_than"

definition lexle :: "nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool" where
  "lexle a b \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a \<le> snd b)"

definition oldC :: "env \<Rightarrow> pterm list \<Rightarrow> bool" where
  "oldC env C \<longleftrightarrow> (\<forall>c\<in>set C. ppat c \<and> below (maxidx env) c)"

lemma lexr_iff: "(a, b) \<in> lexr \<longleftrightarrow> fst a < fst b \<or> (fst a = fst b \<and> snd a < snd b)"
  by (cases a; cases b) auto

lemma lexle_trans: "lexle a b \<Longrightarrow> lexle b c \<Longrightarrow> lexle a c"
  by (auto simp: lexle_def)

lemma lexle_lexr: "lexle a b \<Longrightarrow> (b, c) \<in> lexr \<Longrightarrow> (a, c) \<in> lexr"
  by (auto simp: lexle_def lexr_iff)

lemma lexr_lexle: "(a, b) \<in> lexr \<Longrightarrow> lexle b c \<Longrightarrow> (a, c) \<in> lexr"
  by (auto simp: lexle_def lexr_iff)

lemma le_lexle: "fst a \<le> fst b \<Longrightarrow> snd a \<le> snd b \<Longrightarrow> lexle a b"
  by (auto simp: lexle_def)

lemma le_lexr: "fst a \<le> fst b \<Longrightarrow> snd a < snd b \<Longrightarrow> (a, b) \<in> lexr"
  by (auto simp: lexr_iff)

lemma vsl_simps[simp]: "vsl [] = {}" "vsl (t # ts) = vps t \<union> vsl ts" "vsl (xs @ ys) = vsl xs \<union> vsl ys"
  by (auto simp: vsl_def)

lemma finite_vsl[simp]: "finite (vsl ts)"
  by (simp add: vsl_def)

lemma oldC_simps[simp]: "oldC env [] " "oldC env (t # ts) \<longleftrightarrow> ppat t \<and> below (maxidx env) t \<and> oldC env ts"
  "oldC env (xs @ ys) \<longleftrightarrow> oldC env xs \<and> oldC env ys"
  by (auto simp: oldC_def)

lemma oldC_mono: "oldC env C \<Longrightarrow> maxidx env \<le> maxidx env' \<Longrightarrow> oldC env' C"
  by (auto simp: oldC_def intro: below_mono)

lemma below_vps: "below m t \<Longrightarrow> y \<in> vps t \<Longrightarrow> snd (fst y) \<le> m"
  using vps_vars by (auto simp: below_def)

lemma oldC_vsl:
  assumes "oldC env C"
  shows "\<forall>y\<in>vsl C. snd (fst y) \<le> maxidx env"
proof
  fix y assume "y \<in> vsl C"
  then obtain c where c: "c \<in> set C" "y \<in> vps c" by (auto simp: vsl_def)
  with assms have "below (maxidx env) c" by (simp add: oldC_def)
  from below_vps[OF this c(2)] show "snd (fst y) \<le> maxidx env" .
qed

lemma unb_reach_mono: "A \<subseteq> reach env B \<Longrightarrow> unb env A \<subseteq> unb env B"
  using reach_mono[of A env B] by (auto simp: unb_def)

lemma mu_fst_mono:
  "fin_env env \<Longrightarrow> vsl xs \<subseteq> reach env (vsl ys) \<Longrightarrow> fst (mu env xs) \<le> fst (mu env ys)"
  by (simp add: mu_def card_mono finite_unb unb_reach_mono)

lemma mu_append_snd: "snd (mu env (xs @ ys)) = snd (mu env xs) + snd (mu env ys)"
  by (simp add: mu_def)

lemma mu_Cons_snd: "snd (mu env (x # ys)) = the (psz env x) + snd (mu env ys)"
  by (simp add: mu_def)

definition pairs :: "(pterm \<times> pterm) list \<Rightarrow> pterm list" where
  "pairs ps = concat (map (\<lambda>(a, b). [a, b]) ps)"

lemma pairs_simps[simp]: "pairs [] = []" "pairs ((a, b) # ps) = a # b # pairs ps"
  by (simp_all add: pairs_def)

lemma foldM_measure:
  assumes "\<And>a b e. (a, b) \<in> set ps \<Longrightarrow> tinv ar e \<Longrightarrow> fresh_env e \<Longrightarrow> below (maxidx e) a \<Longrightarrow>
      below (maxidx e) b \<Longrightarrow> (mu e [a, b], m) \<in> lexr \<Longrightarrow>
      \<exists>r. f a b e = Some r \<and> (\<forall>e'. r = Ok e' \<longrightarrow> tinv ar e' \<and> fresh_env e' \<and> extends e' e \<and>
        maxidx e \<le> maxidx e' \<and> (\<forall>C. oldC e C \<longrightarrow> lexle (mu e' C) (mu e (a # b # C))))"
    and "\<forall>(a, b)\<in>set ps. ppat a \<and> ppat b \<and> below (maxidx env) a \<and> below (maxidx env) b"
    and "(mu env (pairs ps), m) \<in> lexr" and "tinv ar env" and "fresh_env env"
  shows "\<exists>r. foldM (\<lambda>(a, b) e. f a b e) ps env = Some r \<and> (\<forall>env'. r = Ok env' \<longrightarrow>
    tinv ar env' \<and> fresh_env env' \<and> extends env' env \<and> maxidx env \<le> maxidx env' \<and>
    (\<forall>C. oldC env C \<longrightarrow> lexle (mu env' C) (mu env (pairs ps @ C))))"
  using assms
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (simp add: return_def lexle_def)
next
  case (Cons p ps)
  obtain a b where p: "p = (a, b)" by force
  have ab: "ppat a" "ppat b" "below (maxidx env) a" "below (maxidx env) b"
    and ps: "\<forall>(a, b)\<in>set ps. ppat a \<and> ppat b \<and> below (maxidx env) a \<and> below (maxidx env) b"
    using Cons.prems(2) p by auto
  note t0 = tinvD[OF Cons.prems(4)]
  have oR: "oldC env (pairs ps)" using ps by (induction ps) auto
  have "lexle (mu env [a, b]) (mu env (pairs (p # ps)))"
  proof (rule le_lexle)
    show "fst (mu env [a, b]) \<le> fst (mu env (pairs (p # ps)))"
      using reach_incl[of "vsl (pairs (p # ps))" env] p by (intro mu_fst_mono[OF t0(1)]) auto
    show "snd (mu env [a, b]) \<le> snd (mu env (pairs (p # ps)))" using p by (simp add: mu_def)
  qed
  then have lt: "(mu env [a, b], m) \<in> lexr" using Cons.prems(3) by (rule lexle_lexr)
  from Cons.prems(1)[of a b env, OF _ Cons.prems(4,5) ab(3,4) lt] p
  obtain r1 where r1: "f a b env = Some r1"
    and P1: "\<forall>e'. r1 = Ok e' \<longrightarrow> tinv ar e' \<and> fresh_env e' \<and> extends e' env \<and>
      maxidx env \<le> maxidx e' \<and> (\<forall>C. oldC env C \<longrightarrow> lexle (mu e' C) (mu env (a # b # C)))"
    by auto
  show ?case
  proof (cases r1)
    case (Err e')
    with r1 p show ?thesis by (simp add: bindM_def)
  next
    case (Ok e1)
    with P1 have e1: "tinv ar e1" "fresh_env e1" "extends e1 env" "maxidx env \<le> maxidx e1"
      and L1: "\<And>C. oldC env C \<Longrightarrow> lexle (mu e1 C) (mu env (a # b # C))" by auto
    have ps1: "\<forall>(a, b)\<in>set ps. ppat a \<and> ppat b \<and> below (maxidx e1) a \<and> below (maxidx e1) b"
      using ps e1(4) by (auto intro: below_mono)
    have lt1: "(mu e1 (pairs ps), m) \<in> lexr"
      using lexle_lexr[OF L1[OF oR]] Cons.prems(3) p by simp
    from Cons.IH[OF Cons.prems(1)[OF list.set_intros(2)] ps1 lt1 e1(1,2)]
    obtain r2 where r2: "foldM (\<lambda>(a, b) e. f a b e) ps e1 = Some r2"
      and P2: "\<forall>env'. r2 = Ok env' \<longrightarrow> tinv ar env' \<and> fresh_env env' \<and> extends env' e1 \<and>
        maxidx e1 \<le> maxidx env' \<and> (\<forall>C. oldC e1 C \<longrightarrow> lexle (mu env' C) (mu e1 (pairs ps @ C)))"
      by blast
    have "tinv ar env' \<and> fresh_env env' \<and> extends env' env \<and> maxidx env \<le> maxidx env' \<and>
      (\<forall>C. oldC env C \<longrightarrow> lexle (mu env' C) (mu env (pairs (p # ps) @ C)))" if "r2 = Ok env'" for env'
    proof -
      from P2 that have q: "tinv ar env'" "fresh_env env'" "extends env' e1" "maxidx e1 \<le> maxidx env'"
        and L2: "\<And>C. oldC e1 C \<Longrightarrow> lexle (mu env' C) (mu e1 (pairs ps @ C))" by auto
      have "lexle (mu env' C) (mu env (pairs (p # ps) @ C))" if "oldC env C" for C
        using lexle_trans[OF L2[OF oldC_mono[OF that e1(4)]] L1[of "pairs ps @ C"]] that oR p by simp
      with q e1 show ?thesis by (auto intro: extends_trans)
    qed
    with r1 r2 Ok p show ?thesis by (simp add: bindM_def)
  qed
qed

lemma psz_incr_Bound0:
  assumes ti: "tinv ar env" and pt: "ppat t" and nA: "\<not> is_Abs t" and ht: "hn env t = Some t"
  shows "the (psz env (incr t $ Bound 0)) \<le> the (psz env t) + 1"
proof -
  note t0 = tinvD[OF ti]
  have nn: "nonneg (\<lambda>i. i + 1)" by (simp add: nonneg_def)
  have it: "incr t = rbv (\<lambda>i. i + 1) t" by (rule incr_ren[OF ppat_proper[OF pt]])
  from psz_term[OF t0 pt] obtain n where n: "psz env t = Some n" by blast
  from pt nA show ?thesis
  proof (cases rule: ppat_nonAbsE)
    case (rigid h ts)
    have "is_flex (rbv (\<lambda>i. i + 1) t) = is_flex t" by (rule is_flex_rbv)
    then have nf: "\<not> is_flex (rbv (\<lambda>i. i + 1) t $ Bound 0)"
      using rigid is_rigid_not_flex by (simp add: is_flex_def)
    have "psz env (rbv (\<lambda>i. i + 1) t) = Some n" by (rule psz_rbv[OF n t0(3,4) pt nn])
    with nf n show ?thesis by (simp add: it psz_App psz_atoms)
  next
    case (flex x T iss)
    have lx: "lk env x T = None" using hn_flex_unbound[OF ht[unfolded flex(1)] t0(1,2)] .
    have e: "incr t $ Bound 0 = app (Var x T) (map (\<lambda>i. i + 1) iss @ [0])"
      unfolding it by (simp only: flex(1) rbv_app_Var app_snoc)
    have "psz env (incr t $ Bound 0) = Some (fsz (app (Var x T) (map (\<lambda>i. i + 1) iss @ [0])))"
      by (simp add: e psz_flex hn_unbound[OF lx])
    moreover have "n = fsz t" using n flex(1) by (simp add: psz_flex hn_unbound[OF lx])
    ultimately show ?thesis using flex(1) n by (simp add: fsz_def)
  qed
qed

lemma zip_eq_term: "\<exists>r. zip_eq xs ys = Some r"
  by (induction xs ys rule: zip_eq.induct) (auto intro!: bindM_term)

lemma rigid_clash_term: "\<exists>r. rigid_clash binders h1 h2 = Some r \<and> (\<forall>x. r \<noteq> Ok x)"
  by (auto simp: rigid_clash_def raise_def split: pterm.splits)

lemma pairs_zip: "length xs = length ys \<Longrightarrow> vsl (pairs (zip xs ys)) = vsl xs \<union> vsl ys"
  by (induction xs ys rule: list_induct2) auto

lemma pairs_zip_sum: "length xs = length ys \<Longrightarrow>
    sum_list (map g (pairs (zip xs ys))) = sum_list (map g xs) + sum_list (map (g :: pterm \<Rightarrow> nat) ys)"
  by (induction xs ys rule: list_induct2) auto

lemma pairs_zip_set: "(a, b) \<in> set (zip xs ys) \<Longrightarrow> a \<in> set xs \<and> b \<in> set ys"
  by (auto dest: set_zip_leftD set_zip_rightD)

text \<open>The property of results of \<^const>\<open>unif\<close> established by induction.\<close>

definition uq :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> pterm list \<Rightarrow> env res \<Rightarrow> bool" where
  "uq ar env P r \<longleftrightarrow> (\<forall>env'. r = Ok env' \<longrightarrow> tinv ar env' \<and> fresh_env env' \<and> extends env' env \<and>
    maxidx env \<le> maxidx env' \<and> (\<forall>C. oldC env C \<longrightarrow> lexle (mu env' C) (mu env (P @ C))))"

lemma uq_Err[simp]: "uq ar env P (Err e)"
  by (simp add: uq_def)

lemma uq_mono:
  "uq ar env P r \<Longrightarrow> (\<And>C. oldC env C \<Longrightarrow> lexle (mu env (P @ C)) (mu env (Q @ C))) \<Longrightarrow> uq ar env Q r"
  unfolding uq_def by (blast intro: lexle_trans)

lemma uq_bindM:
  assumes "\<exists>r. m = Some r" "\<And>x. m = Some (Ok x) \<Longrightarrow> \<exists>r. f x = Some r \<and> uq ar env P r"
  shows "\<exists>r. bindM m f = Some r \<and> uq ar env P r"
  using assms by (auto simp: bindM_def split: res.splits)

lemma lexle_unb_less:
  assumes "fin_env env'" "card (unb env' (vsl (P @ C))) < fst (mu env (P @ C))"
  shows "lexle (mu env' C) (mu env (P @ C))"
proof -
  have "unb env' (vsl C) \<subseteq> unb env' (vsl (P @ C))" by (rule unb_subset) simp
  then have "fst (mu env' C) \<le> card (unb env' (vsl (P @ C)))"
    unfolding mu_def by (auto intro!: card_mono finite_unb[OF assms(1)])
  with assms(2) show ?thesis by (simp add: lexle_def)
qed

lemma uq_prunes:
  assumes ti: "tinv ar env" and p: "prunes ar env env' S"
  shows "uq ar env P (Ok env')"
  unfolding uq_def
proof (intro allI impI conjI)
  fix e assume "Ok env' = Ok e"
  then have e: "e = env'" by simp
  show "tinv ar e" "fresh_env e" "extends e env" "maxidx env \<le> maxidx e"
    using prunesD(1-4)[OF p] e by simp_all
  fix C assume c: "oldC env C"
  show "lexle (mu e C) (mu env (P @ C))"
  proof (rule le_lexle)
    have "card (unb env' (vsl C)) \<le> card (unb env (vsl C))"
      by (rule prunesD(6)[OF p finite_vsl oldC_vsl[OF c]])
    moreover have "fst (mu env C) \<le> fst (mu env (P @ C))"
      using reach_incl[of "vsl (P @ C)" env] by (intro mu_fst_mono[OF tinvD(1)[OF ti]]) auto
    ultimately show "fst (mu e C) \<le> fst (mu env (P @ C))" by (simp add: e mu_def)
    have "sum_list (map (\<lambda>t. the (psz env' t)) C) = sum_list (map (\<lambda>t. the (psz env t)) C)"
      using c prunesD(7)[OF p] by (intro arg_cong[where f = sum_list] map_cong) (auto simp: oldC_def)
    then show "snd (mu e C) \<le> snd (mu env (P @ C))" by (simp add: e mu_def)
  qed
qed

lemma uq_unb_less:
  assumes "tinv ar env''" "fresh_env env''" "extends env'' env" "maxidx env \<le> maxidx env''"
    and "\<And>C. oldC env C \<Longrightarrow> card (unb env'' (vsl (P @ C))) < card (unb env (vsl (P @ C)))"
  shows "uq ar env P (Ok env'')"
proof -
  have "lexle (mu env'' C) (mu env (P @ C))" if "oldC env C" for C
    by (rule lexle_unb_less[OF tinvD(1)[OF assms(1)]]) (use assms(5)[OF that] in \<open>simp only: mu_def fst_conv\<close>)
  with assms(1-4) show ?thesis by (simp add: uq_def)
qed

lemma old_vsl:
  "below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow> oldC env C \<Longrightarrow>
    \<forall>y\<in>vsl ([s, t] @ C). snd (fst y) \<le> maxidx env"
  using below_vps[of "maxidx env" s] below_vps[of "maxidx env" t] oldC_vsl[of env C] by auto

lemma unb_vsl_member:
  "lk env x T = None \<Longrightarrow> (x, T) \<in> vsl P \<Longrightarrow> (x, T) \<in> unb env (vsl (P @ C))"
  using reach_incl[of "vsl (P @ C)" env] by (auto simp: unb_def)

subsection \<open>Termination of unification\<close>

lemma unif_term:
  "mu env [s, t] = m \<Longrightarrow> tinv ar env \<Longrightarrow> fresh_env env \<Longrightarrow> binders_ok ar bs \<Longrightarrow>
    wf_term ar (length bs) s \<Longrightarrow> wf_term ar (length bs) t \<Longrightarrow> ppat s \<Longrightarrow> ppat t \<Longrightarrow>
    below (maxidx env) s \<Longrightarrow> below (maxidx env) t \<Longrightarrow>
    \<exists>r. unif alg bs s t env = Some r \<and> uq ar env [s, t] r"
proof (induction m arbitrary: env s t bs rule: wf_induct_rule[OF wf_lex_prod[OF wf_less_than wf_less_than]])
  case (1 m env s t bs)
  have mu: "mu env [s, t] = m" and ti: "tinv ar env" and fr: "fresh_env env"
    and bok: "binders_ok ar bs" and ws: "wf_term ar (length bs) s" and wt: "wf_term ar (length bs) t"
    and ps: "ppat s" and pt: "ppat t" and bs: "below (maxidx env) s" and bt: "below (maxidx env) t"
    using "1.prems" by simp_all
  have IH: "\<exists>r. unif alg bs' a b env' = Some r \<and> uq ar env' [a, b] r"
    if "(mu env' [a, b], m) \<in> lexr" "tinv ar env'" "fresh_env env'" "binders_ok ar bs'"
      "wf_term ar (length bs') a" "wf_term ar (length bs') b" "ppat a" "ppat b"
      "below (maxidx env') a" "below (maxidx env') b" for env' a b bs'
    using "1.IH"[OF that(1) refl that(2-)] .
  note t0 = tinvD[OF ti]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF t0(3)])
  define R where "R = (\<lambda>s0 t0. if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            unif alg ((name, Ts) # bs) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env bs F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env bs F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)))"
  have u_eq: "unif alg bs s t env = head_norm env s \<bind> (\<lambda>s0. head_norm env t \<bind> (\<lambda>t0. R s0 t0))"
    unfolding R_def by (subst unif.simps) (rule refl)
  from hn_term[OF t0 ps] obtain s0 where hs: "hn env s = Some s0" by blast
  from hn_term[OF t0 pt] obtain t0 where ht: "hn env t = Some t0" by blast
  have red: "lexle (mu env ([s0, t0] @ C)) (mu env ([s, t] @ C))" for C
  proof (rule le_lexle)
    let ?Y = "vsl ([s, t] @ C)"
    have "vps s0 \<subseteq> reach env ?Y"
      using hn_ppat_aux[OF hs t0(3,4) ps] reach_subset[of "vps s" ?Y env] by auto
    moreover have "vps t0 \<subseteq> reach env ?Y"
      using hn_ppat_aux[OF ht t0(3,4) pt] reach_subset[of "vps t" ?Y env] by auto
    moreover have "vsl C \<subseteq> reach env ?Y" using reach_incl[of ?Y env] by simp
    ultimately have "vsl ([s0, t0] @ C) \<subseteq> reach env ?Y" by simp
    then show "fst (mu env ([s0, t0] @ C)) \<le> fst (mu env ([s, t] @ C))" by (rule mu_fst_mono[OF t0(1)])
    show "snd (mu env ([s0, t0] @ C)) \<le> snd (mu env ([s, t] @ C))"
      using psz_hn[OF hs ps t0(3,4)] psz_hn[OF ht pt t0(3,4)] by (simp add: mu_def)
  qed
  have main: "\<exists>r. R s0 t0 = Some r \<and> uq ar env [s0, t0] r"
    if hhs: "head_norm env s = Some (Ok s0)" and hht: "head_norm env t = Some (Ok t0)"
  proof -
    let ?n = "length bs"
    have ps0: "ppat s0" using hn_ppat_aux[OF hs t0(3,4) ps] by simp
    have pt0: "ppat t0" using hn_ppat_aux[OF ht t0(3,4) pt] by simp
    from head_norm_sound[OF hhs refl t0(3)] ws have ws0: "wf_term ar ?n s0" by (auto simp: wf_term_def)
    from head_norm_sound[OF hht refl t0(3)] wt have wt0: "wf_term ar ?n t0" by (auto simp: wf_term_def)
    have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hhs refl t0(3) fr bs])
    have bt0: "below (maxidx env) t0" by (rule below_head_norm[OF hht refl t0(3) fr bt])
    have hs0: "hn env s0 = Some s0" by (rule hn_idem[OF hs])
    have ht0: "hn env t0 = Some t0" by (rule hn_idem[OF ht])
    have m0: "lexle (mu env [s0, t0]) m" using red[of "[]"] mu by simp
    have P: "\<And>u. ppat u \<Longrightarrow> psz env u = Some (the (psz env u))" by (rule psz_some[OF ti])
    show ?thesis
    proof (cases "is_Abs s0")
      case sA: True
      then obtain ns Ts ts where s0a: "s0 = Abs ns Ts ts" by (cases s0) auto
      have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
      have pts: "ppat ts" using ps0 s0a by (auto dest: ppat_AbsD)
      have bts: "below (maxidx env) ts" using bs0 s0a by simp
      have wts: "wf_term ar (Suc ?n) ts" using ws0 s0a by (simp add: wf_term_def)
      have pzs: "the (psz env s0) = the (psz env ts) + 2"
        unfolding s0a psz_Abs by (subst P[OF pts]) simp
      show ?thesis
      proof (cases "is_Abs t0")
        case True
        then obtain nt Tt tt where t0a: "t0 = Abs nt Tt tt" by (cases t0) auto
        have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
        have ptt: "ppat tt" using pt0 t0a by (auto dest: ppat_AbsD)
        have btt: "below (maxidx env) tt" using bt0 t0a by simp
        have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
        have pzt: "the (psz env t0) = the (psz env tt) + 2"
          unfolding t0a psz_Abs by (subst P[OF ptt]) simp
        define nm where "nm = (if ns = STR '''' then nt else ns)"
        show ?thesis
        proof (cases "Ts = Tt")
          case False
          with sA True s0a t0a show ?thesis
            by (simp add: R_def Let_def unify_types_ground[OF gTs gTt] bindM_def raise_def)
        next
          case Teq: True
          have Req: "R s0 t0 = unif alg ((nm, Ts) # bs) ts tt env"
            using sA True s0a t0a Teq by (simp add: R_def Let_def nm_def unify_types_ground[OF gTt gTt] return_def bindM_def)
          have bok': "binders_ok ar ((nm, Ts) # bs)" using bok gTs by (simp add: binders_ok_def)
          have le: "lexle (mu env ([ts, tt] @ C)) (mu env ([s0, t0] @ C))" for C
            using s0a t0a pzs pzt by (intro le_lexle) (simp_all add: mu_def)
          have "(mu env [ts, tt], mu env [s0, t0]) \<in> lexr"
            using s0a t0a pzs pzt by (intro le_lexr) (simp_all add: mu_def)
          from lexr_lexle[OF this m0] have lt: "(mu env [ts, tt], m) \<in> lexr" .
          from IH[OF lt ti fr bok' _ _ pts ptt bts btt] wts wtt
          obtain r where r: "unif alg ((nm, Ts) # bs) ts tt env = Some r" and q: "uq ar env [ts, tt] r"
            by auto
          have "uq ar env [s0, t0] r" using uq_mono[OF q le] .
          with r Req show ?thesis by simp
        qed
      next
        case False
        have Req: "R s0 t0 = unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env"
          using sA False s0a by (simp add: R_def)
        have bok': "binders_ok ar ((ns, Ts) # bs)" using bok gTs by (simp add: binders_ok_def)
        have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
          using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
            intro: no_loose_bound_lift)
        have pi: "ppat (incr t0 $ Bound 0)" by (rule ppat_incr_Bound0[OF pt0 False])
        have bi: "below (maxidx env) (incr t0 $ Bound 0)" using bt0 by (simp add: below_def vars_incr)
        have vi: "vps (incr t0 $ Bound 0) = vps t0" using incr_ren[OF ppat_proper[OF pt0]] by simp
        have pzi: "the (psz env (incr t0 $ Bound 0)) \<le> the (psz env t0) + 1"
          by (rule psz_incr_Bound0[OF ti pt0 False ht0])
        have le: "lexle (mu env ([ts, incr t0 $ Bound 0] @ C)) (mu env ([s0, t0] @ C))" for C
          using s0a vi pzs pzi by (intro le_lexle) (simp_all add: mu_def)
        have "(mu env [ts, incr t0 $ Bound 0], mu env [s0, t0]) \<in> lexr"
          using s0a vi pzs pzi by (intro le_lexr) (simp_all add: mu_def)
        from lexr_lexle[OF this m0] have lt: "(mu env [ts, incr t0 $ Bound 0], m) \<in> lexr" .
        from IH[OF lt ti fr bok' _ _ pts pi bts bi] wts wi
        obtain r where r: "unif alg ((ns, Ts) # bs) ts (incr t0 $ Bound 0) env = Some r"
          and q: "uq ar env [ts, incr t0 $ Bound 0] r"
          by auto
        have "uq ar env [s0, t0] r" using uq_mono[OF q le] .
        with r Req show ?thesis by simp
      qed
    next
      case nsA: False
      show ?thesis
      proof (cases "is_Abs t0")
        case True
        then obtain nt Tt tt where t0a: "t0 = Abs nt Tt tt" by (cases t0) auto
        have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
        have ptt: "ppat tt" using pt0 t0a by (auto dest: ppat_AbsD)
        have btt: "below (maxidx env) tt" using bt0 t0a by simp
        have wtt: "wf_term ar (Suc ?n) tt" using wt0 t0a by (simp add: wf_term_def)
        have pzt: "the (psz env t0) = the (psz env tt) + 2"
          unfolding t0a psz_Abs by (subst P[OF ptt]) simp
        have Req: "R s0 t0 = unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env"
          using nsA True t0a by (simp add: R_def)
        have bok': "binders_ok ar ((nt, Tt) # bs)" using bok gTt by (simp add: binders_ok_def)
        have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
          using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
            intro: no_loose_bound_lift)
        have pi: "ppat (incr s0 $ Bound 0)" by (rule ppat_incr_Bound0[OF ps0 nsA])
        have bi: "below (maxidx env) (incr s0 $ Bound 0)" using bs0 by (simp add: below_def vars_incr)
        have vi: "vps (incr s0 $ Bound 0) = vps s0" using incr_ren[OF ppat_proper[OF ps0]] by simp
        have pzi: "the (psz env (incr s0 $ Bound 0)) \<le> the (psz env s0) + 1"
          by (rule psz_incr_Bound0[OF ti ps0 nsA hs0])
        have le: "lexle (mu env ([incr s0 $ Bound 0, tt] @ C)) (mu env ([s0, t0] @ C))" for C
          using t0a vi pzt pzi by (intro le_lexle) (simp_all add: mu_def)
        have "(mu env [incr s0 $ Bound 0, tt], mu env [s0, t0]) \<in> lexr"
          using t0a vi pzt pzi by (intro le_lexr) (simp_all add: mu_def)
        from lexr_lexle[OF this m0] have lt: "(mu env [incr s0 $ Bound 0, tt], m) \<in> lexr" .
        from IH[OF lt ti fr bok' _ _ pi ptt bi btt] wi wtt
        obtain r where r: "unif alg ((nt, Tt) # bs) (incr s0 $ Bound 0) tt env = Some r"
          and q: "uq ar env [incr s0 $ Bound 0, tt] r"
          by auto
        have "uq ar env [s0, t0] r" using uq_mono[OF q le] .
        with r Req show ?thesis by simp
      next
        case ntA: False
        obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
        obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
        note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
        have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
          using ws0 s0e by (simp_all add: wf_term_list_comb)
        have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
          using wt0 t0e by (simp_all add: wf_term_list_comb)
        have pss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
          using wss(2) wts(2) by (auto simp: wf_term_def)
        have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
          using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
        note sps = ppat_spine[OF ps0[unfolded s0e] nApp(1) nsA[unfolded s0e]]
        note spt = ppat_spine[OF pt0[unfolded t0e] nApp(2) ntA[unfolded t0e]]
        consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
          | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
          | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
          | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
          by (cases hs; cases ht) auto
        then show ?thesis
        proof cases
          case (VV F Fty G Gty)
          from nsA ntA shs sht VV have Req: "R s0 t0 = ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
              if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js))"
            by (simp add: R_def)
          from ppat_strip_flex[OF shs[unfolded VV(1)] ps0] obtain iss
            where iss: "ss = map Bound iss" "\<forall>i\<in>set iss. 0 \<le> i" by blast
          from ppat_strip_flex[OF sht[unfolded VV(2)] pt0] obtain jss
            where jss: "ts = map Bound jss" "\<forall>i\<in>set jss. 0 \<le> i" by blast
          have s0f: "s0 = app (Var F Fty) iss" using s0e VV iss by (simp add: app_list_comb)
          have t0f: "t0 = app (Var G Gty) jss" using t0e VV jss by (simp add: app_list_comb)
          have lF: "lk env F Fty = None" using hn_flex_unbound[OF hs0[unfolded s0f] t0(1,2)] .
          have lG: "lk env G Gty = None" using hn_flex_unbound[OF ht0[unfolded t0f] t0(1,2)] .
          have gF: "ground ar Fty" and gG: "ground ar Gty"
            using wss(1) wts(1) VV by (simp_all add: wf_term_def)
          have Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env"
            using bs0 bt0 s0e t0e VV by (simp_all add: below_list_comb)
          have ppss: "\<forall>t\<in>set ss. ppat t" using iss by (auto intro: ppat_Bound)
          have ppts: "\<forall>t\<in>set ts. ppat t" using jss by (auto intro: ppat_Bound)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF ti ppss]])
            fix "is" assume iS: "ints_of' env ss = Some (Ok is)"
            note iS' = ints_of'_sound[OF iS t0(3) pss]
            show "\<exists>r. ints_of' env ts \<bind> (\<lambda>js. if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js) = Some r \<and> uq ar env [s0, t0] r"
            proof (rule uq_bindM[OF ints_of'_term[OF ti ppts]])
              fix js assume jS: "ints_of' env ts = Some (Ok js)"
              note jS' = ints_of'_sound[OF jS t0(3) pts]
              show "\<exists>r. (if F = G then flexflex1 env bs F Fty is js
                  else flexflex2 env bs F Fty is G Gty js) = Some r \<and> uq ar env [s0, t0] r"
              proof (cases "F = G")
                case True
                from flexflex1_term[OF ti fr Fm gF bok, of "is" js] obtain r
                  where r: "flexflex1 env bs F Fty is js = Some r"
                    and p: "\<forall>env''. r = Ok env'' \<longrightarrow> prunes ar env env'' {(F, Fty)}" by blast
                have "uq ar env [s0, t0] r" using p uq_prunes[OF ti] by (cases r) auto
                with r True show ?thesis by simp
              next
                case False
                from flexflex2_term[OF ti fr Fm Gm gF gG bok iS'(1) jS'(1) iS'(2) jS'(2) False lF lG]
                obtain r where r: "flexflex2 env bs F Fty is G Gty js = Some r"
                  and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                    tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
                    (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
                      (G, Gty) \<in> unb env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
                  by blast
                have "uq ar env [s0, t0] r"
                proof (cases r)
                  case (Ok e)
                  with q have e: "tinv ar e" "fresh_env e" "extends e env" "maxidx env \<le> maxidx e"
                    and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (F, Fty) \<in> unb env Y \<Longrightarrow>
                      (G, Gty) \<in> unb env Y \<Longrightarrow> card (unb e Y) < card (unb env Y)"
                    by auto
                  have "card (unb e (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                    if "oldC env C" for C
                    using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lF]
                      unb_vsl_member[OF lG]] s0f t0f by simp
                  then have "uq ar env [s0, t0] (Ok e)" by (rule uq_unb_less[OF e])
                  with Ok show ?thesis by simp
                qed simp
                with r False show ?thesis by simp
              qed
            qed
          qed
        next
          case (VR F Fty)
          from nsA ntA shs sht VR have Req: "R s0 t0 = ints_of' env ss \<bind> (\<lambda>is. flexrigid env bs F Fty is t0)"
            by (cases ht) (simp_all add: R_def)
          from ppat_strip_flex[OF shs[unfolded VR(1)] ps0] obtain iss
            where iss: "ss = map Bound iss" "\<forall>i\<in>set iss. 0 \<le> i" by blast
          have s0f: "s0 = app (Var F Fty) iss" using s0e VR iss by (simp add: app_list_comb)
          have lF: "lk env F Fty = None" using hn_flex_unbound[OF hs0[unfolded s0f] t0(1,2)] .
          have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
          have Fm: "snd F \<le> maxidx env" using bs0 s0e VR by (simp add: below_list_comb)
          have ppss: "\<forall>t\<in>set ss. ppat t" using iss by (auto intro: ppat_Bound)
          have wt0': "typs_ok ar t0" "no_loose_bound (tr t0) ?n" using wt0 by (simp_all add: wf_term_def)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF ti ppss]])
            fix "is" assume iS: "ints_of' env ss = Some (Ok is)"
            note iS' = ints_of'_sound[OF iS t0(3) pss]
            from flexrigid_term[OF ti fr pt0 wt0'(1) bt0 Fm bok iS'(2) gF wt0'(2)]
            obtain r where r: "flexrigid env bs F Fty is t0 = Some r"
              and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
                (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (F, Fty) \<in> unb env Y \<longrightarrow>
                  vps t0 \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
              by blast
            have "uq ar env [s0, t0] r"
            proof (cases r)
              case (Ok e)
              with q have e: "tinv ar e" "fresh_env e" "extends e env" "maxidx env \<le> maxidx e"
                and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (F, Fty) \<in> unb env Y \<Longrightarrow>
                  vps t0 \<subseteq> reach env Y \<Longrightarrow> card (unb e Y) < card (unb env Y)"
                by auto
              have "card (unb e (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                if "oldC env C" for C
                using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lF]]
                  reach_incl[of "vsl ([s0, t0] @ C)" env] s0f by auto
              then have "uq ar env [s0, t0] (Ok e)" by (rule uq_unb_less[OF e])
              with Ok show ?thesis by simp
            qed simp
            with r show "\<exists>r. flexrigid env bs F Fty is t0 = Some r \<and> uq ar env [s0, t0] r" by blast
          qed
        next
          case (RV G Gty)
          from nsA ntA shs sht RV have Req: "R s0 t0 = ints_of' env ts \<bind> (\<lambda>js. flexrigid env bs G Gty js s0)"
            by (cases hs) (simp_all add: R_def)
          from ppat_strip_flex[OF sht[unfolded RV(2)] pt0] obtain jss
            where jss: "ts = map Bound jss" "\<forall>i\<in>set jss. 0 \<le> i" by blast
          have t0f: "t0 = app (Var G Gty) jss" using t0e RV jss by (simp add: app_list_comb)
          have lG: "lk env G Gty = None" using hn_flex_unbound[OF ht0[unfolded t0f] t0(1,2)] .
          have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
          have Gm: "snd G \<le> maxidx env" using bt0 t0e RV by (simp add: below_list_comb)
          have ppts: "\<forall>t\<in>set ts. ppat t" using jss by (auto intro: ppat_Bound)
          have ws0': "typs_ok ar s0" "no_loose_bound (tr s0) ?n" using ws0 by (simp_all add: wf_term_def)
          show ?thesis unfolding Req
          proof (rule uq_bindM[OF ints_of'_term[OF ti ppts]])
            fix js assume jS: "ints_of' env ts = Some (Ok js)"
            note jS' = ints_of'_sound[OF jS t0(3) pts]
            from flexrigid_term[OF ti fr ps0 ws0'(1) bs0 Gm bok jS'(2) gG ws0'(2)]
            obtain r where r: "flexrigid env bs G Gty js s0 = Some r"
              and q: "\<forall>env''. r = Ok env'' \<longrightarrow>
                tinv ar env'' \<and> fresh_env env'' \<and> extends env'' env \<and> maxidx env \<le> maxidx env'' \<and>
                (\<forall>Y. finite Y \<longrightarrow> (\<forall>y\<in>Y. snd (fst y) \<le> maxidx env) \<longrightarrow> (G, Gty) \<in> unb env Y \<longrightarrow>
                  vps s0 \<subseteq> reach env Y \<longrightarrow> card (unb env'' Y) < card (unb env Y))"
              by blast
            have "uq ar env [s0, t0] r"
            proof (cases r)
              case (Ok e)
              with q have e: "tinv ar e" "fresh_env e" "extends e env" "maxidx env \<le> maxidx e"
                and lt: "\<And>Y. finite Y \<Longrightarrow> \<forall>y\<in>Y. snd (fst y) \<le> maxidx env \<Longrightarrow> (G, Gty) \<in> unb env Y \<Longrightarrow>
                  vps s0 \<subseteq> reach env Y \<Longrightarrow> card (unb e Y) < card (unb env Y)"
                by auto
              have "card (unb e (vsl ([s0, t0] @ C))) < card (unb env (vsl ([s0, t0] @ C)))"
                if "oldC env C" for C
                using lt[OF finite_vsl old_vsl[OF bs0 bt0 that] unb_vsl_member[OF lG]]
                  reach_incl[of "vsl ([s0, t0] @ C)" env] t0f by auto
              then have "uq ar env [s0, t0] (Ok e)" by (rule uq_unb_less[OF e])
              with Ok show ?thesis by simp
            qed simp
            with r show "\<exists>r. flexrigid env bs G Gty js s0 = Some r \<and> uq ar env [s0, t0] r" by blast
          qed
        next
          case RR
          have rs: "is_rigid hs" "\<forall>t\<in>set ss. ppat t" using sps RR by auto
          have rt: "is_rigid ht" "\<forall>t\<in>set ts. ppat t" using spt RR by auto
          have gh: "typs_ok ar hs" "typs_ok ar ht" using wss(1) wts(1) by (simp_all add: wf_term_def)
          have bss: "\<forall>t\<in>set ss. below (maxidx env) t" using bs0 s0e by (simp add: below_list_comb)
          have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bt0 t0e by (simp add: below_list_comb)
          have "\<forall>t\<in>set ss. \<exists>n. psz env t = Some n" using rs(2) psz_some[OF ti] by blast
          then have "psz env s0 = Some (1 + sum_list (map (\<lambda>t. the (psz env t)) ss))"
            by (subst s0e) (rule psz_rigid_sum[OF rs(1)])
          then have pzs: "the (psz env s0) = 1 + sum_list (map (\<lambda>t. the (psz env t)) ss)" by simp
          have "\<forall>t\<in>set ts. \<exists>n. psz env t = Some n" using rt(2) psz_some[OF ti] by blast
          then have "psz env t0 = Some (1 + sum_list (map (\<lambda>t. the (psz env t)) ts))"
            by (subst t0e) (rule psz_rigid_sum[OF rt(1)])
          then have pzt: "the (psz env t0) = 1 + sum_list (map (\<lambda>t. the (psz env t)) ts)" by simp
          have fold: "\<exists>r. zip_eq ss ts \<bind> (\<lambda>ps. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env) = Some r \<and>
            uq ar env [s0, t0] r"
          proof (rule uq_bindM[OF zip_eq_term])
            fix ps assume "zip_eq ss ts = Some (Ok ps)"
            then have len: "length ss = length ts" and ps: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
            have le: "lexle (mu env (pairs ps @ C)) (mu env ([s0, t0] @ C))" for C
            proof (rule le_lexle)
              have "vsl (pairs ps @ C) \<subseteq> vsl ([s0, t0] @ C)"
                using pairs_zip[OF len] s0e t0e by (auto simp: ps vps_list_comb vsl_def)
              then show "fst (mu env (pairs ps @ C)) \<le> fst (mu env ([s0, t0] @ C))"
                using reach_incl[of "vsl ([s0, t0] @ C)" env] by (intro mu_fst_mono[OF t0(1)]) blast
              show "snd (mu env (pairs ps @ C)) \<le> snd (mu env ([s0, t0] @ C))"
                using pzs pzt pairs_zip_sum[OF len] by (simp add: mu_def ps)
            qed
            have lt: "(mu env (pairs ps), m) \<in> lexr"
            proof (rule lexr_lexle[OF _ m0], rule le_lexr)
              show "fst (mu env (pairs ps)) \<le> fst (mu env [s0, t0])" using le[of "[]"] by (auto simp: lexle_def)
              show "snd (mu env (pairs ps)) < snd (mu env [s0, t0])"
                using pzs pzt pairs_zip_sum[OF len] by (simp add: mu_def ps)
            qed
            have prem: "\<forall>(a, b)\<in>set ps. ppat a \<and> ppat b \<and> below (maxidx env) a \<and> below (maxidx env) b"
              using rs(2) rt(2) bss bts by (auto simp: ps dest: pairs_zip_set)
            have step: "\<exists>r. unif alg bs a b e = Some r \<and> (\<forall>e'. r = Ok e' \<longrightarrow> tinv ar e' \<and> fresh_env e' \<and>
                extends e' e \<and> maxidx e \<le> maxidx e' \<and> (\<forall>C. oldC e C \<longrightarrow> lexle (mu e' C) (mu e (a # b # C))))"
              if "(a, b) \<in> set ps" "tinv ar e" "fresh_env e" "below (maxidx e) a" "below (maxidx e) b"
                "(mu e [a, b], m) \<in> lexr" for a b e
            proof -
              from that(1) have "a \<in> set ss" "b \<in> set ts" by (auto simp: ps dest: pairs_zip_set)
              with IH[OF that(6,2,3) bok _ _ _ _ that(4,5)] wss(2) wts(2) rs(2) rt(2)
              show ?thesis by (simp add: uq_def)
            qed
            from foldM_measure[where f = "\<lambda>a b e. unif alg bs a b e", OF step prem lt ti fr]
            obtain r where r: "foldM (\<lambda>(a, b) e. unif alg bs a b e) ps env = Some r"
              and q: "\<forall>env'. r = Ok env' \<longrightarrow> tinv ar env' \<and> fresh_env env' \<and> extends env' env \<and>
                maxidx env \<le> maxidx env' \<and> (\<forall>C. oldC env C \<longrightarrow> lexle (mu env' C) (mu env (pairs ps @ C)))"
              by blast
            have "uq ar env [s0, t0] r" using q le unfolding uq_def by (blast intro: lexle_trans)
            with r show "\<exists>r. foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env = Some r \<and> uq ar env [s0, t0] r"
              by blast
          qed
          have nA: "\<not> is_Abs hs" "\<not> is_Abs ht" using rs(1) rt(1) by (auto simp: is_rigid_def)
          have rcl: "\<exists>r. rigid_clash bs hs ht = Some r \<and> uq ar env [s0, t0] r"
            using rigid_clash_term[of bs hs ht] by (auto simp: uq_def)
          have Req: "R s0 t0 = (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. unif alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)"
            using nsA ntA shs sht RR nA by (simp add: R_def)
          show ?thesis
          proof (cases hs)
            case hC: (Const a Ta)
            then have gTa: "ground ar Ta" using gh(1) by simp
            show ?thesis
            proof (cases ht)
              case (Const b Tb)
              then have gTb: "ground ar Tb" using gh(2) by simp
              show ?thesis using fold hC Const
                by (simp add: Req unify_types_ground[OF gTa gTb] return_def raise_def bindM_def)
            qed (use rcl RR nA nApp hC in \<open>simp_all add: Req\<close>)
          next
            case hF: (Free a Ta)
            then have gTa: "ground ar Ta" using gh(1) by simp
            show ?thesis
            proof (cases ht)
              case (Free b Tb)
              then have gTb: "ground ar Tb" using gh(2) by simp
              show ?thesis using fold hF Free
                by (simp add: Req unify_types_ground[OF gTa gTb] return_def raise_def bindM_def)
            qed (use rcl RR nA nApp hF in \<open>simp_all add: Req\<close>)
          next
            case hB: (Bound i)
            show ?thesis
            proof (cases ht)
              case (Bound j)
              show ?thesis using fold hB Bound by (simp add: Req raise_def)
            qed (use rcl RR nA nApp hB in \<open>simp_all add: Req\<close>)
          qed (use RR nA nApp in simp_all)
        qed
      qed
    qed
  qed
  from hn_head_norm[OF hs e] hn_head_norm[OF ht e] show ?case
  proof (elim disjE exE)
    assume hhs: "head_norm env s = Some (Ok s0)" and hht: "head_norm env t = Some (Ok t0)"
    from main[OF hhs hht] obtain r where r: "R s0 t0 = Some r" and q: "uq ar env [s0, t0] r" by blast
    have "uq ar env [s, t] r" using uq_mono[OF q red] by simp
    with r hhs hht u_eq show ?thesis by (simp add: bindM_def)
  qed (simp_all add: u_eq bindM_def)
qed

text \<open>
  Termination of \<^const>\<open>unify\<close>: on \<open>\<beta>\<close>-normal patterns (\<^const>\<open>ppat\<close>) whose variables are
  not newer than the environment (\<^const>\<open>below\<close>), in a finite, acyclic, well-formed environment
  whose bindings are \<open>\<beta>\<close>-normal patterns, \<^const>\<open>unify\<close> terminates, either with a result or with
  an exception. No typing assumptions are needed.
\<close>

theorem unify_term:
  assumes "fin_env env" "acyc env" "wf_env ar env" "env_ppat env" "fresh_env env"
    and "wf_term ar 0 s" "wf_term ar 0 t" "ppat s" "ppat t"
    and "below (maxidx env) s" "below (maxidx env) t"
  shows "unify alg s t env \<noteq> None"
proof -
  have ti: "tinv ar env" using assms(1-4) by (simp add: tinv_def)
  have bok: "binders_ok ar []" by (simp add: binders_ok_def)
  from unif_term[OF refl ti assms(5) bok _ _ assms(8-11)] assms(6,7)
  show ?thesis by (auto simp: unify_def)
qed

text \<open>
  Soundness, continued: under the same assumptions, a result of \<^const>\<open>unify\<close> is again such an
  environment, so that unification problems can be chained (as in \<open>Unify.unifiers\<close>).
\<close>

theorem unify_invariants:
  assumes "unify alg s t env = Some (Ok env')"
    and "fin_env env" "acyc env" "wf_env ar env" "env_ppat env" "fresh_env env"
    and "wf_term ar 0 s" "wf_term ar 0 t" "ppat s" "ppat t"
    and "below (maxidx env) s" "below (maxidx env) t"
  shows "fin_env env'" "acyc env'" "wf_env ar env'" "env_ppat env'" "fresh_env env'"
    "maxidx env \<le> maxidx env'"
proof -
  have ti: "tinv ar env" using assms(2-5) by (simp add: tinv_def)
  have bok: "binders_ok ar []" by (simp add: binders_ok_def)
  from unif_term[OF refl ti assms(6) bok _ _ assms(9-12)] assms(7,8)
  obtain r where r: "unify alg s t env = Some r" and q: "uq ar env [s, t] r"
    by (auto simp: unify_def)
  from r assms(1) q show "fin_env env'" "acyc env'" "wf_env ar env'" "env_ppat env'" "fresh_env env'"
    "maxidx env \<le> maxidx env'"
    by (simp_all add: uq_def tinv_def)
qed

end
