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
  with reach_Domain[of env X] show ?thesis by (rule finite_subset[rotated])
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
      with 1 Var show ?thesis by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def)
    next
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      show ?thesis
      proof (cases "U = T")
        case True
        with Some p 1 Var have hu: "h env u = Some t'" by (simp add: lk_def)
        from IH[OF hu] Some p True Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def)
      next
        case False
        with Some p Var show ?thesis
          by (simp add: head_norm.simps[of env "Var x T"] lookup_lk e lk_def var_clash_def raise_def)
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
          from IH[OF this] hf nfa App hn_eq show ?thesis by simp
        next
          case nA: False
          with rest have "t' = nf $ u" by (cases nf) auto
          with hf nA App hn_eq show ?thesis by (cases nf) (simp_all add: return_def)
        qed
      next
        assume "\<exists>e. head_norm env f = Some (Err e)"
        with App hn_eq show ?thesis by (auto simp: bindM_def)
      qed
    qed
  qed (use 1 in \<open>simp_all add: head_norm.simps[of env] return_def\<close>)
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
      with r r2 \<open>r = Ok p\<close> p Ok q show ?thesis by (simp add: return_def)
    next
      case (Err e')
      with r r2 \<open>r = Ok p\<close> p show ?thesis by (simp add: bindM_def)
    qed
  next
    case (Err e')
    with r show ?thesis by (simp add: bindM_def raise_def)
  qed
qed


end
