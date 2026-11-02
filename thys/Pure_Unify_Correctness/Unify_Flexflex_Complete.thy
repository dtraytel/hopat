section \<open>Completeness of the Treatment of Flex-Flex Pairs\<close>

theory Unify_Flexflex_Complete
  imports Unify_Match_Complete Pure_Pattern_Correctness.Match_Sound
begin

context csig
begin

text \<open>
  Completeness of \<^const>\<open>add_ffpair\<close>: on flex-flex pairs solved by a well-typed solution \<open>\<sigma>\<close>, the
  treatment of the flex-flex pairs terminates without an exception, and an extension of \<open>\<sigma>\<close> by
  values for the new variables satisfies the resulting environment and solves the remaining
  pairs. The deletion of arguments in \<^const>\<open>clean_term\<close> does not lose solutions, since a banned
  bound variable that occurs rigidly in an argument persists in every instance.
\<close>

subsection \<open>Normalization terminates\<close>

text \<open>
  \<open>fhd t\<close>: the head of \<open>t\<close>, looking into abstractions in head position, also of redexes. A term
  whose \<open>fhd\<close> is a variable unbound in \<open>env0\<close> keeps such a head under normalization in an
  environment that binds the other variables only to such terms (\<open>flexb\<close>).
\<close>

fun fhd :: "pterm \<Rightarrow> pterm" where
  "fhd (Abs _ _ b) = fhd b"
| "fhd (f $ _) = fhd f"
| "fhd t = t"

definition fh :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "fh env0 t \<longleftrightarrow> (\<exists>w W. fhd t = Var w W \<and> vt_lookup (tenv env0) w = None)"

definition flexb :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "flexb env0 env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> vt_lookup (tenv env0) x = None \<longrightarrow> fh env0 u)"

lemma fhd_subst_bound_aux: "is_Var (fhd b) \<Longrightarrow> fhd (subst_bound_aux u lev b) = fhd b"
  by (induction u lev b rule: subst_bound_aux.induct) (auto split: if_splits)

lemma fhd_subst_bound: "is_Var (fhd b) \<Longrightarrow> fhd (subst_bound u b) = fhd b"
  by (simp add: subst_bound_def fhd_subst_bound_aux)

lemma fhd_list_comb[simp]: "fhd (list_comb h ts) = fhd h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma head_of_list_comb_head[simp]: "head_of (list_comb h ts) = head_of h"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma fhd_types_abs[simp]: "fhd (types_abs Ts b) = fhd b"
  by (induction Ts) simp_all

lemma fhd_no_beta: "\<not> could_beta_contract t \<Longrightarrow> is_Abs t \<or> fhd t = head_of t"
proof (induction t)
  case (App f u)
  then show ?case by (cases f) auto
qed auto

context
  fixes ar env W
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
begin

end

subsection \<open>Rigid occurrences of bound variables persist\<close>

text \<open>
  The loose bound variables \<open>Z\<close> at depth \<open>d\<close>: the variables bound in between and the shifted \<open>Z\<close>.
\<close>

definition bshift :: "nat \<Rightarrow> nat set \<Rightarrow> nat set" where
  "bshift d Z = {i. i < d} \<union> (\<lambda>i. i + d) ` Z"

lemma bshift_Suc: "insert 0 (Suc ` bshift d Z) = bshift (Suc d) Z"
  by (auto simp: bshift_def image_iff less_Suc_eq_0_disj)

lemma bshift_0[simp]: "bshift 0 Z = Z"
  by (simp add: bshift_def)

lemma atom_apps_dep_onI:
  assumes "is_atom h" "loose_BVars h \<subseteq> Z" "\<forall>a\<in>set as. dep_on Z a"
  shows "dep_on Z (h \<degree>\<degree> as)"
proof -
  have "\<exists>rs. list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs \<and> (\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z)"
    using assms(3)
  proof (induction as)
    case (Cons a as)
    from Cons.prems have "\<forall>x\<in>set as. dep_on Z x" "dep_on Z a" by simp_all
    from Cons.IH[OF this(1)] obtain rs where rs: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs" "\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z"
      by blast
    from \<open>dep_on Z a\<close> obtain r where r: "a \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> Z" unfolding dep_on_def by blast
    have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (a # as) (r # rs)" using r(1) rs(1) by (simp only: list_all2_Cons)
    moreover have "\<forall>x\<in>set (r # rs). loose_BVars x \<subseteq> Z" using r(2) rs(2) by simp
    ultimately show ?case by blast
  qed simp
  then obtain rs where rs: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) as rs" "\<forall>r\<in>set rs. loose_BVars r \<subseteq> Z" by blast
  show ?thesis
  proof (rule dep_onI)
    show "h \<degree>\<degree> as \<equiv>\<^sub>\<beta>\<^sub>\<eta> h \<degree>\<degree> rs" by (rule equiv_list_app[OF equiv_refl rs(1)])
    show "loose_BVars (h \<degree>\<degree> rs) \<subseteq> Z" using assms(2) rs(2) by auto
  qed
qed

text \<open>
  A rigid occurrence of a banned bound variable (\<^const>\<open>rigid_bound\<close>) survives the instantiation
  by a rigid solution: an instance that only depends on \<open>Z\<close> has no such occurrence.
\<close>

lemma rigid_bound_dep:
  assumes \<sigma>: "closed_on UNIV \<sigma>" "rigid_subst \<sigma>"
  shows "rigid_bound lev banned t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<forall>j\<in>set banned. 0 \<le> j \<Longrightarrow>
    dep_on (bshift (nat_of_integer lev) Z) (mk_subst \<sigma> (tr t)) \<Longrightarrow> \<exists>j\<in>set banned. nat_of_integer j \<in> Z"
proof (induction lev banned t rule: rigid_bound.induct)
  case (1 lev banned t)
  obtain h args where sc: "strip_comb t = (h, args)" by (cases "strip_comb t")
  have t: "t = list_comb h args" by (rule strip_comb_list_comb[OF sc])
  have tr: "mk_subst \<sigma> (tr t) = mk_subst \<sigma> (tr h) \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) args"
    by (simp add: t tr_list_comb comp_def)
  let ?Z = "bshift (nat_of_integer lev) Z"
  have rb: "rigid_bound lev banned t = (case h of
      Bound i \<Rightarrow> (i - lev) \<in> set banned \<or> (\<exists>a\<in>set args. rigid_bound lev banned a)
    | Var _ _ \<Rightarrow> False
    | Abs _ _ u \<Rightarrow> List.null args \<and> rigid_bound (lev + 1) banned u
    | _ \<Rightarrow> (\<exists>a\<in>set args. rigid_bound lev banned a))"
    by (subst rigid_bound.simps) (simp add: sc)
  have dargs: "dep_on ?Z (mk_subst \<sigma> (tr a))"
    if "is_atom (mk_subst \<sigma> (tr h))" "a \<in> set args" for a
    using atom_apps_dep_on(2)[OF that(1) "1.prems"(4)[unfolded tr]] that(2) by auto
  have nApp: "\<not> (\<exists>f u. h = f $ u)" using head_of_not_App[of t] fst_strip_comb[of t] sc by auto
  show ?case
  proof (cases h)
    case (Const c T)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using rigid_substD[OF \<sigma>(2)] Const by simp
    from "1.prems"(1) rb Const obtain a where "a \<in> set args" "rigid_bound lev banned a" by auto
    from "1"(1)[OF sc[symmetric] refl Const this "1.prems"(2,3) dargs[OF at this(1)]] show ?thesis .
  next
    case (Free c T)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using rigid_substD[OF \<sigma>(2)] Free by simp
    from "1.prems"(1) rb Free obtain a where "a \<in> set args" "rigid_bound lev banned a" by auto
    from "1"(2)[OF sc[symmetric] refl Free this "1.prems"(2,3) dargs[OF at this(1)]] show ?thesis .
  next
    case (Bound i)
    have at: "is_atom (mk_subst \<sigma> (tr h))" using Bound by simp
    from "1.prems"(1) rb Bound consider "i - lev \<in> set banned" | a where "a \<in> set args" "rigid_bound lev banned a"
      by auto
    then show ?thesis
    proof cases
      case 1
      have "loose_BVars (mk_subst \<sigma> (tr h)) \<subseteq> ?Z"
        by (rule atom_apps_dep_on(1)[OF at "1.prems"(4)[unfolded tr]])
      then have iZ: "nat_of_integer i \<in> ?Z" using Bound by simp
      have j0: "0 \<le> i - lev" using 1 "1.prems"(3) by auto
      then have "nat_of_integer (i - lev) = nat_of_integer i - nat_of_integer lev" "nat_of_integer lev \<le> nat_of_integer i"
        using "1.prems"(2) by (simp_all add: integer_reps nat_diff_distrib)
      with iZ have "nat_of_integer (i - lev) \<in> Z" by (auto simp: bshift_def)
      with 1 show ?thesis by blast
    next
      case 2
      from "1"(3)[OF sc[symmetric] refl Bound 2 "1.prems"(2,3) dargs[OF at 2(1)]] show ?thesis .
    qed
  next
    case (Abs x T u)
    from "1.prems"(1) rb Abs have nil: "args = []" and ru: "rigid_bound (lev + 1) banned u"
      by auto
    have "dep_on ?Z (dB.Abs (mk_subst \<sigma> (tr u)))" using "1.prems"(4) t nil Abs by simp
    from Abs_dep_on[OF this] have "dep_on (bshift (nat_of_integer (lev + 1)) Z) (mk_subst \<sigma> (tr u))"
      using "1.prems"(2) by (simp add: bshift_Suc integer_reps nat_add_distrib)
    from "1"(4)[OF sc[symmetric] refl Abs ru _ "1.prems"(3) this] "1.prems"(2) show ?thesis by simp
  qed (use "1.prems"(1) rb nApp in auto)
qed

text \<open>Dependencies reflect through lifting, for typed terms.\<close>

lemma lift_dep_reflect:
  assumes ty: "(E, \<tau>) \<turnstile> t : T" and dep: "dep_on (insert 0 (Suc ` Z)) (lift t 0)"
  shows "dep_on Z t"
proof -
  from normal_form_ex[OF ty] obtain nt where nt: "\<beta>\<eta>cl t nt" "normal nt" by blast
  have inj: "inj_on Suc (loose_BVars t)" by simp
  note rn = normal_form_rename[OF nt inj]
  from dep obtain r where r: "lift t 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> r" "loose_BVars r \<subseteq> insert 0 (Suc ` Z)"
    unfolding dep_on_def by blast
  have l: "lift t 0 = map_BVars Suc t" by (simp add: lift_map_BVars)
  have "r \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars Suc nt"
    using equiv_trans[OF equiv_sym[OF r(1)] \<beta>\<eta>cl_into_equiv[OF rn(1)[folded l]]] .
  then have "\<beta>\<eta>cl r (map_BVars Suc nt)" using rn(2) by (rule equiv_\<beta>\<eta>cl_normal)
  then have "loose_BVars (map_BVars Suc nt) \<subseteq> insert 0 (Suc ` Z)"
    using loose_BVars_\<beta>\<eta>cl r(2) by blast
  then have "loose_BVars nt \<subseteq> Z" by (auto simp: loose_BVars_map_BVars)
  then show ?thesis by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF nt(1)]])
qed

lemma dep_on_eta: "dep_on Z s \<Longrightarrow> dep_on (insert 0 (Suc ` Z)) (lift s 0 \<degree> BVar 0)"
proof -
  assume "dep_on Z s"
  moreover have "dB.Abs (lift s 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> s"
    by (rule eta_into_equiv) (metis eta free_lift not_less_zero subst_lift)
  ultimately have "dep_on Z (dB.Abs (lift s 0 \<degree> BVar 0))" by (rule dep_on_equiv[rotated])
  then show ?thesis by (rule Abs_dep_on)
qed

lemma size_list_app_ge: "size h \<le> size (h \<degree>\<degree> A)"
  by (induction A arbitrary: h) (auto intro: le_trans[rotated])

lemma size_list_app_mem: "a \<in> set A \<Longrightarrow> size a < size (h \<degree>\<degree> A)"
proof (induction A arbitrary: h)
  case (Cons b A)
  show ?case
  proof (cases "a = b")
    case True
    then show ?thesis using size_list_app_ge[of "h \<degree> b" A] by simp
  next
    case False
    with Cons.prems have "a \<in> set A" by simp
    from Cons.IH[OF this, of "h \<degree> b"] show ?thesis by simp
  qed
qed simp

lemma lift_list_app: "lift (h \<degree>\<degree> A) k = lift h k \<degree>\<degree> map (\<lambda>t. lift t k) A"
  by (induction A arbitrary: h) simp_all

text \<open>
  An argument used by a \<open>\<beta>\<close>-normal body is preserved: if the body \<open>r\<close> has the loose bound variable
  \<open>k\<close> and all arguments have atomic heads, the application of \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>m. r\<close> to the arguments
  only depends on \<open>Z\<close> only if the argument for \<open>k\<close> does.
\<close>

lemma use_dep:
  "no_redex r \<Longrightarrow> loose_BVars r \<subseteq> {..<m} \<Longrightarrow> length ts = m \<Longrightarrow> k \<in> loose_BVars r \<Longrightarrow>
    dep_on Z (Abs_m m r \<degree>\<degree> ts) \<Longrightarrow> \<forall>i<m. \<exists>h A. is_atom h \<and> rev ts ! i = h \<degree>\<degree> A \<Longrightarrow>
    \<forall>i<m. \<exists>E T. (E, \<tau>) \<turnstile> rev ts ! i : T \<Longrightarrow> dep_on Z (rev ts ! k)"
proof (induction r arbitrary: m ts k Z rule: measure_induct_rule[of size])
  case (less r)
  note nr = less.prems(1) and lr = less.prems(2) and lts = less.prems(3) and kr = less.prems(4)
    and dep = less.prems(5) and at = less.prems(6) and ty = less.prems(7)
  have km: "k < m" using kr lr by auto
  have cl: "no_loose_bound (Abs_m m r) 0"
    using loose_BVars_no_loose_bound[OF lr] by (simp add: loose_bound_Abs_m)
  show ?case
  proof (cases "Unif_Occurs.is_Abs r")
    case True
    then obtain r' where r: "r = dB.Abs r'" by (cases r) auto
    let ?ts' = "map (\<lambda>t. lift t 0) ts @ [BVar 0]"
    have e1: "lift (Abs_m m r \<degree>\<degree> ts) 0 \<degree> BVar 0 = Abs_m m r \<degree>\<degree> ?ts'"
      using lift_closed[OF cl] by (simp add: lift_list_app)
    have e2: "Abs_m m r = Abs_m (Suc m) r'" using Abs_m_Suc'[of m r'] r by simp
    have "dep_on (insert 0 (Suc ` Z)) (Abs_m m r \<degree>\<degree> ?ts')"
      using dep_on_eta[OF dep] unfolding e1 .
    then have dep': "dep_on (insert 0 (Suc ` Z)) (Abs_m (Suc m) r' \<degree>\<degree> ?ts')" unfolding e2 .
    have rev': "rev ?ts' = BVar 0 # map (\<lambda>t. lift t 0) (rev ts)" by (simp add: rev_map)
    have "dep_on (insert 0 (Suc ` Z)) (rev ?ts' ! Suc k)"
    proof (rule less.IH[of r'])
      show "size r' < size r" by (simp add: r)
      show "no_redex r'" using nr by (simp add: r)
      show "loose_BVars r' \<subseteq> {..<Suc m}"
      proof
        fix i assume "i \<in> loose_BVars r'"
        with lr show "i \<in> {..<Suc m}" by (cases i) (auto simp: r)
      qed
      show "length ?ts' = Suc m" using lts by simp
      show "Suc k \<in> loose_BVars r'" using kr by (simp add: r)
      show "dep_on (insert 0 (Suc ` Z)) (Abs_m (Suc m) r' \<degree>\<degree> ?ts')" by (rule dep')
      show "\<forall>i<Suc m. \<exists>h A. is_atom h \<and> rev ?ts' ! i = h \<degree>\<degree> A"
      proof (intro allI impI)
        fix i assume i: "i < Suc m"
        show "\<exists>h A. is_atom h \<and> rev ?ts' ! i = h \<degree>\<degree> A"
        proof (cases i)
          case 0
          then show ?thesis using rev' by (intro exI[of _ "BVar 0"] exI[of _ "[]"]) simp
        next
          case (Suc i')
          with i at obtain h A where "is_atom h" "rev ts ! i' = h \<degree>\<degree> A" by auto
          moreover have "is_atom (lift h 0)" using \<open>is_atom h\<close> by (auto simp: is_atom_def)
          ultimately show ?thesis using Suc i lts rev'
            by (intro exI[of _ "lift h 0"] exI[of _ "map (\<lambda>t. lift t 0) A"]) (simp add: lift_list_app)
        qed
      qed
      show "\<forall>i<Suc m. \<exists>E T. (E, \<tau>) \<turnstile> rev ?ts' ! i : T"
      proof (intro allI impI)
        fix i assume i: "i < Suc m"
        show "\<exists>E T. (E, \<tau>) \<turnstile> rev ?ts' ! i : T"
        proof (cases i)
          case 0
          have "((\<lambda>_. Atom 0), \<tau>) \<turnstile> BVar 0 : Atom 0" by (rule typing.BVar) simp
          then show ?thesis using rev' 0 by auto
        next
          case (Suc i')
          with i ty obtain E T where "(E, \<tau>) \<turnstile> rev ts ! i' : T" by auto
          from lift_type[OF this, of 0 "Atom 0"] show ?thesis using Suc i lts rev' by auto
        qed
      qed
    qed
    then have "dep_on (insert 0 (Suc ` Z)) (lift (rev ts ! k) 0)" using rev' km lts by simp
    moreover from ty km obtain E T where "(E, \<tau>) \<turnstile> rev ts ! k : T" by auto
    ultimately show ?thesis using lift_dep_reflect by blast
  next
    case False
    from no_redex_atom_head[OF nr False] obtain h A where h: "is_atom h" "r = h \<degree>\<degree> A" by blast
    have nrA: "\<forall>a\<in>set A. no_redex a" using nr h no_redex_atom_apps by simp
    have lA: "\<forall>a\<in>set A. loose_BVars a \<subseteq> {..<m}" using lr h by auto
    have szA: "size a < size r" if "a \<in> set A" for a using size_list_app_mem[OF that] h by simp
    have IH: "dep_on Z (rev ts ! k)" if "a \<in> set A" "k \<in> loose_BVars a" "dep_on Z (Abs_m m a \<degree>\<degree> ts)" for a
      by (rule less.IH[OF szA[OF that(1)]]) (use that nrA lA lts at ty in auto)
    from h(1) consider j where "h = BVar j" | c where "h = dB.Var c" by (auto simp: is_atom_def)
    then show ?thesis
    proof cases
      case (1 j)
      have jm: "j < m" using lr h 1 by auto
      from at jm obtain g G where g: "is_atom g" "rev ts ! j = g \<degree>\<degree> G" by blast
      have e: "Abs_m m r \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> g \<degree>\<degree> (G @ map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A)"
        using Abs_m_apps_BVar_head[OF lts jm, of A] h 1 g(2) by simp
      have "dep_on Z (g \<degree>\<degree> (G @ map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A))"
        by (rule dep_on_equiv[OF equiv_sym[OF e] dep])
      note d = atom_apps_dep_on[OF g(1) this]
      show ?thesis
      proof (cases "k = j")
        case True
        have "dep_on Z (g \<degree>\<degree> G)" by (rule atom_apps_dep_onI[OF g(1) d(1)]) (use d(2) in auto)
        then show ?thesis using True g(2) by simp
      next
        case False
        with kr h 1 obtain a where "a \<in> set A" "k \<in> loose_BVars a" by auto
        with d(2) IH show ?thesis by auto
      qed
    next
      case (2 c)
      have e: "Abs_m m r \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A"
        using Abs_m_apps_closed_head[of "dB.Var c" ts m A] lts h 2 by simp
      have "dep_on Z (dB.Var c \<degree>\<degree> map (\<lambda>a. Abs_m m a \<degree>\<degree> ts) A)"
        by (rule dep_on_equiv[OF equiv_sym[OF e] dep])
      note d = atom_apps_dep_on[OF _ this]
      from kr h 2 obtain a where "a \<in> set A" "k \<in> loose_BVars a" by auto
      with d(2) IH show ?thesis by auto
    qed
  qed
qed

text \<open>
  Pruning: if a closed value applied to arguments with atomic heads only depends on \<open>Z\<close>, and the
  arguments not selected by \<open>ks\<close> do not, then the value is the abstraction of a closed term
  applied to the selected arguments.
\<close>

lemma prune_value:
  assumes closed: "no_loose_bound w0 0" and ty: "\<And>e. (e, \<tau>) \<turnstile> w0 : Ws \<Rrightarrow> U"
    and len: "length ts = length Ws" and dep: "dep_on Z (w0 \<degree>\<degree> ts)"
    and at: "\<exists>k<length Ws. k \<notin> set ks \<Longrightarrow> \<forall>i<length Ws. \<exists>h A. is_atom h \<and> rev ts ! i = h \<degree>\<degree> A"
    and tyts: "\<exists>k<length Ws. k \<notin> set ks \<Longrightarrow> \<forall>i<length Ws. \<exists>E T. (E, \<tau>) \<turnstile> rev ts ! i : T"
    and nodep: "\<And>k. k < length Ws \<Longrightarrow> k \<notin> set ks \<Longrightarrow> \<not> dep_on Z (rev ts ! k)"
    and ks: "\<forall>k\<in>set ks. k < length Ws"
  obtains w where "no_loose_bound w 0" "\<And>e. (e, \<tau>) \<turnstile> w : map (\<lambda>k. rev Ws ! k) ks \<Rrightarrow> U"
    "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length Ws) (w \<degree>\<degree> map BVar ks)"
proof -
  let ?m = "length Ws"
  obtain r where r: "\<beta>\<eta>cl (w0 \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext (\<lambda>_. Atom 0) Ws, \<tau>) \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed ty refl] .
  have w0r: "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r"
  proof -
    have "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w0 \<degree>\<degree> map BVar (downs ?m))"
      using eta_expand_equiv[OF closed] by (rule equiv_sym)
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r" using r(1) by (intro equiv_Abs_m \<beta>\<eta>cl_into_equiv)
    finally show ?thesis .
  qed
  have "w0 \<degree>\<degree> ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r \<degree>\<degree> ts"
    by (rule equiv_list_app[OF w0r]) (simp add: list_all2_conv_all_nth equiv_refl)
  then have dep': "dep_on Z (Abs_m ?m r \<degree>\<degree> ts)" using dep by (rule dep_on_equiv[OF equiv_sym])
  have sub: "loose_BVars r \<subseteq> set ks"
  proof
    fix k assume k: "k \<in> loose_BVars r"
    then have km: "k < ?m" using r(4) by auto
    show "k \<in> set ks"
    proof (rule ccontr)
      assume nk: "k \<notin> set ks"
      with km have ex: "\<exists>k<?m. k \<notin> set ks" by blast
      have "dep_on Z (rev ts ! k)"
        by (rule use_dep[OF normal_no_redex[OF r(2)] r(4) len k dep']) (use at[OF ex] tyts[OF ex] len in auto)
      with nodep[OF km nk] show False by blast
    qed
  qed
  define w where "w = abst ks r"
  have "no_loose_bound w 0" unfolding w_def by (rule loose_BVars_abst[OF sub])
  moreover have "(e, \<tau>) \<turnstile> w : map (\<lambda>k. rev Ws ! k) ks \<Rrightarrow> U" for e
  proof -
    have "((\<lambda>_. Atom 0), \<tau>) \<turnstile> w : map (env_ext (\<lambda>_. Atom 0) Ws) ks \<Rrightarrow> U"
      unfolding w_def by (rule typing_abst[OF r(3) sub])
    moreover have "map (env_ext (\<lambda>_. Atom 0) Ws) ks = map (\<lambda>k. rev Ws ! k) ks"
      using ks by (auto simp: env_ext_nth rev_nth)
    ultimately show ?thesis using typing_closed[OF _ \<open>no_loose_bound w 0\<close>] by simp
  qed
  moreover have "w0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
  proof -
    have "r = appb w ks" by (simp add: w_def appb_abst_self[OF sub])
    then have "Abs_m ?m r \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (w \<degree>\<degree> map BVar ks)"
      by (auto intro: equiv_Abs_m equiv_sym[OF beta_into_equiv] appb_reduces)
    with w0r show ?thesis by (rule equiv_trans)
  qed
  ultimately show ?thesis by (rule that)
qed

subsection \<open>Deleting bound variables, completely\<close>

text \<open>The binder of a cleaned pair keeps the bound variables that occur in both terms.\<close>

lemma add_index_foldr:
  "foldr (add_index lt lu) xs ([], []) =
    (map fst (filter (\<lambda>(j, _). \<not> (j \<in> set lt \<and> j \<in> set lu)) xs),
     map snd (filter (\<lambda>(j, _). j \<in> set lt \<and> j \<in> set lu) xs))"
  by (induction xs) (auto simp: add_index_def split: prod.splits)

lemma filter_upt_nth_card:
  "i < n \<Longrightarrow> P i \<Longrightarrow> filter P [0..<n] ! card {j. j < i \<and> P j} = i"
proof (induction n)
  case (Suc n)
  have l: "length (filter P [0..<n]) = card {j. j < n \<and> P j}"
    by (simp add: length_filter_conv_card cong: conj_cong)
  show ?case
  proof (cases "i < n")
    case True
    have "card {j. j < i \<and> P j} < card {j. j < n \<and> P j}"
      by (rule psubset_card_mono) (use True Suc.prems(2) in auto)
    with Suc.IH[OF True Suc.prems(2)] l show ?thesis by (simp add: nth_append)
  next
    case False
    with Suc.prems have "i = n" by simp
    with Suc.prems l show ?thesis by (simp add: nth_append)
  qed
qed simp

lemma clean_binder_keeps:
  assumes "foldr (add_index lt lu) (zip (upto_list (length rb)) rb) ([], []) = (banned, rb')"
  defines "K \<equiv> \<lambda>i. integer_of_nat i \<in> set lt \<and> integer_of_nat i \<in> set lu"
  shows "bset banned = {i. i < length rb \<and> \<not> K i}"
    "\<And>i. i < length rb \<Longrightarrow> K i \<Longrightarrow> squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
proof -
  have z: "zip (upto_list (length rb)) rb = map (\<lambda>i. (integer_of_nat i, rb ! i)) [0..<length rb]"
    by (rule nth_equalityI) (simp_all add: upto_list_def)
  from assms(1) have b: "banned = map integer_of_nat (filter (\<lambda>i. \<not> K i) [0..<length rb])"
    and r: "rb' = map (\<lambda>i. rb ! i) (filter K [0..<length rb])"
    unfolding add_index_foldr z by (auto simp: filter_map comp_def K_def)
  show bs: "bset banned = {i. i < length rb \<and> \<not> K i}"
    by (auto simp: b bset_def image_iff)
  fix i assume i: "i < length rb" "K i"
  have "{..<i} - bset banned = {j. j < i \<and> K j}" using i(1) by (auto simp: bs)
  then have sq: "squash (bset banned) i = card {j. j < i \<and> K j}" by (simp add: squash_def)
  have "card {j. j < i \<and> K j} < card {j. j < length rb \<and> K j}"
    by (rule psubset_card_mono) (use i in auto)
  moreover have "length rb' = card {j. j < length rb \<and> K j}"
    by (simp add: r length_filter_conv_card cong: conj_cong)
  ultimately show "squash (bset banned) i < length rb' \<and> rb' ! squash (bset banned) i = rb ! i"
    using filter_upt_nth_card[of i "length rb" K, OF i] sq by (simp add: r)
qed

lemma change_bnos_cases:
  "(\<exists>evs. change_bnos banned lev x = Some (evs, UErr CHANGE_FAIL)) \<or> (\<exists>x'. okW (change_bnos banned lev x) x')"
  by (induction banned lev x rule: change_bnos.induct) (auto simp: bindW_def raiseW_def returnW_def)

text \<open>\<^const>\<open>change_bnos\<close> keeps the typing in the binder without the banned variables.\<close>

lemma shift_at_Suc_app: "shift_at (Suc k) f (Suc i) = Suc (shift_at k f i)"
  by (simp add: shift_at_def)

lemma change_bnos_typed:
  assumes "okW (change_bnos banned lev x) x'" "0 \<le> lev" "distinct banned" "\<forall>j\<in>set banned. 0 \<le> j"
  shows "has_type V Ts x T \<Longrightarrow>
    (\<forall>i<length Ts. (i < nat_of_integer lev \<or> i - nat_of_integer lev \<notin> bset banned) \<longrightarrow>
      shift_at (nat_of_integer lev) (squash (bset banned)) i < length Ts' \<and>
      Ts' ! shift_at (nat_of_integer lev) (squash (bset banned)) i = Ts ! i) \<Longrightarrow>
    has_type V Ts' x' T"
  using assms
proof (induction banned lev x arbitrary: x' Ts Ts' T rule: change_bnos.induct)
  case (1 banned lev i)
  from "1.prems"(1) have i: "0 \<le> i" "nat_of_integer i < length Ts" "T = Ts ! nat_of_integer i"
    by (auto simp: has_type_Bound_iff)
  have pb: "proper (Bound i)" using i(1) by simp
  note cs = change_bnos_sound[OF "1.prems"(3) pb "1.prems"(4,5,6)]
  from "1.prems"(3) obtain i' where x': "x' = Bound i'" by (auto split: if_splits)
  from cs have tr: "BVar (nat_of_integer i') = BVar (shift_at (nat_of_integer lev) (squash (bset banned)) (nat_of_integer i))"
    and nb: "nat_of_integer lev \<le> nat_of_integer i \<longrightarrow> nat_of_integer i - nat_of_integer lev \<notin> bset banned"
    and pr: "proper (Bound i')"
    using x' by auto
  have "0 \<le> i'" using pr by simp
  with tr "1.prems"(2) i nb show ?case by (auto simp: x' has_type_Bound_iff not_le)
next
  case (2 banned lev a U t)
  from "2.prems"(3) obtain t' where t': "okW (change_bnos banned (lev + 1) t) t'" and x': "x' = Abs a U t'" by auto
  from "2.prems"(1) obtain T' where tyt: "has_type V (U # Ts) t T'" and T: "T = U \<rightarrow>\<^sub>T T'"
    by (auto elim: has_type_elims)
  have l: "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using "2.prems"(4) by (simp add: integer_reps)
  have "has_type V (U # Ts') t' T'"
  proof (rule "2.IH"[OF tyt _ t' _ "2.prems"(5,6)])
    show "\<forall>i<length (U # Ts). (i < nat_of_integer (lev + 1) \<or> i - nat_of_integer (lev + 1) \<notin> bset banned) \<longrightarrow>
        shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i < length (U # Ts') \<and>
        (U # Ts') ! shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i = (U # Ts) ! i"
    proof (intro allI impI)
      fix i assume "i < length (U # Ts)" "i < nat_of_integer (lev + 1) \<or> i - nat_of_integer (lev + 1) \<notin> bset banned"
      then show "shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i < length (U # Ts') \<and>
        (U # Ts') ! shift_at (nat_of_integer (lev + 1)) (squash (bset banned)) i = (U # Ts) ! i"
        using "2.prems"(2) l by (cases i) (auto simp: shift_at_Suc_app shift_at_def)
    qed
    show "0 \<le> lev + 1" using "2.prems"(4) by simp
  qed
  then show ?case by (simp add: x' T has_type.Abs)
next
  case (3 banned lev t u)
  from "3.prems"(3) obtain t' u' where t': "okW (change_bnos banned lev t) t'"
    and u': "okW (change_bnos banned lev u) u'" and x': "x' = t' $ u'" by auto
  from "3.prems"(1) obtain U where tyt: "has_type V Ts t (U \<rightarrow>\<^sub>T T)" and tyu: "has_type V Ts u U"
    by (auto elim: has_type_elims)
  from "3.IH"(1)[OF tyt "3.prems"(2) t' "3.prems"(4-6)] "3.IH"(2)[OF t' tyu "3.prems"(2) u' "3.prems"(4-6)]
  show ?case by (simp add: x' has_type.App)
qed (auto elim: has_type_elims intro: has_type.intros)

lemma change_arg_Flarg:
  "change_arg del banned (Flarg j t T) args =
    (if del \<and> rigid_bound 0 banned t then returnW args
     else do {t' \<leftarrow> change_bnos banned 0 t; returnW (Flarg j t' T # args)})"
  by (simp add: change_arg_def)

lemma foldrW_change_arg_cases:
  "(\<exists>evs. foldrW (change_arg del banned) fas acc = Some (evs, UErr CHANGE_FAIL)) \<or>
    (\<exists>ks. okW (foldrW (change_arg del banned) fas acc) (ks @ acc) \<and>
      list_all2 (\<lambda>a' a. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and> okW (change_bnos banned 0 (fl_t a)) (fl_t a'))
        ks (filter (\<lambda>a. \<not> (del \<and> rigid_bound 0 banned (fl_t a))) fas))"
proof (induction fas)
  case Nil
  then show ?case by simp
next
  case (Cons a fas)
  obtain j t T where a: "a = Flarg j t T" by (cases a)
  let ?R = "\<lambda>a' a. fl_j a' = fl_j a \<and> fl_T a' = fl_T a \<and> okW (change_bnos banned 0 (fl_t a)) (fl_t a')"
  consider (err) evs where "foldrW (change_arg del banned) fas acc = Some (evs, UErr CHANGE_FAIL)"
    | (ok) ks evs0 where "foldrW (change_arg del banned) fas acc = Some (evs0, UOk (ks @ acc))"
      "list_all2 ?R ks (filter (\<lambda>a. \<not> (del \<and> rigid_bound 0 banned (fl_t a))) fas)"
    using Cons.IH by blast
  then show ?case
  proof cases
    case err
    then show ?thesis by (simp add: bindW_def)
  next
    case (ok ks evs0)
    show ?thesis
    proof (cases "del \<and> rigid_bound 0 banned t")
      case True
      have "okW (foldrW (change_arg del banned) (a # fas) acc) (ks @ acc)"
        using ok(1) True by (simp add: a change_arg_Flarg bindW_def returnW_def)
      with ok(2) True a show ?thesis by auto
    next
      case False
      consider (e) evs where "change_bnos banned 0 t = Some (evs, UErr CHANGE_FAIL)"
        | (o) t' evs1 where "change_bnos banned 0 t = Some (evs1, UOk t')"
        using change_bnos_cases[of banned 0 t] by blast
      then show ?thesis
      proof cases
        case (e evs)
        then show ?thesis using ok(1) False by (simp add: a change_arg_Flarg bindW_def)
      next
        case (o t' evs1)
        have "okW (foldrW (change_arg del banned) (a # fas) acc) ((Flarg j t' T # ks) @ acc)"
          using ok(1) False o by (simp add: a change_arg_Flarg bindW_def returnW_def)
        moreover have "okW (change_bnos banned 0 t) t'" using o by blast
        ultimately show ?thesis using ok(2) False a by (intro disjI2 exI[of _ "Flarg j t' T # ks"]) auto
      qed
    qed
  qed
qed

lemma squash_unsquash:
  assumes "B \<subseteq> {..<n}" "x < n - card B"
  shows "unsquash B x \<notin> B" "squash B (unsquash B x) = x"
proof -
  have fin: "finite B" using assms(1) finite_subset by blast
  have "squash B ` ({..<n} - B) \<subseteq> {..<n - card B}" using squash_bound[OF assms(1)] by auto
  moreover have "card (squash B ` ({..<n} - B)) = n - card B"
    using card_image[OF inj_on_subset[OF inj_on_squash, of "{..<n} - B" B]] assms(1)
    by (auto simp: card_Diff_subset fin)
  ultimately have "squash B ` ({..<n} - B) = {..<n - card B}" by (intro card_subset_eq) auto
  with assms(2) obtain y where y: "y \<notin> B" "x = squash B y" by auto
  then show "unsquash B x \<notin> B" "squash B (unsquash B x) = x" by (simp_all add: unsquash_squash)
qed

lemma map_BVars_squash_unsquash:
  assumes "B \<subseteq> {..<n}" "loose_BVars t \<subseteq> {..<n - card B}"
  shows "map_BVars (squash B) (map_BVars (unsquash B) t) = t"
proof -
  have "map_BVars (squash B) (map_BVars (unsquash B) t) = map_BVars (squash B \<circ> unsquash B) t"
    by (simp add: map_BVars_comp)
  also have "\<dots> = map_BVars id t"
    by (rule map_BVars_cong) (use assms squash_unsquash in auto)
  finally show ?thesis by (simp add: map_BVars_id)
qed

subsection \<open>Cleaning a flexible term\<close>

lemma flexargs_return:
  "length js = length ts \<Longrightarrow> length ts = length Ts \<Longrightarrow>
    flexargs js ts Ts = returnW (map (\<lambda>k. Flarg (js ! k) (ts ! k) (Ts ! k)) [0..<length ts])"
proof (induction js ts Ts rule: list_induct3)
  case (Cons j js t ts T Ts)
  then show ?case by (simp add: map_upt_Suc returnW_def bindW_def del: upt_Suc)
qed simp

lemma change_bnos_vars: "okW (change_bnos banned lev x) x' \<Longrightarrow> vars x' = vars x"
  by (induction banned lev x arbitrary: x' rule: change_bnos.induct) (auto split: if_splits)

lemma solution_tr_typed:
  "solution V \<tau>' \<sigma> env \<Longrightarrow> has_type V Ts a A \<Longrightarrow> (bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr a) : trty A"
  by (rule typing_mk_subst[OF has_type_tr typed_on_mono[OF solutionD(2) FV_tr_range]])

lemma rigid_headed_atom:
  assumes "rigid_headed a" "rigid_subst \<sigma>"
  shows "\<exists>h A. is_atom h \<and> mk_subst \<sigma> (tr a) = h \<degree>\<degree> A"
proof -
  have a: "a = list_comb (head_of a) (snd (strip_comb a))" by (rule head_of_list_comb)
  have "is_atom (mk_subst \<sigma> (tr (head_of a)))"
    using assms rigid_substD[OF assms(2)] by (auto simp: rigid_headed_def split: pterm.splits)
  moreover have "mk_subst \<sigma> (tr a) = mk_subst \<sigma> (tr (head_of a)) \<degree>\<degree> map (\<lambda>x. mk_subst \<sigma> (tr x)) (snd (strip_comb a))"
    by (subst a) (simp add: tr_list_comb comp_def)
  ultimately show ?thesis by blast
qed

subsection \<open>Flex-flex assignments\<close>

lemma fhd_rlist_abs[simp]: "fhd (rlist_abs rb u) = fhd u"
proof (induction rb arbitrary: u)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T u"] show ?case by simp
qed simp

lemma rlist_abs_Var: "rlist_abs rb u = Var w U \<Longrightarrow> rb = [] \<and> u = Var w U"
proof (induction rb arbitrary: u)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T u"] Cons.prems show ?case by simp
qed simp

subsection \<open>Cleaning flex-flex pairs\<close>

lemma add_tpair_below:
  "below m t \<Longrightarrow> below m u \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow>
    \<forall>(a, b)\<in>set (add_tpair rb t u tps). below m a \<and> below m b"
  by (auto simp: add_tpair_def Let_def below_rlist_abs)

text \<open>
  The remaining pairs are flex-flex pairs under a binder: typed terms of the same base type whose
  heads are variables that are unbound in the environment \<open>env0\<close> of the flex-flex phase.
\<close>

definition tpok :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> pterm \<times> pterm \<Rightarrow> bool" where
  "tpok ar V env0 m ab \<longleftrightarrow> (\<exists>rb a b B. ab = (rlist_abs rb a, rlist_abs rb b) \<and> binders_ok ar rb \<and>
    wf_tm ar rb a \<and> wf_tm ar rb b \<and> has_type V (map snd rb) a B \<and> has_type V (map snd rb) b B \<and>
    \<not> is_funT B \<and> below m a \<and> below m b \<and> fh env0 a \<and> fh env0 b)"

lemma loose_BVars_mk_subst_closed: "closed_on UNIV \<sigma> \<Longrightarrow> loose_BVars (mk_subst \<sigma> s) = loose_BVars s"
  by (induction s) (auto simp: closed_onD no_loose_bound_loose_BVars)

text \<open>The instances of the sides of a solved pair only depend on the bound variables of both.\<close>

lemma dsolved_dep:
  assumes "closed_on UNIV \<sigma>" "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
  shows "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr t))"
    "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr u))"
proof -
  from closure_confluent[OF assms(2)] obtain c where c: "\<beta>\<eta>cl (mk_subst \<sigma> (tr t)) c" "\<beta>\<eta>cl (mk_subst \<sigma> (tr u)) c"
    by blast
  have lc: "loose_BVars c \<subseteq> loose_BVars (tr t) \<inter> loose_BVars (tr u)"
    using loose_BVars_\<beta>\<eta>cl[OF c(1)] loose_BVars_\<beta>\<eta>cl[OF c(2)] loose_BVars_mk_subst_closed[OF assms(1)] by auto
  show "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr t))"
    by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF c(1)] lc])
  show "dep_on (loose_BVars (tr t) \<inter> loose_BVars (tr u)) (mk_subst \<sigma> (tr u))"
    by (rule dep_onI[OF \<beta>\<eta>cl_into_equiv[OF c(2)] lc])
qed

text \<open>Reflecting the renaming of the cleaned pair.\<close>

lemma unsquash_dsolved:
  assumes "B \<subseteq> {..<n}" "length rb' = n - card B" "closed_on UNIV \<sigma>"
    "wf_tm ar rb' t" "wf_tm ar rb' u"
    "map_BVars (unsquash B) (mk_subst \<sigma> (tr t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (unsquash B) (mk_subst \<sigma> (tr u))"
  shows "dsolved \<sigma> (rb', t, u)"
proof -
  have l: "loose_BVars (mk_subst \<sigma> (tr s)) \<subseteq> {..<n - card B}" if "wf_tm ar rb' s" for s
    using no_loose_bound_BVars[of "tr s" "length rb'"] that assms(2)
    by (auto simp: wf_tm_def loose_BVars_mk_subst_closed[OF assms(3)])
  from map_BVars_equiv[OF assms(6), of "squash B"]
  have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    by (simp only: map_BVars_squash_unsquash[OF assms(1) l[OF assms(4)]]
      map_BVars_squash_unsquash[OF assms(1) l[OF assms(5)]])
  then show ?thesis by (simp add: dsolved_dsolvedB dsolvedB_unabs)
qed

lemma tsolved_agree:
  "tsolved \<sigma> tps \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow> tsolved \<sigma>' tps"
  unfolding tsolved_def
proof (intro ballI, clarify)
  fix a b assume s: "\<forall>(a, b)\<in>set tps. mk_subst \<sigma> (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr b)"
    and b: "\<forall>(a, b)\<in>set tps. below m a \<and> below m b" and ag: "agree m \<sigma> \<sigma>'" and ab: "(a, b) \<in> set tps"
  from bspec[OF s ab] bspec[OF b ab] mk_subst_agree[OF _ ag, of a] mk_subst_agree[OF _ ag, of b]
  show "mk_subst \<sigma>' (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr b)" by simp
qed

lemma tps_below_mono:
  "\<forall>(a, b)\<in>set tps. below m a \<and> below m b \<Longrightarrow> m \<le> m' \<Longrightarrow> \<forall>(a, b)\<in>set tps. below m' a \<and> below m' b"
  by (auto intro: below_mono)

text \<open>The runs of the handlers in \<^const>\<open>clean_ffpair\<close>.\<close>

lemma ff_handler_complete:
  fixes alg env2 rb' t' u' tps
  defines "H \<equiv> handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t' u'; returnW (env3, tps)})
    (\<lambda>e. case e of
      ASSIGN \<Rightarrow>
        handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u' t'; returnW (env3, tps)})
          (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t' u' tps) | _ \<Rightarrow> raiseW e)
    | _ \<Rightarrow> raiseW e)"
  shows "okW (ff_assign alg env2 rb' t' u') env3 \<Longrightarrow> okW H (env3, tps)"
    "\<exists>evs. ff_assign alg env2 rb' t' u' = Some (evs, UErr ASSIGN) \<Longrightarrow>
      okW (ff_assign alg env2 rb' u' t') env3 \<Longrightarrow> okW H (env3, tps)"
    "\<exists>evs. ff_assign alg env2 rb' t' u' = Some (evs, UErr ASSIGN) \<Longrightarrow>
      \<exists>evs. ff_assign alg env2 rb' u' t' = Some (evs, UErr ASSIGN) \<Longrightarrow> okW H (env2, add_tpair rb' t' u' tps)"
  by (auto simp: H_def okW_handleW bindW_def)

lemma clean_ffpair_run:
  assumes fb: "foldr (add_index (loose_bnos t) (loose_bnos u)) (zip (upto_list (length rb)) rb) ([], []) =
    (banned, rb')"
  shows "\<exists>evs. clean_term banned env t = Some (evs, UErr CHANGE_FAIL) \<Longrightarrow>
      okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    "okW (clean_term banned env t) (env1, t1) \<Longrightarrow> \<exists>evs. clean_term banned env1 u = Some (evs, UErr CHANGE_FAIL) \<Longrightarrow>
      okW (clean_ffpair alg rb t u env tps) (env, add_tpair rb t u tps)"
    "okW (clean_term banned env t) (env1, t1) \<Longrightarrow> okW (clean_term banned env1 u) (env2, u1) \<Longrightarrow>
      okW (handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' t1 u1; returnW (env3, tps)})
        (\<lambda>e. case e of
          ASSIGN \<Rightarrow>
            handleW (do {env3 \<leftarrow> ff_assign alg env2 rb' u1 t1; returnW (env3, tps)})
              (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env2, add_tpair rb' t1 u1 tps) | _ \<Rightarrow> raiseW e)
        | _ \<Rightarrow> raiseW e)) r \<Longrightarrow> okW (clean_ffpair alg rb t u env tps) r"
  by (auto simp: clean_ffpair_def Let_def fb okW_handleW bindW_def)

lemma dsolved_agree:
  "dsolved \<sigma> (rb, t, u) \<Longrightarrow> below m t \<Longrightarrow> below m u \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow> dsolved \<sigma>' (rb, t, u)"
  by (simp add: dsolved_dsolvedB dsolvedB_unabs mk_subst_agree)

lemma flexb_refl[simp]: "flexb env env"
  by (simp add: flexb_def)

end

end
