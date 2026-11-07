section \<open>Strong Normalization of Well-Typed Pure Terms\<close>

theory Pure_SN
  imports Pure_Typing "HOL-Proofs-Lambda.ListOrder"
begin

text \<open>
  Well-typed Pure terms terminate under \<open>\<beta>\<close>-reduction, following
  \<^file>\<open>~~/src/HOL/Proofs/Lambda/ListApplication.thy\<close>,
  \<^file>\<open>~~/src/HOL/Proofs/Lambda/ListBeta.thy\<close>,
  \<^file>\<open>~~/src/HOL/Proofs/Lambda/InductTermi.thy\<close> and
  \<^file>\<open>~~/src/HOL/Proofs/Lambda/StrongNorm.thy\<close> (by Tobias Nipkow and Stefan Berghofer).
  The variables of the de Bruijn terms there become the atoms of Pure: constants, free and
  schematic variables, and bound variables.
\<close>


subsection \<open>Application to a list of terms\<close>

abbreviation apps :: "pterm \<Rightarrow> pterm list \<Rightarrow> pterm"  (infixl \<open>\<degree>\<degree>\<close> 150) where
  "t \<degree>\<degree> ts \<equiv> foldl App t ts"

lemma list_comb_apps: "list_comb t ts = t \<degree>\<degree> ts"
  by (simp add: list_comb_def)

fun atom :: "pterm \<Rightarrow> bool" where
  "atom (Abs _ _ _) \<longleftrightarrow> False"
| "atom (_ $ _) \<longleftrightarrow> False"
| "atom _ \<longleftrightarrow> True"

lemma atom_neq [simp]: "atom h \<Longrightarrow> h \<noteq> s $ t" "atom h \<Longrightarrow> h \<noteq> Abs a T u"
  by (auto elim: atom.elims)

lemma apps_eq_tail_conv [iff]: "(r \<degree>\<degree> ts = s \<degree>\<degree> ts) = (r = s)"
  by (induction ts rule: rev_induct) auto

lemma atom_eq_apps_conv [simp]: "atom h \<Longrightarrow> (h = s \<degree>\<degree> ss) = (h = s \<and> ss = [])"
  by (induction ss arbitrary: s) (auto elim: atom.elims)

lemma atom_apps_eq_atom_apps_conv [simp]:
  "atom h \<Longrightarrow> atom h' \<Longrightarrow> (h \<degree>\<degree> rs = h' \<degree>\<degree> ss) = (h = h' \<and> rs = ss)"
proof (induction rs arbitrary: ss rule: rev_induct)
  case Nil
  then show ?case by (cases ss rule: rev_exhaust) auto
next
  case (snoc r rs)
  then show ?case by (cases ss rule: rev_exhaust) auto
qed

lemma App_eq_foldl_conv:
  "(r $ s = t \<degree>\<degree> ts) = (if ts = [] then r $ s = t else (\<exists>ss. ts = ss @ [s] \<and> r = t \<degree>\<degree> ss))"
  by (cases ts rule: rev_exhaust) auto

lemma Abs_eq_apps_conv [iff]: "(Abs a T r = s \<degree>\<degree> ss) = (Abs a T r = s \<and> ss = [])"
  by (induction ss rule: rev_induct) auto

lemma apps_eq_Abs_conv [iff]: "(s \<degree>\<degree> ss = Abs a T r) = (s = Abs a T r \<and> ss = [])"
  by (induction ss rule: rev_induct) auto

lemma Abs_apps_eq_Abs_apps_conv [iff]:
  "(Abs a T r \<degree>\<degree> rs = Abs b U s \<degree>\<degree> ss) = (a = b \<and> T = U \<and> r = s \<and> rs = ss)"
proof (induction rs arbitrary: ss rule: rev_induct)
  case (snoc x xs)
  then show ?case by (induction ss rule: rev_induct) auto
qed auto

lemma Abs_App_neq_atom_apps [simp]: "atom h \<Longrightarrow> Abs a T s $ t \<noteq> h \<degree>\<degree> ss"
  by (induction ss arbitrary: s t rule: rev_induct) auto

lemma atom_apps_neq_Abs_apps [simp]: "atom h \<Longrightarrow> h \<degree>\<degree> ts \<noteq> Abs a T r \<degree>\<degree> ss"
proof (induction ss arbitrary: ts rule: rev_induct)
  case Nil
  then show ?case by (cases ts rule: rev_exhaust) auto
next
  case (snoc x xs)
  then show ?case by (cases ts rule: rev_exhaust) auto
qed

lemma ex_head_tail: "\<exists>ts h. t = h \<degree>\<degree> ts \<and> (atom h \<or> (\<exists>a T u. h = Abs a T u))"
proof (induction t)
  case (App t1 t2)
  then obtain ts1 h1 where "t1 = h1 \<degree>\<degree> ts1" "atom h1 \<or> (\<exists>a T u. h1 = Abs a T u)" by blast
  then show ?case by (intro exI[of _ "ts1 @ [t2]"] exI[of _ h1]) auto
qed (auto intro: exI[of _ "[]"])

lemma size_apps [simp]: "size (r \<degree>\<degree> rs) = size r + foldl (+) 0 (map size rs) + length rs"
  by (induction rs rule: rev_induct) auto

lemma lift_map [simp]: "lift (t \<degree>\<degree> ts) i = lift t i \<degree>\<degree> map (\<lambda>t. lift t i) ts"
  by (induction ts arbitrary: t) simp_all

lemma subst_map [simp]: "(t \<degree>\<degree> ts)[u/i] = t[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) ts"
  by (induction ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) $ u = t \<degree>\<degree> (ts @ [u])"
  by simp

lemma atom_lift [simp]: "atom (lift h i) \<longleftrightarrow> atom h"
  by (cases h) auto

subsection \<open>Lifting \<open>\<beta>\<close>-reduction to lists\<close>

lemma subst_preserves_beta2 [simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
proof (induction t arbitrary: r s i)
  case (Bound j)
  then show ?case by (simp add: subst_Bound r_into_rtranclp)
next
  case (App t1 t2)
  then show ?case by (simp add: rtrancl_beta_App)
next
  case (Abs a T t)
  then show ?case by (simp add: rtrancl_beta_Abs)
qed simp_all

lemma subst_preserves_beta2': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  by (induction set: rtranclp) (auto intro: rtranclp_trans)

lemma subst0_preserves_beta: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r[t/0] \<rightarrow>\<^sub>\<beta> s[t/0]"
  by simp

abbreviation list_beta :: "pterm list \<Rightarrow> pterm list \<Rightarrow> bool"  (infixl \<open>\<Rightarrow>\<^sub>\<beta>\<^sub>l\<close> 50) where
  "rs \<Rightarrow>\<^sub>\<beta>\<^sub>l ss \<equiv> step1 beta rs ss"

lemma head_atom_reduction:
  "h \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> v \<Longrightarrow> atom h \<Longrightarrow> \<exists>ss. rs \<Rightarrow>\<^sub>\<beta>\<^sub>l ss \<and> v = h \<degree>\<degree> ss"
proof (induction u \<equiv> "h \<degree>\<degree> rs" v arbitrary: rs set: beta)
  case (beta a T s t)
  then show ?case by simp
next
  case (appL s t u)
  then show ?case
    by (cases rs rule: rev_exhaust) (auto 0 3 intro: append_step1I)
next
  case (appR s t u)
  then show ?case
    by (cases rs rule: rev_exhaust) (auto 0 3 intro: disjI2 [THEN append_step1I])
next
  case (abs s t a T)
  then show ?case by (cases rs rule: rev_exhaust) auto
qed

lemma apps_betasE [consumes 1, case_names hd args redex, elim!]:
  assumes major: "r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> s"
    and cases: "\<And>r'. r \<rightarrow>\<^sub>\<beta> r' \<Longrightarrow> s = r' \<degree>\<degree> rs \<Longrightarrow> R"
      "\<And>rs'. rs \<Rightarrow>\<^sub>\<beta>\<^sub>l rs' \<Longrightarrow> s = r \<degree>\<degree> rs' \<Longrightarrow> R"
      "\<And>a T t u us. r = Abs a T t \<Longrightarrow> rs = u # us \<Longrightarrow> s = t[u/0] \<degree>\<degree> us \<Longrightarrow> R"
  shows R
proof -
  from major have
   "(\<exists>r'. r \<rightarrow>\<^sub>\<beta> r' \<and> s = r' \<degree>\<degree> rs) \<or>
    (\<exists>rs'. rs \<Rightarrow>\<^sub>\<beta>\<^sub>l rs' \<and> s = r \<degree>\<degree> rs') \<or>
    (\<exists>a T t u us. r = Abs a T t \<and> rs = u # us \<and> s = t[u/0] \<degree>\<degree> us)"
  proof (induction u \<equiv> "r \<degree>\<degree> rs" s arbitrary: r rs set: beta)
    case (beta a T s t)
    then show ?case
      by (cases rs rule: rev_exhaust) (auto simp: App_eq_foldl_conv split: if_split_asm)
  next
    case (appL s t u)
    show ?case
    proof (cases rs rule: rev_exhaust)
      case Nil
      with appL show ?thesis by auto
    next
      case (snoc ys y)
      with appL have ys: "s = r \<degree>\<degree> ys" "u = y" by auto
      from appL.hyps(2)[OF ys(1)] consider (c1) r' where "r \<rightarrow>\<^sub>\<beta> r'" "t = r' \<degree>\<degree> ys"
        | (c2) rs' where "ys \<Rightarrow>\<^sub>\<beta>\<^sub>l rs'" "t = r \<degree>\<degree> rs'"
        | (c3) a T t' u' us where "r = Abs a T t'" "ys = u' # us" "t = (t' :: pterm)[u'/0] \<degree>\<degree> us"
        by blast
      then show ?thesis
      proof cases
        case c1
        with snoc ys show ?thesis by auto
      next
        case c2
        then have "ys @ [y] \<Rightarrow>\<^sub>\<beta>\<^sub>l rs' @ [y]" by (intro append_step1I) simp
        with c2 snoc ys show ?thesis by auto
      next
        case c3
        with snoc ys show ?thesis by auto
      qed
    qed
  next
    case (appR s t u)
    then show ?case
    proof (cases rs rule: rev_exhaust)
      case (snoc ys y)
      with appR show ?thesis by (clarify, auto 0 3 intro!: exI intro: append_step1I)
    qed auto
  next
    case (abs s t a T)
    then show ?case by (cases rs rule: rev_exhaust) auto
  qed
  with cases show ?thesis by blast
qed

lemma apps_preserves_beta [simp]: "r \<rightarrow>\<^sub>\<beta> s \<Longrightarrow> r \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta> s \<degree>\<degree> ss"
  by (induction ss rule: rev_induct) auto

lemma apps_preserves_beta2 [simp]: "r \<rightarrow>\<^sub>\<beta>\<^sup>* s \<Longrightarrow> r \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta>\<^sup>* s \<degree>\<degree> ss"
  by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma apps_preserves_betas [simp]: "rs \<Rightarrow>\<^sub>\<beta>\<^sub>l ss \<Longrightarrow> r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> r \<degree>\<degree> ss"
proof (induction rs arbitrary: ss rule: rev_induct)
  case (snoc x xs)
  then show ?case by (cases ss rule: rev_exhaust) (auto dest: Snoc_step1_SnocD)
qed simp


subsection \<open>Terminating terms\<close>

inductive IT :: "pterm \<Rightarrow> bool" where
  Atom [intro]: "atom h \<Longrightarrow> listsp IT rs \<Longrightarrow> IT (h \<degree>\<degree> rs)"
| Lambda [intro]: "IT r \<Longrightarrow> IT (Abs a T r)"
| Beta [intro]: "IT ((r[s/0]) \<degree>\<degree> ss) \<Longrightarrow> IT s \<Longrightarrow> IT ((Abs a T r $ s) \<degree>\<degree> ss)"

lemma termip_reds: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> termip beta t \<Longrightarrow> termip beta t'"
  by (induction rule: rtranclp_induct) (auto intro: accp_downward)

lemma double_induction_lemma:
  fixes r s t :: pterm
  assumes "termip beta s" and "termip beta t" and "t = r[s/0] \<degree>\<degree> ss"
  shows "termip beta (Abs a T r $ s \<degree>\<degree> ss)"
  using assms
proof (induction s arbitrary: t r ss rule: accp_induct_rule)
  case (1 s)
  note s = this
  from \<open>termip beta t\<close> \<open>t = r[s/0] \<degree>\<degree> ss\<close> show ?case
  proof (induction t arbitrary: r ss rule: accp_induct_rule)
    case (1 t)
    note t = this
    show ?case
    proof (rule accp.accI)
      fix y assume "(beta\<inverse>\<inverse>) y (Abs a T r $ s \<degree>\<degree> ss)"
      then have "Abs a T r $ s \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta> y" by (rule conversepD)
      then show "termip beta y"
      proof (cases rule: apps_betasE)
        case (hd r')
        from \<open>Abs a T r $ s \<rightarrow>\<^sub>\<beta> r'\<close> show ?thesis
        proof cases
          case beta
          with hd t show ?thesis by simp
        next
          case (appL r'')
          then obtain r1 where "r \<rightarrow>\<^sub>\<beta> r1" "r'' = Abs a T r1" by auto
          then have "t \<rightarrow>\<^sub>\<beta> r1[s/0] \<degree>\<degree> ss" using t(3) by (simp add: subst0_preserves_beta)
          then have "termip beta (Abs a T r1 $ s \<degree>\<degree> ss)"
            using t(2)[of "r1[s/0] \<degree>\<degree> ss" r1 ss] by (simp add: conversep_iff[abs_def])
          with hd appL \<open>r'' = _\<close> show ?thesis by simp
        next
          case (appR s')
          have "t \<rightarrow>\<^sub>\<beta>\<^sup>* r[s'/0] \<degree>\<degree> ss" using t(3) appR by simp
          then have "termip beta (r[s'/0] \<degree>\<degree> ss)" using t(1) by (rule termip_reds)
          then have "termip beta (Abs a T r $ s' \<degree>\<degree> ss)"
            using s(2)[of s' "r[s'/0] \<degree>\<degree> ss" r ss] appR by (simp add: conversep_iff[abs_def])
          with hd appR show ?thesis by simp
        qed
      next
        case (args rs')
        then have "t \<rightarrow>\<^sub>\<beta> r[s/0] \<degree>\<degree> rs'" using t(3) by simp
        then have "termip beta (Abs a T r $ s \<degree>\<degree> rs')"
          using t(2)[of "r[s/0] \<degree>\<degree> rs'" r rs'] by (simp add: conversep_iff[abs_def])
        with args show ?thesis by simp
      next
        case redex
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma atom_apps_termi:
  "Wellfounded.accp (step1 (beta\<inverse>\<inverse>)) rs \<Longrightarrow> atom h \<Longrightarrow> termip beta (h \<degree>\<degree> rs)"
proof (induction rule: accp_induct_rule)
  case (1 x)
  show ?case
  proof (rule accp.accI)
    fix y assume "(beta\<inverse>\<inverse>) y (h \<degree>\<degree> x)"
    then have "h \<degree>\<degree> x \<rightarrow>\<^sub>\<beta> y" by (rule conversepD)
    then obtain ss where ss: "step1 beta x ss" "y = h \<degree>\<degree> ss"
      using head_atom_reduction \<open>atom h\<close> by meson
    from ss(1) have "step1 (beta\<inverse>\<inverse>) ss x" by (simp only: in_step1_converse conversep_iff)
    with 1(2) ss(2) \<open>atom h\<close> show "termip beta y" by blast
  qed
qed

lemma Abs_termi: "termip beta r \<Longrightarrow> termip beta (Abs a T r)"
proof (induction rule: accp_induct_rule)
  case (1 x)
  show ?case
  proof (rule accp.accI)
    fix y assume "(beta\<inverse>\<inverse>) y (Abs a T x)"
    then obtain x' where "x \<rightarrow>\<^sub>\<beta> x'" "y = Abs a T x'" by auto
    then show "termip beta y" using 1(2) by (blast intro: conversepI)
  qed
qed

lemma IT_implies_termi: "IT t \<Longrightarrow> termip beta t"
proof (induction set: IT)
  case (Atom h rs)
  then have "listsp (termip beta) rs" by (simp add: in_listsp_conv_set conversep_iff[abs_def])
  then show ?case using lists_accD \<open>atom h\<close> atom_apps_termi by blast
next
  case (Lambda r a T)
  from Lambda.IH show ?case by (rule Abs_termi)
next
  case (Beta r s ss a T)
  then show ?case by (blast intro: double_induction_lemma)
qed


subsection \<open>Properties of \<^const>\<open>IT\<close>\<close>

lemma lift_IT [intro!]: "IT t \<Longrightarrow> 0 \<le> i \<Longrightarrow> IT (lift t i)"
proof (induction arbitrary: i set: IT)
  case (Atom h rs)
  have "listsp IT (map (\<lambda>t. lift t i) rs)" using Atom.IH Atom.prems by (induction rs) auto
  with Atom show ?case by auto
next
  case (Lambda r a T)
  then show ?case by auto
next
  case (Beta r s ss a T)
  have "IT (lift (r[s/0] \<degree>\<degree> ss) i)" using Beta by blast
  then have "IT ((lift r (i + 1))[lift s i/0] \<degree>\<degree> map (\<lambda>t. lift t i) ss)"
    using Beta.prems by simp
  with Beta show ?case by auto
qed

lemma atom_IT [intro]: "atom h \<Longrightarrow> IT h"
  using IT.Atom[of h "[]"] by simp

lemma atom_subst_Bound: "atom h \<Longrightarrow> atom (h[Bound i/j])"
  by (cases h) (auto simp: subst_Bound)

lemma subst_Bound_IT: "IT r \<Longrightarrow> 0 \<le> j \<Longrightarrow> 0 \<le> i \<Longrightarrow> IT (r[Bound i/j])"
proof (induction arbitrary: i j set: IT)
  case (Atom h rs)
  have "listsp IT (map (\<lambda>t. t[Bound i/j]) rs)" using Atom.IH Atom.prems by (induction rs) auto
  with Atom show ?case by (auto intro: atom_subst_Bound)
next
  case (Lambda r a T)
  then show ?case by (auto simp: integer_arith)
next
  case (Beta r s ss a T)
  have "IT ((r[s/0] \<degree>\<degree> ss)[Bound i/j])" using Beta by blast
  then have "IT (r[lift (Bound i) 0 / j + 1][s[Bound i/j]/0] \<degree>\<degree> map (\<lambda>t. t[Bound i/j]) ss)"
    using Beta.prems subst_subst[of 0 j r "Bound i" s] by simp
  moreover have "lift (Bound i) 0 = Bound (i + 1)" using Beta.prems by simp
  ultimately show ?case using Beta by (auto simp: integer_arith)
qed

lemma app_Bound_IT: "IT t \<Longrightarrow> 0 \<le> i \<Longrightarrow> IT (t $ Bound i)"
proof (induction set: IT)
  case (Atom h rs)
  have "listsp IT (rs @ [Bound i])"
    using Atom by (auto intro!: listsp.intros simp: listsp_conj_eq)
  then show ?case using IT.Atom[of h "rs @ [Bound i]"] Atom by simp
next
  case (Lambda r a T)
  then show ?case
    using IT.Beta[of r "Bound i" "[]" a T] subst_Bound_IT[of r 0 i] atom_IT[of "Bound i"] by auto
next
  case (Beta r s ss a T)
  then show ?case using IT.Beta[of r s "ss @ [Bound i]" a T] by simp
qed


context signature
begin

subsection \<open>Typing of lists of terms\<close>

abbreviation funs :: "ptyp list \<Rightarrow> ptyp \<Rightarrow> ptyp"  (infixr \<open>\<Rrightarrow>\<close> 200) where
  "Ts \<Rrightarrow> T \<equiv> foldr (\<rightarrow>\<^sub>T) Ts T"

fun typings :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm list \<Rightarrow> ptyp list \<Rightarrow> bool"  (\<open>_ \<tturnstile> _ : _\<close> [50, 50, 50] 50)
where
  "e \<tturnstile> [] : Ts \<longleftrightarrow> Ts = []"
| "e \<tturnstile> (t # ts) : Ts \<longleftrightarrow> (case Ts of [] \<Rightarrow> False | T # Ts \<Rightarrow> e \<turnstile> t : T \<and> e \<tturnstile> ts : Ts)"

lemma list_app_typeD: "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> \<exists>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> ts : Ts"
proof (induction ts arbitrary: t T)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  from Cons.IH[OF Cons.prems[simplified]] obtain Ts where
    "e \<turnstile> t $ a : Ts \<Rrightarrow> T" "e \<tturnstile> ts : Ts" by blast
  then obtain T0 where "e \<turnstile> t : T0 \<rightarrow>\<^sub>T (Ts \<Rrightarrow> T)" "e \<turnstile> a : T0" "e \<tturnstile> ts : Ts" by auto
  then show ?case by (intro exI[of _ "T0 # Ts"]) simp
qed

lemma list_app_typeE:
  "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> (\<And>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> C) \<Longrightarrow> C"
  using list_app_typeD by blast

lemma list_app_typeI: "e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t \<degree>\<degree> ts : T"
  by (induction ts arbitrary: t Ts) (auto split: list.splits)

lemma lift_types: "e \<tturnstile> ts : Ts \<Longrightarrow> 0 \<le> i \<Longrightarrow> e\<langle>i:U\<rangle> \<tturnstile> map (\<lambda>t. lift t i) ts : Ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits)

lemma substs_lemma:
  "e \<turnstile> u : T \<Longrightarrow> e\<langle>i:T\<rangle> \<tturnstile> ts : Ts \<Longrightarrow> 0 \<le> i \<Longrightarrow> e \<tturnstile> map (\<lambda>t. t[u/i]) ts : Ts"
  by (induction ts arbitrary: Ts) (auto split: list.splits intro: subst_lemma)

lemma subject_reduction_beta': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_beta)


subsection \<open>Well-typed substitution preserves termination\<close>

lemma size_fun_type [simp]: "size (T \<rightarrow>\<^sub>T U) = size T + size U + 3"
  by simp

lemma subst_type_IT:
  "IT t \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> t : T \<Longrightarrow> IT u \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> 0 \<le> i \<Longrightarrow> IT (t[u/i])"
proof (induction U arbitrary: t e T u i rule: measure_induct_rule[of size])
  case (less U)
  note MI = less.IH
  from \<open>IT t\<close> show ?case
    using less.prems(2-)
  proof (induction arbitrary: e T u i set: IT)
    case (Atom h rs)
    let ?R = "\<lambda>t. \<forall>e T' u i. e\<langle>i:U\<rangle> \<turnstile> t : T' \<longrightarrow> IT u \<longrightarrow> e \<turnstile> u : U \<longrightarrow> 0 \<le> i \<longrightarrow> IT (t[u/i])"
    let ?ty = "\<lambda>t. \<exists>T'. e\<langle>i:U\<rangle> \<turnstile> t : T'"
    have R: "listsp ?R rs" using Atom.IH by (induction rs) auto
    from Atom.prems(1) obtain Ts where hT: "e\<langle>i:U\<rangle> \<turnstile> h : Ts \<Rrightarrow> T" and rsT: "e\<langle>i:U\<rangle> \<tturnstile> rs : Ts"
      by (rule list_app_typeE)
    have mapIT: "listsp IT (map (\<lambda>t. t[u/i]) xs)" if "listsp ?R xs" "e\<langle>i:U\<rangle> \<tturnstile> xs : Us" for xs Us
      using that
    proof (induction xs arbitrary: Us)
      case (Cons x xs)
      then obtain U1 Us1 where "Us = U1 # Us1" "e\<langle>i:U\<rangle> \<turnstile> x : U1" "e\<langle>i:U\<rangle> \<tturnstile> xs : Us1"
        by (cases Us) auto
      with Cons Atom.prems show ?case by (auto intro: listsp.intros)
    qed simp
    show ?case
    proof (cases "h = Bound i")
      case True
      show ?thesis
      proof (cases rs)
        case Nil
        with True Atom.prems show ?thesis by simp
      next
        case (Cons a as)
        with rsT obtain T'' Ts' where Ts: "Ts = T'' # Ts'" and aT: "e\<langle>i:U\<rangle> \<turnstile> a : T''"
          and asT: "e\<langle>i:U\<rangle> \<tturnstile> as : Ts'"
          by (cases Ts) auto
        from hT True Ts have U: "U = T'' \<rightarrow>\<^sub>T (Ts' \<Rrightarrow> T)" by auto
        with Atom.prems have uT': "e \<turnstile> u : T'' \<rightarrow>\<^sub>T (Ts' \<Rrightarrow> T)" by simp
        from R Cons have Ra: "?R a" and Ras: "listsp ?R as" by auto
        from Ra aT Atom.prems have aIT: "IT (a[u/i])" by blast
        from aT Atom.prems have aT': "e \<turnstile> a[u/i] : T''" by (blast intro: subst_lemma)
        have "IT ((lift u 0 $ Bound 0)[a[u/i]/0])"
        proof (rule MI[rule_format])
          show "size T'' < size U" using U by simp
          show "IT (lift u 0 $ Bound 0)" using Atom.prems by (auto intro: app_Bound_IT)
          show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 $ Bound 0 : Ts' \<Rrightarrow> T"
            using uT' by (auto intro: lift_type[of e u _ 0, simplified])
        qed (use aIT aT' in auto)
        then have uaIT: "IT (u $ a[u/i])" by simp
        have "IT ((Bound 0 \<degree>\<degree> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as))[(u $ a[u/i])/0])"
        proof (rule MI[rule_format])
          show "size (Ts' \<Rrightarrow> T) < size U" using U by simp
          from Ras asT have "listsp IT (map (\<lambda>t. t[u/i]) as)" by (rule mapIT)
          then have "listsp IT (map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as))"
            by (induction as) (auto intro: listsp.intros)
          then show "IT (Bound 0 \<degree>\<degree> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as))" by auto
          have "e \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts'" using Atom.prems asT by (blast intro: substs_lemma)
          then have "e\<langle>0:Ts' \<Rrightarrow> T\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) : Ts'"
            by (rule lift_types) simp
          then show "e\<langle>0:Ts' \<Rrightarrow> T\<rangle> \<turnstile> Bound 0 \<degree>\<degree> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) : T"
            by (auto intro: list_app_typeI)
          show "e \<turnstile> u $ a[u/i] : Ts' \<Rrightarrow> T" using uT' aT' by auto
        qed (use uaIT in auto)
        with Cons True show ?thesis by (simp add: comp_def)
      qed
    next
      case False
      from R rsT have "listsp IT (map (\<lambda>t. t[u/i]) rs)" by (rule mapIT)
      moreover have "atom (h[u/i])" using False \<open>atom h\<close> by (cases h) (auto simp: subst_Bound)
      ultimately show ?thesis by auto
    qed
  next
    case (Lambda r a T')
    from Lambda.prems(1) obtain T2 where T: "T = T' \<rightarrow>\<^sub>T T2" "e\<langle>i:U\<rangle>\<langle>0:T'\<rangle> \<turnstile> r : T2" by auto
    then have "e\<langle>0:T'\<rangle>\<langle>i + 1:U\<rangle> \<turnstile> r : T2" using Lambda.prems by simp
    moreover have "IT (lift u 0)" "e\<langle>0:T'\<rangle> \<turnstile> lift u 0 : U" using Lambda.prems by auto
    ultimately have "IT (r[lift u 0 / i + 1])"
      using Lambda.IH[of "e\<langle>0:T'\<rangle>" "i + 1" T2 "lift u 0"] Lambda.prems by (simp add: integer_arith)
    then show ?case by auto
  next
    case (Beta r s ss a T')
    have "IT (Abs a T' (r[lift u 0 / i + 1]) $ s[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) ss)"
    proof (rule IT.Beta)
      have "Abs a T' r $ s \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta> r[s/0] \<degree>\<degree> ss" by simp
      then have "e\<langle>i:U\<rangle> \<turnstile> r[s/0] \<degree>\<degree> ss : T" by (rule subject_reduction_beta[OF Beta.prems(1)])
      then have "IT ((r[s/0] \<degree>\<degree> ss)[u/i])" using Beta.prems Beta.IH(1) by blast
      then show "IT (r[lift u 0 / i + 1][s[u/i]/0] \<degree>\<degree> map (\<lambda>t. t[u/i]) ss)"
        using Beta.prems subst_subst[of 0 i r u s] by simp
      obtain V where "e\<langle>i:U\<rangle> \<turnstile> Abs a T' r $ s : V"
        using list_app_typeD[OF Beta.prems(1)] by blast
      then obtain T'' where "e\<langle>i:U\<rangle> \<turnstile> s : T''" by auto
      then show "IT (s[u/i])" using Beta.prems Beta.IH(2) by blast
    qed
    then show ?case by simp
  qed
qed


subsection \<open>Well-typed terms are strongly normalizing\<close>

lemma type_implies_IT: "e \<turnstile> t : T \<Longrightarrow> IT t"
proof (induction rule: typing.induct)
  case (App e s T U t)
  have "IT ((Bound 0 $ lift t 0)[s/0])"
  proof (rule subst_type_IT)
    have "IT (lift t 0)" using \<open>IT t\<close> by auto
    then show "IT (Bound 0 $ lift t 0)" using IT.Atom[of "Bound 0" "[lift t 0]"] by simp
    show "e\<langle>0:T \<rightarrow>\<^sub>T U\<rangle> \<turnstile> Bound 0 $ lift t 0 : U"
      using App.hyps(2) by (auto intro: lift_type[of e t T 0, simplified])
  qed (use App in auto)
  then show ?case by simp
qed auto

theorem type_implies_termi: "e \<turnstile> t : T \<Longrightarrow> termip beta t"
  by (rule IT_implies_termi) (rule type_implies_IT)

end

end
