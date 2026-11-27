section \<open>Applications to Lists of Terms\<close>

text \<open>
  Applications of a term to a list of arguments, their reductions and their typing, and the
  combination of \<open>\<beta>\<close> and \<open>\<eta>\<close>. These facts are independent of strong normalization
  (theory \<open>Pure_SN\<close>) and of normal forms (theory \<open>Pure_Normal\<close>).
\<close>

theory Pure_Apps
  imports Pure_Typing "HOL-Proofs-Lambda.ListOrder"
begin

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

lemma subst_map [simp]: "(t \<degree>\<degree> ts)[u/i] = t[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) ts"
  by (induction ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) $ u = t \<degree>\<degree> (ts @ [u])"
  by simp

subsection \<open>Lifting \<open>\<beta>\<close>-reduction to lists\<close>

abbreviation list_beta :: "pterm list \<Rightarrow> pterm list \<Rightarrow> bool"  (infixl \<open>\<Rightarrow>\<^sub>\<beta>\<^sub>l\<close> 50) where
  "rs \<Rightarrow>\<^sub>\<beta>\<^sub>l ss \<equiv> step1 beta rs ss"

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

subsection \<open>Typing of lists of terms\<close>

context signature
begin

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

lemma subject_reduction_beta': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induction rule: rtranclp_induct) (auto intro: subject_reduction_beta)

end

subsection \<open>\<open>\<beta>\<close>- and \<open>\<eta>\<close>-reduction together\<close>

abbreviation beta_eta :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<close> 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> t \<equiv> sup beta eta s t"

abbreviation beta_eta_reds :: "pterm \<Rightarrow> pterm \<Rightarrow> bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>*\<close> 50) where
  "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<equiv> (sup beta eta)\<^sup>*\<^sup>* s t"

lemma beta_reds_beta_eta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma eta_reds_beta_eta_reds: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma aconv_term_refl [simp]: "aconv_term t t"
  by (simp add: aconv_term_unname)

end
