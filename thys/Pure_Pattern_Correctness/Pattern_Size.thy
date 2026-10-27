section \<open>A Size Measure for Well-Typed Terms\<close>

theory Pattern_Size
  imports Pattern_Solutions
begin

text \<open>
  For the termination of unification on well-typed terms that need not be patterns, we measure a
  term by the size of the \<open>\<beta>\<close>-normal form of its instance under the environment. As for patterns,
  a flexible term \<open>F t\<^sub>1 \<dots> t\<^sub>k\<close> counts as the \<open>\<eta>\<close>-expansion of \<open>F\<close> to its arity, without its
  arguments, so that pruning bindings do not change the size.
\<close>

subsection \<open>\<open>\<beta>\<close>-normal forms\<close>

lemma beta_normal_reds: "\<beta>_normal t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<Longrightarrow> u = t"
  by (erule converse_rtranclpE) auto

lemma \<beta>_nf_ex: "termip beta t \<Longrightarrow> \<exists>u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> \<beta>_normal u"
proof (induction rule: accp_induct_rule)
  case (1 t)
  show ?case
  proof (cases "\<beta>_normal t")
    case False
    then obtain t' where t': "t \<rightarrow>\<^sub>\<beta> t'" by blast
    with 1 obtain u where "t' \<rightarrow>\<^sub>\<beta>\<^sup>* u" "\<beta>_normal u" by blast
    with t' show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed auto
qed

lemma \<beta>_nf_normal: "termip beta t \<Longrightarrow> \<beta>_normal (\<beta>_nf t)"
  using \<beta>_nf_ex[of t] \<beta>_nf_eq by auto

lemma termip_reds': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> termip beta t \<Longrightarrow> termip beta t'"
  by (induction rule: rtranclp_induct) (auto intro: accp_downward)

lemma \<beta>_nf_reds: "termip beta t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> \<beta>_nf t' = \<beta>_nf t"
  by (metis \<beta>_nf_eq \<beta>_nf_normal \<beta>_nf_reduces rtranclp_trans termip_reds')

definition typable :: "dB \<Rightarrow> bool" where
  "typable t \<longleftrightarrow> (\<exists>e T. e \<turnstile> t : T)"

lemma typable_termip: "typable t \<Longrightarrow> termip beta t"
  by (auto simp: typable_def intro: type_implies_termi)

lemma typableI: "e \<turnstile> t : T \<Longrightarrow> typable t"
  unfolding typable_def by blast

lemma typable_Abs: "typable (dB.Abs t) \<Longrightarrow> typable t"
  by (auto simp: typable_def elim!: abs_typeE)

lemma typable_apps: "typable (h \<degree>\<degree> ts) \<Longrightarrow> typable h \<and> (\<forall>t\<in>set ts. typable t)"
  by (auto simp: typable_def elim!: list_app_typeE dest!: lists_typings simp: in_listsp_conv_set) blast

lemma \<beta>_nf_Abs:
  assumes "typable (dB.Abs t)"
  shows "\<beta>_nf (dB.Abs t) = dB.Abs (\<beta>_nf t)"
proof (rule \<beta>_nf_eq)
  have "termip beta t" by (rule typable_termip[OF typable_Abs[OF assms]])
  from \<beta>_nf_reduces[of t] \<beta>_nf_normal[OF this] show "dB.Abs t \<rightarrow>\<^sub>\<beta>\<^sup>* dB.Abs (\<beta>_nf t)" "\<beta>_normal (dB.Abs (\<beta>_nf t))" by auto
qed

lemma rtrancl_beta_apps_args:
  "list_all2 (\<lambda>t u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u) ts us \<Longrightarrow> h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* h \<degree>\<degree> us"
proof (induction ts us arbitrary: h rule: list_all2_induct)
  case (Cons t ts u us)
  have "h \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* (h \<degree> u) \<degree>\<degree> ts"
    using Cons.hyps(1) by (simp add: rtrancl_beta_AppR)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* (h \<degree> u) \<degree>\<degree> us" by (rule Cons.IH)
  finally show ?case by simp
qed simp

lemma \<beta>_normal_atom_apps:
  assumes "(\<exists>n. h = dB.Var n) \<or> (\<exists>i. h = BVar i)" "\<forall>u\<in>set us. \<beta>_normal u"
  shows "\<beta>_normal (h \<degree>\<degree> us)"
proof (rule notI, elim exE)
  fix v assume "h \<degree>\<degree> us \<rightarrow>\<^sub>\<beta> v"
  with assms(1) obtain ss where "us => ss"
    using head_Var_reduction head_BVar_reduction by blast
  then show False using assms(2) by (auto simp: step1_def)
qed

lemma \<beta>_nf_atom_apps:
  assumes "typable (h \<degree>\<degree> ts)" "(\<exists>n. h = dB.Var n) \<or> (\<exists>i. h = BVar i)"
  shows "\<beta>_nf (h \<degree>\<degree> ts) = h \<degree>\<degree> map \<beta>_nf ts"
proof (rule \<beta>_nf_eq)
  have t: "\<forall>t\<in>set ts. termip beta t" using typable_apps[OF assms(1)] typable_termip by blast
  show "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* h \<degree>\<degree> map \<beta>_nf ts"
    by (rule rtrancl_beta_apps_args) (auto simp: list_all2_conv_all_nth \<beta>_nf_reduces)
  show "\<beta>_normal (h \<degree>\<degree> map \<beta>_nf ts)"
    by (rule \<beta>_normal_atom_apps[OF assms(2)]) (use t \<beta>_nf_normal in auto)
qed


subsection \<open>The size of \<open>\<beta>\<close>-normal forms\<close>

fun ty_arity :: "type \<Rightarrow> nat" where
  "ty_arity (Fun T U) = Suc (ty_arity U)"
| "ty_arity (Atom n) = 0"

lemma ty_arity_funs: "ty_arity (Ts \<Rrightarrow> T) = length Ts + ty_arity T"
  by (induction Ts) auto

fun dhd :: "dB \<Rightarrow> dB" where
  "dhd (s \<degree> t) = dhd s"
| "dhd t = t"

fun dnargs :: "dB \<Rightarrow> nat" where
  "dnargs (s \<degree> t) = Suc (dnargs s)"
| "dnargs t = 0"

lemma dhd_apps[simp]: "dhd (h \<degree>\<degree> ts) = dhd h"
  by (induction ts rule: rev_induct) (simp_all add: app_last[symmetric])

lemma dnargs_apps[simp]: "dnargs (h \<degree>\<degree> ts) = dnargs h + length ts"
  by (induction ts rule: rev_induct) (simp_all add: app_last[symmetric])

fun flex_head :: "dB \<Rightarrow> bool" where
  "flex_head (dB.Var n) = (\<not> rigid_code n)"
| "flex_head _ = False"

fun head_code :: "dB \<Rightarrow> nat" where
  "head_code (dB.Var n) = n"
| "head_code _ = 0"

fun msz :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> nat" where
  "msz \<tau> (dB.Abs t) = msz \<tau> t + 2"
| "msz \<tau> (s \<degree> t) = (if flex_head (dhd s) then 2 * (ty_arity (\<tau> (head_code (dhd s))) - Suc (dnargs s)) + 1
    else msz \<tau> s + msz \<tau> t)"
| "msz \<tau> (dB.Var n) = (if rigid_code n then 1 else 2 * ty_arity (\<tau> n) + 1)"
| "msz \<tau> (BVar i) = 1"

lemma msz_rigid_apps:
  "(\<exists>i. h = BVar i) \<or> (\<exists>n. h = dB.Var n \<and> rigid_code n) \<Longrightarrow> msz \<tau> (h \<degree>\<degree> ts) = 1 + sum_list (map (msz \<tau>) ts)"
  by (induction ts rule: rev_induct) (auto simp: app_last[symmetric])

lemma msz_flex_apps:
  "\<not> rigid_code n \<Longrightarrow> msz \<tau> (dB.Var n \<degree>\<degree> ts) = 2 * (ty_arity (\<tau> n) - length ts) + 1"
  by (induction ts rule: rev_induct) (auto simp: app_last[symmetric])

lemma dhd_lift: "dhd (lift t k) = lift (dhd t) k"
  by (induction t arbitrary: k) auto

lemma dnargs_lift[simp]: "dnargs (lift t k) = dnargs t"
  by (induction t arbitrary: k) auto

lemma msz_lift[simp]: "msz \<tau> (lift t k) = msz \<tau> t"
proof (induction t arbitrary: k)
  case (App s u)
  show ?case
    by (cases "dhd s") (simp_all add: dhd_lift App.IH)
qed auto

lemma msz_Abs_m[simp]: "msz \<tau> (Abs_m m t) = msz \<tau> t + 2 * m"
  by (induction m) auto


subsection \<open>Pruning substitutions preserve the size\<close>

lemma liftn_lift_comm: "liftn m (lift s k) k = lift (liftn m s k) k"
  by (induction s arbitrary: k) auto

lemma Abs_m_subst_gen: "(Abs_m m b)[s/k] = Abs_m m (b[liftn m s 0/k + m])"
proof (induction m arbitrary: s k)
  case (Suc m)
  have "liftn m (lift s 0) 0 = liftn (Suc m) s 0" by (simp add: liftn_lift_comm)
  then show ?case by (simp add: Suc.IH)
qed simp

lemma Abs_m_flex_apps:
  "\<exists>us. Abs_m m (dB.Var H \<degree>\<degree> vs) \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* Abs_m (m - length ts) (dB.Var H \<degree>\<degree> us) \<and>
    length us = length vs + (length ts - m)"
proof (induction ts arbitrary: m vs)
  case (Cons t ts)
  show ?case
  proof (cases m)
    case 0
    then show ?thesis by (intro exI[of _ "vs @ t # ts"]) simp
  next
    case (Suc m')
    let ?vs = "map (\<lambda>v. v[liftn m' t 0/m']) vs"
    have "Abs_m m (dB.Var H \<degree>\<degree> vs) \<degree> t \<rightarrow>\<^sub>\<beta> Abs_m m' (dB.Var H \<degree>\<degree> ?vs)"
      using beta.beta[of "Abs_m m' (dB.Var H \<degree>\<degree> vs)" t] by (simp add: Suc Abs_m_subst_gen)
    then have step: "Abs_m m (dB.Var H \<degree>\<degree> vs) \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta> Abs_m m' (dB.Var H \<degree>\<degree> ?vs) \<degree>\<degree> ts"
      by simp
    from Cons.IH[of m' ?vs] obtain us where
      red: "Abs_m m' (dB.Var H \<degree>\<degree> ?vs) \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* Abs_m (m' - length ts) (dB.Var H \<degree>\<degree> us)"
      and len: "length us = length vs + (length ts - m')"
      by auto
    have "Abs_m m (dB.Var H \<degree>\<degree> vs) \<degree>\<degree> (t # ts) \<rightarrow>\<^sub>\<beta>\<^sup>* Abs_m (m' - length ts) (dB.Var H \<degree>\<degree> us)"
      by (rule converse_rtranclp_into_rtranclp[OF step red])
    with len Suc show ?thesis by (intro exI[of _ us]) simp
  qed
qed auto

lemma \<beta>_nf_Abs_m: "typable (Abs_m m t) \<Longrightarrow> \<beta>_nf (Abs_m m t) = Abs_m m (\<beta>_nf t)"
  by (induction m) (auto simp: \<beta>_nf_Abs dest: typable_Abs)

lemma typable_Abs_m: "typable (Abs_m m t) \<Longrightarrow> typable t"
  by (induction m) (auto dest: typable_Abs)

lemma typable_reds: "typable t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<Longrightarrow> typable u"
  by (auto simp: typable_def intro: subject_reduction')

text \<open>
  A pruning substitution maps each variable \<open>n \<in> D\<close> of arity \<open>m\<close> to
  \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>m. H x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>k\<close> for a flexible \<open>H\<close> of arity \<open>k\<close>.
\<close>

definition pruning :: "(nat \<Rightarrow> type) \<Rightarrow> nat set \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "pruning \<tau> D \<rho> \<longleftrightarrow> (\<forall>n. n \<notin> D \<longrightarrow> \<rho> n = dB.Var n) \<and>
    (\<forall>n\<in>D. \<not> rigid_code n \<and> (\<exists>H ks m a. \<rho> n = Abs_m m (dB.Var H \<degree>\<degree> map BVar ks) \<and>
      \<not> rigid_code H \<and> ty_arity (\<tau> n) = m + a \<and> ty_arity (\<tau> H) = length ks + a)) \<and>
    (\<forall>n\<in>D. \<forall>e. (e, \<tau>) \<turnstile> \<rho> n : \<tau> n)"

lemma size_apps_ge: "size r \<le> size (r \<degree>\<degree> rs)"
  by (induction rs arbitrary: r) (auto intro: le_trans[rotated])

lemma size_apps_arg: "t \<in> set ts \<Longrightarrow> size t < size (h \<degree>\<degree> ts)"
proof (induction ts arbitrary: h)
  case (Cons a ts)
  show ?case
  proof (cases "t = a")
    case True
    have "size a < size (h \<degree> a)" by simp
    also have "\<dots> \<le> size ((h \<degree> a) \<degree>\<degree> ts)" by (rule size_apps_ge)
    finally show ?thesis using True by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    from Cons.IH[OF this, of "h \<degree> a"] show ?thesis by (simp del: size_apps)
  qed
qed simp

lemma typing_Var_apps_arity: "(e, \<tau>) \<turnstile> dB.Var n \<degree>\<degree> ts : T \<Longrightarrow> length ts \<le> ty_arity (\<tau> n)"
  by (erule list_app_typeE) (auto simp: ty_arity_funs dest: typings_length)

lemma msz_pruning:
  assumes "(e, \<tau>) \<turnstile> X : T" "\<beta>_normal X" "pruning \<tau> D \<rho>"
  shows "msz \<tau> (\<beta>_nf (mk_subst \<rho> X)) = msz \<tau> X"
  using assms(1,2)
proof (induction X arbitrary: e T rule: measure_induct_rule[of size])
  case (less X)
  note pr = assms(3)[unfolded pruning_def]
  have tyr: "typed_on (FV X) \<tau> \<tau> \<rho>"
    unfolding typed_on_def
  proof (intro ballI allI)
    fix n e' assume "n \<in> FV X"
    show "(e', \<tau>) \<turnstile> \<rho> n : \<tau> n" by (cases "n \<in> D") (use pr in auto)
  qed
  have tyX: "(e, \<tau>) \<turnstile> mk_subst \<rho> X : T" by (rule typing_mk_subst[OF less.prems(1) tyr])
  from ex_head_tail[of X] obtain ts h where X: "X = h \<degree>\<degree> ts"
    and h: "(\<exists>n. h = BVar n) \<or> (\<exists>u. h = dB.Abs u) \<or> (\<exists>n. h = dB.Var n)" by blast
  have sub: "size t < size X" if "t \<in> set ts" for t
    using that X size_apps_arg by blast
  from less.prems(1) X obtain Ts where tyh: "(e, \<tau>) \<turnstile> h : Ts \<Rrightarrow> T" and tyts: "(e, \<tau>) \<tturnstile> ts : Ts"
    by (auto elim: list_app_typeE)
  have nts: "\<forall>t\<in>set ts. \<beta>_normal t"
  proof
    fix t assume t: "t \<in> set ts"
    show "\<beta>_normal t"
    proof
      assume "\<exists>u. t \<rightarrow>\<^sub>\<beta> u"
      then obtain u where "t \<rightarrow>\<^sub>\<beta> u" by blast
      obtain ys zs where ts: "ts = ys @ t # zs" using split_list[OF t] by blast
      have "step1 beta ts (ys @ u # zs)" unfolding step1_def ts using \<open>t \<rightarrow>\<^sub>\<beta> u\<close> by blast
      then have "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> h \<degree>\<degree> (ys @ u # zs)" by (rule apps_preserves_betas)
      then show False using less.prems(2) unfolding X by (meson notE)
    qed
  qed
  have IH: "msz \<tau> (\<beta>_nf (mk_subst \<rho> t)) = msz \<tau> t" if "t \<in> set ts" for t
  proof -
    from tyts that obtain U where "(e, \<tau>) \<turnstile> t : U"
      by (auto dest: lists_typings simp: in_listsp_conv_set)
    from less.IH[OF sub[OF that] this] nts that show ?thesis by blast
  qed
  have tts: "typable (mk_subst \<rho> h \<degree>\<degree> map (mk_subst \<rho>) ts)" using tyX X by (simp add: typableI)
  consider (B) i where "h = BVar i" | (R) n where "h = dB.Var n" "n \<notin> D" | (D) n where "h = dB.Var n" "n \<in> D"
    | (A) u where "h = dB.Abs u" using h by blast
  then show ?case
  proof cases
    case B
    with tts have "\<beta>_nf (mk_subst \<rho> X) = BVar i \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<rho> t)) ts"
      by (simp add: X \<beta>_nf_atom_apps comp_def)
    with B X IH show ?thesis by (simp add: msz_rigid_apps comp_def cong: map_cong)
  next
    case R
    with pr have \<rho>n: "\<rho> n = dB.Var n" by simp
    with R tts have nf: "\<beta>_nf (mk_subst \<rho> X) = dB.Var n \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst \<rho> t)) ts"
      by (simp add: X \<beta>_nf_atom_apps comp_def)
    show ?thesis
    proof (cases "rigid_code n")
      case True
      with nf R X IH show ?thesis by (simp add: msz_rigid_apps comp_def cong: map_cong)
    qed (use nf R X in \<open>simp add: msz_flex_apps\<close>)
  next
    case D
    from pr D obtain H ks m a where \<rho>n: "\<rho> n = Abs_m m (dB.Var H \<degree>\<degree> map BVar ks)"
      and H: "\<not> rigid_code H" "ty_arity (\<tau> n) = m + a" "ty_arity (\<tau> H) = length ks + a"
      and nr: "\<not> rigid_code n" by blast
    have len: "length ts \<le> ty_arity (\<tau> n)"
      using typing_Var_apps_arity less.prems(1) X D by blast
    from Abs_m_flex_apps[of m H "map BVar ks" "map (mk_subst \<rho>) ts"] obtain us where
      red: "\<rho> n \<degree>\<degree> map (mk_subst \<rho>) ts \<rightarrow>\<^sub>\<beta>\<^sup>* Abs_m (m - length ts) (dB.Var H \<degree>\<degree> us)"
      and lus: "length us = length ks + (length ts - m)" using \<rho>n by auto
    have tts': "typable (\<rho> n \<degree>\<degree> map (mk_subst \<rho>) ts)" using tts D by simp
    have ty': "typable (Abs_m (m - length ts) (dB.Var H \<degree>\<degree> us))"
      by (rule typable_reds[OF tts' red])
    then have "typable (dB.Var H \<degree>\<degree> us)" by (rule typable_Abs_m)
    then have "\<beta>_nf (Abs_m (m - length ts) (dB.Var H \<degree>\<degree> us)) =
        Abs_m (m - length ts) (dB.Var H \<degree>\<degree> map \<beta>_nf us)"
      using ty' by (simp add: \<beta>_nf_Abs_m \<beta>_nf_atom_apps)
    moreover have "\<beta>_nf (mk_subst \<rho> X) = \<beta>_nf (Abs_m (m - length ts) (dB.Var H \<degree>\<degree> us))"
      using \<beta>_nf_reds[OF typable_termip[OF tts'] red] D X by simp
    ultimately show ?thesis using D X H nr lus len by (simp add: msz_flex_apps)
  next
    case A
    show ?thesis
    proof (cases ts)
      case Nil
      with A X less.prems(1) obtain U V where tyu: "(e\<langle>0:U\<rangle>, \<tau>) \<turnstile> u : V" by (auto elim: abs_typeE)
      have "\<beta>_normal u"
      proof
        assume "\<exists>u'. u \<rightarrow>\<^sub>\<beta> u'"
        then obtain u' where "u \<rightarrow>\<^sub>\<beta> u'" by blast
        then have "X \<rightarrow>\<^sub>\<beta> dB.Abs u'" using A X Nil by simp
        with less.prems(2) show False by blast
      qed
      from less.IH[OF _ tyu this] A X Nil have "msz \<tau> (\<beta>_nf (mk_subst \<rho> u)) = msz \<tau> u" by simp
      moreover have "typable (dB.Abs (mk_subst \<rho> u))" using tts A Nil by simp
      ultimately show ?thesis using A X Nil by (simp add: \<beta>_nf_Abs)
    next
      case (Cons t ts')
      have "X \<rightarrow>\<^sub>\<beta> u[t/0] \<degree>\<degree> ts'" using A X Cons by simp
      with less.prems(2) show ?thesis by blast
    qed
  qed
qed


lemma \<beta>_normal_lift: "\<beta>_normal t \<Longrightarrow> \<beta>_normal (lift t k)"
proof (induction t arbitrary: k)
  case (Abs t)
  show ?case
  proof
    assume "\<exists>u. lift (dB.Abs t) k \<rightarrow>\<^sub>\<beta> u"
    then obtain u where "lift t (Suc k) \<rightarrow>\<^sub>\<beta> u" by auto
    moreover have "\<beta>_normal t" using Abs.prems by blast
    ultimately show False using Abs.IH by blast
  qed
next
  case (App s u)
  have ns: "\<beta>_normal s" and nu: "\<beta>_normal u" using App.prems by blast+
  have nA: "\<not> (\<exists>r. s = dB.Abs r)" using App.prems by blast
  show ?case
  proof
    assume "\<exists>v. lift (s \<degree> u) k \<rightarrow>\<^sub>\<beta> v"
    then obtain v where step: "lift s k \<degree> lift u k \<rightarrow>\<^sub>\<beta> v" unfolding lift.simps by meson
    have "lift s k \<noteq> dB.Abs r" for r using nA by (cases s) auto
    with step App.IH ns nu show False by blast
  qed
qed auto

lemma \<beta>_nf_lift:
  assumes "typable t"
  shows "\<beta>_nf (lift t k) = lift (\<beta>_nf t) k"
proof (rule \<beta>_nf_eq)
  show "lift t k \<rightarrow>\<^sub>\<beta>\<^sup>* lift (\<beta>_nf t) k" by (rule lift_preserves_beta'[OF \<beta>_nf_reduces])
  show "\<beta>_normal (lift (\<beta>_nf t) k)" by (rule \<beta>_normal_lift[OF \<beta>_nf_normal[OF typable_termip[OF assms]]])
qed


subsection \<open>The instance of a term under an environment\<close>

definition env_inst :: "env \<Rightarrow> nat \<Rightarrow> dB" where
  "env_inst env = env_map env (\<lambda>x. dB.Var (code (AVar x)))"

definition Ms :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "Ms env W t = msz (tau W) (\<beta>_nf (mk_subst (env_inst env) (tr t)))"

context
  fixes ar env W
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
begin

lemma inst_g: "no_loose_bound (dB.Var (code (AVar x))) 0 \<and> (\<forall>e. (e, tau W) \<turnstile> dB.Var (code (AVar x)) : trty (W x))"
  by auto

lemma inst_closed: "closed_on UNIV (env_inst env)"
  unfolding env_inst_def by (rule env_map_closed[OF ac ety wf inst_g])

lemma inst_typed: "typed_on (range code) (tau W) (tau W) (env_inst env)"
  unfolding env_inst_def by (rule env_map_typed[OF ac ety wf inst_g])

lemma inst_rigid: "rigid_code n \<Longrightarrow> env_inst env n = dB.Var n"
  unfolding env_inst_def by (rule env_map_rigid[OF ac ety])

lemma inst_bound: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
    env_inst env (code (AVar x)) = mk_subst (env_inst env) (tr u)"
  unfolding env_inst_def by (rule env_map_bound[OF ac ety])

lemma inst_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> env_inst env (code (AVar x)) = dB.Var (code (AVar x))"
  unfolding env_inst_def by (rule env_map_unbound[OF ac ety])

lemma inst_tr_typed: "has_type W Ts t T \<Longrightarrow> (bnd_env Ts, tau W) \<turnstile> mk_subst (env_inst env) (tr t) : trty T"
  by (rule typing_mk_subst[OF has_type_tr typed_on_mono[OF inst_typed FV_tr_range]])

lemma inst_typable: "has_type W Ts t T \<Longrightarrow> typable (mk_subst (env_inst env) (tr t))"
  by (rule typableI[OF inst_tr_typed])

lemma inst_subst_bound:
  "proper t \<Longrightarrow> proper u \<Longrightarrow>
    mk_subst (env_inst env) (tr (subst_bound u t)) = (mk_subst (env_inst env) (tr t))[mk_subst (env_inst env) (tr u)/0]"
  using inst_closed by (simp add: tr_subst_bound mk_subst_subst closed_on_def)

lemma head_norm_inst_aux:
  assumes "head_norm e t = Some r"
  shows "e = env \<Longrightarrow> r = Ok t' \<Longrightarrow> proper t \<Longrightarrow>
    proper t' \<and> mk_subst (env_inst env) (tr t) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst (env_inst env) (tr t')"
  using assms
proof (induction e t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn e t r)
  let ?\<theta> = "env_inst env"
  have t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using "1.hyps" "1.prems"(2) unfolding "1.prems"(1) by simp
  have pt: "proper t" using "1.prems" by simp
  note IH = "1.IH"[OF _ refl refl]
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (T, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest pt show ?thesis by simp
    next
      case 2
      with wf_envD(2)[OF wf] have u: "proper u" by auto
      from 2 rest have "hn env u = Some (Ok t')" by simp
      from IH[OF this u] inst_bound[OF 2(2)] Var show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "hn env body = Some (Ok b')" "t' = pterm.Abs a T b'" by auto
    with IH[OF this(1)] pt Abs show ?thesis by auto
  next
    case (App f u)
    have pf: "proper f" "proper u" using pt App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
      have pb: "proper body" using pf f by simp
      from IH[OF h proper_subst_bound[OF pb pf(2)]] have
        "proper t'" "mk_subst ?\<theta> (tr (subst_bound u body)) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst ?\<theta> (tr t')" by auto
      moreover have "mk_subst ?\<theta> (tr t) \<rightarrow>\<^sub>\<beta> mk_subst ?\<theta> (tr (subst_bound u body))"
        using App f by (simp add: inst_subst_bound[OF pb pf(2)])
      ultimately show ?thesis by (auto intro: converse_rtranclp_into_rtranclp)
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF nf pf(1)] have pnf: "proper nf" and rnf: "mk_subst ?\<theta> (tr f) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst ?\<theta> (tr nf)"
        by auto
      have fu: "mk_subst ?\<theta> (tr t) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst ?\<theta> (tr (nf $ u))"
        using rnf App by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have pb: "proper body" using pnf nfa by simp
        from IH[OF h proper_subst_bound[OF pb pf(2)]] have
          "proper t'" "mk_subst ?\<theta> (tr (subst_bound u body)) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst ?\<theta> (tr t')" by auto
        moreover have "mk_subst ?\<theta> (tr (nf $ u)) \<rightarrow>\<^sub>\<beta> mk_subst ?\<theta> (tr (subst_bound u body))"
          using nfa by (simp add: inst_subst_bound[OF pb pf(2)])
        ultimately show ?thesis using fu by (auto intro: rtranclp_trans converse_rtranclp_into_rtranclp)
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with fu pnf pf show ?thesis by simp
      qed
    qed
  qed (use t' pt in auto)
qed

lemma head_norm_inst:
  "head_norm env t = Some (Ok t') \<Longrightarrow> proper t \<Longrightarrow>
    proper t' \<and> mk_subst (env_inst env) (tr t) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst (env_inst env) (tr t')"
  using head_norm_inst_aux by blast

lemma Ms_reds:
  assumes "has_type W Ts t T" "mk_subst (env_inst env) (tr t) \<rightarrow>\<^sub>\<beta>\<^sup>* mk_subst (env_inst env) (tr t')"
  shows "Ms env W t' = Ms env W t"
  by (simp add: Ms_def \<beta>_nf_reds[OF typable_termip[OF inst_typable[OF assms(1)]] assms(2)])

lemma Ms_head_norm:
  "head_norm env t = Some (Ok t') \<Longrightarrow> proper t \<Longrightarrow> has_type W Ts t T \<Longrightarrow> Ms env W t' = Ms env W t"
  using head_norm_inst Ms_reds by blast

lemma Ms_Abs: "has_type W Ts (pterm.Abs a U b) T \<Longrightarrow> Ms env W (pterm.Abs a U b) = Ms env W b + 2"
  using inst_typable[of Ts "pterm.Abs a U b" T] by (simp add: Ms_def \<beta>_nf_Abs)

lemma inst_list_comb:
  "mk_subst (env_inst env) (tr (list_comb h ts)) =
    mk_subst (env_inst env) (tr h) \<degree>\<degree> map (\<lambda>t. mk_subst (env_inst env) (tr t)) ts"
  by (simp add: tr_list_comb comp_def)

lemma Ms_rigid:
  assumes "is_rigid h" "has_type W Ts (list_comb h ts) T"
  shows "Ms env W (list_comb h ts) = 1 + sum_list (map (Ms env W) ts)"
proof -
  let ?\<theta> = "env_inst env"
  have h: "mk_subst ?\<theta> (tr h) = tr h \<and> ((\<exists>n. tr h = dB.Var n \<and> rigid_code n) \<or> (\<exists>i. tr h = BVar i))"
    using assms(1) by (auto simp: is_rigid_def inst_rigid)
  have ty: "typable (tr h \<degree>\<degree> map (\<lambda>t. mk_subst ?\<theta> (tr t)) ts)"
    using inst_typable[OF assms(2)] h by (simp add: inst_list_comb)
  have "\<beta>_nf (mk_subst ?\<theta> (tr (list_comb h ts))) = tr h \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst ?\<theta> (tr t))) ts"
    using \<beta>_nf_atom_apps[OF ty] h by (auto simp: inst_list_comb comp_def)
  then show ?thesis using h by (auto simp: Ms_def[abs_def] msz_rigid_apps comp_def)
qed

lemma Ms_flex:
  assumes "vt_lookup (tenv env) F = None" "has_type W Ts (list_comb (pterm.Var F U) ts) T"
  shows "Ms env W (list_comb (pterm.Var F U) ts) = 2 * (ty_arity (trty (W F)) - length ts) + 1"
proof -
  let ?\<theta> = "env_inst env"
  have h: "mk_subst ?\<theta> (tr (pterm.Var F U)) = dB.Var (code (AVar F))"
    by (simp add: inst_unbound[OF assms(1)])
  have ty: "typable (dB.Var (code (AVar F)) \<degree>\<degree> map (\<lambda>t. mk_subst ?\<theta> (tr t)) ts)"
    using inst_typable[OF assms(2)] h by (simp add: inst_list_comb)
  have "\<beta>_nf (mk_subst ?\<theta> (tr (list_comb (pterm.Var F U) ts))) =
      dB.Var (code (AVar F)) \<degree>\<degree> map (\<lambda>t. \<beta>_nf (mk_subst ?\<theta> (tr t))) ts"
    using \<beta>_nf_atom_apps[OF ty] h by (auto simp: inst_list_comb comp_def)
  then show ?thesis by (simp add: Ms_def msz_flex_apps)
qed

lemma inst_incr:
  "proper t \<Longrightarrow> mk_subst (env_inst env) (tr (incr t)) = lift (mk_subst (env_inst env) (tr t)) 0"
  using inst_closed by (simp add: incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)

lemma Ms_incr: "proper t \<Longrightarrow> has_type W Ts t T \<Longrightarrow> Ms env W (incr t) = Ms env W t"
  by (simp add: Ms_def inst_incr \<beta>_nf_lift[OF inst_typable])

lemma Ms_Bound: "0 \<le> i \<Longrightarrow> has_type W Ts (Bound i) T \<Longrightarrow> Ms env W (Bound i) = 1"
  using Ms_rigid[of "Bound i" Ts "[]" T] by (simp add: is_rigid_def)

lemma Ms_eta:
  assumes "is_rigid h \<or> (\<exists>F U. h = pterm.Var F U \<and> vt_lookup (tenv env) F = None)"
    and "proper (list_comb h ts)" "has_type W Ts (list_comb h ts) (U' \<rightarrow>\<^sub>T V)"
  shows "Ms env W (incr (list_comb h ts) $ Bound 0) + 1 \<le> Ms env W (list_comb h ts) + 2"
proof -
  have e: "incr (list_comb h ts) $ Bound 0 = list_comb (incr h) (map incr ts @ [Bound 0])"
    by (simp add: incr_def[abs_def] incr_aux_list_comb list_comb_snoc)
  have ty': "has_type W (U' # Ts) (list_comb (incr h) (map incr ts @ [Bound 0])) V"
    unfolding e[symmetric] using has_type_incr[OF assms(3), of U']
    by (intro has_type.App[of _ _ _ U']) (auto simp: has_type_Bound_iff)
  from assms(3) obtain Us where tyts: "list_all2 (has_type W Ts) ts Us" by (auto simp: has_type_list_comb)
  have pts: "\<forall>t\<in>set ts. proper t" using assms(2) by (simp add: proper_list_comb)
  have Mi: "map (Ms env W \<circ> incr) ts = map (Ms env W) ts"
    using tyts pts by (induction ts Us rule: list_all2_induct) (auto simp: Ms_incr)
  from assms(1) show ?thesis
  proof
    assume r: "is_rigid h"
    then have ri: "is_rigid (incr h)" by (auto simp: is_rigid_def incr_def)
    have "Ms env W (list_comb (incr h) (map incr ts @ [Bound 0])) =
        1 + sum_list (map (Ms env W) (map incr ts)) + Ms env W (Bound 0)"
      using Ms_rigid[OF ri ty'] by simp
    also have "Ms env W (Bound 0) = 1" by (rule Ms_Bound) (auto simp: has_type_Bound_iff)
    finally show ?thesis using Ms_rigid[OF r assms(3)] Mi e by simp
  next
    assume "\<exists>F U. h = pterm.Var F U \<and> vt_lookup (tenv env) F = None"
    then obtain F U where h: "h = pterm.Var F U" and F: "vt_lookup (tenv env) F = None" by blast
    have hi: "incr h = h" using h by (simp add: incr_def)
    have "Ms env W (list_comb (incr h) (map incr ts @ [Bound 0])) =
        2 * (ty_arity (trty (W F)) - Suc (length ts)) + 1"
      using Ms_flex[OF F, of "U' # Ts" U "map incr ts @ [Bound 0]" V] ty' hi h by simp
    then show ?thesis using Ms_flex[OF F assms(3)[unfolded h]] e h by simp
  qed
qed

end


subsection \<open>Extensions by pruning bindings\<close>

lemma msz_cong: "(\<And>n. n \<in> FV X \<Longrightarrow> \<tau> n = \<tau>' n) \<Longrightarrow> msz \<tau> X = msz \<tau>' X"
proof (induction X)
  case (App s u)
  have "\<tau> (head_code (dhd s)) = \<tau>' (head_code (dhd s))" if "flex_head (dhd s)"
  proof -
    have "head_code (dhd s) \<in> FV s" using that by (induction s) (auto elim: flex_head.elims)
    with App.prems show ?thesis by simp
  qed
  with App show ?case by auto
qed auto

lemma inst_FV_old:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env" and fr: "fresh_env env"
  shows "snd x \<le> maxidx env \<Longrightarrow> n \<in> FV (env_inst env (code (AVar x))) \<Longrightarrow>
    rigid_code n \<or> (\<exists>y. n = code (AVar y) \<and> snd y \<le> maxidx env)"
proof (induction x rule: wf_induct_rule[OF wf_dvar[OF ac ety]])
  case (1 x)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    with "1.prems" show ?thesis by (auto simp: inst_unbound[OF ac wf ety None])
  next
    case (Some b)
    obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)" using Some by (cases b) auto
    from "1.prems"(2) obtain m where m: "m \<in> FV (tr u)" "n \<in> FV (env_inst env m)"
      by (auto simp: inst_bound[OF ac wf ety lk] FV_mk_subst)
    from FV_tr[OF m(1)] show ?thesis
    proof
      assume "rigid_code m"
      with m(2) show ?thesis by (simp add: inst_rigid[OF ac wf ety])
    next
      assume "\<exists>y\<in>vars u. m = code (AVar y)"
      then obtain y where y: "y \<in> vars u" "m = code (AVar y)" by blast
      have "snd y \<le> maxidx env" using fresh_envD[OF fr lk] y(1) by (simp add: below_def)
      moreover have "(y, x) \<in> dvar env" by (rule dvarI[OF lk y(1)])
      ultimately show ?thesis using "1.IH" m(2) y(2) by blast
    qed
  qed
qed

lemma inst_tr_FV_old:
  assumes "acyc env" "wf_env ar env" "env_typed W env" "fresh_env env" "below (maxidx env) t"
    "n \<in> FV (mk_subst (env_inst env) (tr t))"
  shows "rigid_code n \<or> (\<exists>y. n = code (AVar y) \<and> snd y \<le> maxidx env)"
proof -
  from assms(6) obtain m where m: "m \<in> FV (tr t)" "n \<in> FV (env_inst env m)" by (auto simp: FV_mk_subst)
  from FV_tr[OF m(1)] show ?thesis
  proof
    assume "rigid_code m"
    with m(2) show ?thesis by (simp add: inst_rigid[OF assms(1-3)])
  next
    assume "\<exists>y\<in>vars t. m = code (AVar y)"
    with assms(5) m(2) inst_FV_old[OF assms(1-4)] show ?thesis by (auto simp: below_def)
  qed
qed

definition prune_rho :: "env \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> dB" where
  "prune_rho env env' n = (case atom_of n of
      AVar y \<Rightarrow> if n = code (AVar y) \<and> vt_lookup (tenv env) y = None then env_inst env' n else dB.Var n
    | _ \<Rightarrow> dB.Var n)"

lemma inst_extend:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env"
    and ac': "acyc env'" and wf': "wf_env ar env'" and ety': "env_typed W' env'" and ext: "extends env' env"
  shows "env_inst env' (code (AVar x)) = mk_subst (prune_rho env env') (env_inst env (code (AVar x)))"
proof (induction x rule: wf_induct_rule[OF wf_dvar[OF ac ety]])
  case (1 x)
  let ?\<rho> = "prune_rho env env'"
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    then show ?thesis by (simp add: inst_unbound[OF ac wf ety None] prune_rho_def)
  next
    case (Some b)
    obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)" using Some by (cases b) auto
    have lk': "vt_lookup (tenv env') x = Some (U, u)" using ext lk unfolding extends_def by blast
    have "mk_subst (env_inst env') (tr u) = mk_subst (?\<rho> \<circ>\<^sub>s env_inst env) (tr u)"
    proof (rule mk_subst_cong)
      fix m assume "m \<in> FV (tr u)"
      from FV_tr[OF this] show "env_inst env' m = (?\<rho> \<circ>\<^sub>s env_inst env) m"
      proof
        assume "rigid_code m"
        then show ?thesis
          by (auto simp: inst_rigid[OF ac wf ety] inst_rigid[OF ac' wf' ety'] prune_rho_def rigid_code_def)
      next
        assume "\<exists>y\<in>vars u. m = code (AVar y)"
        then obtain y where "y \<in> vars u" "m = code (AVar y)" by blast
        with "1.IH" dvarI[OF lk] show ?thesis by simp
      qed
    qed
    then show ?thesis by (simp add: inst_bound[OF ac wf ety lk] inst_bound[OF ac' wf' ety' lk'])
  qed
qed

lemma inst_extend_tr:
  assumes "acyc env" "wf_env ar env" "env_typed W env"
    "acyc env'" "wf_env ar env'" "env_typed W' env'" "extends env' env"
  shows "mk_subst (env_inst env') (tr t) = mk_subst (prune_rho env env') (mk_subst (env_inst env) (tr t))"
proof -
  have "mk_subst (env_inst env') (tr t) = mk_subst (prune_rho env env' \<circ>\<^sub>s env_inst env) (tr t)"
  proof (rule mk_subst_cong)
    fix m assume "m \<in> FV (tr t)"
    from FV_tr[OF this] show "env_inst env' m = (prune_rho env env' \<circ>\<^sub>s env_inst env) m"
    proof
      assume "rigid_code m"
      then show ?thesis
        by (auto simp: inst_rigid[OF assms(1-3)] inst_rigid[OF assms(4-6)] prune_rho_def rigid_code_def)
    qed (auto simp: inst_extend[OF assms])
  qed
  then show ?thesis by simp
qed

text \<open>
  An extension prunes if every new binding is of the form \<open>\<lambda>x\<^sub>1 \<dots> x\<^sub>m. H x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>k\<close> for an unbound
  \<open>H\<close>, where \<open>F\<close> and \<open>H\<close> have the same type after the bound arguments.
\<close>

definition prunes_inst :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "prunes_inst W' env env' \<longleftrightarrow> (\<forall>y. vt_lookup (tenv env) y = None \<longrightarrow> vt_lookup (tenv env') y \<noteq> None \<longrightarrow>
    (\<exists>H ks m a. env_inst env' (code (AVar y)) = Abs_m m (dB.Var (code (AVar H)) \<degree>\<degree> map BVar ks) \<and>
      vt_lookup (tenv env') H = None \<and> ty_arity (trty (W' y)) = m + a \<and> ty_arity (trty (W' H)) = length ks + a))"

lemma Ms_prune:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed W env" and fr: "fresh_env env"
    and ac': "acyc env'" and wf': "wf_env ar env'" and ety': "env_typed W' env'" and ext: "extends env' env"
    and ag: "agreeV (maxidx env) W W'" and pi: "prunes_inst W' env env'"
    and ty: "has_type W Ts t T" and bt: "below (maxidx env) t"
  shows "Ms env' W' t = Ms env W t"
proof -
  let ?\<rho> = "prune_rho env env'" and ?X = "mk_subst (env_inst env) (tr t)"
  have tyX: "(bnd_env Ts, tau W) \<turnstile> ?X : trty T" by (rule inst_tr_typed[OF ac wf ety ty])
  have FVo: "tau W n = tau W' n" if "n \<in> FV ?X" for n
    using inst_tr_FV_old[OF ac wf ety fr bt that] ag
    by (auto simp: rigid_code_def agreeV_def)
  have tyX': "(bnd_env Ts, tau W') \<turnstile> ?X : trty T" by (rule typing_free_cong[OF tyX FVo])
  let ?N = "\<beta>_nf ?X"
  have red: "?X \<rightarrow>\<^sub>\<beta>\<^sup>* ?N" by (rule \<beta>_nf_reduces)
  have nN: "\<beta>_normal ?N" by (rule \<beta>_nf_normal[OF typable_termip[OF typableI[OF tyX]]])
  have tyN: "(bnd_env Ts, tau W') \<turnstile> ?N : trty T" by (rule subject_reduction'[OF red tyX'])
  have FVN: "tau W n = tau W' n" if "n \<in> FV ?N" for n
    using FVo FV_beta_rtrancl[OF red] that by blast
  have \<rho>closed: "subst_no_loose_bound ?\<rho>"
  proof
    fix n show "no_loose_bound (?\<rho> n) 0"
      using closed_onD[OF inst_closed[OF ac' wf' ety'], of n] by (auto simp: prune_rho_def split: atom.splits)
  qed
  have tyt': "has_type W' Ts t T" by (rule has_type_agreeV[OF ty bt ag])
  have eq: "mk_subst (env_inst env') (tr t) = mk_subst ?\<rho> ?X"
    by (rule inst_extend_tr[OF ac wf ety ac' wf' ety' ext])
  have tr: "termip beta (mk_subst ?\<rho> ?X)"
    using inst_typable[OF ac' wf' ety' tyt'] eq by (simp add: typable_termip)
  have "\<beta>_nf (mk_subst ?\<rho> ?X) = \<beta>_nf (mk_subst ?\<rho> ?N)"
    by (rule \<beta>_nf_reds[OF tr fact8_1[OF red \<rho>closed], symmetric])
  moreover have "pruning (tau W') {n. \<exists>y. n = code (AVar y) \<and> vt_lookup (tenv env) y = None \<and>
      vt_lookup (tenv env') y \<noteq> None} ?\<rho>"
    unfolding pruning_def
  proof (intro conjI allI impI ballI)
    fix n assume nD: "n \<notin> {n. \<exists>y. n = code (AVar y) \<and> vt_lookup (tenv env) y = None \<and>
      vt_lookup (tenv env') y \<noteq> None}"
    show "?\<rho> n = dB.Var n"
    proof (cases "\<exists>y. n = code (AVar y) \<and> vt_lookup (tenv env) y = None")
      case True
      then obtain y where y: "n = code (AVar y)" "vt_lookup (tenv env) y = None" by blast
      with nD have "vt_lookup (tenv env') y = None" by blast
      with y show ?thesis by (simp add: prune_rho_def inst_unbound[OF ac' wf' ety'])
    next
      case False
      then show ?thesis by (auto simp: prune_rho_def split: atom.splits)
    qed
  next
    fix n assume "n \<in> {n. \<exists>y. n = code (AVar y) \<and> vt_lookup (tenv env) y = None \<and>
      vt_lookup (tenv env') y \<noteq> None}"
    then obtain y where y: "n = code (AVar y)" "vt_lookup (tenv env) y = None"
      "vt_lookup (tenv env') y \<noteq> None" by blast
    from pi[unfolded prunes_inst_def, rule_format, OF y(2,3)] obtain H ks m a where
      H: "env_inst env' (code (AVar y)) = Abs_m m (dB.Var (code (AVar H)) \<degree>\<degree> map BVar ks)"
        "vt_lookup (tenv env') H = None" "ty_arity (trty (W' y)) = m + a"
        "ty_arity (trty (W' H)) = length ks + a"
      by blast
    show "\<not> rigid_code n" using y by simp
    show "\<exists>H ks m a. ?\<rho> n = Abs_m m (dB.Var H \<degree>\<degree> map BVar ks) \<and> \<not> rigid_code H \<and>
        ty_arity (tau W' n) = m + a \<and> ty_arity (tau W' H) = length ks + a"
      using H y by (intro exI[of _ "code (AVar H)"] exI[of _ ks] exI[of _ m] exI[of _ a])
        (simp add: prune_rho_def)
    fix e show "(e, tau W') \<turnstile> ?\<rho> n : tau W' n"
      using typed_onD[OF inst_typed[OF ac' wf' ety'], of n e] y by (simp add: prune_rho_def)
  qed
  then have "msz (tau W') (\<beta>_nf (mk_subst ?\<rho> ?N)) = msz (tau W') ?N"
    by (rule msz_pruning[OF tyN nN])
  ultimately show ?thesis
    using msz_cong[of ?N "tau W" "tau W'"] FVN eq by (simp add: Ms_def)
qed

end
