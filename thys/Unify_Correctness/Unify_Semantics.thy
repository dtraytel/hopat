section \<open>Semantics of Disagreement Pairs\<close>

theory Unify_Semantics
  imports Unify_Monad
begin

context pure_sig_gen
begin

text \<open>
  A disagreement pair \<open>(rb, t, u)\<close> relates two terms under the binders \<open>rb\<close> (innermost first:
  \<open>Bound 0\<close> refers to \<open>hd rb\<close>). As for pattern unification, a type instantiation \<open>\<rho>\<close> and a
  substitution \<open>\<sigma>\<close> act on a term by \<^const>\<open>ap\<close>; the pair is solved if the instances are
  \<open>\<alpha>\<beta>\<eta>\<close>-equivalent. A pair is well-typed at \<open>\<rho>\<close> if both sides have the same type under the
  instantiated binders, and their loose bound variables are bound by \<open>rb\<close>.
\<close>

definition dvars :: "dpair list \<Rightarrow> (indexname \<times> ptyp) set" where
  "dvars dps = (\<Union>(rb, t, u)\<in>set dps. vars t \<union> vars u)"

definition dsolved :: "tinst \<Rightarrow> vsubst \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dsolved \<rho> \<sigma> dps \<longleftrightarrow> (\<forall>(rb, t, u)\<in>set dps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"

definition dtyped :: "tinst \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dtyped \<rho> dps \<longleftrightarrow> (\<forall>(rb, t, u)\<in>set dps. (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
    \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb))"

lemma dvars_simps [simp]:
  "dvars [] = {}" "dvars ((rb, t, u) # dps) = vars t \<union> vars u \<union> dvars dps" "dvars (dps @ dps') = dvars dps \<union> dvars dps'"
  by (auto simp: dvars_def)

lemma dsolved_simps [simp]:
  "dsolved \<rho> \<sigma> []" "dsolved \<rho> \<sigma> ((rb, t, u) # dps) \<longleftrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<and> dsolved \<rho> \<sigma> dps"
  "dsolved \<rho> \<sigma> (dps @ dps') \<longleftrightarrow> dsolved \<rho> \<sigma> dps \<and> dsolved \<rho> \<sigma> dps'"
  unfolding dsolved_def set_append ball_Un by auto

lemma dtyped_simps [simp]:
  "dtyped \<rho> []"
  "dtyped \<rho> ((rb, t, u) # dps) \<longleftrightarrow> (\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T) \<and>
    \<not> loose_bvar t (ilength rb) \<and> \<not> loose_bvar u (ilength rb) \<and> dtyped \<rho> dps"
  "dtyped \<rho> (dps @ dps') \<longleftrightarrow> dtyped \<rho> dps \<and> dtyped \<rho> dps'"
  unfolding dtyped_def set_append ball_Un by auto

lemma dsolved_mono: "dsolved \<rho> \<sigma> dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> dsolved \<rho> \<sigma> dps'"
  and dtyped_mono: "dtyped \<rho> dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> dtyped \<rho> dps'"
  and dvars_mono: "set dps' \<subseteq> set dps \<Longrightarrow> dvars dps' \<subseteq> dvars dps"
  unfolding dsolved_def dtyped_def dvars_def by blast+

lemma dsolved_set: "set dps = set dps' \<Longrightarrow> dsolved \<rho> \<sigma> dps \<longleftrightarrow> dsolved \<rho> \<sigma> dps'"
  and dtyped_set: "set dps = set dps' \<Longrightarrow> dtyped \<rho> dps \<longleftrightarrow> dtyped \<rho> dps'"
  and dvars_set: "set dps = set dps' \<Longrightarrow> dvars dps = dvars dps'"
  unfolding dsolved_def dtyped_def dvars_def by simp_all

subsection \<open>Flex-flex pairs as equations\<close>

text \<open>
  A pair \<open>(rb, t, u)\<close> stands for the equation of the abstractions of its sides over its
  binders (\<open>rb\<close> lists the binders innermost first). \<open>deqv E \<rho> dps\<close>: the pairs follow from the
  equations \<open>E\<close> by \<^const>\<open>eqv\<close>, in every environment of their binders.
\<close>

lemma integer_of_nat_nat_of_integer: "0 \<le> i \<Longrightarrow> integer_of_nat (nat_of_integer i) = i"
  by (simp add: integer_eq_iff integer_reps)

lemma integer_of_nat_nonneg: "0 \<le> integer_of_nat a"
  by (simp add: integer_less_eq_iff integer_of_nat.rep_eq)

lemma downto0_list_nth: "k < n \<Longrightarrow> downto0_list n ! k = integer_of_nat (n - 1 - k)"
  by (simp add: downto0_list_def rev_nth)

lemma wt_subst_Var: "wt_subst (\<lambda>x T. Var x T)"
  unfolding wt_subst_def closed_subst_def by (auto simp: closed_def)

lemma ap_Var: "ap \<rho> (\<lambda>x T. Var x T) t = inst \<rho> t"
proof -
  have "vsubst (\<lambda>x T. Var x T) s = s" for s by (induction s) auto
  then show ?thesis by (simp add: ap_def)
qed

lemma ap_Var_fun: "ap \<rho> (\<lambda>x T. Var x T) = inst \<rho>"
  by (rule ext) (rule ap_Var)

definition dp_eqs :: "tinst \<Rightarrow> dpair list \<Rightarrow> (pterm \<times> pterm) set" where
  "dp_eqs \<rho> dps = {(inst \<rho> (abs_list (rev rb) t), inst \<rho> (abs_list (rev rb) u)) | rb t u. (rb, t, u) \<in> set dps}"

definition deqv :: "(pterm \<times> pterm) set \<Rightarrow> tinst \<Rightarrow> dpair list \<Rightarrow> bool" where
  "deqv E \<rho> dps \<longleftrightarrow> (\<forall>(rb, t, u)\<in>set dps. \<forall>e T. bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow> e \<turnstile> inst \<rho> u : T \<longrightarrow>
    eqv E e (inst \<rho> t) (inst \<rho> u))"

lemma dp_eqs_simps [simp]:
  "dp_eqs \<rho> [] = {}" "dp_eqs \<rho> (dps @ dps') = dp_eqs \<rho> dps \<union> dp_eqs \<rho> dps'"
  by (auto simp: dp_eqs_def)

lemma dp_eqs_set: "set dps = set dps' \<Longrightarrow> dp_eqs \<rho> dps = dp_eqs \<rho> dps'"
  by (simp add: dp_eqs_def)

lemma deqv_set: "set dps = set dps' \<Longrightarrow> deqv E \<rho> dps \<longleftrightarrow> deqv E \<rho> dps'"
  by (simp add: deqv_def)

lemma deqv_simps [simp]:
  "deqv E \<rho> []" "deqv E \<rho> (dps @ dps') \<longleftrightarrow> deqv E \<rho> dps \<and> deqv E \<rho> dps'"
  by (simp_all add: deqv_def ball_Un)

lemma deqv_mono: "deqv E \<rho> dps \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> deqv E' \<rho> dps"
  unfolding deqv_def by (blast intro: eqv_mono)

lemma eqv_abs_list:
  "eqv E (pushes e (map snd bs)) s t \<Longrightarrow> \<forall>(x, T)\<in>set bs. cert_typ alg ar T \<Longrightarrow>
    eqv E e (abs_list bs s) (abs_list bs t)"
proof (induction bs arbitrary: e)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by (cases b)
  from Cons.prems b have "eqv E (pushes (e\<langle>0:T\<rangle>) (map snd bs)) s t" "cert_typ alg ar T" by auto
  from eqv_abs[OF Cons.IH[OF this(1)] this(2)] Cons.prems(2) b show ?case by auto
qed simp

lemma rev_inst_binders:
  "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)) = rev (map (\<lambda>b. tsubst \<rho> (snd b)) rb)"
  by (induction rb) auto

lemma bs_env_pushes:
  assumes "\<forall>(x, T)\<in>set rb. cert_typ alg ar (tsubst \<rho> T)"
  shows "bs_env \<rho> (pushes e (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)))) rb"
  unfolding bs_env_def rev_inst_binders
proof (intro conjI allI impI)
  fix i :: integer assume i: "0 \<le> i" "i < ilength rb"
  then have "nat_of_integer i < length rb" by (simp add: nat_of_integer_less_ilength)
  then show "pushes e (rev (map (\<lambda>b. tsubst \<rho> (snd b)) rb)) i = tsubst \<rho> (snd (rb ! nat_of_integer i))"
    using i by (simp add: pushes_nth ilength_eq)
qed (use assms in blast)

text \<open>The binders of a well-typed pair can be pushed onto any environment:\<close>

lemma dtyped_pushes:
  assumes ty: "dtyped \<rho> [(rb, t, u)]"
  obtains T where "bs_env \<rho> (pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)))) rb"
    "pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb))) \<turnstile> inst \<rho> t : T"
    "pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb))) \<turnstile> inst \<rho> u : T"
    "\<forall>(x, T)\<in>set (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)). cert_typ alg ar T"
proof -
  from ty obtain e T where bs: "bs_env \<rho> e rb" and tt: "e \<turnstile> inst \<rho> t : T" and tu: "e \<turnstile> inst \<rho> u : T"
    and lt: "\<not> loose_bvar t (ilength rb)" and lu: "\<not> loose_bvar u (ilength rb)"
    by auto
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  have c: "\<forall>(x, T)\<in>set rb. cert_typ alg ar (tsubst \<rho> T)" using bs by (simp add: bs_env_def)
  let ?e = "pushes e0 (map snd ?bs)"
  have bs': "bs_env \<rho> ?e rb" by (rule bs_env_pushes[OF c])
  have agree: "?e i = e i" if "0 \<le> i" "loose_bvar1 (inst \<rho> s) i" "\<not> loose_bvar s (ilength rb)" for i s
  proof -
    from that have "i < ilength rb" using loose_bvar1_imp loose_bvar_mono[of s i "ilength rb"] by fastforce
    with that(1) bs bs' show ?thesis by (simp add: bs_env_def)
  qed
  have "?e \<turnstile> inst \<rho> t : T" using typing_env_cong[OF tt] agree[OF _ _ lt] by blast
  moreover have "?e \<turnstile> inst \<rho> u : T" using typing_env_cong[OF tu] agree[OF _ _ lu] by blast
  moreover have "\<forall>(x, T)\<in>set ?bs. cert_typ alg ar T" using c by auto
  ultimately show ?thesis using that bs' by blast
qed

lemma dtyped_mem: "dtyped \<rho> dps \<Longrightarrow> (rb, t, u) \<in> set dps \<Longrightarrow> dtyped \<rho> [(rb, t, u)]"
  by (auto simp: dtyped_def)

text \<open>A pair that follows from equations gives its closed equation, in every environment:\<close>

lemma deqv_closed:
  assumes d: "deqv E \<rho> [(rb, t, u)]" and ty: "dtyped \<rho> [(rb, t, u)]"
  shows "eqv E e0 (inst \<rho> (abs_list (rev rb) t)) (inst \<rho> (abs_list (rev rb) u))"
proof -
  obtain T where bs: "bs_env \<rho> (pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)))) rb"
    and tt: "pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb))) \<turnstile> inst \<rho> t : T"
    and tu: "pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb))) \<turnstile> inst \<rho> u : T"
    and c: "\<forall>(x, T)\<in>set (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)). cert_typ alg ar T"
    by (rule dtyped_pushes[OF ty])
  from d bs tt tu have "eqv E (pushes e0 (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)))) (inst \<rho> t) (inst \<rho> u)"
    by (auto simp: deqv_def)
  from eqv_abs_list[OF this c] show ?thesis by (simp add: inst_abs_list)
qed

text \<open>A pair is a consequence of its closed equation:\<close>

lemma closed_eqv_use:
  assumes ceq: "eqv E e (inst \<rho> (abs_list (rev rb) t)) (inst \<rho> (abs_list (rev rb) u))" and bs: "bs_env \<rho> e rb"
    and tt: "e \<turnstile> inst \<rho> t : T" and tu: "e \<turnstile> inst \<rho> u : T"
    and lt: "\<not> loose_bvar t (ilength rb)" and lu: "\<not> loose_bvar u (ilength rb)"
  shows "eqv E e (inst \<rho> t) (inst \<rho> u)"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  let ?js = "downto0_list (length rb)"
  have c: "\<forall>(x, T)\<in>set rb. cert_typ alg ar (tsubst \<rho> T)" using bs by (simp add: bs_env_def)
  have cs: "\<forall>T\<in>snd ` set ?bs. cert_typ alg ar T" using c by auto
  have len: "length ?bs = length ?js" by (simp add: downto0_list_def)
  have js0: "\<forall>j\<in>set ?js. 0 \<le> j" by (auto simp: downto0_list_def integer_of_nat_nonneg)
  have rjs: "rev ?js = map integer_of_nat [0..<length rb]" by (simp add: downto0_list_def)
  have bren_id: "bren (rev ?js) k = k" if "0 \<le> k" "k < ilength rb" for k
  proof -
    have "k < ilength ?js" using that by (simp add: downto0_list_def ilength_eq)
    with bren_rev[OF that(1) this] that rjs show ?thesis
      by (simp add: nat_of_integer_less_ilength ilength_eq integer_of_nat_nat_of_integer)
  qed
  have ren: "rename (bren (rev ?js)) 0 (inst \<rho> s) = inst \<rho> s" if "\<not> loose_bvar s (ilength rb)" for s
    by (rule rename_id_on[where m="ilength rb"]) (use bren_id that in simp_all)
  have tys: "map snd ?bs = map e ?js"
  proof (rule nth_equalityI)
    show "length (map snd ?bs) = length (map e ?js)" by (simp add: downto0_list_def)
    fix i assume "i < length (map snd ?bs)"
    then have i: "i < length rb" by simp
    let ?k = "integer_of_nat (length rb - 1 - i)"
    have k: "0 \<le> ?k" "?k < ilength rb" "nat_of_integer ?k = length rb - 1 - i"
      using i by (simp_all add: ilength_eq integer_reps)
    have "e ?k = tsubst \<rho> (snd (rb ! (length rb - 1 - i)))"
      using bs k unfolding bs_env_def by metis
    moreover have "length ?js = length rb" by (simp add: downto0_list_def)
    ultimately show "map snd ?bs ! i = map e ?js ! i"
      using i by (simp add: rev_nth downto0_list_nth split_def)
  qed
  have pe: "pushes e (map snd ?bs) \<turnstile> inst \<rho> s : T" if "e \<turnstile> inst \<rho> s : T" "\<not> loose_bvar s (ilength rb)" for s
  proof (rule typing_env_cong[OF that(1)])
    fix i assume i: "0 \<le> i" "loose_bvar1 (inst \<rho> s) i"
    then have "i < ilength rb" using that(2) loose_bvar1_imp loose_bvar_mono[of s i "ilength rb"] by fastforce
    with i(1) bs bs_env_pushes[OF c, of e] show "pushes e (map snd ?bs) i = e i" by (simp add: bs_env_def)
  qed
  have tl: "e \<turnstile> inst \<rho> (abs_list (rev rb) s) \<degree>\<degree> map Bound ?js : T"
    if "e \<turnstile> inst \<rho> s : T" "\<not> loose_bvar s (ilength rb)" for s
  proof -
    have "e \<turnstile> inst \<rho> (abs_list (rev rb) s) : map snd ?bs \<Rrightarrow> T"
      using typing_abs_list[OF pe[OF that] cs] by (simp add: inst_abs_list)
    moreover have "e \<tturnstile> map Bound ?js : map e ?js" by (rule typings_Bounds) (use js0 in auto)
    ultimately show ?thesis using tys by (auto intro: list_app_typeI)
  qed
  have red: "inst \<rho> (abs_list (rev rb) s) \<degree>\<degree> map Bound ?js \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> s" if "\<not> loose_bvar s (ilength rb)" for s
    using beta_abs_list_apps[OF len js0, of "inst \<rho> s"] ren[OF that] by (simp add: inst_abs_list)
  have cv: "eqv E e (inst \<rho> (abs_list (rev rb) s) \<degree>\<degree> map Bound ?js) (inst \<rho> s)"
    if "e \<turnstile> inst \<rho> s : T" "\<not> loose_bvar s (ilength rb)" for s
    using beta_eta_conv[OF beta_reds_beta_eta_reds[OF red[OF that(2)]]] tl[OF that] that(1)
    by (intro eqv_conv) (auto simp: wt_def)
  from eqv_apps_head[OF ceq tl[OF tt lt] tl[OF tu lu]]
  show ?thesis using cv[OF tt lt] cv[OF tu lu] by (blast intro: eqv_trans eqv_sym)
qed

lemma dp_eqs_use:
  assumes p: "(rb, t, u) \<in> set dps" and E: "dp_eqs \<rho> dps \<subseteq> E" and bs: "bs_env \<rho> e rb"
    and tt: "e \<turnstile> inst \<rho> t : T" and tu: "e \<turnstile> inst \<rho> u : T"
    and lt: "\<not> loose_bvar t (ilength rb)" and lu: "\<not> loose_bvar u (ilength rb)"
  shows "eqv E e (inst \<rho> t) (inst \<rho> u)"
proof (rule closed_eqv_use[OF _ bs tt tu lt lu])
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  have "dtyped \<rho> [(rb, t, u)]" using bs tt tu lt lu by auto
  then obtain T' where t': "pushes e (map snd ?bs) \<turnstile> inst \<rho> t : T'"
    and u': "pushes e (map snd ?bs) \<turnstile> inst \<rho> u : T'" and c: "\<forall>(x, T)\<in>set ?bs. cert_typ alg ar T"
    by (rule dtyped_pushes)
  have cs: "\<forall>T\<in>snd ` set ?bs. cert_typ alg ar T" using c by auto
  have "(inst \<rho> (abs_list (rev rb) t), inst \<rho> (abs_list (rev rb) u)) \<in> E"
    using p E by (auto simp: dp_eqs_def)
  from eqv_ax[OF this] typing_abs_list[OF t' cs] typing_abs_list[OF u' cs]
  show "eqv E e (inst \<rho> (abs_list (rev rb) t)) (inst \<rho> (abs_list (rev rb) u))"
    by (simp add: inst_abs_list)
qed

text \<open>Equations that follow from other equations can be replaced by them:\<close>

lemma eqv_subst_eqs:
  "eqv (A \<union> B) e s t \<Longrightarrow> (\<And>l r e. (l, r) \<in> B \<Longrightarrow> eqv A' e l r) \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> eqv A' e s t"
  by (induction rule: eqv.induct) (auto intro: eqv.intros)

lemma conv_abs_list:
  "wt (abs_list bs s) \<Longrightarrow> wt (abs_list bs t) \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> abs_list bs s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs t"
proof (induction bs)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  from Cons.prems b have "wt (abs_list bs s)" "wt (abs_list bs t)" by (auto dest: wt_AbsD)
  from Cons.IH[OF this Cons.prems(3)] Cons.prems b show ?case by (simp add: conv_Abs)
qed simp

text \<open>A solved pair solves its closed equation:\<close>

lemma dsolved_closed:
  assumes ty: "dtyped \<rho> [(rb, t, u)]" and \<sigma>: "wt_subst \<sigma>" and s: "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "vsubst \<sigma> (inst \<rho> (abs_list (rev rb) t)) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> (inst \<rho> (abs_list (rev rb) u))"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (rev rb)"
  obtain T where tt: "pushes undefined (map snd ?bs) \<turnstile> inst \<rho> t : T"
    and tu: "pushes undefined (map snd ?bs) \<turnstile> inst \<rho> u : T" and c: "\<forall>(x, T)\<in>set ?bs. cert_typ alg ar T"
    by (rule dtyped_pushes[OF ty])
  have cs: "\<forall>T\<in>snd ` set ?bs. cert_typ alg ar T" using c by auto
  have "wt (abs_list ?bs (ap \<rho> \<sigma> s))" if "pushes undefined (map snd ?bs) \<turnstile> inst \<rho> s : T" for s
    using typing_abs_list[OF typing_ap[OF that \<sigma>] cs] by (auto simp: wt_def)
  from conv_abs_list[OF this[OF tt] this[OF tu] s]
  show ?thesis using ap_abs_list[of \<rho> \<sigma> "rev rb" t] ap_abs_list[of \<rho> \<sigma> "rev rb" u] by (simp add: ap_def)
qed

text \<open>A well-typed pair follows from the equations that include its closed equation:\<close>

lemma deqv_self: "dtyped \<rho> dps \<Longrightarrow> dp_eqs \<rho> dps \<subseteq> E \<Longrightarrow> deqv E \<rho> dps"
  unfolding deqv_def by (auto intro: dp_eqs_use simp: dtyped_def)

lemma deqv_single:
  "deqv E \<rho> [(rb, t, u)] \<longleftrightarrow>
    (\<forall>e T. bs_env \<rho> e rb \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow> e \<turnstile> inst \<rho> u : T \<longrightarrow> eqv E e (inst \<rho> t) (inst \<rho> u))"
  by (simp add: deqv_def)

lemma deqv_Cons: "deqv E \<rho> (p # dps) \<longleftrightarrow> deqv E \<rho> [p] \<and> deqv E \<rho> dps"
  using deqv_simps(2)[of E \<rho> "[p]" dps] by simp

lemma deqv_single_sym: "deqv E \<rho> [(rb, u, t)] \<Longrightarrow> deqv E \<rho> [(rb, t, u)]"
  unfolding deqv_single by (blast intro: eqv.eqv_sym)

lemma dp_eqs_Cons:
  "dp_eqs \<rho> ((rb, t, u) # dps) = insert (inst \<rho> (abs_list (rev rb) t), inst \<rho> (abs_list (rev rb) u)) (dp_eqs \<rho> dps)"
  by (auto simp: dp_eqs_def)

text \<open>The closed equations of well-typed pairs hold in every environment:\<close>

lemma dp_eqs_eqv:
  assumes ty: "dtyped \<rho> dps" and E: "dp_eqs \<rho> dps \<subseteq> E" and lr: "(l, r) \<in> dp_eqs \<rho> dps"
  shows "eqv E e l r"
proof -
  from lr obtain rb t u where p: "(rb, t, u) \<in> set dps" and l: "l = inst \<rho> (abs_list (rev rb) t)"
    and r: "r = inst \<rho> (abs_list (rev rb) u)"
    by (auto simp: dp_eqs_def)
  have "dp_eqs \<rho> [(rb, t, u)] \<subseteq> E" using E p by (auto simp: dp_eqs_def)
  from deqv_closed[OF deqv_self[OF dtyped_mem[OF ty p] this] dtyped_mem[OF ty p]] show ?thesis
    unfolding l r .
qed

text \<open>
  A step from \<open>(env, dps)\<close> to \<open>(env', dps')\<close> extends the environment, and for every type
  instantiation that solves the type environment of a final extension \<open>env''\<close>, it keeps the
  typing invariants of the pattern development, and the pairs \<open>dps\<close> follow from the bindings of
  \<open>env'\<close> and the pairs \<open>dps'\<close> as equations. Every solution of \<open>env''\<close> that solves \<open>dps'\<close> then
  solves \<open>dps\<close> (\<open>dstepD\<close>). The set \<open>X\<close> holds the variables of other pairs, whose types stay
  consistent. This generalises \<^const>\<open>step_ok\<close> of pattern unification to lists of pairs.
\<close>
definition dstep :: "env \<Rightarrow> dpair list \<Rightarrow> env \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dstep env dps env' dps' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> nfree env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      dtyped \<rho> dps \<longrightarrow> vinv \<rho> env (X \<union> dvars dps) \<longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps)"

lemma deqv_eqs:
  assumes "deqv (A \<union> B) \<rho> dps" "\<And>l r e. (l, r) \<in> B \<Longrightarrow> eqv A' e l r" "A \<subseteq> A'"
  shows "deqv A' \<rho> dps"
  using assms(1) unfolding deqv_def by (fast intro: eqv_subst_eqs[OF _ assms(2) assms(3)])

lemma deqv_trans:
  assumes d1: "deqv (binds \<rho> env1 \<union> dp_eqs \<rho> dps1) \<rho> dps" and d2: "deqv (binds \<rho> env2 \<union> dp_eqs \<rho> dps2) \<rho> dps1"
    and ty: "dtyped \<rho> dps1" and ex: "extends env1 env2"
  shows "deqv (binds \<rho> env2 \<union> dp_eqs \<rho> dps2) \<rho> dps"
proof (rule deqv_eqs[OF d1])
  fix l r e assume "(l, r) \<in> dp_eqs \<rho> dps1"
  then obtain rb t u where p: "(rb, t, u) \<in> set dps1" and l: "l = inst \<rho> (abs_list (rev rb) t)"
    and r: "r = inst \<rho> (abs_list (rev rb) u)"
    by (auto simp: dp_eqs_def)
  from d2 p have "deqv (binds \<rho> env2 \<union> dp_eqs \<rho> dps2) \<rho> [(rb, t, u)]" by (auto simp: deqv_def)
  from deqv_closed[OF this dtyped_mem[OF ty p]] show "eqv (binds \<rho> env2 \<union> dp_eqs \<rho> dps2) e l r"
    unfolding l r .
qed (use binds_extends[OF ex] in blast)

text \<open>Pairs that follow from the bindings of an extension and from solved pairs are solved:\<close>

lemma deqv_dsolved:
  assumes d: "deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps" and ty: "dtyped \<rho> dps" and ty': "dtyped \<rho> dps'"
    and ex: "extends env' env''" and s: "solution \<rho> \<sigma> env''" and sd: "dsolved \<rho> \<sigma> dps'"
  shows "dsolved \<rho> \<sigma> dps"
proof -
  have E: "vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r" if "(l, r) \<in> dp_eqs \<rho> dps'" for l r
  proof -
    from that obtain rb t u where p: "(rb, t, u) \<in> set dps'" and l: "l = inst \<rho> (abs_list (rev rb) t)"
      and r: "r = inst \<rho> (abs_list (rev rb) u)"
      by (auto simp: dp_eqs_def)
    from sd p have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (auto simp: dsolved_def)
    from dsolved_closed[OF dtyped_mem[OF ty' p] solutionD(3)[OF s] this] show ?thesis unfolding l r .
  qed
  have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" if p: "(rb, t, u) \<in> set dps" for rb t u
  proof -
    from ty p obtain e T where "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
      by (fastforce simp: dtyped_def)
    with d p have "eqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') e (inst \<rho> t) (inst \<rho> u)" by (auto simp: deqv_def)
    then have "eqv (binds \<rho> env'' \<union> dp_eqs \<rho> dps') e (inst \<rho> t) (inst \<rho> u)"
      by (rule eqv_mono) (use binds_extends[OF ex] in blast)
    from eqv_ap[OF this s E] show ?thesis .
  qed
  then show ?thesis by (auto simp: dsolved_def)
qed

lemma dstepI:
  assumes "extends env env'"
    and "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow> nfree env'' \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
  shows "dstep env dps env' dps'"
  using assms unfolding dstep_def by blast

lemma dstepD:
  assumes "dstep env dps env' dps'"
  shows "extends env env'"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow> nfree env'' \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps)"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow> nfree env'' \<Longrightarrow> deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
proof -
  show "extends env env'" using assms unfolding dstep_def by blast
  assume "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env" "dtyped \<rho> dps" "vinv \<rho> env (X \<union> dvars dps)"
    "nfree env''"
  with assms have r: "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
    unfolding dstep_def by blast
  then show "deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps" by blast
  from r \<open>dtyped \<rho> dps\<close> \<open>extends env' env''\<close>
  show "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps)"
    using deqv_dsolved by blast
qed

lemma dstep_refl: "dstep env dps env dps"
  by (rule dstepI) (auto intro: deqv_self)

lemma dstep_trans:
  assumes s1: "dstep env dps env1 dps1" and s2: "dstep env1 dps1 env2 dps2"
  shows "dstep env dps env2 dps2"
proof (rule dstepI)
  note e1 = dstepD(1)[OF s1] and e2 = dstepD(1)[OF s2]
  show "extends env env2" by (rule extends_trans[OF e1 e2])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" and ex: "extends env2 env''" and w: "wt_env \<rho> env"
    and d: "dtyped \<rho> dps" and v: "vinv \<rho> env (X \<union> dvars dps)" and nf: "nfree env''"
  have ex1: "extends env1 env''" by (rule extends_trans[OF e2 ex])
  from dstepD(2,3)[OF s1 t ex1 w d v nf] have r1: "wt_env \<rho> env1" "dtyped \<rho> dps1" "vinv \<rho> env1 (X \<union> dvars dps1)"
    "deqv (binds \<rho> env1 \<union> dp_eqs \<rho> dps1) \<rho> dps"
    by blast+
  from dstepD(2,3)[OF s2 t ex r1(1-3) nf] deqv_trans[OF r1(4) _ r1(2) e2]
  show "wt_env \<rho> env2 \<and> dtyped \<rho> dps2 \<and> vinv \<rho> env2 (X \<union> dvars dps2) \<and>
      deqv (binds \<rho> env2 \<union> dp_eqs \<rho> dps2) \<rho> dps"
    by blast
qed

text \<open>Other pairs are carried along unchanged:\<close>

lemma dstep_frame:
  assumes s: "dstep env dps env' dps'"
  shows "dstep env (dps @ fs) env' (dps' @ fs)"
proof (rule dstepI)
  show "extends env env'" by (rule dstepD(1)[OF s])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" and ex: "extends env' env''" and w: "wt_env \<rho> env"
    and d: "dtyped \<rho> (dps @ fs)" and v: "vinv \<rho> env (X \<union> dvars (dps @ fs))" and nf: "nfree env''"
  have v': "vinv \<rho> env ((X \<union> dvars fs) \<union> dvars dps)" using v by (simp add: Un_ac)
  from dstepD(2,3)[OF s t ex w _ v' nf] d
  have r: "wt_env \<rho> env'" "dtyped \<rho> dps'" "vinv \<rho> env' ((X \<union> dvars fs) \<union> dvars dps')"
    "deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
    by auto
  have "deqv (binds \<rho> env' \<union> dp_eqs \<rho> (dps' @ fs)) \<rho> dps" by (rule deqv_mono[OF r(4)]) auto
  moreover have "deqv (binds \<rho> env' \<union> dp_eqs \<rho> (dps' @ fs)) \<rho> fs" using d by (auto intro: deqv_self)
  ultimately show "wt_env \<rho> env' \<and> dtyped \<rho> (dps' @ fs) \<and> vinv \<rho> env' (X \<union> dvars (dps' @ fs)) \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> (dps' @ fs)) \<rho> (dps @ fs)"
    using d r(1-3) by (simp add: Un_ac)
qed

lemma dstep_set:
  assumes "dstep env dps env' dps'" "set dps = set ds" "set dps' = set ds'"
  shows "dstep env ds env' ds'"
  using assms unfolding dstep_def by (simp add: deqv_set[OF assms(2)] dtyped_set[OF assms(2)]
    dvars_set[OF assms(2)] dp_eqs_set[OF assms(3)] dtyped_set[OF assms(3)] dvars_set[OF assms(3)])

text \<open>A sound step of pattern unification is a step on one pair:\<close>

lemma step_ok_dstep:
  assumes "step_ok env bs s t env'"
  shows "dstep env [(bs, s, t)] env' []"
proof (rule dstepI)
  show "extends env env'" by (rule step_okD(1)[OF assms])
  fix \<rho> env'' X assume t: "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env"
    and d: "dtyped \<rho> [(bs, s, t)]" and v: "vinv \<rho> env (X \<union> dvars [(bs, s, t)])" and nf: "nfree env''"
  have v': "vinv \<rho> env (X \<union> vars s \<union> vars t)" using v by (simp add: Un_assoc)
  from d obtain e T where w: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
    and l: "\<not> loose_bvar s (ilength bs)" "\<not> loose_bvar t (ilength bs)" by auto
  from step_okD(2)[OF assms t w v' l nf] have r: "wt_env \<rho> env'" "vinv \<rho> env' X" by auto
  have "deqv (binds \<rho> env') \<rho> [(bs, s, t)]"
    unfolding deqv_def using step_okD(2)[OF assms t _ _ _ v' l nf] by auto
  with r show "wt_env \<rho> env' \<and> dtyped \<rho> [] \<and> vinv \<rho> env' (X \<union> dvars []) \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> []) \<rho> [(bs, s, t)]"
    by simp
qed
end

subsection \<open>Without loose names\<close>

context pure_sig
begin

lemma dstep_def:
  "dstep env dps env' dps' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> env'' X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> dtyped \<rho> dps \<longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps)"
  by (simp add: dstep_def)

lemma dstepI:
  assumes "extends env env'"
    and "\<And>\<rho> env'' X. tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
  shows "dstep env dps env' dps'"
  using assms by (intro dstepI) simp_all

lemma dstepD:
  assumes "dstep env dps env' dps'"
  shows "extends env env'"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow>
      wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> dsolved \<rho> \<sigma> dps' \<longrightarrow> dsolved \<rho> \<sigma> dps)"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> dtyped \<rho> dps \<Longrightarrow>
      vinv \<rho> env (X \<union> dvars dps) \<Longrightarrow> deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> dps"
  by (rule dstepD(1)[OF assms], (rule dstepD(2)[OF assms]; (assumption | simp)),
    (rule dstepD(3)[OF assms]; (assumption | simp)))

end

end
