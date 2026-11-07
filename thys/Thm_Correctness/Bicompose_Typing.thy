section \<open>Well-Formed Problems of Unification\<close>

theory Bicompose_Typing
  imports Bicompose_Sound
begin

text \<open>
  The unifiers that \<open>bicompose_aux\<close> enumerates are characterized for well-formed problems
  (\<^const>\<open>pure_sig.pinv_all\<close>, the invariant \<^const>\<open>pure_sig.sinv\<close> of unification). The
  problems are well-formed if the proof state and the rule are well-typed and their type
  variables have unique sorts; if the rule is incremented, variables with the same name must
  also have the same type, otherwise \<open>bicompose_aux\<close> unifies their types.
\<close>

context pure_sig
begin

subsection \<open>Well-typed theorems\<close>

text \<open>
  A theorem with maximal index \<open>m\<close>: its proposition is well-typed and closed, its hypotheses
  are well-typed, closed and contain no schematic variables or type variables (as
  \<open>Thm.assume\<close> requires), and both sides of each flex-flex pair are closed and have a common
  type; the indices of the schematic variables and type variables are at most \<open>m\<close>.
\<close>

definition wt_thm :: "integer \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "wt_thm m hs tps P \<longleftrightarrow> wtp P \<and> ibelow m P \<and> (\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}) \<and>
    (\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow m t \<and> ibelow m u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T))"

definition vars_thm :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vars_thm tps P = vars P \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u)"

definition tvars_thm :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> (indexname \<times> psort) set" where
  "tvars_thm tps P = ttvars P \<union> (\<Union>(t, u)\<in>set tps. ttvars t \<union> ttvars u)"

text \<open>Variables with the same name have the same type:\<close>

definition vtcons :: "(indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vtcons X \<longleftrightarrow> (\<forall>x T U. (x, T) \<in> X \<longrightarrow> (x, U) \<in> X \<longrightarrow> T = U)"

lemma finite_ttvars [simp]: "finite (ttvars t)"
proof -
  have "finite (typs t)" by (induction t) auto
  then show ?thesis by (simp add: ttvars_def)
qed

lemma finite_vars_thm [simp]: "finite (vars_thm tps P)"
  by (auto simp: vars_thm_def)

lemma finite_tvars_thm [simp]: "finite (tvars_thm tps P)"
  by (auto simp: tvars_thm_def)

lemma vars_typs_cert: "e \<turnstile> t : T \<Longrightarrow> (x, U) \<in> vars t \<Longrightarrow> cert_typ alg ar U"
  using typing_typs vars_typs by blast

lemma vtvars_ttvars: "(x, U) \<in> vars t \<Longrightarrow> tvars U \<subseteq> ttvars t"
  using vars_typs[of x U t] unfolding ttvars_def by blast

lemma tcert_ttvars: "e \<turnstile> t : T \<Longrightarrow> tcert alg (ttvars t)"
proof -
  assume ty: "e \<turnstile> t : T"
  have "sort_ok alg S" if "(v, S) \<in> tvars U" "cert_typ alg ar U" for v S U
    using that by (induction U) (auto simp: cert_typ_def)
  with typing_typs[OF ty] show ?thesis by (auto simp: tcert_def ttvars_def)
qed

subsection \<open>Well-formed problems\<close>

lemma tcovered_sub: "P \<subseteq> K \<Longrightarrow> tcovered \<theta> K P"
  by (auto simp: tcovered_def uvarsA_def)

lemma vt_is_empty_vt_empty [simp]: "vt_is_empty vt_empty"
  by transfer simp

lemma empty_env_simps [simp]:
  "maxidx (empty_env m) = m" "tenv (empty_env m) = vt_empty" "tyenv (empty_env m) = vt_empty"
  "tvars_env vt_empty = {}"
  by (simp_all add: empty_env_def tvars_env_def vt_is_empty_lookup)

text \<open>The environment of an incremented rule:\<close>

lemma einv_empty_env:
  assumes "scons A" "\<forall>p\<in>A. snd (fst p) \<le> m" "tcert alg A"
  shows "einv A A (empty_env m)"
  using assms
  by (simp add: einv_def tvinv_def tinv_def tacyc_empty scert_def tsorted_empty
      acyc_def dep_def acyclic_def closed_env_def bbelow_def vt_is_empty_lookup tcovered_sub)

text \<open>A problem in an environment without term bindings is well-formed if its sides are closed and have a common type, and the types of its variables are consistent:\<close>

lemma sinv_intro:
  assumes ei: "einv A K env" and te: "vt_is_empty (tenv env)"
    and X: "finite X" "below (maxidx env) X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> vcons \<rho> X"
    and tus: "\<forall>(t, u)\<in>set tus. vars t \<union> vars u \<subseteq> X \<and> ttvars t \<union> ttvars u \<subseteq> A \<and> closed t \<and> closed u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "sinv A K X env (tdps tus)"
proof -
  have ev: "evars env = {}" using te by (simp add: evars_def bnds_def vt_is_empty_lookup)
  have "winv env X"
    unfolding winv_def
  proof (intro allI impI conjI)
    fix \<rho> assume "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    then show "vinv \<rho> env X" using vc X(2) ev by (simp add: vinv_def)
  qed (use te in \<open>simp add: wt_env_def vt_is_empty_lookup\<close>)
  moreover have "pok A env [] X t u" if "(t, u) \<in> set tus" for t u
  proof -
    from tus that have h: "vars t \<union> vars u \<subseteq> X" "ttvars t \<union> ttvars u \<subseteq> A" "closed t" "closed u"
      and "\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T" by auto
    then obtain T where ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
    note t = h ty
    have "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T" if "cert_inst \<rho>" for \<rho>
      using typing_inst[OF t(5) cert_inst_inst_ok[OF that]] typing_inst[OF t(6) cert_inst_inst_ok[OF that]]
      by (auto simp: bs_env_def)
    then show ?thesis
      using t X(3) ev by (auto simp: pok_def btvars_def closed_def)
  qed
  ultimately show ?thesis using ei by (auto simp: sinv_def)
qed


subsection \<open>Unification of the types of variables\<close>

text \<open>
  \<open>unify_var_types\<close> collects the types of each variable of the proof state and the rule in a
  table and unifies them.
\<close>

definition vtab :: "(indexname \<times> ptyp list) list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vtab tab = {(x, T). \<exists>Ts. (x, Ts) \<in> set tab \<and> T \<in> set Ts}"

lemma vtab_simps: "vtab [] = {}" "vtab ((x, Ts) # tab) = Pair x ` set Ts \<union> vtab tab"
  by (auto simp: vtab_def)

lemma vtab_insert_list: "vtab (insert_list xT tab) = insert xT (vtab tab)"
  by (induction xT tab rule: insert_list.induct) (auto simp: vtab_simps list_ex_iff)

lemma fst_insert_list: "fst ` set (insert_list (x, T) tab) = insert x (fst ` set tab)"
  by (induction "(x, T)" tab rule: insert_list.induct) auto

lemma distinct_insert_list: "distinct (map fst tab) \<Longrightarrow> distinct (map fst (insert_list xT tab))"
proof (induction xT tab rule: insert_list.induct)
  case (2 xi T yj Ts tab)
  then show ?case using fst_insert_list[of xi T tab] by auto
qed simp

lemma vtab_add_vars: "vtab (add_vars t tab) = vars t \<union> vtab tab"
  by (induction t tab rule: add_vars.induct) (auto simp: vtab_insert_list)

lemma distinct_add_vars: "distinct (map fst tab) \<Longrightarrow> distinct (map fst (add_vars t tab))"
  by (induction t tab rule: add_vars.induct) (auto simp: distinct_insert_list)

lemma set_insert_key: "set (insert_key p qs) = insert p (set qs)"
  by (induction p qs rule: insert_key.induct) auto

lemma distinct_insert_key:
  "distinct (map fst (insert_key p qs)) \<longleftrightarrow> fst p \<notin> fst ` set qs \<and> distinct (map fst qs)"
  by (induction p qs rule: insert_key.induct) (auto simp: set_insert_key)

lemma set_sort_keys: "set (sort_keys tab) = set tab"
  by (induction tab) (simp_all add: sort_keys_def set_insert_key)

lemma distinct_sort_keys: "distinct (map fst (sort_keys tab)) \<longleftrightarrow> distinct (map fst tab)"
proof (induction tab)
  case (Cons a tab)
  then show ?case
    using set_sort_keys[of tab] by (simp add: sort_keys_def distinct_insert_key)
qed (simp add: sort_keys_def)

lemma vars_full_prop_of: "ok (full_prop_of tps P) p \<Longrightarrow> vars p = vars_thm tps P"
proof -
  assume "ok (full_prop_of tps P) p"
  then obtain eqs where l: "list_all2 (\<lambda>tu eq. ok (mk_equals tu) eq) tps eqs" and p: "p = list_implies eqs P"
    by (auto simp: full_prop_of_def ok_mapM)
  from l have "(\<Union>A\<in>set eqs. vars A) = (\<Union>(t, u)\<in>set tps. vars t \<union> vars u)"
    by (induction rule: list_all2_induct) (auto simp: mk_equals_def)
  then show ?thesis by (simp add: p vars_list_implies vars_thm_def Un_ac)
qed

text \<open>Type unification keeps the invariant of the environments:\<close>

lemma unify_types_einv:
  assumes "ok (unify_types alg T U env) env'" "einv A K env" "finite K"
    "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar T"
    "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar U"
  shows "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
    maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
proof -
  have "(\<exists>env''. unify_types alg T U env = return env'' \<and> einv A K env'' \<and> tenv env'' = tenv env \<and>
      textends (tyenv env) (tyenv env'') \<and> maxidx env \<le> maxidx env'' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'') \<and> tnew A env A env'' \<and>
      (\<forall>\<rho>. tsol (tyenv env'') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env'' = tyenv env \<or> card (uvarsA (tyenv env'') K) < card (uvarsA (tyenv env) K))) \<or>
    (\<exists>u. unify_types alg T U env = raise (Unif u))"
    by (rule unify_types_term[OF assms(2,3,4) _ _ assms(6)]) (use assms(5,7) in \<open>simp_all add: cert_typ_def\<close>)
  then show ?thesis
  proof
    assume "\<exists>env''. unify_types alg T U env = return env'' \<and> einv A K env'' \<and> tenv env'' = tenv env \<and>
      textends (tyenv env) (tyenv env'') \<and> maxidx env \<le> maxidx env'' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'') \<and> tnew A env A env'' \<and>
      (\<forall>\<rho>. tsol (tyenv env'') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U) \<and>
      (tyenv env'' = tyenv env \<or> card (uvarsA (tyenv env'') K) < card (uvarsA (tyenv env) K))"
    then obtain env'' where u: "unify_types alg T U env = return env''"
      and p: "einv A K env'' \<and> tenv env'' = tenv env \<and>
      textends (tyenv env) (tyenv env'') \<and> maxidx env \<le> maxidx env'' \<and>
      tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'') \<and>
      (\<forall>\<rho>. tsol (tyenv env'') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
      by blast
    from assms(1) u have "env' = env''" by (simp add: return_def)
    with p show ?thesis by simp
  next
    assume "\<exists>u. unify_types alg T U env = raise (Unif u)"
    with assms(1) show ?thesis by (auto simp: raise_def)
  qed
qed

lemma foldM_unify_types_einv:
  assumes "ok (foldM (\<lambda>U env. unify_types alg T U env) Us env) env'" "einv A K env" "finite K"
    "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar T"
    "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar U"
  shows "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
    maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> (\<forall>U\<in>set Us. tsubst \<rho> T = tsubst \<rho> U))"
  using assms
proof (induction Us arbitrary: env)
  case (Cons U Us)
  from Cons.prems(1) obtain e1 where u: "ok (unify_types alg T U env) e1"
    and f: "ok (foldM (\<lambda>U env. unify_types alg T U env) Us e1) env'"
    by auto
  have tU: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar U" using Cons.prems(6) by auto
  note s1 = unify_types_einv[OF u Cons.prems(2,3,4,5) tU]
  have IH: "einv A K env' \<and> tenv env' = tenv e1 \<and> textends (tyenv e1) (tyenv env') \<and>
      maxidx e1 \<le> maxidx env' \<and> tvars_env (tyenv e1) \<subseteq> tvars_env (tyenv env') \<and>
      (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> (\<forall>U\<in>set Us. tsubst \<rho> T = tsubst \<rho> U))"
  proof (rule Cons.IH[OF f _ Cons.prems(3) _ Cons.prems(5)])
    show "einv A K e1" using s1 by blast
    show "tvars T \<subseteq> tvars_env (tyenv e1) \<union> A" using Cons.prems(4) s1 by blast
    show "\<forall>U\<in>set Us. tvars U \<subseteq> tvars_env (tyenv e1) \<union> A \<and> cert_typ alg ar U"
      using Cons.prems(6) s1 by fastforce
  qed
  have "tsubst \<rho> T = tsubst \<rho> U" if "tsol (tyenv env') \<rho>" for \<rho>
  proof -
    have "tsol (tyenv e1) \<rho>" by (rule tsol_textends[OF _ that]) (use IH in blast)
    with s1 show ?thesis by blast
  qed
  moreover have "textends (tyenv env) (tyenv env')" by (rule textends_trans) (use s1 IH in blast)+
  moreover have "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')" using s1 IH by blast
  moreover have "tenv env' = tenv env" "maxidx env \<le> maxidx env'" "einv A K env'" using s1 IH by auto
  moreover have "\<forall>U\<in>set Us. tsubst \<rho> T = tsubst \<rho> U" if "tsol (tyenv env') \<rho>" for \<rho>
    using IH that by blast
  ultimately show ?case by simp
qed (simp add: return_def textends_def)

lemma unify_vars_einv:
  assumes "ok (unify_vars alg Ts env) env'" "einv A K env" "finite K"
    "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar T"
  shows "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and>
    maxidx env \<le> maxidx env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> (\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U))"
proof (cases Ts)
  case Nil
  with assms show ?thesis by (simp add: return_def textends_def)
next
  case (Cons T Us)
  with foldM_unify_types_einv[of T Us env env' A K] assms show ?thesis by auto metis
qed

lemma foldM_unify_vars_einv:
  assumes "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env) env'" "einv A K env" "finite K"
    "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar T"
  shows "einv A K env' \<and> tenv env' = tenv env \<and> textends (tyenv env) (tyenv env') \<and> maxidx env \<le> maxidx env' \<and>
    (\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> (\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U))"
  using assms
proof (induction tab arbitrary: env)
  case (Cons xTs tab)
  obtain x Ts where xTs: "xTs = (x, Ts)" by (cases xTs)
  from Cons.prems(1) xTs obtain e1 where u: "ok (unify_vars alg Ts env) e1"
    and f: "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab e1) env'"
    by auto
  have tT: "\<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv env) \<union> A \<and> cert_typ alg ar T"
    using Cons.prems(4) xTs by auto
  note s1 = unify_vars_einv[OF u Cons.prems(2,3) tT]
  have tt: "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv e1) \<union> A \<and> cert_typ alg ar T"
    using Cons.prems(4) s1 by fastforce
  from Cons.IH[OF f _ Cons.prems(3) tt] s1
  have IH: "einv A K env'" "tenv env' = tenv e1" "textends (tyenv e1) (tyenv env')" "maxidx e1 \<le> maxidx env'"
    "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> (\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U)"
    by blast+
  have "\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U" if "tsol (tyenv env') \<rho>" for \<rho>
    using s1 tsol_textends[OF IH(3) that] by blast
  moreover have "textends (tyenv env) (tyenv env')" by (rule textends_trans) (use s1 IH in blast)+
  moreover have "tenv env' = tenv env" "maxidx env \<le> maxidx env'" using s1 IH by auto
  moreover have "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U"
    if "tsol (tyenv env') \<rho>" for \<rho>
    using IH(5) that by blast
  ultimately show ?case
    unfolding xTs list.set ball_simps prod.case using IH(1) by blast
qed (simp add: return_def textends_def)

text \<open>The types of variables with the same name are unified:\<close>

lemma unify_var_types_einv:
  assumes u: "okT (unify_var_types alg (tps1, P1) (tps2, P2) (empty_env m)) (Some env)"
    and ei: "einv A K (empty_env m)" "finite K"
    and ty: "\<forall>(x, T)\<in>vars_thm tps1 P1 \<union> vars_thm tps2 P2. tvars T \<subseteq> A \<and> cert_typ alg ar T"
  shows "einv A K env" "vt_is_empty (tenv env)" "m \<le> maxidx env"
    "tsol (tyenv env) \<rho> \<Longrightarrow> (x, T) \<in> vars_thm tps1 P1 \<union> vars_thm tps2 P2 \<Longrightarrow>
      (x, U) \<in> vars_thm tps1 P1 \<union> vars_thm tps2 P2 \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  let ?V = "vars_thm tps1 P1 \<union> vars_thm tps2 P2"
  let ?f = "do {
      p1 \<leftarrow> full_prop_of tps1 P1;
      p2 \<leftarrow> full_prop_of tps2 P2;
      let vars = sort_keys (add_vars p2 (add_vars p1 []));
      foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) vars (empty_env m)}"
  obtain f where f: "f = ?f" by simp
  have "ok f env"
    using u unfolding unify_var_types_def fst_conv snd_conv f[symmetric]
    by (cases f) (simp_all split: res.splits exn.splits)
  then have "ok ?f env" by (simp only: f)
  then obtain p1 p2 where p1: "ok (full_prop_of tps1 P1) p1" and p2: "ok (full_prop_of tps2 P2) p2"
    and fo: "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) (sort_keys (add_vars p2 (add_vars p1 [])))
      (empty_env m)) env"
    by (auto simp: Let_def)
  let ?tab = "sort_keys (add_vars p2 (add_vars p1 []))"
  have vt: "vtab ?tab = ?V"
    using vars_full_prop_of[OF p1] vars_full_prop_of[OF p2]
    by (auto simp: vtab_def set_sort_keys vtab_add_vars[unfolded vtab_def] split: prod.splits)
  have ds: "distinct (map fst ?tab)" by (simp add: distinct_sort_keys distinct_add_vars)
  have "\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. tvars T \<subseteq> tvars_env (tyenv (empty_env m)) \<union> A \<and> cert_typ alg ar T"
  proof (intro ballI, clarify)
    fix x Ts T assume "(x, Ts) \<in> set ?tab" "T \<in> set Ts"
    then have "(x, T) \<in> vtab ?tab" unfolding vtab_def by blast
    with vt have "(x, T) \<in> ?V" by simp
    with ty have "tvars T \<subseteq> A \<and> cert_typ alg ar T" by blast
    then show "tvars T \<subseteq> tvars_env (tyenv (empty_env m)) \<union> A \<and> cert_typ alg ar T" by auto
  qed
  from foldM_unify_vars_einv[OF fo ei this]
  have r: "einv A K env" "tenv env = tenv (empty_env m)" "m \<le> maxidx env"
    "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> (\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U)"
    by (auto simp: empty_env_def)
  show "einv A K env" "m \<le> maxidx env" by (fact r(1), fact r(3))
  show "vt_is_empty (tenv env)" using r(2) by simp
  assume "tsol (tyenv env) \<rho>" "(x, T) \<in> ?V" "(x, U) \<in> ?V"
  then have "(x, T) \<in> vtab ?tab" "(x, U) \<in> vtab ?tab" "tsol (tyenv env) \<rho>" by (simp_all add: vt)
  then obtain Ts Us where Ts: "(x, Ts) \<in> set ?tab" "T \<in> set Ts" and Us: "(x, Us) \<in> set ?tab" "U \<in> set Us"
    unfolding vtab_def by blast
  have "Ts = Us" by (rule eq_key_imp_eq_value[OF ds Ts(1) Us(1)])
  with r(4) \<open>tsol (tyenv env) \<rho>\<close> Ts Us show "tsubst \<rho> T = tsubst \<rho> U" by fastforce
qed



subsection \<open>The problems of a call\<close>

text \<open>A pair of a problem with variables in \<open>X\<close> and type variables in \<open>A\<close>:\<close>

definition gpair :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "gpair X A t u \<longleftrightarrow> vars t \<union> vars u \<subseteq> X \<and> ttvars t \<union> ttvars u \<subseteq> A \<and> closed t \<and> closed u \<and>
    (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"

lemma typs_abs_pre: "typs (abs_pre p X) \<subseteq> typs (lift_pre p X)"
  by (induction p X rule: abs_pre.induct) auto

lemma ttvars_abs_pre: "ttvars (abs_pre p X) \<subseteq> ttvars (lift_pre p X)"
  using typs_abs_pre[of p X] by (auto simp: ttvars_def)

lemma ttvars_list_forall: "btvars ps \<union> ttvars Y \<subseteq> ttvars (list_forall ps Y)"
  by (induction ps Y rule: list_forall.induct) (auto simp: btvars_def all_const_def)

lemma ttvars_list_implies: "A \<in> set As \<Longrightarrow> ttvars A \<subseteq> ttvars (list_implies As B)"
  "ttvars B \<subseteq> ttvars (list_implies As B)"
  by (induction As) (auto simp: implies_def)

lemma length_lparams: "length (lparams p) = length (ptys p)"
  by (induction p rule: lparams.induct) auto

lemma closure_typed:
  assumes ok: "\<forall>i\<in>set p. litem_ok i" and w: "wtp (lift_pre p X)"
  shows "closed (abs_pre p X)" "e \<turnstile> abs_pre p X : ptys p \<Rrightarrow> propT"
proof -
  note t = typing_lift_pre[OF ok wtpD(2)[OF w, of e]]
  have "snd ` set (lparams p) = set (ptys p)" by (induction p rule: lparams.induct) auto
  with t have c: "\<forall>T\<in>snd ` set (lparams p). cert_typ alg ar T" by simp
  show "e \<turnstile> abs_pre p X : ptys p \<Rrightarrow> propT"
    using typing_abs_list[of e "lparams p" X propT] t c by (simp add: abs_pre_abs_list)
  have "\<not> loose_bvar X (0 + ilength (ptys p))"
    by (rule loose_bvar_lift_pre[OF ok]) (use wtpD(1)[OF w] in \<open>simp add: closed_def\<close>)
  then show "closed (abs_pre p X)"
    by (simp add: closed_def abs_pre_abs_list loose_bvar_abs_list ilength_eq length_lparams)
qed

lemma eres_closure_typed:
  assumes ap: "assum_problems k A = (params, asms, concl)" and w: "wtp A" and X: "X \<in> insert concl (set asms)"
  shows "closed (rlist_abs params X)" "e \<turnstile> rlist_abs params X : map snd (rev params) \<Rrightarrow> propT"
    "vars (rlist_abs params X) \<subseteq> vars A" "ttvars (rlist_abs params X) \<subseteq> ttvars A"
proof -
  note st = assum_problems_struct[OF ap wtpD(2)[OF w, of e]]
  have cps: "\<forall>(a, T)\<in>set (rev params). cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    using st(1) wtpD(2)[OF w, of e] by (simp add: typing_list_forall)
  have tX: "pushes e (map snd (rev params)) \<turnstile> X : propT" using st(2,3) X by auto
  have c: "\<forall>T\<in>snd ` set (rev params). cert_typ alg ar T" using cps by auto
  from typing_abs_list[OF tX c] show "e \<turnstile> rlist_abs params X : map snd (rev params) \<Rrightarrow> propT"
    by (simp add: rlist_abs_abs_list)
  have "\<not> loose_bvar (list_implies asms concl) (0 + ilength (rev params))"
    using wtpD(1)[OF w] st(1) by (simp add: closed_def loose_bvar_list_forall)
  then have "\<not> loose_bvar X (0 + ilength (rev params))" using X by (auto simp: loose_bvar_list_implies)
  then show "closed (rlist_abs params X)" by (simp add: closed_def rlist_abs_abs_list loose_bvar_abs_list)
  show "vars (rlist_abs params X) \<subseteq> vars A" using X st(1) by (auto simp: vars_list_implies)
  have "ttvars X \<subseteq> ttvars (list_implies asms concl)"
    using X ttvars_list_implies(1)[of X asms concl] ttvars_list_implies(2)[of concl asms] by auto
  moreover have "btvars (rev params) = btvars params" by (simp add: btvars_def)
  ultimately show "ttvars (rlist_abs params X) \<subseteq> ttvars A"
    using ttvars_list_forall[of "rev params" "list_implies asms concl"] st(1)
    by (auto simp: rlist_abs_abs_list ttvars_abs_list)
qed

lemma vars_tvars_thm:
  "vars P \<subseteq> vars_thm tps P" "ttvars P \<subseteq> tvars_thm tps P"
  "(t, u) \<in> set tps \<Longrightarrow> vars t \<union> vars u \<subseteq> vars_thm tps P"
  "(t, u) \<in> set tps \<Longrightarrow> ttvars t \<union> ttvars u \<subseteq> tvars_thm tps P"
  by (auto simp: vars_thm_def tvars_thm_def)

text \<open>
  The problems of a call satisfy the invariant of unification, for the type variables \<open>A\<close> and
  the variables \<open>X\<close> of the proof state and the rule:
\<close>

definition sinv_all :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    bspec \<Rightarrow> bool" where
  "sinv_all A K X sp \<longleftrightarrow>
    (\<not> sp_eres sp \<longrightarrow> sinv A K X (sp_env sp) (tdps (bc_dpairs (sp_ctx sp)))) \<and>
    (sp_eres sp \<longrightarrow> (\<forall>asm\<in>set (asms_of sp). sinv A K X (sp_env sp) (tdps (eres_prob sp asm))))"

lemma sinv_all_pinv_all: "sinv_all A K X sp \<Longrightarrow> finite K \<Longrightarrow> finite X \<Longrightarrow> pinv_all sp"
  unfolding sinv_all_def pinv_all_def pwf_def by blast

text \<open>The problems of a call are well-formed if the proof state and the rule are well-typed:\<close>

theorem sinv_all_call_spec:
  assumes state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and ei: "einv A K env" "finite K" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
    and A: "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> A"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow>
      vcons \<rho> (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
  shows "sinv_all A K (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies (rev rAs) B))
    (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?R = "list_implies (rev rAs) B"
  let ?X = "vars_thm stpairs ?S \<union> vars_thm rtpairs ?R"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  let ?sp = "BSpec cfg vl env ctx rAs eres_flg"
  have sp: "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B = ?sp"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have wS: "wtp ?S" "ibelow smax ?S" and wR: "wtp ?R" "ibelow rmax ?R"
    using state rule by (simp_all add: wt_thm_def)
  have wBi: "wtp Bi" and wB: "wtp B" and wAs: "\<forall>X\<in>set (rev rAs). wtp X"
    using wtp_list_implies[OF wS(1)] wtp_list_implies[OF wR(1)] by simp_all
  have vS: "vars Bi \<subseteq> vars ?S" and vR: "vars B \<subseteq> vars ?R" "\<forall>X\<in>set (rev rAs). vars X \<subseteq> vars ?R"
    by (auto simp: vars_list_implies)
  have tS: "ttvars Bi \<subseteq> ttvars ?S" and tR: "ttvars B \<subseteq> ttvars ?R" "\<forall>X\<in>set (rev rAs). ttvars X \<subseteq> ttvars ?R"
    using ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C] ttvars_list_implies(2)[of B "rev rAs"]
      ttvars_list_implies(1)[of _ "rev rAs" B] by auto
  have XS: "vars ?S \<subseteq> ?X" "vars ?R \<subseteq> ?X" using vars_tvars_thm(1) by blast+
  have AS: "ttvars ?S \<subseteq> A" "ttvars ?R \<subseteq> A" using A vars_tvars_thm(2) by blast+
  text \<open>The pairs of the problems:\<close>
  have tps: "gpair ?X A t u" if "(t, u) \<in> set (rtpairs @ stpairs)" for t u
  proof -
    from that consider "(t, u) \<in> set rtpairs" | "(t, u) \<in> set stpairs" by auto
    then show ?thesis
    proof cases
      case 1
      with rule have "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        unfolding wt_thm_def by blast
      moreover have "ttvars t \<union> ttvars u \<subseteq> A" using vars_tvars_thm(4)[OF 1] A by blast
      moreover have "vars t \<union> vars u \<subseteq> ?X" using vars_tvars_thm(3)[OF 1] by blast
      ultimately show ?thesis by (simp add: gpair_def)
    next
      case 2
      with state have "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
        unfolding wt_thm_def by blast
      moreover have "ttvars t \<union> ttvars u \<subseteq> A" using vars_tvars_thm(4)[OF 2] A by blast
      moreover have "vars t \<union> vars u \<subseteq> ?X" using vars_tvars_thm(3)[OF 2] by blast
      ultimately show ?thesis by (simp add: gpair_def)
    qed
  qed
  have BBi_ok: "gpair ?X A (fst BBi) (snd BBi)"
  proof (cases lifted)
    case True
    from lift[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0" by blast
    from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" by auto
    have BBi': "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    have c: "closed (abs_pre p B0)" "closed (abs_pre p Bi0)"
      and t: "\<And>e. e \<turnstile> abs_pre p B0 : ptys p \<Rrightarrow> propT" "\<And>e. e \<turnstile> abs_pre p Bi0 : ptys p \<Rrightarrow> propT"
      using closure_typed[OF ok] wB wBi B Bi by auto
    have "vars (abs_pre p B0) \<subseteq> vars B" "vars (abs_pre p Bi0) \<subseteq> vars Bi"
      by (simp_all add: B Bi vars_lift_pre)
    moreover have "ttvars (abs_pre p B0) \<subseteq> ttvars B" "ttvars (abs_pre p Bi0) \<subseteq> ttvars Bi"
      using ttvars_abs_pre B Bi by auto
    moreover have "\<exists>T. \<forall>e. e \<turnstile> abs_pre p B0 : T \<and> e \<turnstile> abs_pre p Bi0 : T" using t by blast
    ultimately show ?thesis
      using BBi' c vS vR tS tR XS AS by (auto simp: gpair_def)
  next
    case False
    then have "BBi = (B, Bi)" by (simp add: BBi_def)
    then show ?thesis
      using wB wBi vS vR tS tR XS AS by (auto simp: gpair_def wtp_def)
  qed
  have dps: "\<forall>(t, u)\<in>set (BBi # rtpairs @ stpairs). gpair ?X A t u"
    using tps BBi_ok by auto
  have pw: "sinv A K ?X env (tdps tus)" if "\<forall>(t, u)\<in>set tus. gpair ?X A t u" for tus
  proof (rule sinv_intro[OF ei(1,3)])
    show "finite ?X" by simp
    show "below (maxidx env) ?X"
      using wS(2) wR(2) ei(4) state rule
      by (fastforce simp: below_def vars_thm_def ibelow_def wt_thm_def)
    show "vtvars ?X \<subseteq> tvars_env (tyenv env) \<union> A"
    proof -
      have "tvars T \<subseteq> A" if "(x, T) \<in> ?X" for x T
      proof -
        from that have "tvars T \<subseteq> tvars_thm stpairs ?S \<union> tvars_thm rtpairs ?R"
          by (auto simp: vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
        with A show ?thesis by blast
      qed
      then show ?thesis by (auto simp: vtvars_def)
    qed
    show "\<forall>(t, u)\<in>set tus. vars t \<union> vars u \<subseteq> ?X \<and> ttvars t \<union> ttvars u \<subseteq> A \<and> closed t \<and> closed u \<and>
        (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      using that by (simp add: gpair_def)
  qed (rule vc)
  have "sinv_all A K ?X ?sp"
    unfolding sinv_all_def
  proof (intro conjI impI ballI)
    assume "\<not> sp_eres ?sp"
    show "sinv A K ?X (sp_env ?sp) (tdps (bc_dpairs (sp_ctx ?sp)))" using pw[OF dps] by (simp add: ctx_def)
  next
    fix asm assume er: "sp_eres ?sp" and asm: "asm \<in> set (asms_of ?sp)"
    then obtain A1 As where rA: "rev rAs = A1 # As" by (cases "rev rAs") (auto simp: asms_of_def)
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_prob ?sp asm = (rlist_abs params asm, rlist_abs params concl) # bc_dpairs ctx"
      "asm \<in> set asms"
      using rA ap asm by (simp_all add: eres_prob_def eres_of_def asms_of_def ctx_def)
    have wA1: "wtp A1" "vars A1 \<subseteq> vars ?R" "ttvars A1 \<subseteq> ttvars ?R" using wAs vR(2) tR(2) rA by auto
    note c1 = eres_closure_typed[OF ap wA1(1), of asm] and c2 = eres_closure_typed[OF ap wA1(1), of concl]
    have "\<exists>T. \<forall>e. e \<turnstile> rlist_abs params asm : T \<and> e \<turnstile> rlist_abs params concl : T"
      using c1(2) c2(2) e(2) by blast
    then have g: "gpair ?X A (rlist_abs params asm) (rlist_abs params concl)"
      using c1 c2 e(2) wA1(2,3) XS AS by (auto simp: gpair_def)
    have "\<forall>(t, u)\<in>set (eres_prob ?sp asm). gpair ?X A t u"
      using g dps e(1) by (simp add: ctx_def)
    from pw[OF this] show "sinv A K ?X (sp_env ?sp) (tdps (eres_prob ?sp asm))" by simp
  qed
  then show ?thesis by (simp only: sp)
qed

corollary pinv_all_call_spec:
  assumes state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and ei: "einv A K env" "finite K" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
    and A: "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> A"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow>
      vcons \<rho> (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
  shows "pinv_all (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
  by (rule sinv_all_pinv_all[OF sinv_all_call_spec[OF assms] ei(2)]) (assumption | intro finite_UnI finite_vars_thm)+

end

end
