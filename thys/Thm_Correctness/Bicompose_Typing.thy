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

lemma finite_vars [simp]: "finite (vars t)"
  by (induction t) auto

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

lemma ibelow_mono: "ibelow m t \<Longrightarrow> m \<le> n \<Longrightarrow> ibelow n t"
  by (auto simp: ibelow_def)


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

lemma pwf_intro:
  assumes ei: "einv A K env" "finite K" and te: "vt_is_empty (tenv env)"
    and X: "finite X" "below (maxidx env) X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and vc: "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> vcons \<rho> X"
    and tus: "\<forall>(t, u)\<in>set tus. vars t \<union> vars u \<subseteq> X \<and> ttvars t \<union> ttvars u \<subseteq> A \<and> closed t \<and> closed u \<and>
      (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "pwf env tus"
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
    from tus that obtain T where t: "vars t \<union> vars u \<subseteq> X" "ttvars t \<union> ttvars u \<subseteq> A" "closed t" "closed u"
      "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
    have "\<exists>e T. bs_env \<rho> e [] \<and> e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T" if "cert_inst \<rho>" for \<rho>
      using typing_inst[OF t(5) cert_inst_inst_ok[OF that]] typing_inst[OF t(6) cert_inst_inst_ok[OF that]]
      by (auto simp: bs_env_def)
    then show ?thesis
      using t X(3) ev by (auto simp: pok_def btvars_def closed_def)
  qed
  ultimately have "sinv A K X env (tdps tus)" using ei by (auto simp: sinv_def)
  with ei(2) X(1) show ?thesis unfolding pwf_def by blast
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
  proof (elim disjE exE conjE)
    fix env'' assume "unify_types alg T U env = return env''" "einv A K env''" "tenv env'' = tenv env"
      "textends (tyenv env) (tyenv env'')" "maxidx env \<le> maxidx env''"
      "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env'')" "\<forall>\<rho>. tsol (tyenv env'') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    with assms(1) show ?thesis by (simp add: return_def)
  next
    fix u assume "unify_types alg T U env = raise (Unif u)"
    with assms(1) show ?thesis by (simp add: raise_def)
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
  ultimately show ?case using IH s1 by auto
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
  ultimately show ?case using IH s1 xTs by auto
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
    using vt ty by (auto simp: vtab_def)
  from foldM_unify_vars_einv[OF fo ei this]
  have r: "einv A K env" "tenv env = tenv (empty_env m)" "m \<le> maxidx env"
    "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> (\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tsubst \<rho> T = tsubst \<rho> U)"
    by (auto simp: empty_env_def)
  show "einv A K env" "m \<le> maxidx env" by (fact r(1), fact r(3))
  show "vt_is_empty (tenv env)" using r(2) by (simp add: empty_env_def, transfer, simp)
  assume "tsol (tyenv env) \<rho>" "(x, T) \<in> ?V" "(x, U) \<in> ?V"
  then have "(x, T) \<in> vtab ?tab" "(x, U) \<in> vtab ?tab" "tsol (tyenv env) \<rho>" by (simp_all add: vt)
  then obtain Ts Us where Ts: "(x, Ts) \<in> set ?tab" "T \<in> set Ts" and Us: "(x, Us) \<in> set ?tab" "U \<in> set Us"
    unfolding vtab_def by blast
  have "Ts = Us" by (rule eq_key_imp_eq_value[OF ds Ts(1) Us(1)])
  with r(4) \<open>tsol (tyenv env) \<rho>\<close> Ts Us show "tsubst \<rho> T = tsubst \<rho> U" by fastforce
qed

end

end
