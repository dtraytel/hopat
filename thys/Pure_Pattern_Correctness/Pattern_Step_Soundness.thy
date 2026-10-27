section \<open>Soundness of Successful Unification\<close>

theory Pattern_Step_Soundness
  imports Pattern_Semantics
begin

text \<open>
  If \<^const>\<open>unif\<close> returns an environment \<open>env'\<close>, then \<open>env'\<close> extends the given environment
  and every substitution satisfying \<open>env'\<close> unifies the two terms. This direction does not need
  types or patterns.
\<close>

subsection \<open>Lists of bound variables\<close>

lemma ok_ints_of: "ok (ints_of ts) is \<longleftrightarrow> ts = map Bound is \<and> distinct is"
proof (induction ts arbitrary: "is")
  case (Cons t ts)
  show ?case
    by (cases t) (auto simp: Cons.IH)
qed auto

lemma app_list_comb: "app s is = list_comb s (map Bound is)"
  by (induction "is" arbitrary: s) (simp_all add: app_def list_comb_def)

lemma env_equiv_list_comb:
  assumes "env \<Turnstile> h \<approx> h'" "list_all2 (env_equiv env) ts us"
  shows "env \<Turnstile> list_comb h ts \<approx> list_comb h' us"
  using assms(2,1)
  by (induction ts us arbitrary: h h' rule: list_all2_induct)
    (auto simp: list_comb_def intro: env_equiv_App)

lemma ints_of'_sound:
  assumes "ok (ints_of' env ts) is" "wf_env ar env" "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
  shows "distinct is" "\<forall>i\<in>set is. 0 \<le> i" "list_all2 (\<lambda>t i. env \<Turnstile> t \<approx> Bound i) ts is"
    "\<And>k. \<forall>t\<in>set ts. no_loose_bound (tr t) k \<Longrightarrow> \<forall>i\<in>set is. nat_of_integer i < k"
proof -
  from assms(1) obtain ts' where hn: "list_all2 (\<lambda>t t'. ok (head_norm env t) t') ts ts'"
    and ints: "ok (ints_of ts') is"
    by (auto simp: ints_of'_def ok_mapM)
  from ints have ts': "ts' = map Bound is" "distinct is" by (simp_all add: ok_ints_of)
  then show "distinct is" by simp
  have len: "length ts = length is" using hn ts'(1) by (auto dest: list_all2_lengthD)
  have *: "0 \<le> is ! j \<and> env \<Turnstile> ts ! j \<approx> Bound (is ! j) \<and>
    (\<forall>k. no_loose_bound (tr (ts ! j)) k \<longrightarrow> nat_of_integer (is ! j) < k)" if "j < length is" for j
  proof -
    from hn ts'(1) that len have "ok (head_norm env (ts ! j)) (Bound (is ! j))"
      by (auto simp: list_all2_conv_all_nth)
    from head_norm_sound[OF this refl assms(2)] assms(3) that len show ?thesis
      by auto
  qed
  then show "\<forall>i\<in>set is. 0 \<le> i" by (auto simp: in_set_conv_nth)
  show "list_all2 (\<lambda>t i. env \<Turnstile> t \<approx> Bound i) ts is"
    using * len by (simp add: list_all2_conv_all_nth)
  show "\<forall>i\<in>set is. nat_of_integer i < k" if "\<forall>t\<in>set ts. no_loose_bound (tr t) k" for k
  proof
    fix i assume "i \<in> set is"
    then obtain j where "j < length is" "i = is ! j" by (auto simp: in_set_conv_nth)
    with *[OF this(1)] that len show "nat_of_integer i < k" by (metis nth_mem)
  qed
qed

lemma ints_of'_equiv:
  assumes "ok (ints_of' env ts) is" "wf_env ar env" "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
  shows "env \<Turnstile> list_comb h ts \<approx> app h is"
  using ints_of'_sound(3)[OF assms]
  by (auto simp: app_list_comb list_all2_map2 intro!: env_equiv_list_comb)

subsection \<open>Abstractions applied to bound variables\<close>

text \<open>
  \<open>ren xs\<close> maps the bound variables of the body of \<open>Abs_m (length xs) b\<close> to the arguments
  \<open>xs\<close> it is applied to (the last argument instantiates the innermost binder).
\<close>

definition ren :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "ren xs i = (if i < length xs then xs ! (length xs - Suc i) else i - length xs)"

lemma Abs_m_apps_equiv:
  "Abs_m (length xs) b \<degree>\<degree> map BVar xs \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren xs) b"
proof -
  have "Abs_m (length xs) b \<degree>\<degree> map BVar xs \<rightarrow>\<^sub>\<beta>\<^sup>* appb (Abs_m (length xs) b) xs"
    by (rule appb_reduces)
  also have "appb (Abs_m (length xs) b) xs = map_BVars (ren xs) b"
    by (simp add: appb_Abs_m ren_def[abs_def])
  finally show ?thesis by (rule beta_into_equiv)
qed

lemma ren_idx: "j \<in> set xs \<Longrightarrow> ren xs (the (Unification.idx xs j)) = j"
  using idx_None_iff[of xs j] idx_SomeD[of xs j] by (auto simp: ren_def)

lemma map_BVars_subst_closed: "closed_on UNIV \<sigma> \<Longrightarrow> map_BVars f (\<sigma> n) = \<sigma> n"
  using map_BVars_no_loose[of "\<sigma> n" 0 f] by (simp add: closed_onD)

abbreviation nats :: "integer list \<Rightarrow> nat list" where
  "nats is \<equiv> map nat_of_integer is"

lemma tr_app': "tr (app s is) = tr s \<degree>\<degree> map BVar (nats is)"
  by (simp add: tr_app comp_def)

lemma ok_idx: "ok (idx is j) k \<longleftrightarrow> (\<exists>n. Unification.idx is j = Some n \<and> k = integer_of_nat n)"
  by (induction "is") (auto simp: ilength_eq)

lemma idx_map_inj_on:
  "inj_on f (insert y (set xs)) \<Longrightarrow> Unification.idx (map f xs) (f y) = Unification.idx xs y"
  by (induction xs) (auto simp: inj_on_def)

lemma inj_on_nat_of_integer: "\<forall>i\<in>A. 0 \<le> i \<Longrightarrow> inj_on nat_of_integer A"
  by (auto simp: inj_on_def nat_of_integer_eq_iff)

subsection \<open>Updating environments\<close>

lemma ok_update:
  assumes "ok (update (F, T) t env) env'"
  shows "vt_lookup (tenv env) F = None" "tenv env' = vt_update (F, (T, t)) (tenv env)"
    "tyenv env' = tyenv env" "maxidx env' = maxidx env"
proof -
  have "vt_lookup (tenv env) F = None \<and> tenv env' = vt_update (F, (T, t)) (tenv env) \<and>
    tyenv env' = tyenv env \<and> maxidx env' = maxidx env"
    using assms
    by (cases env; cases "vt_lookup (tenv env) F")
      (auto simp: update_def update_new_def vt_defined_lookup split: if_splits)
  then show "vt_lookup (tenv env) F = None" "tenv env' = vt_update (F, (T, t)) (tenv env)"
    "tyenv env' = tyenv env" "maxidx env' = maxidx env"
    by simp_all
qed

lemma ok_update_extends: "ok (update (F, T) t env) env' \<Longrightarrow> extends env' env"
  using ok_update[of F T t env env'] by (auto simp: extends_def)

lemma ok_update_lookup:
  "ok (update (F, T) t env) env' \<Longrightarrow> vt_lookup (tenv env') F = Some (T, t)"
  using ok_update[of F T t env env'] by simp

lemma ok_update_wf_env:
  assumes "ok (update (F, T) t env) env'" "wf_env ar env"
    "proper t" "typs_ok ar t" "ground ar T" "no_loose_bound (tr t) 0"
  shows "wf_env ar env'"
  using assms ok_update[OF assms(1)] by (auto simp: wf_env_def)

lemma genvar_simps:
  assumes "genvar a env T = (env', G)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env' = maxidx env + 1"
    "G = pterm.Var (a, maxidx env + 1) T"
  using assms by (auto simp: genvar_def split: env.splits)

lemma genvar_extends: "genvar a env T = (env', G) \<Longrightarrow> extends env' env"
  by (simp add: extends_def genvar_simps)

lemma genvar_wf_env: "genvar a env T = (env', G) \<Longrightarrow> wf_env ar env \<Longrightarrow> wf_env ar env'"
  by (simp add: wf_env_def genvar_simps)

text \<open>The semantics of a binding \<open>F := \<lambda>is. b\<close> created with \<^const>\<open>mkabs\<close>.\<close>

lemma sat_binding_app:
  assumes "sat \<sigma> env" "closed_on UNIV \<sigma>" "vt_lookup (tenv env) F = Some (T, u)"
    "ok (mkabs binders is b) u" "length js = length is"
  shows "mk_subst \<sigma> (tr (app (pterm.Var F T) js)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats js)) (mk_subst \<sigma> (tr b))"
proof -
  have "mk_subst \<sigma> (tr (app (pterm.Var F T) js)) = \<sigma> (code (AVar F)) \<degree>\<degree> map BVar (nats js)"
    by (simp add: tr_app' comp_def)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats js)) (mk_subst \<sigma> (tr b)) \<degree>\<degree> map BVar (nats js)"
    using satD[OF assms(1,3)] ok_mkabs[OF assms(4)] assms(5)
    by (intro equiv_list_app) (auto simp: list_all2_refl)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats js)) (mk_subst \<sigma> (tr b))"
    by (rule Abs_m_apps_equiv)
  finally show ?thesis .
qed

lemma map_BVars_app_Var:
  "closed_on UNIV \<sigma> \<Longrightarrow> map_BVars f (mk_subst \<sigma> (tr (app (pterm.Var G T) ks))) =
    \<sigma> (code (AVar G)) \<degree>\<degree> map (\<lambda>k. BVar (f (nat_of_integer k))) ks"
  using map_BVars_no_loose[of "\<sigma> (code (AVar G))" 0 f]
  by (simp add: tr_app' closed_onD comp_def)

subsection \<open>New variable types\<close>

declare split_type.simps[simp del]

lemma split_type_ground:
  "ok (split_type T n Ts) (Us, U) \<Longrightarrow> ground ar T \<Longrightarrow> \<forall>T\<in>set Ts. ground ar T \<Longrightarrow>
    (\<forall>T\<in>set Us. ground ar T) \<and> ground ar U"
proof (induction T n Ts rule: split_type.induct)
  case (1 T n Ts)
  then show ?case
    by (subst (asm) split_type.simps) (auto split: ptyp.splits list.splits if_splits)
qed

lemma type_of_G_ground:
  assumes "ok (type_of_G env T n is) U" "vt_is_empty (tyenv env)" "ground ar T"
  shows "ground ar U"
proof -
  from assms(1,2) obtain Ts V Us where st: "ok (split_type T n []) (Ts, V)"
    and Us: "list_all2 (\<lambda>i U. ok (nth Ts i) U) is Us" and U: "U = foldr fun_type Us V"
    by (auto simp: type_of_G_def norm_type_def ok_mapM)
  from split_type_ground[OF st assms(3)] have "\<forall>T\<in>set Ts. ground ar T" "ground ar V" by auto
  moreover from Us have "\<forall>U\<in>set Us. U \<in> set Ts"
    by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth ok_nth)
  ultimately show ?thesis unfolding U by (induction Us) auto
qed

subsection \<open>Flex-flex problems with the same head\<close>

lemma integer_of_nat_Suc: "integer_of_nat (Suc p) = integer_of_nat p + 1"
  by (simp add: integer_eq_iff)

lemma ok_mk_ff_list_aux:
  "ok (mk_ff_list_aux is js k) ks \<Longrightarrow>
    length is = length js \<and> (\<forall>k'\<in>set ks. \<exists>p<length is. k' = k - integer_of_nat p \<and> is ! p = js ! p)"
proof (induction "is" js k arbitrary: ks rule: mk_ff_list_aux.induct)
  case (2 i "is" j js k)
  obtain ks' where len: "length is = length js"
    and ks': "\<forall>k'\<in>set ks'. \<exists>p<length is. k' = k - 1 - integer_of_nat p \<and> is ! p = js ! p"
    and ks: "ks = (if i = j then k # ks' else ks')"
    using "2.prems" "2.IH" by (cases "i = j") fastforce+
  show ?case
  proof (intro conjI ballI)
    show "length (i # is) = length (j # js)" using len by simp
    fix k' assume "k' \<in> set ks"
    with ks consider "k' = k" "i = j" | "k' \<in> set ks'" by (auto split: if_splits)
    then show "\<exists>p<length (i # is). k' = k - integer_of_nat p \<and> (i # is) ! p = (j # js) ! p"
    proof cases
      case 1
      then show ?thesis by (intro exI[of _ 0]) (simp add: integer_eq_iff)
    next
      case 2
      with ks' obtain p where "p < length is" "k' = k - 1 - integer_of_nat p" "is ! p = js ! p"
        by blast
      then show ?thesis by (intro exI[of _ "Suc p"]) (simp add: integer_of_nat_Suc)
    qed
  qed
qed auto

lemma mk_ff_list_ren:
  assumes "ok (mk_ff_list is js) ks"
  shows "length is = length js"
    "\<And>k. k \<in> set ks \<Longrightarrow> 0 \<le> k \<and> nat_of_integer k < length is \<and>
      ren (nats is) (nat_of_integer k) = ren (nats js) (nat_of_integer k)"
proof -
  from ok_mk_ff_list_aux[of "is" js "ilength is - 1" ks] assms
  have len: "length is = length js"
    and ks: "\<forall>k'\<in>set ks. \<exists>p<length is. k' = ilength is - 1 - integer_of_nat p \<and> is ! p = js ! p"
    by (auto simp: mk_ff_list_def)
  then show "length is = length js" by simp
  fix k assume "k \<in> set ks"
  with ks obtain p where p: "p < length is" "k = ilength is - 1 - integer_of_nat p" "is ! p = js ! p"
    by blast
  then have "nat_of_integer k = length is - Suc p" "0 \<le> k"
    by (simp_all add: ilength_eq integer_reps nat_diff_distrib)
  with p len show "0 \<le> k \<and> nat_of_integer k < length is \<and>
      ren (nats is) (nat_of_integer k) = ren (nats js) (nat_of_integer k)"
    by (auto simp: ren_def)
qed


subsection \<open>New bindings\<close>

definition binders_ok :: "(name \<Rightarrow> nat) \<Rightarrow> binders \<Rightarrow> bool" where
  "binders_ok ar binders \<longleftrightarrow> (\<forall>(x, T)\<in>set binders. ground ar T)"

lemma ok_mkabs_typs_ok:
  "ok (mkabs binders is t) u \<Longrightarrow> binders_ok ar binders \<Longrightarrow> typs_ok ar u \<longleftrightarrow> typs_ok ar t"
  by (induction "is" arbitrary: u)
    (auto simp: binders_ok_def ok_nth split: prod.splits dest!: nth_mem)

lemma no_loose_bound_app:
  "no_loose_bound (tr (app s ks)) n \<longleftrightarrow>
    no_loose_bound (tr s) n \<and> (\<forall>k\<in>set ks. nat_of_integer k < n)"
  by (induction ks arbitrary: s) (auto simp: app_def)

lemma ok_mk_new_hnf:
  assumes "ok (mk_new_hnf env binders is F T js) env'"
  obtains Gty env1 G t where "ok (type_of_G env T (ilength is) js) Gty"
    "genvar (fst F) env Gty = (env1, G)" "ok (mkabs binders is (app G js)) t"
    "ok (update (F, T) t env1) env'"
proof -
  from assms obtain Gty where Gty: "ok (type_of_G env T (ilength is) js) Gty"
    and rest: "ok (let (env', G) = genvar (fst F) env Gty in
      mk_hnf binders is G js \<bind> (\<lambda>t. update (F, T) t env')) env'"
    by (auto simp: mk_new_hnf_def)
  obtain env1 G where G: "genvar (fst F) env Gty = (env1, G)" by force
  with rest obtain t where "ok (mkabs binders is (app G js)) t" "ok (update (F, T) t env1) env'"
    by (auto simp: mk_hnf_def)
  with Gty G that show ?thesis by blast
qed

text \<open>A new binding \<open>F := \<lambda>is. G ks\<close>.\<close>

lemma binding_sound:
  assumes "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
    "ok (update (F, T) t env) env'" "wf_env ar env" "ground ar T" "ground ar Gty"
    "binders_ok ar binders" "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length is"
  shows "extends env' env" "wf_env ar env'" "vt_lookup (tenv env') F = Some (T, t)"
    "\<And>\<sigma> js. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> length js = length is \<Longrightarrow>
       mk_subst \<sigma> (tr (app (pterm.Var F T) js)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
       \<sigma> (code (AVar G)) \<degree>\<degree> map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ks"
proof -
  show "extends env' env" by (rule ok_update_extends[OF assms(2)])
  show "wf_env ar env'"
  proof (rule ok_update_wf_env[OF assms(2,3)])
    show "proper t" "typs_ok ar t" "ground ar T" "no_loose_bound (tr t) 0"
      using ok_mkabs[OF assms(1)] ok_mkabs_typs_ok[OF assms(1,6)] assms(4,5,7)
      by (auto simp: proper_app typs_ok_app loose_bound_Abs_m no_loose_bound_app)
  qed
  show lk: "vt_lookup (tenv env') F = Some (T, t)" by (rule ok_update_lookup[OF assms(2)])
  fix \<sigma> :: "nat \<Rightarrow> dB" and js :: "integer list"
  assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'" and len: "length js = length is"
  have "mk_subst \<sigma> (tr (app (pterm.Var F T) js)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
    map_BVars (ren (nats js)) (mk_subst \<sigma> (tr (app (pterm.Var G Gty) ks)))"
    by (rule sat_binding_app[OF \<sigma>(2,1) lk assms(1) len])
  also have "\<dots> = \<sigma> (code (AVar G)) \<degree>\<degree> map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ks"
    by (rule map_BVars_app_Var[OF \<sigma>(1)])
  finally show "mk_subst \<sigma> (tr (app (pterm.Var F T) js)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
       \<sigma> (code (AVar G)) \<degree>\<degree> map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ks" .
qed

lemma ren_map_cong:
  "(\<And>k. k \<in> set ks \<Longrightarrow> ren xs (nat_of_integer k) = ren ys (nat_of_integer k)) \<Longrightarrow>
    h \<degree>\<degree> map (\<lambda>k. BVar (ren xs (nat_of_integer k))) ks =
    h \<degree>\<degree> map (\<lambda>k. BVar (ren ys (nat_of_integer k))) ks"
  by (metis (mono_tags, lifting) map_eq_conv)

lemma flexflex1_sound:
  assumes "ok (flexflex1 env binders F Fty is js) env'" "wf_env ar env" "ground ar Fty"
    "binders_ok ar binders"
  shows "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var F Fty) js"
proof -
  have "extends env' env \<and> wf_env ar env' \<and>
    env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var F Fty) js"
  proof (cases "is = js")
    case True
    with assms(1,2) show ?thesis by (simp add: flexflex1_def)
  next
    case False
    with assms(1) obtain ks where ks: "ok (mk_ff_list is js) ks"
      and hnf: "ok (mk_new_hnf env binders is F Fty ks) env'"
      by (auto simp: flexflex1_def)
    note ff = mk_ff_list_ren[OF ks]
    from hnf obtain Gty env1 G t where Gty: "ok (type_of_G env Fty (ilength is) ks) Gty"
      and G: "genvar (fst F) env Gty = (env1, G)" and t: "ok (mkabs binders is (app G ks)) t"
      and env': "ok (update (F, Fty) t env1) env'"
      by (rule ok_mk_new_hnf)
    have Gty': "ground ar Gty"
      using type_of_G_ground[OF Gty wf_envD(1)[OF assms(2)] assms(3)] .
    note G' = genvar_simps[OF G]
    have wf1: "wf_env ar env1" by (rule genvar_wf_env[OF G assms(2)])
    have ks_ok: "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length is" using ff(2) by blast
    note nb = binding_sound[OF t[unfolded G'(4)] env' wf1 assms(3) Gty' assms(4) ks_ok]
    have "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var F Fty) js"
    proof (rule env_equivI)
      fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
      let ?G = "\<sigma> (code (AVar (fst F, maxidx env + 1)))"
      have "mk_subst \<sigma> (tr (app (pterm.Var F Fty) is)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        ?G \<degree>\<degree> map (\<lambda>k. BVar (ren (nats is) (nat_of_integer k))) ks"
        by (rule nb(4)[OF \<sigma> refl])
      also have "\<dots> = ?G \<degree>\<degree> map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ks"
        using ff(2) by (intro ren_map_cong) blast
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (pterm.Var F Fty) js))"
        using nb(4)[OF \<sigma> ff(1)[symmetric]] by (rule equiv_sym)
      finally show "mk_subst \<sigma> (tr (app (pterm.Var F Fty) is)) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
        mk_subst \<sigma> (tr (app (pterm.Var F Fty) js))" .
    qed
    with extends_trans[OF nb(1) genvar_extends[OF G]] nb(2) show ?thesis by simp
  qed
  then show "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var F Fty) js"
    by simp_all
qed

subsection \<open>Flex-flex problems with different heads\<close>

lemma ok_idx_ren:
  assumes "ok (idx xs k) k'" "\<forall>i\<in>set xs. 0 \<le> i" "0 \<le> k"
  shows "0 \<le> k' \<and> nat_of_integer k' < length xs \<and> ren (nats xs) (nat_of_integer k') = nat_of_integer k"
proof -
  from assms(1) obtain n where n: "Unification.idx xs k = Some n" "k' = integer_of_nat n"
    by (auto simp: ok_idx)
  from idx_SomeD[OF n(1)] have nl: "n < length xs" and k: "xs ! (length xs - Suc n) = k" by auto
  then have "k \<in> set xs" by (metis diff_less length_greater_0_conv list.size(3) not_less0 nth_mem zero_less_Suc)
  have inj: "inj_on nat_of_integer (insert k (set xs))"
    using assms(2,3) \<open>k \<in> set xs\<close> by (intro inj_on_nat_of_integer) auto
  have "Unification.idx (nats xs) (nat_of_integer k) = Some n"
    using idx_map_inj_on[OF inj] n(1) by simp
  moreover note \<open>k \<in> set xs\<close> nl
  ultimately show ?thesis
    using ren_idx[of "nat_of_integer k" "nats xs"] n(2) by (auto simp: integer_reps)
qed

lemma ok_mapM_idx:
  assumes "ok (mapM (idx xs) ks) ks'" "\<forall>i\<in>set xs. 0 \<le> i" "\<forall>k\<in>set ks. 0 \<le> k"
  shows "\<forall>k'\<in>set ks'. 0 \<le> k' \<and> nat_of_integer k' < length xs"
    "map (\<lambda>k. BVar (ren (nats xs) (nat_of_integer k))) ks' = map (\<lambda>k. BVar (nat_of_integer k)) ks"
proof -
  have *: "0 \<le> k' \<and> nat_of_integer k' < length xs \<and> ren (nats xs) (nat_of_integer k') = nat_of_integer k"
    if "ok (idx xs k) k'" "0 \<le> k" for k k'
    using ok_idx_ren[OF that(1) assms(2) that(2)] .
  from assms(1) have all2: "list_all2 (\<lambda>k k'. ok (idx xs k) k') ks ks'" by (simp add: ok_mapM)
  then show "\<forall>k'\<in>set ks'. 0 \<le> k' \<and> nat_of_integer k' < length xs"
    using * assms(3) by (auto simp: list_all2_conv_all_nth in_set_conv_nth) (metis nth_mem)+
  show "map (\<lambda>k. BVar (ren (nats xs) (nat_of_integer k))) ks' = map (\<lambda>k. BVar (nat_of_integer k)) ks"
    using all2 * assms(3) by (auto simp: list_all2_conv_all_nth intro!: nth_equalityI)
qed

lemma binding_idx_sound:
  assumes "ok (mapM (idx xs) ks) ks'" "ok (mkabs binders xs (app (pterm.Var H Hty) ks')) t"
    "ok (update (F, T) t env) env'" "wf_env ar env" "ground ar T" "ground ar Hty"
    "binders_ok ar binders" "\<forall>i\<in>set xs. 0 \<le> i" "\<forall>k\<in>set ks. 0 \<le> k"
  shows "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F T) xs \<approx> app (pterm.Var H Hty) ks"
proof -
  note idx = ok_mapM_idx[OF assms(1,8,9)]
  note b = binding_sound[OF assms(2-7) idx(1)]
  show "extends env' env" "wf_env ar env'" using b by simp_all
  show "env' \<Turnstile> app (pterm.Var F T) xs \<approx> app (pterm.Var H Hty) ks"
  proof (rule env_equivI)
    fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
    from b(4)[OF \<sigma> refl] idx(2)
    show "mk_subst \<sigma> (tr (app (pterm.Var F T) xs)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (pterm.Var H Hty) ks))"
      by (simp add: tr_app' comp_def)
  qed
qed

lemma ff_sound:
  assumes "ok (ff env binders F Fty is G Gty js) env'" "wf_env ar env" "ground ar Fty" "ground ar Gty"
    "binders_ok ar binders" "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j"
  shows "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
proof -
  have "extends env' env \<and> wf_env ar env' \<and>
    env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
  proof (cases "subset js is")
    case True
    with assms(1) obtain ks t where ks: "ok (mapM (idx is) js) ks"
      and t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
      and env': "ok (update (F, Fty) t env) env'"
      by (auto simp: ff_def)
    from binding_idx_sound[OF ks t env' assms(2,3,4,5,6,7)] show ?thesis by simp
  next
    case False
    let ?ks = "inter js is"
    from False assms(1) obtain ks' Hty where
      ks': "ok (mapM (idx is) ?ks) ks'" and Hty: "ok (type_of_G env Fty (ilength is) ks') Hty"
      and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain tG tF env2 where
      tG: "ok (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) tG"
      and tF: "ok (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) tF"
      and env2: "ok (update (F, Fty) tF env1) env2" and env': "ok (update (G, Gty) tG env2) env'"
      by auto
    from tF obtain ksF where ksF: "ok (mapM (idx is) ?ks) ksF"
      and tF': "ok (mkabs binders is (app H ksF)) tF" by auto
    from tG obtain ksG where ksG: "ok (mapM (idx js) ?ks) ksG"
      and tG': "ok (mkabs binders js (app H ksG)) tG" by auto
    have ks_nonneg: "\<forall>k\<in>set ?ks. 0 \<le> k" using assms(6) by (auto simp: inter_def)
    have Hty': "ground ar Hty" by (rule type_of_G_ground[OF Hty wf_envD(1)[OF assms(2)] assms(3)])
    note G' = genvar_simps[OF H]
    have wf1: "wf_env ar env1" by (rule genvar_wf_env[OF H assms(2)])
    note bF = binding_idx_sound[OF ksF tF'[unfolded G'(4)] env2 wf1 assms(3) Hty' assms(5,6) ks_nonneg]
    note bG = binding_idx_sound[OF ksG tG'[unfolded G'(4)] env' bF(2) assms(4) Hty' assms(5,7) ks_nonneg]
    have "extends env' env"
      using extends_trans[OF bG(1) extends_trans[OF bF(1) genvar_extends[OF H]]] .
    moreover have "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
      using env_equiv_trans[OF env_equiv_extends[OF bF(3) bG(1)] env_equiv_sym[OF bG(3)]] .
    ultimately show ?thesis using bG(2) by simp
  qed
  then show "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
    by simp_all
qed

lemma flexflex2_sound:
  assumes "ok (flexflex2 env binders F Fty is G Gty js) env'" "wf_env ar env" "ground ar Fty"
    "ground ar Gty" "binders_ok ar binders" "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j"
  shows "extends env' env" "wf_env ar env'"
    "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
  using assms ff_sound[of env binders F Fty "is" G Gty js env' ar]
    ff_sound[of env binders G Gty js F Fty "is" env' ar]
  by (auto simp: flexflex2_def split: if_splits intro: env_equiv_sym)

subsection \<open>Projections\<close>

text \<open>
  \<open>bren xs d\<close> maps the bound variables of a projected term (at depth \<open>d\<close>) bren to those of
  the original term.
\<close>

definition bren :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bren xs d v = (if v < d then v else ren xs (v - d) + d)"

lemma bren_0: "bren xs 0 = ren xs"
  by (simp add: bren_def fun_eq_iff)

lemma bren_Suc[simp]: "(\<lambda>v. case v of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (bren xs d a)) = bren xs (Suc d)"
  by (auto simp: bren_def fun_eq_iff split: nat.splits)

lemma map_BVars_bren_Abs: "map_BVars (bren xs d) (dB.Abs t) = dB.Abs (map_BVars (bren xs (Suc d)) t)"
  by simp

lemma ok_trans:
  assumes "ok (trans xs d i) j" "0 \<le> d" "0 \<le> i" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "0 \<le> j \<and> nat_of_integer j < nat_of_integer d + length xs \<and>
    bren (nats xs) (nat_of_integer d) (nat_of_integer j) = nat_of_integer i"
proof (cases "i < d")
  case True
  from True assms(1) have j: "j = i" by (simp add: trans_def)
  with True assms(2,3) have "nat_of_integer j < nat_of_integer d" by (simp add: nat_of_integer_less_iff)
  with j assms(3) show ?thesis by (auto simp: bren_def)
next
  case False
  with assms(1) obtain k where k: "ok (idx xs (i - d)) k" "j = k + d" by (auto simp: trans_def)
  from ok_idx_ren[OF k(1) assms(4)] False
  have "0 \<le> k" "nat_of_integer k < length xs" "ren (nats xs) (nat_of_integer k) = nat_of_integer (i - d)"
    by auto
  moreover have "nat_of_integer d \<le> nat_of_integer i"
    using False by (simp add: integer_reps nat_mono)
  ultimately show ?thesis using k(2) False assms(2)
    by (auto simp: bren_def nat_of_integer_add nat_of_integer_less_iff[symmetric] nat_of_integer_diff)
qed

lemma ok_try_trans:
  assumes "ok (try_trans xs d i) r" "0 \<le> d" "0 \<le> i" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "r = None \<or> (\<exists>j. r = Some j \<and> 0 \<le> j \<and> nat_of_integer j < nat_of_integer d + length xs \<and>
    bren (nats xs) (nat_of_integer d) (nat_of_integer j) = nat_of_integer i)"
proof -
  from assms(1) consider "ok (trans xs d i) (the r)" "r \<noteq> None" | "r = None"
    by (auto simp: try_trans_def trans_def ok_handle split: if_splits)
  then show ?thesis using ok_trans[OF _ assms(2-4)] by cases auto
qed

lemma mk_proj_list_aux_ren:
  "length zs = length os \<Longrightarrow>
    map (\<lambda>k. ren (pre @ zs) (nat_of_integer k)) (mk_proj_list_aux os (integer_of_nat (length zs) - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os)) \<and>
    (\<forall>k\<in>set (mk_proj_list_aux os (integer_of_nat (length zs) - 1)). 0 \<le> k \<and> nat_of_integer k < length zs)"
proof (induction os arbitrary: pre zs)
  case (Cons opt os)
  then obtain z zs' where zs: "zs = z # zs'" "length zs' = length os" by (cases zs) auto
  let ?j = "integer_of_nat (length os)"
  have j: "integer_of_nat (length zs) - 1 = ?j"
    by (simp add: zs integer_eq_iff)
  have eq: "mk_proj_list_aux (opt # os) (integer_of_nat (length zs) - 1) =
    (if opt \<noteq> None then ?j # mk_proj_list_aux os (?j - 1) else mk_proj_list_aux os (?j - 1))"
    by (simp only: j mk_proj_list_aux.simps)
  have r: "ren (pre @ zs) (nat_of_integer ?j) = z"
    by (simp add: ren_def zs nth_append)
  from Cons.IH[of zs' "pre @ [z]"] zs(2)
  have ih: "map (\<lambda>k. ren (pre @ zs) (nat_of_integer k)) (mk_proj_list_aux os (?j - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs' os))"
    "\<forall>k\<in>set (mk_proj_list_aux os (?j - 1)). 0 \<le> k \<and> nat_of_integer k < length zs'"
    by (simp_all add: zs)
  show ?case
    unfolding eq using ih r by (auto simp: zs integer_reps)
qed simp

lemma mk_proj_list_ren:
  "length zs = length os \<Longrightarrow>
    map (\<lambda>k. ren zs (nat_of_integer k)) (mk_proj_list os) = map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
  "length zs = length os \<Longrightarrow>
    \<forall>k\<in>set (mk_proj_list os). 0 \<le> k \<and> nat_of_integer k < length zs"
  using mk_proj_list_aux_ren[of zs os "[]"] by (simp_all add: mk_proj_list_def ilength_eq)

lemma map_filter_bren:
  assumes "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> f l = g j)) js os"
  shows "map f (List.map_filter id os) = map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip (map g js) os))"
  using assms by (induction js os rule: list_all2_induct) auto

lemma set_map_filter_id: "set (List.map_filter id os) = {l. Some l \<in> set os}"
  by (induction os) (auto split: option.splits)

lemma mapAccM_ok:
  assumes "ok (mapAccM f xs e) (ys, e')"
    and "\<And>x e y e1. x \<in> set xs \<Longrightarrow> ok (f x e) (y, e1) \<Longrightarrow> P e \<Longrightarrow> P e1 \<and> R e1 e \<and> Q x y e1"
    and "\<And>x y e1 e2. Q x y e1 \<Longrightarrow> R e2 e1 \<Longrightarrow> Q x y e2"
    and "\<And>e1 e2 e3. R e3 e2 \<Longrightarrow> R e2 e1 \<Longrightarrow> R e3 e1" and "\<And>e. R e e"
    and "P e"
  shows "P e' \<and> R e' e \<and> list_all2 (\<lambda>x y. Q x y e') xs ys"
  using assms(1,2,6)
proof (induction xs arbitrary: e ys)
  case (Cons x xs)
  from Cons.prems(1) obtain y e1 ys' where y: "ok (f x e) (y, e1)"
    and ys': "ok (mapAccM f xs e1) (ys', e')" and ys: "ys = y # ys'"
    by (auto split: prod.splits)
  from Cons.prems(2)[OF _ y Cons.prems(3)] have e1: "P e1" "R e1 e" "Q x y e1" by auto
  from Cons.IH[OF ys' _ e1(1)] Cons.prems(2) have "P e'" "R e' e1" "list_all2 (\<lambda>x y. Q x y e') xs ys'"
    by auto
  with e1 ys assms(3,4) show ?case by blast
qed (auto simp: assms(5))

lemma no_loose_bound_list_comb:
  "no_loose_bound (tr (list_comb h ts)) n \<longleftrightarrow>
    no_loose_bound (tr h) n \<and> (\<forall>t\<in>set ts. no_loose_bound (tr t) n)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

text \<open>Soundness of \<^const>\<open>pr\<close> (projection of the rigid side of a flex-rigid problem).\<close>

definition pr_result :: "(name \<Rightarrow> nat) \<Rightarrow> integer list \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "pr_result ar xs d s s' env' \<longleftrightarrow>
    proper s' \<and> typs_ok ar s' \<and> no_loose_bound (tr s') (nat_of_integer d + length xs) \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow>
      mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s')))"

lemma pr_result_extends: "pr_result ar xs d s s' env1 \<Longrightarrow> extends env2 env1 \<Longrightarrow> pr_result ar xs d s s' env2"
  by (auto simp: pr_result_def intro: sat_extends)

lemma pr_sound:
  assumes "pr xs s env d binders = Some r"
  shows "r = Ok (s', env') \<Longrightarrow> wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> proper s \<Longrightarrow>
    typs_ok ar s \<Longrightarrow> 0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow>
    extends env' env \<and> wf_env ar env' \<and> pr_result ar xs d s s' env'"
  using assms
proof (induction xs s env d binders r arbitrary: s' env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d binders r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and d: "0 \<le> d"
    and xs: "\<forall>x\<in>set xs. 0 \<le> x"
    using "1.prems" by simp_all
  from "1.hyps" "1.prems"(1) have "ok (head_norm env s \<bind> (\<lambda>s0.
      if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
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
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))) (s', env')"
    by (simp only:)
  then obtain s0 where hn: "ok (head_norm env s) s0" and rest: "ok (
      if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
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
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')})) (s', env')"
    unfolding ok_bindM by blast
  from head_norm_sound[OF hn refl wf] "1.prems"
  have s0: "proper s0" "typs_ok ar s0" "env \<Turnstile> s \<approx> s0" by auto
  show ?case
  proof (cases "is_Abs s0")
    case True
    then obtain a T t where s0a: "s0 = pterm.Abs a T t" by (cases s0) auto
    with rest True obtain t' where t': "ok (prr xs t env (d + 1) ((a, T) # binders)) (t', env')"
      and s': "s' = pterm.Abs a T t'"
      by (auto split: prod.splits)
    have bok': "binders_ok ar ((a, T) # binders)" using bok s0(2) s0a by (simp add: binders_ok_def)
    from "1.IH"[OF t' refl wf bok'] s0 s0a d xs
    have ih: "extends env' env" "wf_env ar env'" "pr_result ar xs (d + 1) t t' env'"
      by auto
    have "pr_result ar xs d s s' env'"
      unfolding pr_result_def
    proof (intro conjI allI impI)
      show "proper s'" "typs_ok ar s'" using ih(3) s' s0 s0a by (auto simp: pr_result_def)
      show "no_loose_bound (tr s') (nat_of_integer d + length xs)"
        using ih(3) s' d by (auto simp: pr_result_def nat_of_integer_add)
      fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
      have "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr s0)"
        using env_equivD[OF s0(3) \<sigma>(1) sat_extends[OF \<sigma>(2) ih(1)]] .
      also have "mk_subst \<sigma> (tr s0) = dB.Abs (mk_subst \<sigma> (tr t))" by (simp add: s0a)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (map_BVars (bren (nats xs) (Suc (nat_of_integer d))) (mk_subst \<sigma> (tr t')))"
        using ih(3) \<sigma> d by (auto simp: pr_result_def nat_of_integer_add intro: equiv_Abs)
      also have "\<dots> = map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))"
        by (simp add: s' map_BVars_bren_Abs)
      finally show "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))" .
    qed
    with ih show ?thesis by blast
  next
    case False
    obtain h ts where hts: "strip_comb s0 = (h, ts)" by force
    note s0_eq = strip_comb_list_comb[OF hts]
    have ts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t" "proper h" "typs_ok ar h"
      using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = pterm.Var F Fty" by (cases h) auto
      from rest False hts h obtain js js' Hty where js: "ok (ints_of' env ts) js"
        and js': "ok (mapM (try_trans xs d) js) js'"
        and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
        and rest2: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow>
          mk_hnf binders js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
            (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (s', env')"
        by (auto simp: Let_def)
      obtain env1 H where H: "genvar (fst F) env Hty = (env1, H)" by force
      with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
        and env': "ok (update (F, Fty) t env1) env'" and s': "s' = app H (List.map_filter id js')"
        by (auto simp: mk_hnf_def)
      let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
      note ints = ints_of'_sound[OF js wf ts(1)]
      have js'2: "list_all2 (\<lambda>j opt. ok (try_trans xs d j) opt) js js'" using js' by (simp add: ok_mapM)
      then have len: "length js' = length js" by (simp add: list_all2_lengthD)
      have tt: "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> 0 \<le> l \<and>
          nat_of_integer l < nat_of_integer d + length xs \<and>
          bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer j)) js js'"
      proof -
        have "js' ! p = None \<or> (\<exists>l. js' ! p = Some l \<and> 0 \<le> l \<and>
          nat_of_integer l < nat_of_integer d + length xs \<and>
          bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer (js ! p))"
          if p: "p < length js" for p
        proof -
          from js'2 p have "ok (try_trans xs d (js ! p)) (js' ! p)" by (simp add: list_all2_conv_all_nth)
          from ok_try_trans[OF this d _ xs] ints(2) p show ?thesis by auto
        qed
        with len show ?thesis by (simp add: list_all2_conv_all_nth)
      qed
      have ls: "\<forall>l\<in>set ?ls. 0 \<le> l \<and> nat_of_integer l < nat_of_integer d + length xs"
        using tt by (fastforce simp: set_map_filter_id list_all2_conv_all_nth in_set_conv_nth)
      have ks: "\<forall>k\<in>set ?ks. 0 \<le> k \<and> nat_of_integer k < length js"
        using mk_proj_list_ren(2)[of "nats js" js'] len by simp
      have Fty: "ground ar Fty" using ts(3) h by simp
      have Hty': "ground ar Hty" by (rule type_of_G_ground[OF Hty wf_envD(1)[OF wf] Fty])
      note G' = genvar_simps[OF H]
      have wf1: "wf_env ar env1" by (rule genvar_wf_env[OF H wf])
      note b = binding_sound[OF t[unfolded G'(4)] env' wf1 Fty Hty' bok ks]
      have ext: "extends env' env" by (rule extends_trans[OF b(1) genvar_extends[OF H]])
      have "pr_result ar xs d s s' env'"
        unfolding pr_result_def
      proof (intro conjI allI impI)
        show "proper s'" "typs_ok ar s'" "no_loose_bound (tr s') (nat_of_integer d + length xs)"
          using ls Hty' by (auto simp: s' G'(4) proper_app typs_ok_app no_loose_bound_app)
        fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
        let ?H = "\<sigma> (code (AVar (fst F, maxidx env + 1)))"
        have "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (list_comb h ts))"
          using env_equivD[OF s0(3) \<sigma>(1) sat_extends[OF \<sigma>(2) ext]] s0_eq by simp
        also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (pterm.Var F Fty) js))"
          using env_equivD[OF ints_of'_equiv[OF js wf ts(1)] \<sigma>(1) sat_extends[OF \<sigma>(2) ext]] h
          by simp
        also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?H \<degree>\<degree> map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ?ks"
          by (rule b(4)[OF \<sigma> refl])
        also have "map (\<lambda>k. BVar (ren (nats js) (nat_of_integer k))) ?ks =
            map BVar (map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip (nats js) js')))"
          using mk_proj_list_ren(1)[of "nats js" js', symmetric] len by (simp add: comp_def)
        also have "map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip (nats js) js')) =
            map (\<lambda>l. bren (nats xs) (nat_of_integer d) (nat_of_integer l)) ?ls"
          using tt by (intro map_filter_bren[symmetric]) (auto elim!: list_all2_mono)
        also have "?H \<degree>\<degree> map BVar (map (\<lambda>l. bren (nats xs) (nat_of_integer d) (nat_of_integer l)) ?ls) =
            map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))"
          by (simp add: s' G'(4) map_BVars_app_Var[OF \<sigma>(1)] comp_def)
        finally show "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))" .
      qed
      with ext b(2) show ?thesis by simp
    next
      case False
      have nAbs: "\<not> is_Abs h"
      proof
        assume "is_Abs h"
        with rest \<open>\<not> is_Abs s0\<close> hts False show False by simp
      qed
      from rest \<open>\<not> is_Abs s0\<close> hts False nAbs obtain h' ts' where
        h': "ok (case h of Bound i \<Rightarrow> trans xs d i \<bind> (\<lambda>j. return (Bound j)) | _ \<Rightarrow> return h) h'"
        and mt: "ok (mapAccM (\<lambda>s env. prr xs s env d binders) ts env) (ts', env')"
        and s': "s' = list_comb h' ts'"
        by (auto split: prod.splits)
      have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
      have hd: "proper h'" "typs_ok ar h'" "no_loose_bound (tr h') (nat_of_integer d + length xs)"
        "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow>
          map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr h')) = mk_subst \<sigma> (tr h)"
      proof -
        have "proper h' \<and> typs_ok ar h' \<and> no_loose_bound (tr h') (nat_of_integer d + length xs) \<and>
          (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow>
            map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr h')) = mk_subst \<sigma> (tr h))"
        proof (cases h)
          case (Bound i)
          with h' obtain j where j: "ok (trans xs d i) j" "h' = Bound j" by auto
          from ok_trans[OF j(1) d _ xs] ts(2) Bound j(2) show ?thesis by auto
        qed (use h' ts(3) nApp nAbs False in \<open>auto simp: map_BVars_subst_closed\<close>)
        then show "proper h'" "typs_ok ar h'" "no_loose_bound (tr h') (nat_of_integer d + length xs)"
          "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow>
            map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr h')) = mk_subst \<sigma> (tr h)"
          by simp_all
      qed
      have m: "wf_env ar env' \<and> extends env' env \<and> list_all2 (\<lambda>x y. pr_result ar xs d x y env') ts ts'"
      proof (rule mapAccM_ok[OF mt, where P = "wf_env ar" and R = "\<lambda>e1 e. extends e1 e"])
        fix x e y e1
        assume x: "x \<in> set ts" and y: "ok (prr xs x e d binders) (y, e1)" and e: "wf_env ar e"
        from "1.IH"[OF y refl e bok _ _ d xs] ts(1) x
        show "wf_env ar e1 \<and> extends e1 e \<and> pr_result ar xs d x y e1" by auto
      qed (auto intro: pr_result_extends extends_trans wf)
      then have ts': "list_all2 (\<lambda>x y. pr_result ar xs d x y env') ts ts'" by simp
      have "pr_result ar xs d s s' env'"
        unfolding pr_result_def
      proof (intro conjI allI impI)
        show "proper s'" "typs_ok ar s'" "no_loose_bound (tr s') (nat_of_integer d + length xs)"
          using ts' hd(1-3)
          by (auto simp: s' proper_list_comb typs_ok_list_comb no_loose_bound_list_comb
            pr_result_def list_all2_conv_all_nth in_set_conv_nth)
        fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
        have "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (list_comb h ts))"
          using env_equivD[OF s0(3) \<sigma>(1) sat_extends[OF \<sigma>(2)]] m s0_eq by simp
        also have "\<dots> = mk_subst \<sigma> (tr h) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
          by (simp add: tr_list_comb comp_def)
        also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr h) \<degree>\<degree>
            map (\<lambda>t. map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr t))) ts'"
          using ts' \<sigma> by (intro equiv_list_app) (auto simp: list_all2_map1 list_all2_map2 pr_result_def
            elim!: list_all2_mono)
        also have "\<dots> = map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))"
          by (simp add: s' tr_list_comb hd(4)[OF \<sigma>(1)] comp_def)
        finally show "mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
          map_BVars (bren (nats xs) (nat_of_integer d)) (mk_subst \<sigma> (tr s'))" .
      qed
      with m show ?thesis by simp
    qed
  qed
qed

lemma downto0_nats: "downto0 is n \<Longrightarrow> -1 \<le> n \<and> nats is = downs (nat_of_integer (n + 1))"
proof (induction "is" arbitrary: n)
  case (Cons i "is")
  from Cons.prems have i: "i = n" and d: "downto0 is (n - 1)" by simp_all
  from Cons.IH[OF d] have n: "-1 \<le> n - 1" and isd: "nats is = downs (nat_of_integer (n - 1 + 1))"
    by simp_all
  have n': "-1 \<le> n" "nat_of_integer (n + 1) = Suc (nat_of_integer n)" "n - 1 + 1 = n"
    using n by (simp_all add: integer_reps nat_add_distrib)
  have "nats (i # is) = nat_of_integer n # downs (nat_of_integer n)" by (simp add: i isd n'(3))
  also have "\<dots> = downs (nat_of_integer (n + 1))" by (simp add: n'(2))
  finally show ?case using n'(1) by simp
qed (simp add: integer_reps)

lemma ren_downs: "v < m \<Longrightarrow> ren (downs m) v = v"
  by (simp add: ren_def downs_nth)

lemma proj_sound:
  assumes "ok (proj s env binders is) (u, env')" "wf_env ar env" "binders_ok ar binders" "proper s"
    "typs_ok ar s" "\<forall>i\<in>set is. 0 \<le> i" "no_loose_bound (tr s) (length binders)"
  shows "extends env' env" "wf_env ar env'" "proper u" "typs_ok ar u" "no_loose_bound (tr u) (length is)"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow>
      mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (mk_subst \<sigma> (tr u))"
proof -
  have "extends env' env \<and> wf_env ar env' \<and> proper u \<and> typs_ok ar u \<and> no_loose_bound (tr u) (length is) \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env' \<longrightarrow>
      mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (mk_subst \<sigma> (tr u)))"
  proof (cases "downto0 is (ilength binders - 1)")
    case True
    from downto0_nats[OF True] have "nats is = downs (length binders)" by simp
    then have len: "length is = length binders" by (metis length_downs length_map)
    have "map_BVars (ren (nats is)) (mk_subst \<sigma> (tr s)) = mk_subst \<sigma> (tr s)" if "closed_on UNIV \<sigma>" for \<sigma>
    proof (rule map_BVars_no_loose)
      show "no_loose_bound (mk_subst \<sigma> (tr s)) (length binders)"
        using assms(7) that by (auto intro: mk_subst_no_loose_bound closed_on_mono)
      show "\<forall>j<length binders. ren (nats is) j = j"
        using \<open>nats is = downs (length binders)\<close> by (simp add: ren_downs)
    qed
    with True assms(1,2,4,5,7) len show ?thesis by (auto simp: proj_def)
  next
    case False
    with assms(1) have "pr is s env 0 binders = Some (Ok (u, env'))" by (simp add: proj_def)
    from pr_sound[OF this refl assms(2-5) _ assms(6)] show ?thesis
      by (auto simp: pr_result_def bren_0)
  qed
  then show "extends env' env" "wf_env ar env'" "proper u" "typs_ok ar u"
    "no_loose_bound (tr u) (length is)"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow>
      mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (mk_subst \<sigma> (tr u))"
    by simp_all
qed

subsection \<open>Flex-rigid problems\<close>

lemma flexrigid_sound:
  assumes "ok (flexrigid env binders F Fty is t) env'" "wf_env ar env" "binders_ok ar binders"
    "ground ar Fty" "proper t" "typs_ok ar t" "\<forall>i\<in>set is. 0 \<le> i"
    "no_loose_bound (tr t) (length binders)"
  shows "extends env' env" "wf_env ar env'" "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> t"
proof -
  have hnd: "\<not> ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e) y"
    for e and y :: env by (cases e) simp_all
  from assms(1) obtain u env1 u' where pj: "ok (proj t env binders is) (u, env1)"
    and u': "ok (mkabs binders is u) u'" and env': "ok (update (F, Fty) u' env1) env'"
    by (auto simp: flexrigid_def ok_handle hnd split: if_splits prod.splits)
  note p = proj_sound[OF pj assms(2,3,5,6,7,8)]
  show ext: "extends env' env" by (rule extends_trans[OF ok_update_extends[OF env'] p(1)])
  show "wf_env ar env'"
  proof (rule ok_update_wf_env[OF env' p(2)])
    show "proper u'" "typs_ok ar u'" "ground ar Fty" "no_loose_bound (tr u') 0"
      using ok_mkabs[OF u'] ok_mkabs_typs_ok[OF u' assms(3)] p(3-5) assms(4)
      by (auto simp: loose_bound_Abs_m)
  qed
  show "env' \<Turnstile> app (pterm.Var F Fty) is \<approx> t"
  proof (rule env_equivI)
    fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env'"
    have "mk_subst \<sigma> (tr (app (pterm.Var F Fty) is)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (mk_subst \<sigma> (tr u))"
      by (rule sat_binding_app[OF \<sigma>(2,1) ok_update_lookup[OF env'] u' refl])
    also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
      using p(6)[OF \<sigma>(1) sat_extends[OF \<sigma>(2) ok_update_extends[OF env']]] by (rule equiv_sym)
    finally show "mk_subst \<sigma> (tr (app (pterm.Var F Fty) is)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" .
  qed
qed


subsection \<open>Unification\<close>

lemma tr_incr_aux: "proper t \<Longrightarrow> 0 \<le> d \<Longrightarrow> tr (incr_aux d t) = lift (tr t) (nat_of_integer d)"
  by (induction d t rule: incr_aux.induct)
    (auto simp: nat_of_integer_less_iff nat_of_integer_add not_less)

lemma proper_incr_aux: "proper t \<Longrightarrow> proper (incr_aux d t)"
  by (induction d t rule: incr_aux.induct) auto

lemma typs_ok_incr_aux: "typs_ok ar (incr_aux d t) \<longleftrightarrow> typs_ok ar t"
  by (induction d t rule: incr_aux.induct) auto

lemma no_loose_bound_lift: "no_loose_bound t n \<Longrightarrow> k \<le> n \<Longrightarrow> no_loose_bound (lift t k) (Suc n)"
  by (induction t arbitrary: k n) auto

lemma eta_lift_equiv: "dB.Abs (lift u 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> u"
proof -
  have "dB.Abs (lift u 0 \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> (lift u 0)[dummy/0]" by (rule eta.eta) simp
  then show ?thesis by (simp add: eta_into_equiv)
qed

lemma env_equiv_eta:
  assumes "env \<Turnstile> b \<approx> incr u $ Bound 0" "proper u"
  shows "env \<Turnstile> pterm.Abs a T b \<approx> u"
proof (rule env_equivI)
  fix \<sigma> :: "nat \<Rightarrow> dB" assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> env"
  have "mk_subst \<sigma> (tr (pterm.Abs a T b)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (mk_subst \<sigma> (tr (incr u $ Bound 0)))"
    using env_equivD[OF assms(1) \<sigma>] by (simp add: equiv_Abs)
  also have "mk_subst \<sigma> (tr (incr u $ Bound 0)) = lift (mk_subst \<sigma> (tr u)) 0 \<degree> BVar 0"
    using assms(2) \<sigma>(1) by (simp add: incr_def tr_incr_aux mk_subst_lift_on closed_on_mono)
  also have "dB.Abs (lift (mk_subst \<sigma> (tr u)) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    by (rule eta_lift_equiv)
  finally show "mk_subst \<sigma> (tr (pterm.Abs a T b)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" .
qed

lemma ok_zip_eq: "ok (zip_eq xs ys) ps \<longleftrightarrow> length xs = length ys \<and> ps = zip xs ys"
  by (induction xs ys arbitrary: ps rule: zip_eq.induct) auto

lemma foldM_ok:
  assumes "ok (foldM f xs e) e'"
    and "\<And>x e e1. x \<in> set xs \<Longrightarrow> ok (f x e) e1 \<Longrightarrow> P e \<Longrightarrow> P e1 \<and> R e1 e \<and> Q x e1"
    and "\<And>x e1 e2. Q x e1 \<Longrightarrow> R e2 e1 \<Longrightarrow> Q x e2"
    and "\<And>e1 e2 e3. R e3 e2 \<Longrightarrow> R e2 e1 \<Longrightarrow> R e3 e1" and "\<And>e. R e e"
    and "P e"
  shows "P e' \<and> R e' e \<and> (\<forall>x\<in>set xs. Q x e')"
  using assms(1,2,6)
proof (induction xs arbitrary: e)
  case (Cons x xs)
  from Cons.prems(1) obtain e1 where e1: "ok (f x e) e1" and rest: "ok (foldM f xs e1) e'" by auto
  from Cons.prems(2)[OF _ e1 Cons.prems(3)] have h: "P e1" "R e1 e" "Q x e1" by auto
  from Cons.IH[OF rest _ \<open>P e1\<close>] Cons.prems(2) have t: "P e'" "R e' e1" "\<forall>x\<in>set xs. Q x e'"
    by auto
  have "R e' e" by (rule assms(4)[OF t(2) h(2)])
  moreover have "Q x e'" by (rule assms(3)[OF h(3) t(2)])
  ultimately show ?case using t(1,3) by simp
qed (auto simp: assms(5))

lemma not_ok_rigid_clash: "\<not> ok (rigid_clash binders h1 h2) y"
  by (simp add: rigid_clash_def split: pterm.splits)

text \<open>The invariant of \<^const>\<open>unif\<close>: well-formed terms that are closed below the binders.\<close>

definition wf_term :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "wf_term ar n t \<longleftrightarrow> proper t \<and> typs_ok ar t \<and> no_loose_bound (tr t) n"

lemma env_equiv_tr_eq: "tr s = tr t \<Longrightarrow> env \<Turnstile> s \<approx> t"
  by (simp add: env_equiv_def)

lemma wf_term_list_comb:
  "wf_term ar n (list_comb h ts) \<longleftrightarrow> wf_term ar n h \<and> (\<forall>t\<in>set ts. wf_term ar n t)"
  by (auto simp: wf_term_def proper_list_comb typs_ok_list_comb no_loose_bound_list_comb)

theorem unif_sound:
  assumes "unif alg binders s t env = Some r"
  shows "r = Ok env' \<Longrightarrow> wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow>
    wf_term ar (length binders) s \<Longrightarrow> wf_term ar (length binders) t \<Longrightarrow>
    extends env' env \<and> wf_env ar env' \<and> env' \<Turnstile> s \<approx> t"
  using assms
proof (induction alg binders s t env r arbitrary: env' rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg binders s t env r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders"
    and ws: "wf_term ar (length binders) s" and wt: "wf_term ar (length binders) t"
    using "1.prems" by simp_all
  from "1.hyps" "1.prems"(1) have "ok (do {
      s' \<leftarrow> head_norm env s;
      t' \<leftarrow> head_norm env t;
      if is_Abs s' \<and> is_Abs t' then
        (case (s', t') of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s' then
        (case s' of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t' $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t' then
        (case t' of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s' $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s'; (ht, ts) = strip_comb t' in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht))
    }) env'"
    by (simp only:)
  then obtain s0 t0 where hs: "ok (head_norm env s) s0" and ht: "ok (head_norm env t) t0"
    and rest: "ok (
      if is_Abs s0 \<and> is_Abs t0 then
        (case (s0, t0) of
          (pterm.Abs ns Ts ts, pterm.Abs nt Tt tt) \<Rightarrow> do {
            let name = (if ns = STR '''' then nt else ns);
            env' \<leftarrow> unify_types alg Ts Tt env;
            uni alg ((name, Ts) # binders) ts tt env'}
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs s0 then
        (case s0 of
          pterm.Abs ns Ts ts \<Rightarrow> uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else if is_Abs t0 then
        (case t0 of
          pterm.Abs nt Tt tt \<Rightarrow> uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env
        | _ \<Rightarrow> raise (Failure (STR ''unif'')))
      else
        (let (hs, ss) = strip_comb s0; (ht, ts) = strip_comb t0 in
          if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (pterm.Var F Fty, pterm.Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env binders F Fty is js
                else flexflex2 env binders F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env binders F Fty is t0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              pterm.Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env binders F Fty is s0}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht))) env'"
    unfolding ok_bindM by blast
  from head_norm_sound[OF hs refl wf] ws
  have ws0: "wf_term ar (length binders) s0" and s0: "env \<Turnstile> s \<approx> s0"
    by (auto simp: wf_term_def)
  from head_norm_sound[OF ht refl wf] wt
  have wt0: "wf_term ar (length binders) t0" and t0: "env \<Turnstile> t \<approx> t0"
    by (auto simp: wf_term_def)
  let ?n = "length binders"
  have "extends env' env \<and> wf_env ar env' \<and> env' \<Turnstile> s0 \<approx> t0"
  proof (cases "is_Abs s0")
    case sA: True
    then obtain ns Ts ts where s0a: "s0 = pterm.Abs ns Ts ts" by (cases s0) auto
    have gTs: "ground ar Ts" using ws0 s0a by (simp add: wf_term_def)
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
      define nm where "nm = (if ns = STR '''' then nt else ns)"
      let ?b = "(nm, Ts) # binders"
      from rest s0a t0a have "ok (unify_types alg Ts Tt env \<bind> uni alg ?b ts tt) env'"
        by (simp add: Let_def nm_def)
      then have u: "ok (uni alg ?b ts tt env) env'"
        by (auto simp: unify_types_ground[OF gTs gTt] split: if_splits)
      have bok': "binders_ok ar ?b" using bok gTs by (simp add: binders_ok_def)
      from "1.IH"[OF u refl wf bok'] ws0 wt0 s0a t0a
      have "extends env' env" "wf_env ar env'" "env' \<Turnstile> ts \<approx> tt" by (auto simp: wf_term_def)
      then show ?thesis using s0a t0a by (auto intro: env_equiv_Abs)
    next
      case False
      from rest sA False s0a have u: "ok (uni alg ((ns, Ts) # binders) ts (incr t0 $ Bound 0) env) env'"
        by simp
      have bok': "binders_ok ar ((ns, Ts) # binders)" using bok gTs by (simp add: binders_ok_def)
      have wi: "wf_term ar (Suc ?n) (incr t0 $ Bound 0)"
        using wt0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
          intro: no_loose_bound_lift)
      from "1.IH"[OF u refl wf bok'] ws0 s0a wi
      have "extends env' env" "wf_env ar env'" "env' \<Turnstile> ts \<approx> incr t0 $ Bound 0"
        by (auto simp: wf_term_def)
      then show ?thesis using s0a env_equiv_eta wt0 by (auto simp: wf_term_def)
    qed
  next
    case nsA: False
    show ?thesis
    proof (cases "is_Abs t0")
      case True
      then obtain nt Tt tt where t0a: "t0 = pterm.Abs nt Tt tt" by (cases t0) auto
      have gTt: "ground ar Tt" using wt0 t0a by (simp add: wf_term_def)
      from rest nsA True t0a have u: "ok (uni alg ((nt, Tt) # binders) (incr s0 $ Bound 0) tt env) env'"
        by simp
      have bok': "binders_ok ar ((nt, Tt) # binders)" using bok gTt by (simp add: binders_ok_def)
      have wi: "wf_term ar (Suc ?n) (incr s0 $ Bound 0)"
        using ws0 by (auto simp: wf_term_def incr_def tr_incr_aux proper_incr_aux typs_ok_incr_aux
          intro: no_loose_bound_lift)
      from "1.IH"[OF u refl wf bok'] wi wt0 t0a
      have e: "extends env' env" "wf_env ar env'" "env' \<Turnstile> incr s0 $ Bound 0 \<approx> tt"
        by (auto simp: wf_term_def)
      have "env' \<Turnstile> pterm.Abs nt Tt tt \<approx> s0"
        using env_equiv_eta[OF env_equiv_sym[OF e(3)]] ws0 by (simp add: wf_term_def)
      then show ?thesis using e t0a by (auto intro: env_equiv_sym)
    next
      case nAt: False
      obtain hs ss where shs: "strip_comb s0 = (hs, ss)" by force
      obtain ht ts where sht: "strip_comb t0 = (ht, ts)" by force
      note s0e = strip_comb_list_comb[OF shs] and t0e = strip_comb_list_comb[OF sht]
      have wss: "wf_term ar ?n hs" "\<forall>t\<in>set ss. wf_term ar ?n t"
        using ws0 s0e by (simp_all add: wf_term_list_comb)
      have wts: "wf_term ar ?n ht" "\<forall>t\<in>set ts. wf_term ar ?n t"
        using wt0 t0e by (simp_all add: wf_term_list_comb)
      have ss: "\<forall>t\<in>set ss. proper t \<and> typs_ok ar t" and ts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
        using wss(2) wts(2) by (auto simp: wf_term_def)
      have wt0': "proper t0" "typs_ok ar t0" "no_loose_bound (tr t0) ?n"
        and ws0': "proper s0" "typs_ok ar s0" "no_loose_bound (tr s0) ?n"
        using wt0 ws0 by (simp_all add: wf_term_def)
      consider (VV) F Fty G Gty where "hs = pterm.Var F Fty" "ht = pterm.Var G Gty"
        | (VR) F Fty where "hs = pterm.Var F Fty" "\<not> is_Var ht"
        | (RV) G Gty where "\<not> is_Var hs" "ht = pterm.Var G Gty"
        | (RR) "\<not> is_Var hs" "\<not> is_Var ht"
        by (cases hs; cases ht) auto
      then show ?thesis
      proof cases
        case VV
        from rest nsA nAt shs sht VV obtain "is" js where iss: "ok (ints_of' env ss) is"
          and js: "ok (ints_of' env ts) js"
          and ff: "ok (if F = G then flexflex1 env binders F Fty is js
            else flexflex2 env binders F Fty is G Gty js) env'"
          by auto
        have gF: "ground ar Fty" and gG: "ground ar Gty" using wss(1) wts(1) VV by (simp_all add: wf_term_def)
        have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
          using ints_of'_equiv[OF iss wf ss] s0e VV by simp
        have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
          using ints_of'_equiv[OF js wf ts] t0e VV by simp
        have r: "extends env' env \<and> wf_env ar env' \<and>
          env' \<Turnstile> app (pterm.Var F Fty) is \<approx> app (pterm.Var G Gty) js"
        proof (cases "F = G")
          case True
          with ff have "ok (flexflex1 env binders F Fty is js) env'" by simp
          note r = flexflex1_sound[OF this wf gF bok]
          have "env' \<Turnstile> app (pterm.Var F Fty) js \<approx> app (pterm.Var G Gty) js"
            by (rule env_equiv_tr_eq) (simp add: tr_app' True)
          with r show ?thesis using env_equiv_trans[OF r(3)] by blast
        next
          case False
          with ff have "ok (flexflex2 env binders F Fty is G Gty js) env'" by simp
          from flexflex2_sound[OF this wf gF gG bok ints_of'_sound(2)[OF iss wf ss]
            ints_of'_sound(2)[OF js wf ts]]
          show ?thesis by simp
        qed
        then have "env' \<Turnstile> s0 \<approx> t0"
          using env_equiv_trans[OF env_equiv_trans[OF env_equiv_extends[OF eqs] _]
            env_equiv_sym[OF env_equiv_extends[OF eqt]]] by blast
        with r show ?thesis by simp
      next
        case VR
        from rest nsA nAt shs sht VR obtain "is" where iss: "ok (ints_of' env ss) is"
          and fr: "ok (flexrigid env binders F Fty is t0) env'"
          by auto
        have gF: "ground ar Fty" using wss(1) VR by (simp add: wf_term_def)
        have eqs: "env \<Turnstile> s0 \<approx> app (pterm.Var F Fty) is"
          using ints_of'_equiv[OF iss wf ss] s0e VR by simp
        note r = flexrigid_sound[OF fr wf bok gF wt0'(1,2) ints_of'_sound(2)[OF iss wf ss] wt0'(3)]
        then show ?thesis
          using env_equiv_trans[OF env_equiv_extends[OF eqs r(1)] r(3)] by simp
      next
        case RV
        from rest nsA nAt shs sht RV obtain js where js: "ok (ints_of' env ts) js"
          and fr: "ok (flexrigid env binders G Gty js s0) env'"
          by auto
        have gG: "ground ar Gty" using wts(1) RV by (simp add: wf_term_def)
        have eqt: "env \<Turnstile> t0 \<approx> app (pterm.Var G Gty) js"
          using ints_of'_equiv[OF js wf ts] t0e RV by simp
        note r = flexrigid_sound[OF fr wf bok gG ws0'(1,2) ints_of'_sound(2)[OF js wf ts] ws0'(3)]
        then show ?thesis
          using env_equiv_sym[OF env_equiv_trans[OF env_equiv_extends[OF eqt r(1)] r(3)]] by simp
      next
        case RR
        have nAbs: "\<not> is_Abs hs" "\<not> is_Abs ht"
          using rest nsA nAt shs sht RR by (auto split: if_splits)
        have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
          using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
        have ty: "typs_ok ar hs" "typs_ok ar ht" using wss(1) wts(1) by (simp_all add: wf_term_def)
        from rest nsA nAt shs sht RR nAbs
        have rest': "ok (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB binders i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env}
            | _ \<Rightarrow> rigid_clash binders hs ht) env'"
          by simp
        obtain ps where hsht: "hs = ht" and ps: "ok (zip_eq ss ts) ps"
          and fo: "ok (foldM (\<lambda>(s, t) env. uni alg binders s t env) ps env) env'"
          using rest' ty nApp RR nAbs
          by (cases hs; cases ht) (auto simp: unify_types_ground not_ok_rigid_clash split: if_splits)
        from ps have len: "length ss = length ts" and ps': "ps = zip ss ts" by (simp_all add: ok_zip_eq)
        have "wf_env ar env' \<and> extends env' env \<and> (\<forall>x\<in>set ps. (\<lambda>(s, t). env' \<Turnstile> s \<approx> t) x)"
        proof (rule foldM_ok[OF fo, where P = "wf_env ar" and R = "\<lambda>e1 e. extends e1 e"])
          fix x e e1
          assume x: "x \<in> set ps" and e1: "ok ((\<lambda>(s, t) env. uni alg binders s t env) x e) e1"
            and e: "wf_env ar e"
          obtain a b where xab: "x = (a, b)" by force
          with x ps' have "a \<in> set ss" "b \<in> set ts" by (auto dest: set_zip_leftD set_zip_rightD)
          with "1.IH"[of alg binders a b e _ e1] e1 xab e bok wss(2) wts(2)
          show "wf_env ar e1 \<and> extends e1 e \<and> (\<lambda>(s, t). e1 \<Turnstile> s \<approx> t) x" by auto
        qed (auto intro: env_equiv_extends extends_trans wf)
        then have e: "wf_env ar env'" "extends env' env" "\<forall>(s, t)\<in>set (zip ss ts). env' \<Turnstile> s \<approx> t"
          by (simp_all add: ps')
        from e(3) len have "list_all2 (env_equiv env') ss ts" by (simp add: list_all2_iff)
        from env_equiv_list_comb[OF env_equiv_refl this] have "env' \<Turnstile> s0 \<approx> t0"
          by (simp add: s0e t0e hsht)
        with e show ?thesis by simp
      qed
    qed
  qed
  then have e: "extends env' env" "wf_env ar env'" "env' \<Turnstile> s0 \<approx> t0" by simp_all
  have "env' \<Turnstile> s \<approx> t"
    using env_equiv_trans[OF env_equiv_trans[OF env_equiv_extends[OF s0 e(1)] e(3)]
      env_equiv_sym[OF env_equiv_extends[OF t0 e(1)]]] .
  with e show ?case by simp
qed

text \<open>
  Soundness of \<^const>\<open>unify\<close>: if it returns \<open>env'\<close>, then \<open>env'\<close> extends \<open>env\<close>, and every closed
  substitution satisfying \<open>env'\<close> unifies \<open>s\<close> and \<open>t\<close> modulo \<open>\<beta>\<eta>\<close>.
\<close>

theorem unify_sound_Ok:
  assumes "unify alg s t env = Some (Ok env')" "wf_env ar env" "wf_term ar 0 s" "wf_term ar 0 t"
  shows "extends env' env" "wf_env ar env'"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> sat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
proof -
  from unif_sound[OF assms(1)[unfolded unify_def] refl assms(2)] assms(3,4)
  have *: "extends env' env" "wf_env ar env'" "env' \<Turnstile> s \<approx> t"
    by (simp_all add: binders_ok_def)
  then show "extends env' env" "wf_env ar env'" by simp_all
  fix \<sigma> :: "nat \<Rightarrow> dB" assume "closed_on UNIV \<sigma>" "sat \<sigma> env'"
  with * show "sat \<sigma> env \<and> unifies \<sigma> (tr s) (tr t)"
    by (auto simp: unifies_def intro: sat_extends env_equivD)
qed

end
