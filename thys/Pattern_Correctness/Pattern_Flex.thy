section \<open>Soundness of the Flex-Flex Cases\<close>

theory Pattern_Flex
  imports Pattern_Bindings
begin

context pure_sig
begin

subsection \<open>Flex terms\<close>

lemma strip_comb_acc_apps: "strip_comb_acc t ts = (h, us) \<Longrightarrow> t \<degree>\<degree> ts = h \<degree>\<degree> us"
  by (induction t ts rule: strip_comb_acc.induct) simp_all

lemma strip_comb_apps: "strip_comb t = (h, ts) \<Longrightarrow> t = h \<degree>\<degree> ts"
  using strip_comb_acc_apps[of t "[]" h ts] by (simp add: strip_comb_def)

lemma ap_Var_cong: "tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow> ap \<rho> \<sigma> (app (Var x T) is) = ap \<rho> \<sigma> (app (Var x U) is)"
  and inst_Var_cong: "tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow> inst \<rho> (app (Var x T) is) = inst \<rho> (app (Var x U) is)"
  by (simp_all add: app_apps ap_apps inst_apps)

lemma typing_appE:
  assumes "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T"
  obtains "tsubst \<rho> Fty = map e is \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)" "\<forall>i\<in>set is. 0 \<le> i"
proof -
  from assms have "e \<turnstile> Var F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is : T"
    by (simp add: app_apps inst_apps comp_def)
  then obtain Us where F: "e \<turnstile> Var F (tsubst \<rho> Fty) : Us \<Rrightarrow> T" and "e \<tturnstile> map Bound is : Us"
    by (rule list_app_typeE)
  from typings_BoundsD[OF this(2)] have "Us = map e is" "\<forall>i\<in>set is. 0 \<le> i" by simp_all
  moreover from F have "tsubst \<rho> Fty = Us \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)" by auto
  ultimately show ?thesis using that by simp
qed

lemma ints_of'_sound:
  assumes "ok (ints_of' env ts) is" "solution \<rho> \<sigma> env" "wt_env \<rho> env" "e \<tturnstile> map (inst \<rho>) ts : Ts"
  shows "distinct is" "Ts = map e is" "\<forall>i\<in>set is. 0 \<le> i" "list_all2 (\<lambda>t i. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bound i) ts is"
proof -
  from assms(1) obtain ts' where hn: "list_all2 (\<lambda>t t'. ok (head_norm env t) t') ts ts'"
    and ints: "ok (ints_of ts') is"
    by (auto simp: ints_of'_def ok_mapM)
  from ints have ts': "ts' = map Bound is" "distinct is" by (simp_all add: ok_ints_of)
  then show "distinct is" by simp
  have "e \<tturnstile> map (inst \<rho>) us' : Us \<and> list_all2 (\<lambda>t t'. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t') us us'"
    if "list_all2 (\<lambda>t t'. ok (head_norm env t) t') us us'" "e \<tturnstile> map (inst \<rho>) us : Us" for us us' Us
    using that
  proof (induction arbitrary: Us rule: list_all2_induct)
    case (Cons u us u' us')
    then obtain U Us' where Us: "Us = U # Us'" "e \<turnstile> inst \<rho> u : U" "e \<tturnstile> map (inst \<rho>) us : Us'"
      by (cases Us) auto
    from head_norm_sound[OF Cons.hyps(1) refl assms(2,3) Us(2)] Cons.IH[OF Us(3)] Us(1)
    show ?case by simp
  qed simp
  from this[OF hn assms(4)] ts'(1)
  have "e \<tturnstile> map Bound is : Ts" and c: "list_all2 (\<lambda>t i. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bound i) ts is"
    by (simp_all add: comp_def list_all2_map2)
  with typings_BoundsD show "Ts = map e is" "\<forall>i\<in>set is. 0 \<le> i" by blast+
  show "list_all2 (\<lambda>t i. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bound i) ts is" by (rule c)
qed

text \<open>A flex term whose arguments head-normalize to distinct bound variables:\<close>

lemma flex_sound:
  assumes "ok (ints_of' env ss) is" "solution \<rho> \<sigma> env" "wt_env \<rho> env"
    and ty: "e \<turnstile> inst \<rho> (Var F Fty \<degree>\<degree> ss) : T"
  shows "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)"
    "distinct is"
proof -
  from ty have "e \<turnstile> Var F (tsubst \<rho> Fty) \<degree>\<degree> map (inst \<rho>) ss : T" by (simp add: inst_apps)
  then obtain Us where F: "e \<turnstile> Var F (tsubst \<rho> Fty) : Us \<Rrightarrow> T" and ss: "e \<tturnstile> map (inst \<rho>) ss : Us"
    by (rule list_app_typeE)
  note i = ints_of'_sound[OF assms(1-3) ss]
  show ty': "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T"
    using F i(2,3) by (auto simp: app_apps inst_apps comp_def intro!: list_app_typeI typings_Bounds)
  show "distinct is" by (rule i(1))
  have \<sigma>: "wt_subst \<sigma>" using solutionD(3)[OF assms(2)] .
  show "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) is)"
    using conv_apps[of "map (ap \<rho> \<sigma>) ss" "map Bound is" "\<sigma> F (tsubst \<rho> Fty)" "\<sigma> F (tsubst \<rho> Fty)"]
      i(4) wt_ap[OF ty \<sigma>] wt_ap[OF ty' \<sigma>]
    by (simp add: ap_apps app_apps comp_def list_all2_map1 list_all2_map2)
qed


subsection \<open>Sound steps\<close>

text \<open>
  A step from \<open>env\<close> to \<open>env'\<close> on the problem \<open>s =?= t\<close> under the binders \<open>bs\<close> is sound if
  \<open>env'\<close> extends \<open>env\<close> and every solution of an extension of \<open>env'\<close> unifies the problem
  (if it is well-typed and consistent, and its loose bound variables are bound by \<open>bs\<close>), keeping
  the environment well-typed and consistent.
\<close>

definition step_ok :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "step_ok env bs s t env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> \<sigma> env'' e T X. solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> s : T \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow> vinv \<rho> env (X \<union> vars s \<union> vars t) \<longrightarrow>
      \<not> loose_bvar s (ilength bs) \<longrightarrow> \<not> loose_bvar t (ilength bs) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"

lemma step_ok_sym:
  assumes "step_ok env bs s t env'"
  shows "step_ok env bs t s env'"
proof -
  have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s"
    if a: "solution \<rho> \<sigma> env''" "extends env' env''" "wt_env \<rho> env" "bs_env \<rho> e bs"
      "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> s : T" "vinv \<rho> env (X \<union> vars t \<union> vars s)"
      "\<not> loose_bvar t (ilength bs)" "\<not> loose_bvar s (ilength bs)"
    for \<rho> \<sigma> env'' e T X
  proof -
    have "X \<union> vars t \<union> vars s = X \<union> vars s \<union> vars t" by blast
    with a assms have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
      unfolding step_ok_def by auto
    then show ?thesis using conv_sym by blast
  qed
  with assms show ?thesis unfolding step_ok_def by blast
qed


subsection \<open>New bindings\<close>

lemma extends_lookup: "extends env env' \<Longrightarrow> vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env') x = Some b"
  unfolding extends_def by blast

lemma bind_sound:
  assumes u: "ok (mkabs bs xs (app (Var H Hty) ks)) u" and upd: "ok (update (F, Fty) u env) env'"
    and sol: "solution \<rho> \<sigma> env''" and ext: "extends env' env''"
    and wte: "wt_env \<rho> env" and bs: "bs_env \<rho> e bs"
    and ty: "e \<turnstile> inst \<rho> (app (Var F Fty) xs) : T"
    and H: "tsubst \<rho> Hty = map (\<lambda>k. rev (map e xs) ! nat_of_integer k) ks \<Rrightarrow> T"
    and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs"
  shows "wt_env \<rho> env'"
    and "e' \<turnstile> inst \<rho> (app (Var F Fty) ys) : T' \<Longrightarrow> length ys = length xs \<Longrightarrow>
      ap \<rho> \<sigma> (app (Var F Fty) ys) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> H (tsubst \<rho> Hty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev ys) k)) ks"
proof -
  from ty obtain F: "tsubst \<rho> Fty = map e xs \<Rrightarrow> T" "cert_typ alg ar (tsubst \<rho> Fty)"
    by (rule typing_appE)
  have tu: "e' \<turnstile> inst \<rho> u : tsubst \<rho> Fty" for e'
    by (rule new_binding_typing[OF u bs F(1,2) refl H ks])
  from u have u': "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app (Var H Hty) ks)"
    by (simp add: ok_mkabs)
  have "closed u" using ks by (force simp: u' app_apps loose_bvar_apps intro!: closed_abs_list)
  then show "wt_env \<rho> env'" using tu by (rule wt_env_update[OF upd wte])
  have lk: "vt_lookup (tenv env'') F = Some (Fty, u)"
    using ok_update(2)[OF upd] by (intro extends_lookup[OF ext]) simp
  assume "e' \<turnstile> inst \<rho> (app (Var F Fty) ys) : T'" "length ys = length xs"
  then show "ap \<rho> \<sigma> (app (Var F Fty) ys) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> H (tsubst \<rho> Hty) \<degree>\<degree> map (\<lambda>k. Bound (bren (rev ys) k)) ks"
    by (intro binding_app[OF sol lk u' tu]) (use ks in auto)
qed

lemma vinv_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> vinv \<rho> env (X \<union> insert (F, T) (vars t)) \<Longrightarrow> vinv \<rho> env' X"
  by (simp add: vinv_def evars_update ok_update(4) Un_assoc insert_commute)

lemma vars_app [simp]: "vars (app s is) = vars s"
  by (simp add: app_apps vars_apps)

lemma extends_solution: "solution \<rho> \<sigma> env' \<Longrightarrow> extends env env' \<Longrightarrow> solution \<rho> \<sigma> env"
  by (rule solution_extends)


subsection \<open>Flex-flex problems with the same head\<close>

lemma bren_rev: "0 \<le> k \<Longrightarrow> k < ilength xs \<Longrightarrow> bren (rev xs) k = rev xs ! nat_of_integer k"
  using bren_nth[of k "rev xs"] by simp

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
      then show ?thesis by (intro exI[of _ "Suc p"]) (simp add: integer_reps)
    qed
  qed
qed auto

lemma ok_mk_ff_list:
  assumes "ok (mk_ff_list is js) ks"
  shows "length is = length js"
    and "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength is \<and> bren (rev is) k = bren (rev js) k"
proof -
  from ok_mk_ff_list_aux[of "is" js "ilength is - 1" ks] assms
  have len: "length is = length js"
    and ks: "\<forall>k'\<in>set ks. \<exists>p<length is. k' = ilength is - 1 - integer_of_nat p \<and> is ! p = js ! p"
    by (auto simp: mk_ff_list_def)
  then show "length is = length js" by simp
  show "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength is \<and> bren (rev is) k = bren (rev js) k"
  proof
    fix k assume "k \<in> set ks"
    with ks obtain p where p: "p < length is" "k = ilength is - 1 - integer_of_nat p" "is ! p = js ! p"
      by blast
    then have k: "0 \<le> k" "k < ilength is" by (simp_all add: ilength_eq integer_reps)
    have "ilength js = ilength is" using len by (simp add: ilength_eq)
    with p k len rev_nth_ilength[of p "is"] rev_nth_ilength[of p js]
    show "0 \<le> k \<and> k < ilength is \<and> bren (rev is) k = bren (rev js) k"
      by (simp add: bren_rev)
  qed
qed

lemma tsol_extends: "solution \<rho> \<sigma> env' \<Longrightarrow> extends env env' \<Longrightarrow> tsol (tyenv env) \<rho>"
  using solutionD(2) solution_extends by blast

lemma vinv_FG: "vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)}) \<Longrightarrow> tsubst \<rho> Fty = tsubst \<rho> Gty"
  unfolding vinv_def by (rule vconsD[of _ _ F]) auto

lemma flexflex1_sound:
  assumes ff: "ok (flexflex1 env bs F Fty is js) env'"
  shows "extends env env'"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<Longrightarrow> e \<turnstile> inst \<rho> (app (Var F Gty) js) : T \<Longrightarrow>
      vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)}) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js)"
proof -
  have "extends env env' \<and> (solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
    bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<longrightarrow> e \<turnstile> inst \<rho> (app (Var F Gty) js) : T \<longrightarrow>
    vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)}) \<longrightarrow>
    wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js))"
  proof (cases "is = js")
    case True
    with ff have env': "env' = env" by (simp add: flexflex1_def)
    have "ap \<rho> \<sigma> (app (Var F Fty) is) = ap \<rho> \<sigma> (app (Var F Gty) js)"
      if "vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)})"
      using True ap_Var_cong[OF vinv_FG[OF that], of \<sigma> F js] by simp
    then show ?thesis using env' vinv_mono[of \<rho> env _ X] by auto
  next
    case False
    with ff obtain ks where ks: "ok (mk_ff_list is js) ks"
      and hnf: "ok (mk_new_hnf env bs is F Fty ks) env'"
      by (auto simp: flexflex1_def)
    from hnf obtain Gty' where Gty': "ok (type_of_G env Fty (ilength is) ks) Gty'"
      and rest: "ok (let (env1, G) = genvar (fst F) env Gty' in
        mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, Fty) t env1)) env'"
      by (auto simp: mk_new_hnf_def)
    obtain env1 G where G: "genvar (fst F) env Gty' = (env1, G)" by force
    with rest obtain u where u: "ok (mkabs bs is (app G ks)) u" and upd: "ok (update (F, Fty) u env1) env'"
      by (auto simp: mk_hnf_def)
    note g = genvar_simps[OF G]
    have ext: "extends env env'" using extends_trans[OF extends_genvar[OF G] extends_update[OF upd]] .
    moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js)"
      if sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
        and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T"
        and tyG: "e \<turnstile> inst \<rho> (app (Var F Gty) js) : T" and vi: "vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)})"
    proof -
      have FG: "tsubst \<rho> Fty = tsubst \<rho> Gty" by (rule vinv_FG[OF vi])
      have tyG': "e \<turnstile> inst \<rho> (app (Var F Fty) js) : T" using tyG inst_Var_cong[OF FG, of F js] by simp
      from tyF obtain Fty_eq: "tsubst \<rho> Fty = map e is \<Rrightarrow> T" by (rule typing_appE)
      have tsol: "tsol (tyenv env) \<rho>" using tsol_extends[OF sol extends_trans[OF ext ext']] .
      note tG = type_of_G_sound[OF Gty' tsol Fty_eq ilength_map]
      note b = bind_sound[OF u[unfolded g(4)] upd sol ext' _ bs tyF tG(1) tG(2)[simplified]]
      have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF G])
      have len: "length js = length is" using ok_mk_ff_list(1)[OF ks] by simp
      have "map (\<lambda>k. Bound (bren (rev is) k)) ks = map (\<lambda>k. Bound (bren (rev js) k)) ks"
        using ok_mk_ff_list(2)[OF ks] by simp
      then have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) js)"
        using b(2)[OF wte1 tyF refl] b(2)[OF wte1 tyG' len] by (metis conv_sym conv_trans)
      then have c: "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js)"
        using ap_Var_cong[OF FG] by simp
      have "vinv \<rho> env1 (vars G \<union> (X \<union> {(F, Fty), (F, Gty)}))" by (rule vinv_genvar[OF G vi])
      then have "vinv \<rho> env1 (X \<union> insert (F, Fty) (vars u))"
        using u by (auto simp: ok_mkabs elim!: vinv_mono)
      from vinv_update[OF upd this] b(1)[OF wte1] c show ?thesis by blast
    qed
    ultimately show ?thesis by blast
  qed
  then show "extends env env'"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<Longrightarrow> e \<turnstile> inst \<rho> (app (Var F Gty) js) : T \<Longrightarrow>
      vinv \<rho> env (X \<union> {(F, Fty), (F, Gty)}) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Gty) js)"
    by blast+
qed


subsection \<open>Flex-flex problems with different heads\<close>

lemma ok_idx: "ok (idx xs j) k \<Longrightarrow> 0 \<le> k \<and> k < ilength xs \<and> bren (rev xs) k = j"
proof (induction xs)
  case (Cons i xs)
  show ?case
  proof (cases "i = j")
    case True
    with Cons.prems have "k = ilength xs" by simp
    with True show ?thesis
      using bren_rev[of k "i # xs"] by (simp add: nth_append ilength_eq integer_reps)
  next
    case False
    with Cons have k: "0 \<le> k" "k < ilength xs" "bren (rev xs) k = j" by simp_all
    then have "nat_of_integer k < length xs" by (simp add: nat_of_integer_less_ilength)
    with k bren_rev[of k "i # xs"] bren_rev[of k xs] show ?thesis
      by (simp add: nth_append integer_arith)
  qed
qed simp

lemma ok_mapM_idx:
  "ok (mapM (idx xs) ys) ks \<Longrightarrow> (\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs) \<and> map (bren (rev xs)) ks = ys"
proof (induction ys arbitrary: ks)
  case (Cons y ys)
  then obtain k ks' where "ks = k # ks'" "ok (idx xs y) k" "ok (mapM (idx xs) ys) ks'" by auto
  with Cons.IH ok_idx[of xs y k] show ?case by auto
qed simp

lemma rev_map_bren:
  "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs \<Longrightarrow>
    map (\<lambda>k. rev (map e xs) ! nat_of_integer k) ks = map (e \<circ> bren (rev xs)) ks"
  by (auto simp: bren_rev rev_map nat_of_integer_less_ilength)

lemma map_bren_Bound: "map (bren (rev xs)) ks = ys \<Longrightarrow> map (\<lambda>k. Bound (bren (rev xs) k)) ks = map Bound ys"
  by (auto simp: comp_def)

lemma map_bren_types:
  assumes "map (bren (rev xs)) ks = ys" "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs"
  shows "map (\<lambda>k. rev (map e xs) ! nat_of_integer k) ks = map e ys"
proof -
  have "map (\<lambda>k. rev (map e xs) ! nat_of_integer k) ks = map (e \<circ> bren (rev xs)) ks"
    by (rule rev_map_bren[OF assms(2)])
  then show ?thesis by (simp add: assms(1)[symmetric])
qed

lemma vinv_absorb: "Y \<subseteq> evars env \<Longrightarrow> vinv \<rho> env (X \<union> Y) \<longleftrightarrow> vinv \<rho> env X"
proof -
  assume "Y \<subseteq> evars env"
  then have "X \<union> Y \<union> evars env = X \<union> evars env" by blast
  then show ?thesis by (simp add: vinv_def)
qed

lemma ff_sound:
  assumes ff: "ok (ff env bs F Fty is G Gty js) env'"
  shows "extends env env'"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<Longrightarrow> e \<turnstile> inst \<rho> (app (Var G Gty) js) : T \<Longrightarrow>
      vinv \<rho> env (X \<union> {(F, Fty), (G, Gty)}) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
proof -
  have "extends env env' \<and> (solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
    bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<longrightarrow> e \<turnstile> inst \<rho> (app (Var G Gty) js) : T \<longrightarrow>
    vinv \<rho> env (X \<union> {(F, Fty), (G, Gty)}) \<longrightarrow>
    wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js))"
  proof (cases "subset js is")
    case True
    with ff obtain ks u where ks: "ok (mapM (idx is) js) ks"
      and u: "ok (mkabs bs is (app (Var G Gty) ks)) u" and upd: "ok (update (F, Fty) u env) env'"
      by (auto simp: ff_def)
    note ks' = ok_mapM_idx[OF ks]
    have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
      if sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
        and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T"
        and tyG: "e \<turnstile> inst \<rho> (app (Var G Gty) js) : T" and vi: "vinv \<rho> env (X \<union> {(F, Fty), (G, Gty)})"
    proof -
      from tyG obtain Gty_eq: "tsubst \<rho> Gty = map e js \<Rrightarrow> T" by (rule typing_appE)
      have H: "tsubst \<rho> Gty = map (\<lambda>k. rev (map e is) ! nat_of_integer k) ks \<Rrightarrow> T"
        using Gty_eq map_bren_types[OF conjunct2[OF ks'] conjunct1[OF ks'], where e = e] by simp
      note b = bind_sound[OF u upd sol ext' wte bs tyF H conjunct1[OF ks']]
      have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
        using b(2)[OF tyF refl] map_bren_Bound[OF conjunct2[OF ks']] by (simp add: app_apps ap_apps comp_def)
      moreover have "vinv \<rho> env (X \<union> insert (F, Fty) (vars u))"
        using vi u by (auto simp: ok_mkabs insert_commute)
      ultimately show ?thesis using vinv_update[OF upd] b(1) by blast
    qed
    then show ?thesis using extends_update[OF upd] by blast
  next
    case False
    let ?ks = "inter js is"
    from False ff obtain ksF Hty where
      ksF: "ok (mapM (idx is) ?ks) ksF" and Hty: "ok (type_of_G env Fty (ilength is) ksF) Hty"
      and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs bs js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs bs is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain ksG tG tF env2 where ksG: "ok (mapM (idx js) ?ks) ksG"
      and tG: "ok (mkabs bs js (app H ksG)) tG"
      and tF: "ok (mkabs bs is (app H ksF)) tF"
      and upd1: "ok (update (F, Fty) tF env1) env2" and upd2: "ok (update (G, Gty) tG env2) env'"
      using ksF by auto
    note g = genvar_simps[OF H]
    note ksF' = ok_mapM_idx[OF ksF] and ksG' = ok_mapM_idx[OF ksG]
    have ext: "extends env env'"
      using extends_trans[OF extends_trans[OF extends_genvar[OF H] extends_update[OF upd1]]
          extends_update[OF upd2]] .
    moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
        ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
      if sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
        and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T"
        and tyG: "e \<turnstile> inst \<rho> (app (Var G Gty) js) : T" and vi: "vinv \<rho> env (X \<union> {(F, Fty), (G, Gty)})"
    proof -
      from tyF obtain Fty_eq: "tsubst \<rho> Fty = map e is \<Rrightarrow> T" by (rule typing_appE)
      have tsol: "tsol (tyenv env) \<rho>" using tsol_extends[OF sol extends_trans[OF ext ext']] .
      note tH = type_of_G_sound[OF Hty tsol Fty_eq ilength_map]
      have HG: "tsubst \<rho> Hty = map (\<lambda>k. rev (map e js) ! nat_of_integer k) ksG \<Rrightarrow> T"
        using tH(1) map_bren_types[OF conjunct2[OF ksF'] conjunct1[OF ksF'], where e = e]
          map_bren_types[OF conjunct2[OF ksG'] conjunct1[OF ksG'], where e = e] by simp
      have ext2: "extends env2 env''" using extends_trans[OF extends_update[OF upd2] ext'] .
      have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF H])
      note bF = bind_sound[OF tF[unfolded g(4)] upd1 sol ext2 wte1 bs tyF tH(1) tH(2)[simplified]]
      note bG = bind_sound[OF tG[unfolded g(4)] upd2 sol ext' bF(1) bs tyG HG conjunct1[OF ksG']]
      have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (fst G, maxidx env + 1) (tsubst \<rho> Hty) \<degree>\<degree> map Bound ?ks"
        using bF(2)[OF tyF refl] map_bren_Bound[OF conjunct2[OF ksF']] by simp
      moreover have "ap \<rho> \<sigma> (app (Var G Gty) js) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (fst G, maxidx env + 1) (tsubst \<rho> Hty) \<degree>\<degree> map Bound ?ks"
        using bG(2)[OF tyG refl] map_bren_Bound[OF conjunct2[OF ksG']] by simp
      ultimately have c: "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
        by (metis conv_sym conv_trans)
      have "vinv \<rho> env1 (vars H \<union> (X \<union> {(F, Fty), (G, Gty)}))" by (rule vinv_genvar[OF H vi])
      then have "vinv \<rho> env1 ((X \<union> {(G, Gty)}) \<union> insert (F, Fty) (vars tF))"
        using tF by (auto simp: ok_mkabs elim!: vinv_mono)
      from vinv_update[OF upd1 this] have v2: "vinv \<rho> env2 (X \<union> {(G, Gty)})" .
      have "vars tG \<subseteq> evars env2"
        using tF tG evars_update[OF upd1] by (auto simp: ok_mkabs)
      with v2 have "vinv \<rho> env2 (X \<union> insert (G, Gty) (vars tG))"
        using vinv_absorb[of "vars tG" env2 \<rho> "X \<union> {(G, Gty)}"] by (simp add: Un_assoc)
      from vinv_update[OF upd2 this] bG(1) c show ?thesis by blast
    qed
    ultimately show ?thesis by blast
  qed
  then show "extends env env'"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> (app (Var F Fty) is) : T \<Longrightarrow> e \<turnstile> inst \<rho> (app (Var G Gty) js) : T \<Longrightarrow>
      vinv \<rho> env (X \<union> {(F, Fty), (G, Gty)}) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var G Gty) js)"
    by blast+
qed

lemma ff_step:
  "ok (ff env bs F Fty is G Gty js) env' \<Longrightarrow> step_ok env bs (app (Var F Fty) is) (app (Var G Gty) js) env'"
  unfolding step_ok_def using ff_sound[of env bs F Fty "is" G Gty js env'] by (simp add: insert_commute)

lemma flexflex2_step:
  "ok (flexflex2 env bs F Fty is G Gty js) env' \<Longrightarrow>
    step_ok env bs (app (Var F Fty) is) (app (Var G Gty) js) env'"
  by (cases "indexname_less G F") (auto simp: flexflex2_def intro: ff_step step_ok_sym)

lemma flexflex1_step:
  "ok (flexflex1 env bs F Fty is js) env' \<Longrightarrow> step_ok env bs (app (Var F Fty) is) (app (Var F Gty) js) env'"
  unfolding step_ok_def using flexflex1_sound[of env bs F Fty "is" js env'] by (simp add: insert_commute)

end

end
