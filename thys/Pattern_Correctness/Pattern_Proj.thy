section \<open>Soundness of Projection\<close>

theory Pattern_Proj
  imports Pattern_Flex
begin

text \<open>
  \<^const>\<open>pr\<close> projects the rigid side \<open>s\<close> of a flex-rigid problem \<open>F xs =?= s\<close> onto the bound
  variables \<open>xs\<close>: its result \<open>u\<close>, abstracted over \<open>xs\<close>, becomes the binding of \<open>F\<close>. At depth
  \<open>d\<close> (under \<open>d\<close> abstractions of \<open>s\<close>), renaming the bound variables of \<open>u\<close> back gives \<open>s\<close>.
\<close>

context pure_sig
begin

subsection \<open>Translating bound variables\<close>

lemma bren_ge: "ilength js \<le> k \<Longrightarrow> bren js k = k - ilength js"
proof (induction js arbitrary: k)
  case (Cons j js)
  have "0 \<le> ilength js" by simp
  with Cons.prems have "k \<noteq> 0" "ilength js \<le> k - 1" by (simp_all add: integer_arith)
  with Cons.IH[of "k - 1"] show ?case by (simp add: algebra_simps)
qed simp

lemma ok_trans:
  assumes "ok (trans xs d i) j" "0 \<le> d" "0 \<le> i"
  shows "0 \<le> j" "j < d \<Longrightarrow> j = i"
    "d \<le> j \<Longrightarrow> d \<le> i \<and> j - d < ilength xs \<and> bren (rev xs) (j - d) = i - d"
proof -
  have "0 \<le> j \<and> (j < d \<longrightarrow> j = i) \<and> (d \<le> j \<longrightarrow> d \<le> i \<and> j - d < ilength xs \<and> bren (rev xs) (j - d) = i - d)"
  proof (cases "i < d")
    case True
    with assms show ?thesis by (simp add: trans_def)
  next
    case False
    with assms(1) obtain k where k: "ok (idx xs (i - d)) k" "j = k + d" by (auto simp: trans_def)
    from ok_idx[OF k(1)] have k': "0 \<le> k" "k < ilength xs" "bren (rev xs) k = i - d" by simp_all
    have jd: "j - d = k" using k(2) by simp
    have "0 \<le> j" "\<not> j < d" using k(2) k'(1) assms(2) by simp_all
    moreover have "d \<le> i" using False by simp
    ultimately show ?thesis using k' jd by simp
  qed
  then show "0 \<le> j" "j < d \<Longrightarrow> j = i"
    "d \<le> j \<Longrightarrow> d \<le> i \<and> j - d < ilength xs \<and> bren (rev xs) (j - d) = i - d"
    by simp_all
qed

lemma trans_bound: "ok (trans xs d i) j \<Longrightarrow> j < d + ilength xs"
proof -
  assume j: "ok (trans xs d i) j"
  show "j < d + ilength xs"
  proof (cases "i < d")
    case True
    with j have "j < d" by (simp add: trans_def)
    then show ?thesis using ilength_nonneg[of xs] by (simp add: integer_arith)
  next
    case False
    with j obtain k where "ok (idx xs (i - d)) k" "j = k + d" by (auto simp: trans_def)
    with ok_idx[of xs "i - d" k] show ?thesis by (simp add: integer_arith)
  qed
qed

lemma rename_trans:
  "ok (trans xs d i) j \<Longrightarrow> 0 \<le> d \<Longrightarrow> 0 \<le> i \<Longrightarrow> rename (bren (rev xs)) d (Bound j) = Bound i"
  using ok_trans[of xs d i j] by (cases "j < d") (auto simp: integer_arith)

lemma ok_try_trans: "ok (try_trans xs d i) (Some j) \<Longrightarrow> ok (trans xs d i) j"
  by (auto simp: try_trans_def trans_def ok_handle split: if_splits)


subsection \<open>Projection lists\<close>

lemma mk_proj_list_aux_bren:
  "length zs = length os \<Longrightarrow>
    (\<forall>k\<in>set (mk_proj_list_aux os (ilength zs - 1)). 0 \<le> k \<and> k < ilength zs) \<and>
    map (bren (rev zs)) (mk_proj_list_aux os (ilength zs - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
proof (induction os arbitrary: zs)
  case (Cons opt os)
  then obtain z zs' where zs: "zs = z # zs'" "length zs' = length os" by (cases zs) auto
  have j: "ilength zs - 1 = ilength zs'" by (simp add: zs)
  have hd: "bren (rev zs) (ilength zs') = z"
    using bren_rev[of "ilength zs'" zs] by (simp add: zs nth_append ilength_eq integer_reps)
  have tl: "bren (rev zs) k = bren (rev zs') k" if "0 \<le> k" "k < ilength zs'" for k
    using that bren_rev[of k zs] bren_rev[of k zs'] nat_of_integer_less_ilength[of k zs']
    by (simp add: zs nth_append integer_arith)
  from Cons.IH[OF zs(2)] have ih:
    "\<forall>k\<in>set (mk_proj_list_aux os (ilength zs' - 1)). 0 \<le> k \<and> k < ilength zs'"
    "map (bren (rev zs')) (mk_proj_list_aux os (ilength zs' - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs' os))"
    by simp_all
  have "map (bren (rev zs)) (mk_proj_list_aux os (ilength zs' - 1)) =
      map (bren (rev zs')) (mk_proj_list_aux os (ilength zs' - 1))"
    using ih(1) tl by (auto simp: map_eq_conv)
  with ih hd ilength_nonneg[of zs'] show ?case unfolding j by (auto simp: zs integer_arith)
qed simp

lemma mk_proj_list_bren:
  assumes "length zs = length os"
  shows "\<forall>k\<in>set (mk_proj_list os). 0 \<le> k \<and> k < ilength zs"
    and "map (bren (rev zs)) (mk_proj_list os) = map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
proof -
  have "ilength os = ilength zs" using assms by (simp add: ilength_eq)
  with mk_proj_list_aux_bren[OF assms]
  show "\<forall>k\<in>set (mk_proj_list os). 0 \<le> k \<and> k < ilength zs"
    and "map (bren (rev zs)) (mk_proj_list os) = map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
    by (simp_all add: mk_proj_list_def)
qed

lemma set_map_filter_id: "set (List.map_filter id os) = {l. Some l \<in> set os}"
  by (induction os) (auto simp: List.map_filter_def split: option.splits)

lemma map_filter_id_zip:
  "length zs = length os \<Longrightarrow>
    List.map_filter id os = map (the \<circ> snd) (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
  by (induction zs os rule: list_induct2) (auto simp: List.map_filter_def)


subsection \<open>Environments of the projection\<close>

text \<open>At depth \<open>d\<close>, the bound variables at and above \<open>d\<close> of the projection are those of \<open>xs\<close>:\<close>

definition penv :: "(integer \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> integer \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> ptyp" where
  "penv e' Ts d e j = (if j < d then e j else pushes e' Ts (j - d))"

lemma penv_shift: "0 \<le> d \<Longrightarrow> penv e' Ts (d + 1) (e\<langle>0:T\<rangle>) = (penv e' Ts d e)\<langle>0:T\<rangle>"
  by (rule ext) (simp add: penv_def shift_def integer_arith algebra_simps)

lemma penv_trans:
  assumes "ok (trans xs d i) j" "0 \<le> d" "0 \<le> i"
  shows "penv e' (map (\<lambda>x. e (x + d)) xs) d e j = e i"
proof (cases "j < d")
  case False
  with ok_trans(3)[OF assms] have j: "j - d < ilength xs" "bren (rev xs) (j - d) = i - d"
    by simp_all
  have jd: "0 \<le> j - d" using False by simp
  have "rev xs ! nat_of_integer (j - d) + d = i"
    using j bren_rev[OF jd j(1)] by simp
  with j(1) jd False show ?thesis
    by (simp add: penv_def pushes_nth rev_map nat_of_integer_less_ilength)
qed (use ok_trans(2)[OF assms] in \<open>simp add: penv_def\<close>)

lemma penv_renv:
  assumes "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "penv (\<lambda>k. e (k + d)) (map (\<lambda>x. e (x + d)) xs) d e = renv e (bren (rev xs)) d"
proof (rule ext)
  fix j
  show "penv (\<lambda>k. e (k + d)) (map (\<lambda>x. e (x + d)) xs) d e j = renv e (bren (rev xs)) d j"
  proof (cases "j < d")
    case False
    have jd: "0 \<le> j - d" using False by simp
    show ?thesis
    proof (cases "j - d < ilength xs")
      case True
      with jd False bren_rev[OF jd True] show ?thesis
        by (simp add: penv_def renv_def pushes_nth rev_map nat_of_integer_less_ilength)
    next
      case False
      then have "bren (rev xs) (j - d) = j - d - ilength xs" by (simp add: bren_ge)
      then have "bren (rev xs) (j - d) + d = j - d - ilength xs + d" by simp
      with False jd \<open>\<not> j < d\<close> show ?thesis
        by (simp add: penv_def renv_def pushes_nth)
    qed
  qed (simp add: penv_def renv_def)
qed


subsection \<open>Auxiliary facts\<close>

lemma bs_env_Cons:
  "bs_env \<rho> e bs \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> bs_env \<rho> (e\<langle>0:tsubst \<rho> T\<rangle>) ((a, T) # bs)"
proof -
  assume bs: "bs_env \<rho> e bs" and T: "cert_typ alg ar (tsubst \<rho> T)"
  have "(e\<langle>0:tsubst \<rho> T\<rangle>) i = tsubst \<rho> (snd (((a, T) # bs) ! nat_of_integer i))"
    if "0 \<le> i" "i < ilength ((a, T) # bs)" for i
  proof (cases "i = 0")
    case False
    with that have i: "0 \<le> i - 1" "i - 1 < ilength bs" "nat_of_integer i = Suc (nat_of_integer (i - 1))"
      by (simp_all add: integer_arith nat_of_integer.rep_eq)
    with bs False that show ?thesis by (simp add: bs_env_def integer_arith)
  qed simp
  with bs T show ?thesis by (auto simp: bs_env_def)
qed

lemma vinv_hn:
  assumes "vinv \<rho> env (X \<union> Y)" "Y' \<subseteq> Y \<union> evars env"
  shows "vinv \<rho> env (X \<union> Y')"
proof -
  from assms(1) have c: "vcons \<rho> (X \<union> Y \<union> evars env)" "below (maxidx env) (X \<union> Y \<union> evars env)"
    by (simp_all add: vinv_def)
  have sub: "X \<union> Y' \<union> evars env \<subseteq> X \<union> Y \<union> evars env" using assms(2) by blast
  show ?thesis
    unfolding vinv_def using vcons_mono[OF c(1) sub] below_mono[OF c(2) sub order_refl] by simp
qed

lemma typing_rename_ap:
  assumes "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T" "wt_subst \<sigma>" "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "e \<turnstile> rename (bren (rev xs)) d (ap \<rho> \<sigma> u) : T"
proof -
  have n: "nonneg (bren (rev xs))" using assms(4) by (intro nonneg_bren) simp
  have "renv e (bren (rev xs)) d \<turnstile> inst \<rho> u : T"
    using assms(1)[rule_format, of "\<lambda>k. e (k + d)"] penv_renv[OF assms(3,4)] by simp
  from typing_rename[OF this refl n assms(3)]
  have "e \<turnstile> rename (bren (rev xs)) d (inst \<rho> u) : T" .
  then show ?thesis using assms(2,3)
    by (simp add: ap_def vsubst_rename[symmetric] wt_subst_def typing_vsubst)
qed

lemma conv_beta_eta: "wt s \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  by (rule beta_eta_conv[OF beta_reds_beta_eta_reds])


subsection \<open>Soundness of \<^const>\<open>pr\<close>\<close>

definition pr_ok :: "integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "pr_ok xs s env d bs u env' \<longleftrightarrow> extends env env' \<and> \<not> loose_bvar u (d + ilength xs) \<and>
    (\<forall>\<rho> env'' e T X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> s : T \<longrightarrow> vinv \<rho> env (X \<union> vars s) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars u) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)))"

definition prs_ok :: "integer list \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> bool" where
  "prs_ok xs ss env d bs us env' \<longleftrightarrow> extends env env' \<and> (\<forall>u\<in>set us. \<not> loose_bvar u (d + ilength xs)) \<and>
    (\<forall>\<rho> env'' e Ts X. tsol (tyenv env'') \<rho> \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      bs_env \<rho> e bs \<longrightarrow> e \<tturnstile> map (inst \<rho>) ss : Ts \<longrightarrow> vinv \<rho> env (X \<union> \<Union> (vars ` set ss)) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> \<Union> (vars ` set us)) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us : Ts) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow>
        list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) ss us))"

lemma mapAccM_pr_ok:
  assumes "ok (mapAccM (\<lambda>s env. f xs s env d bs) ss env) (us, env')"
    and "\<And>s env u env'. s \<in> set ss \<Longrightarrow> ok (f xs s env d bs) (u, env') \<Longrightarrow> pr_ok xs s env d bs u env'"
  shows "prs_ok xs ss env d bs us env'"
  using assms
proof (induction ss arbitrary: env us)
  case Nil
  then show ?case by (auto simp: prs_ok_def)
next
  case (Cons s ss)
  from Cons.prems(1) obtain u env1 us' where u: "ok (f xs s env d bs) (u, env1)"
    and us': "ok (mapAccM (\<lambda>s env. f xs s env d bs) ss env1) (us', env')" and us: "us = u # us'"
    by (auto split: prod.splits)
  have p1: "pr_ok xs s env d bs u env1" using Cons.prems(2)[OF _ u] by simp
  have p2: "prs_ok xs ss env1 d bs us' env'" using Cons.IH[OF us'] Cons.prems(2) by simp
  have ext: "extends env env'" using p1 p2 by (auto simp: pr_ok_def prs_ok_def intro: extends_trans)
  moreover have "\<forall>u\<in>set us. \<not> loose_bvar u (d + ilength xs)"
    using p1 p2 by (auto simp: pr_ok_def prs_ok_def us)
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> \<Union> (vars ` set us)) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us : Ts) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow>
        list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) (s # ss) us)"
    if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and ty: "e \<tturnstile> map (inst \<rho>) (s # ss) : Ts"
      and vi: "vinv \<rho> env (X \<union> \<Union> (vars ` set (s # ss)))"
    for \<rho> env'' e Ts X
  proof -
    from ty obtain T Ts' where Ts: "Ts = T # Ts'" and ts: "e \<turnstile> inst \<rho> s : T" "e \<tturnstile> map (inst \<rho>) ss : Ts'"
      by (cases Ts) auto
    have ext1: "extends env1 env''"
      using p2 ext' by (auto simp: prs_ok_def intro: extends_trans)
    have "vinv \<rho> env ((X \<union> \<Union> (vars ` set ss)) \<union> vars s)" using vi by (simp add: Un_ac)
    with p1 tsol'' ext1 wte bs ts(1) have r1: "wt_env \<rho> env1"
      "vinv \<rho> env1 ((X \<union> \<Union> (vars ` set ss)) \<union> vars u)"
      "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T"
      "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)"
      unfolding pr_ok_def by blast+
    have "vinv \<rho> env1 ((X \<union> vars u) \<union> \<Union> (vars ` set ss))" using r1(2) by (simp add: Un_ac)
    with p2 tsol'' ext' r1(1) bs ts(2) have r2: "wt_env \<rho> env'"
      "vinv \<rho> env' ((X \<union> vars u) \<union> \<Union> (vars ` set us'))"
      "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us' : Ts'"
      "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow>
        list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) ss us'"
      unfolding prs_ok_def by blast+
    from r1 r2 show ?thesis by (simp add: us Ts Un_ac)
  qed
  ultimately show ?case unfolding prs_ok_def by blast
qed


text \<open>The body of \<^const>\<open>pr\<close> after head normalization, parametric in the recursive call:\<close>

definition pr_step ::
  "(integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> (pterm \<times> env) M) \<Rightarrow>
    integer list \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> (pterm \<times> env) M" where
  "pr_step prr xs s' env d binders =
    (if is_Abs s' then
      (case s' of
        Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders); return (Abs a T t', env')}
      | _ \<Rightarrow> raise (Failure (STR ''pr'')))
    else
      (let (h, ts) = strip_comb s' in
        if is_Var h then
          (case h of
            Var F Fty \<Rightarrow> do {
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
          return (list_comb h' ts', env')}))"

lemma strip_comb_head: "strip_comb s = (h, ts) \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)"
proof -
  have "strip_comb_acc t us = (h, ts) \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)" for t us
    by (induction t us rule: strip_comb_acc.induct) auto
  then show "strip_comb s = (h, ts) \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)" by (simp add: strip_comb_def)
qed

lemma vars_Abs_free: "\<not> is_Var h \<Longrightarrow> \<not> is_Abs h \<Longrightarrow> strip_comb s = (h, ts) \<Longrightarrow> vars h = {}"
  by (cases h) (auto dest: strip_comb_head)

lemma pr_sound:
  assumes "pr xs s env d bs = Some r"
  shows "r = Ok (u, env') \<Longrightarrow> 0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow> pr_ok xs s env d bs u env'"
  using assms
proof (induction xs s env d bs r arbitrary: u env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  note d = "1.prems"(2) and xs0 = "1.prems"(3)
  have IH: "pr_ok xs s1 env1 d1 bs1 u1 env2"
    if "ok (prr xs s1 env1 d1 bs1) (u1, env2)" "0 \<le> d1" for s1 env1 d1 bs1 u1 env2
    using "1.IH"[OF that(1) refl that(2) xs0] .
  have "ok (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs)) (u, env')"
    using "1.hyps" "1.prems"(1) unfolding pr_step_def by simp
  then obtain s' where hn: "ok (head_norm env s) s'" and body: "ok (pr_step prr xs s' env d bs) (u, env')"
    by auto
  text \<open>Common facts about the head normal form:\<close>
  have hnf: "e \<turnstile> inst \<rho> s' : T \<and> (\<forall>\<sigma>. solution \<rho> \<sigma> env \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> s')"
    if "tsol (tyenv env) \<rho>" "wt_env \<rho> env" "e \<turnstile> inst \<rho> s : T" for \<rho> e T
    using head_norm_sound[OF hn refl that] .
  have vhn: "vinv \<rho> env (X \<union> vars s')" if "vinv \<rho> env (X \<union> vars s)" for \<rho> X
    using vinv_hn[OF that head_norm_vars[OF hn refl]] .
  show ?case
  proof (cases "is_Abs s'")
    case True
    then obtain a T0 t where s': "s' = Abs a T0 t" by (cases s') auto
    with body obtain t' where rec: "ok (prr xs t env (d + 1) ((a, T0) # bs)) (t', env')"
      and u: "u = Abs a T0 t'"
      by (auto simp: pr_step_def)
    have p: "pr_ok xs t env (d + 1) ((a, T0) # bs) t' env'" using IH[OF rec] d by simp
    then have ext: "extends env env'" by (simp add: pr_ok_def)
    moreover from p have "\<not> loose_bvar u (d + ilength xs)" by (simp add: pr_ok_def u algebra_simps)
    moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars u) \<and>
        (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T) \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u))"
      if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
        and bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> s : T" and vi: "vinv \<rho> env (X \<union> vars s)"
      for \<rho> env'' e T X
    proof -
      have tsol0: "tsol (tyenv env) \<rho>" using extends_tsol[OF tsol'' extends_trans[OF ext ext']] .
      note h = hnf[OF tsol0 wte ty]
      from h s' obtain U where T: "T = tsubst \<rho> T0 \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> T0)"
        and tt: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> t : U"
        by auto
      have Ts: "map (\<lambda>x. (e\<langle>0:tsubst \<rho> T0\<rangle>) (x + (d + 1))) xs = map (\<lambda>x. e (x + d)) xs"
        using xs0 d by (auto simp: integer_arith algebra_simps)
      from vhn[OF vi] s' have vi': "vinv \<rho> env (X \<union> vars t)" by simp
      note r0 = p[unfolded pr_ok_def, THEN conjunct2, THEN conjunct2, rule_format, OF tsol'' ext' wte bs_env_Cons[OF bs c] tt vi',
          unfolded Ts]
      from r0 have r: "wt_env \<rho> env'" "vinv \<rho> env' (X \<union> vars t')"
        "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) (d + 1) (e\<langle>0:tsubst \<rho> T0\<rangle>) \<turnstile> inst \<rho> t' : U"
        "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) (d + 1) (ap \<rho> \<sigma> t')"
        by blast+
      have tu: "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T"
        using r(3) c by (auto simp: u T penv_shift[OF d])
      have "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
      proof -
        have sol0: "solution \<rho> \<sigma> env" using solution_extends[OF sol extends_trans[OF ext ext']] .
        have "wt (Abs a (tsubst \<rho> T0) (ap \<rho> \<sigma> t))"
          using wt_ap[OF conjunct1[OF h] solutionD(3)[OF sol]] s' by simp
        moreover have "wt (Abs a (tsubst \<rho> T0) (rename (bren (rev xs)) (d + 1) (ap \<rho> \<sigma> t')))"
          using typing_rename_ap[OF tu solutionD(3)[OF sol] d xs0] by (auto simp: u wt_def)
        ultimately have "ap \<rho> \<sigma> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)"
          using conv_Abs[OF _ _ r(4)[rule_format, OF sol]] by (simp add: s' u)
        with conjunct2[OF h, rule_format, OF sol0] show ?thesis by (rule conv_trans)
      qed
      with r tu show ?thesis by (auto simp: u)
    qed
    ultimately show ?thesis by (simp add: pr_ok_def)
  next
    case nAbs: False
    obtain h ts where hts: "strip_comb s' = (h, ts)" by force
    have s': "s' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = Var F Fty" by (cases h) auto
      from body nAbs hts h obtain js js' Hty where js: "ok (ints_of' env ts) js"
        and js': "ok (mapM (try_trans xs d) js) js'"
        and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
        and rest: "ok (let (env1, H) = genvar (fst F) env Hty in
          mk_hnf bs js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
            (\<lambda>env2. return (app H (List.map_filter id js'), env2)))) (u, env')"
        by (auto simp: pr_step_def Let_def)
      obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
      let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
      from rest G obtain t where t: "ok (mkabs bs js (app H ?ks)) t"
        and upd: "ok (update (F, Fty) t env1) env'" and u: "u = app H ?ls"
        by (auto simp: mk_hnf_def)
      note g = genvar_simps[OF G]
      have ext: "extends env env'" using extends_trans[OF extends_genvar[OF G] extends_update[OF upd]] .
      moreover have "\<not> loose_bvar u (d + ilength xs)"
      proof -
        have "l < d + ilength xs" if "l \<in> set ?ls" for l
        proof -
          from that have "Some l \<in> set js'" by (simp add: set_map_filter_id)
          with js' obtain z where "ok (try_trans xs d z) (Some l)"
            by (auto simp: ok_mapM list_all2_conv_all_nth in_set_conv_nth)
          then show ?thesis by (intro trans_bound ok_try_trans)
        qed
        then show ?thesis by (auto simp: u g(4) app_apps loose_bvar_apps not_le)
      qed
      moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars u) \<and>
          (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T) \<and>
          (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u))"
        if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
          and bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> s : T" and vi: "vinv \<rho> env (X \<union> vars s)"
        for \<rho> env'' e T X
      proof -
        have tsol: "tsol (tyenv env) \<rho>" using extends_tsol[OF tsol'' extends_trans[OF ext ext']] .
        note h' = hnf[OF tsol wte ty]
        note f = flex_sound[OF js tsol wte h'[THEN conjunct1, unfolded s' h]]
        from f(1) obtain Fty_eq: "tsubst \<rho> Fty = map e js \<Rrightarrow> T" and cF: "cert_typ alg ar (tsubst \<rho> Fty)"
          and js0: "\<forall>j\<in>set js. 0 \<le> j"
          by (rule typing_appE)
        note tH = type_of_G_sound[OF Hty tsol Fty_eq ilength_map]
        have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_genvar[OF G])
        note b = bind_sound[OF t[unfolded g(4)] upd wte1 bs f(1) tH(1) tH(2)[simplified]]
        text \<open>The projected arguments:\<close>
        let ?P = "filter (\<lambda>(z, opt). opt \<noteq> None) (zip js js')"
        have l2: "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) js js'" using js' by (simp add: ok_mapM)
        then have len: "length js = length js'" by (rule list_all2_lengthD)
        have P: "ok (trans xs d (fst p)) (the (snd p)) \<and> 0 \<le> fst p" if "p \<in> set ?P" for p
        proof -
          from that obtain z l where p: "p = (z, Some l)" "(z, Some l) \<in> set (zip js js')" by auto
          with l2 have "ok (try_trans xs d z) (Some l)" by (auto simp: list_all2_iff)
          moreover have "z \<in> set js" using p(2) by (rule set_zip_leftD)
          ultimately show ?thesis using p(1) js0 by (simp add: ok_try_trans)
        qed
        note mp = mk_proj_list_bren[OF len] and ls = map_filter_id_zip[OF len]
        have args: "map (\<lambda>k. Bound (bren (rev js) k)) ?ks = map (\<lambda>p. Bound (fst p)) ?P"
          using arg_cong[OF mp(2), of "map Bound"] by (simp add: comp_def)
        have "rename (bren (rev xs)) d (Bound (the (snd p))) = Bound (fst p)" if "p \<in> set ?P" for p
          using P[OF that] rename_trans[OF _ d] by blast
        then have ren: "map (rename (bren (rev xs)) d \<circ> Bound) ?ls = map (\<lambda>p. Bound (fst p)) ?P"
          by (simp add: ls map_eq_conv)
        have "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
        proof -
          have sol0: "solution \<rho> \<sigma> env" using solution_extends[OF sol extends_trans[OF ext ext']] .
          note \<sigma> = solutionD(3)[OF sol]
          have c: "closed (\<sigma> (fst F, maxidx env + 1) (tsubst \<rho> Hty))"
            using \<sigma> by (simp add: wt_subst_def closed_substD)
          have "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (app (Var F Fty) js)"
            using conjunct2[OF h', rule_format, OF sol0] f(2)[OF sol0] by (auto simp: s' h intro: conv_trans)
          also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (fst F, maxidx env + 1) (tsubst \<rho> Hty) \<degree>\<degree> map (\<lambda>p. Bound (fst p)) ?P"
            using b(2)[OF sol ext' f(1) refl] args by simp
          also have "\<dots> = rename (bren (rev xs)) d (ap \<rho> \<sigma> u)"
            using ren c d by (simp add: u g(4) app_apps ap_apps rename_apps rename_closed comp_def)
          finally show ?thesis .
        qed
        moreover have "penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T" for e'
        proof -
          let ?E = "penv e' (map (\<lambda>x. e (x + d)) xs) d e"
          have "?E (the (snd p)) = e (fst p)" if "p \<in> set ?P" for p
            using P[OF that] penv_trans[OF _ d] by blast
          then have Ets: "map ?E ?ls = map (\<lambda>p. e (fst p)) ?P"
            by (simp add: ls map_eq_conv)
          have m1: "map (\<lambda>k. rev (map e js) ! nat_of_integer k) ?ks = map (e \<circ> bren (rev js)) ?ks"
            by (rule rev_map_bren[OF tH(2)[simplified]])
          have m2: "map (e \<circ> bren (rev js)) ?ks = map (\<lambda>p. e (fst p)) ?P"
            using arg_cong[OF mp(2), of "map e"] by (simp add: comp_def)
          have Hty': "tsubst \<rho> Hty = map ?E ?ls \<Rrightarrow> T"
            using tH(1) m1 m2 Ets by simp
          have "\<forall>p\<in>set ?P. fst p \<in> set js" by (auto dest: set_zip_leftD)
          then have "\<forall>U\<in>set (map ?E ?ls). cert_typ alg ar U"
            using cF Fty_eq Ets by (auto simp: cert_typ_funs)
          then have "cert_typ alg ar (tsubst \<rho> Hty)" using cF Fty_eq Hty' by (simp add: cert_typ_funs)
          moreover have "0 \<le> the (snd p)" if "p \<in> set ?P" for p
            using P[OF that] ok_trans(1)[OF _ d] by blast
          then have "?E \<tturnstile> map Bound ?ls : map ?E ?ls"
            by (intro typings_Bounds) (auto simp: ls)
          ultimately show ?thesis
            using Hty' by (auto simp: u g(4) app_apps inst_apps comp_def intro!: list_app_typeI)
        qed
        moreover have "vinv \<rho> env' (X \<union> vars u)"
        proof -
          have "vinv \<rho> env1 (vars H \<union> (X \<union> vars s'))" by (rule vinv_genvar[OF G vhn[OF vi]])
          then have "vinv \<rho> env1 ((X \<union> vars u) \<union> insert (F, Fty) (vars t))"
            using t by (auto simp: u ok_mkabs s' h vars_apps elim!: vinv_mono)
          then show ?thesis by (rule vinv_update[OF upd])
        qed
        ultimately show ?thesis using b(1) by blast
      qed
      ultimately show ?thesis unfolding pr_ok_def by blast
    next
      case nVar: False
      show ?thesis
      proof (cases "is_Abs h")
        case True
        with body nAbs nVar hts show ?thesis by (simp add: pr_step_def)
      next
        case nAbs_h: False
        from body nAbs nVar nAbs_h hts obtain h' ts' where
          h': "ok (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h) h'"
          and m: "ok (mapAccM (\<lambda>s env. prr xs s env d bs) ts env) (ts', env')"
          and u: "u = h' \<degree>\<degree> ts'"
          by (auto simp: pr_step_def list_comb_apps split: prod.splits)
        have ps: "prs_ok xs ts env d bs ts' env'"
          using mapAccM_pr_ok[where f = prr and xs = xs and d = d and bs = bs, OF m] IH d by blast
        then have ext: "extends env env'" by (simp add: prs_ok_def)
        have vh: "vars h = {}" by (rule vars_Abs_free[OF nVar nAbs_h hts])
        have lb: "\<not> loose_bvar u (d + ilength xs)"
        proof -
          have "\<not> loose_bvar h' (d + ilength xs)"
          proof (cases h)
            case (Bound i)
            with h' obtain j where "ok (trans xs d i) j" "h' = Bound j" by auto
            then show ?thesis using trans_bound by (auto simp: not_le)
          qed (use h' nVar nAbs_h strip_comb_head[OF hts] in auto)
          with ps show ?thesis by (auto simp: u prs_ok_def loose_bvar_apps)
        qed
        have "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars u) \<and>
            (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T) \<and>
            (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u))"
          if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
            and bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> s : T" and vi: "vinv \<rho> env (X \<union> vars s)"
          for \<rho> env'' e T X
        proof -
          have tsol: "tsol (tyenv env) \<rho>" using extends_tsol[OF tsol'' extends_trans[OF ext ext']] .
          note hh = hnf[OF tsol wte ty]
          from hh have "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: s' inst_apps)
          then obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us"
            by (rule list_app_typeE)
          have vi': "vinv \<rho> env (X \<union> \<Union> (vars ` set ts))"
            using vhn[OF vi] vh by (simp add: s' vars_apps)
          from ps tsol'' ext' wte bs tts vi' have r: "wt_env \<rho> env'"
            "vinv \<rho> env' (X \<union> \<Union> (vars ` set ts'))"
            "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) ts' : Us"
            "\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow>
              list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) ts ts'"
            unfolding prs_ok_def by blast+
          text \<open>The translated head:\<close>
          have hd: "(\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> h' : Us \<Rrightarrow> T) \<and>
              (\<forall>\<sigma>. rename (bren (rev xs)) d (ap \<rho> \<sigma> h') = ap \<rho> \<sigma> h) \<and> vars h' = {}"
          proof (cases h)
            case (Bound i)
            with h' obtain j where j: "ok (trans xs d i) j" "h' = Bound j" by auto
            from th Bound have i: "0 \<le> i" "e i = Us \<Rrightarrow> T" by auto
            then show ?thesis
              using j penv_trans[OF j(1) d i(1)] rename_trans[OF j(1) d i(1)] ok_trans(1)[OF j(1) d i(1)] Bound
              by auto
          qed (use h' th nVar nAbs_h vh strip_comb_head[OF hts] in auto)
          have tu: "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T"
            using hd r(3) by (auto simp: u inst_apps intro: list_app_typeI)
          have "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
          proof -
            have sol0: "solution \<rho> \<sigma> env" using solution_extends[OF sol extends_trans[OF ext ext']] .
            note \<sigma> = solutionD(3)[OF sol]
            have hd': "rename (bren (rev xs)) d (ap \<rho> \<sigma> h') = ap \<rho> \<sigma> h" using hd by blast
            have "ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> h \<degree>\<degree> map (rename (bren (rev xs)) d \<circ> ap \<rho> \<sigma>) ts'"
            proof (rule conv_apps)
              show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) ts) (map (rename (bren (rev xs)) d \<circ> ap \<rho> \<sigma>) ts')"
                using r(4) sol by (simp add: list_all2_map1 list_all2_map2)
              show "wt (ap \<rho> \<sigma> h \<degree>\<degree> map (ap \<rho> \<sigma>) ts)"
                using wt_ap[OF conjunct1[OF hh] \<sigma>] by (simp add: s' ap_apps)
              show "wt (ap \<rho> \<sigma> h \<degree>\<degree> map (rename (bren (rev xs)) d \<circ> ap \<rho> \<sigma>) ts')"
                using typing_rename_ap[OF tu \<sigma> d xs0] hd'
                by (auto simp: u ap_apps rename_apps comp_def wt_def)
            qed simp
            then have "ap \<rho> \<sigma> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)"
              using hd' by (simp add: s' u ap_apps rename_apps comp_def)
            with conjunct2[OF hh, rule_format, OF sol0] show ?thesis by (rule conv_trans)
          qed
          with r(1,2) tu hd show ?thesis by (auto simp: u vars_apps)
        qed
        with ext lb show ?thesis unfolding pr_ok_def by blast
      qed
    qed
  qed
qed


subsection \<open>Flex-rigid problems\<close>

lemma loose_bvar_inst [simp]: "loose_bvar (inst \<rho> t) k = loose_bvar t k"
  by (induction t arbitrary: k) auto

lemma loose_bvar_vsubst [simp]: "closed_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (vsubst \<sigma> t) k = loose_bvar t k"
proof (induction t arbitrary: k)
  case (Var x T)
  then show ?case by (simp add: closed_substD closed_loose_bvar)
next
  case (Abs a T t)
  then show ?case using Abs.IH[of "k + 1"] by (simp add: integer_arith)
qed auto

lemma rename_id_on:
  "(\<And>k. 0 \<le> k \<Longrightarrow> k < m \<Longrightarrow> f k = k) \<Longrightarrow> \<not> loose_bvar t (d + m) \<Longrightarrow> rename f d t = t"
proof (induction f d t rule: rename.induct)
  case (1 f d i)
  then show ?case by (auto simp: integer_arith)
next
  case (2 f d a T t)
  then show ?case by (simp add: algebra_simps)
qed auto

lemma downto0_bren: "downto0 is n \<Longrightarrow> ilength is = n + 1 \<and> (\<forall>k. 0 \<le> k \<longrightarrow> k \<le> n \<longrightarrow> bren (rev is) k = k)"
proof (induction "is" arbitrary: n)
  case (Cons i "is")
  then have i: "i = n" "ilength is = n" "\<forall>k. 0 \<le> k \<longrightarrow> k \<le> n - 1 \<longrightarrow> bren (rev is) k = k" by auto
  have "bren (rev (i # is)) k = k" if "0 \<le> k" "k \<le> n" for k
  proof (cases "k = n")
    case True
    have ln: "nat_of_integer n = length is" using i(2)[symmetric] by (simp add: ilength_eq)
    have "k < ilength (i # is)" using that i(2) by (simp add: integer_arith)
    with bren_rev[OF that(1) this] True ln i(1) show ?thesis by (simp add: nth_append)
  next
    case False
    have k1: "k < ilength is" "k \<le> n - 1" using False that i(2) by (simp_all add: integer_arith)
    have "k < ilength (i # is)" using k1 by (simp add: integer_arith)
    have "bren (rev (i # is)) k = rev (i # is) ! nat_of_integer k" by (rule bren_rev[OF that(1)]) fact
    also have "\<dots> = rev is ! nat_of_integer k"
      using nat_of_integer_less_ilength[OF that(1) k1(1)] by (simp add: nth_append)
    also have "\<dots> = bren (rev is) k" using bren_rev[OF that(1) k1(1)] by simp
    also have "\<dots> = k" using i(3) that(1) k1(2) by simp
    finally show ?thesis .
  qed
  with i show ?case by simp
qed simp

lemma loose_bvar1_imp: "loose_bvar1 t k \<Longrightarrow> loose_bvar t k"
  by (induction t k rule: loose_bvar1.induct) auto

lemma typing_env_nonneg: "e \<turnstile> t : T \<Longrightarrow> (\<And>i. 0 \<le> i \<Longrightarrow> e' i = e i) \<Longrightarrow> e' \<turnstile> t : T"
  by (erule typing_env_cong) simp

lemma bs_types:
  assumes "bs_env \<rho> e bs" "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
  shows "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)) = map e is"
    and "\<forall>T\<in>snd ` set (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)). cert_typ alg ar T"
proof -
  have nth_in: "bs ! nat_of_integer i \<in> set bs" if "i \<in> set is" for i
    using assms(2) that by (simp add: nat_of_integer_less_ilength)
  show "map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)) = map e is"
    using assms by (auto simp: bs_env_def split: prod.splits)
  show "\<forall>T\<in>snd ` set (map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)). cert_typ alg ar T"
    using assms(1) nth_in by (fastforce simp: bs_env_def split: prod.splits)
qed

text \<open>The result of \<^const>\<open>proj\<close>, abstracted over \<open>is\<close> and applied to \<open>is\<close>, is the rigid side:\<close>

lemma proj_sound:
  assumes pj: "ok (proj t env bs is) (u, env1)" and is0: "\<forall>i\<in>set is. 0 \<le> i"
  shows "extends env env1"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env1 env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars t) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> vars u) \<and> (\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> u : T) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u)) \<and>
      \<not> loose_bvar u (ilength is)"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env1 env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars t) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> vars u) \<and> (\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> u : T) \<and>
      ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u) \<and> \<not> loose_bvar u (ilength is)"
proof -
  have "extends env env1 \<and> (tsol (tyenv env'') \<rho> \<longrightarrow> extends env1 env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> bs_env \<rho> e bs \<longrightarrow>
      e \<turnstile> inst \<rho> t : T \<longrightarrow> vinv \<rho> env (X \<union> vars t) \<longrightarrow> \<not> loose_bvar t (ilength bs) \<longrightarrow>
      wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> vars u) \<and> (\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> u : T) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u)) \<and>
      \<not> loose_bvar u (ilength is))"
  proof (cases "downto0 is (ilength bs - 1)")
    case True
    with pj have u: "u = t" "env1 = env" by (simp_all add: proj_def)
    note dt = downto0_bren[OF True]
    have "(\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> t : T) \<and>
        (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> t))"
      if ty: "e \<turnstile> inst \<rho> t : T" and lb: "\<not> loose_bvar t (ilength bs)"
    proof -
      have id: "bren (rev is) k = k" if "0 \<le> k" "k < ilength bs" for k
        using dt that by (simp add: integer_arith)
      have "pushes e' (map e is) \<turnstile> inst \<rho> t : T" for e'
      proof (rule typing_env_cong[OF ty])
        fix i assume i: "0 \<le> i" "loose_bvar1 (inst \<rho> t) i"
        then have "loose_bvar t i" using loose_bvar1_imp by simp
        with lb have "\<not> ilength bs \<le> i" using loose_bvar_mono[of t i "ilength bs"] by blast
        then have "i < ilength bs" by simp
        moreover from this dt have "i < ilength is" by simp
        ultimately show "pushes e' (map e is) i = e i"
          using i(1) id bren_rev[OF i(1), of "is"] nat_of_integer_less_ilength[OF i(1), of "is"]
          by (simp add: pushes_nth rev_map)
      qed
      moreover have "rename (bren (rev is)) 0 (ap \<rho> \<sigma> t) = ap \<rho> \<sigma> t" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
      proof (rule rename_id_on)
        have "closed_subst \<sigma>" using solutionD(3)[OF sol] by (simp add: wt_subst_def)
        with lb show "\<not> loose_bvar (ap \<rho> \<sigma> t) (0 + ilength bs)" by (simp add: ap_def)
      qed (rule id)
      ultimately show ?thesis by simp
    qed
    with u dt show ?thesis by (auto simp: vinv_def)
  next
    case False
    with pj have "ok (pr is t env 0 bs) (u, env1)" by (simp add: proj_def)
    from pr_sound[OF this refl order_refl is0] have p: "pr_ok is t env 0 bs u env1" .
    have pe: "pushes e' (map e is) \<turnstile> inst \<rho> u : T"
      if "penv e' (map (\<lambda>x. e (x + 0)) is) 0 e \<turnstile> inst \<rho> u : T" for e' e \<rho> T
      using typing_env_nonneg[OF that] by (simp add: penv_def)
    from p show ?thesis unfolding pr_ok_def by (simp, blast intro: pe)
  qed
  then show "extends env env1"
    and "tsol (tyenv env'') \<rho> \<Longrightarrow> extends env1 env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars t) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> vars u) \<and> (\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> u : T) \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u)) \<and>
      \<not> loose_bvar u (ilength is)"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env1 env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
      e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars t) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> vars u) \<and> (\<forall>e'. pushes e' (map e is) \<turnstile> inst \<rho> u : T) \<and>
      ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u) \<and> \<not> loose_bvar u (ilength is)"
    using solutionD(2)[of \<rho> \<sigma> env''] by blast+
qed


lemma flexrigid_step:
  assumes fr: "ok (flexrigid env bs F Fty is t) env'"
  shows "step_ok env bs (app (Var F Fty) is) t env'"
proof -
  have nh: False if "ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e) y" for e y
    using that by (cases e) auto
  have "ok (do {(u, env1) \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env1}) env'"
    using fr by (auto simp: flexrigid_def ok_handle split: if_splits dest: nh)
  then obtain u env1 u' where pj: "ok (proj t env bs is) (u, env1)" and mk: "ok (mkabs bs is u) u'"
    and upd: "ok (update (F, Fty) u' env1) env'"
    by (auto split: prod.splits)
  from mk have is_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    and u': "u' = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) u"
    by (simp_all add: ok_mkabs)
  note ps = proj_sound[OF pj] and is_nonneg = is_ok[THEN bspec, THEN conjunct1]
  have ext: "extends env env'" using extends_trans[OF ps(1) extends_update[OF upd]] is_nonneg by blast
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      (\<forall>\<sigma>. solution \<rho> \<sigma> env'' \<longrightarrow> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" and tyt: "e \<turnstile> inst \<rho> t : T"
      and vi: "vinv \<rho> env (X \<union> vars (app (Var F Fty) is) \<union> vars t)"
      and lbt: "\<not> loose_bvar t (ilength bs)"
    for \<rho> env'' e T X
  proof -
    have ext1: "extends env1 env''" using extends_trans[OF extends_update[OF upd] ext'] .
    have vi': "vinv \<rho> env ((X \<union> {(F, Fty)}) \<union> vars t)" using vi by (simp add: Un_ac)
    have is0: "\<forall>i\<in>set is. 0 \<le> i" using is_ok by blast
    note r = proj_sound(2)[OF pj is0 tsol'' ext1 wte bs tyt vi' lbt]
    from tyF obtain Fty_eq: "tsubst \<rho> Fty = map e is \<Rrightarrow> T" by (rule typing_appE)
    note bt = bs_types[OF bs is_ok]
    let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
    have tu': "e' \<turnstile> inst \<rho> u' : tsubst \<rho> Fty" for e'
    proof -
      from r have "pushes e' (map e is) \<turnstile> inst \<rho> u : T" by blast
      then have "pushes e' (map snd ?bs) \<turnstile> inst \<rho> u : T" by (simp only: bt(1))
      from typing_abs_list[OF this bt(2)] have "e' \<turnstile> abs_list ?bs (inst \<rho> u) : map e is \<Rrightarrow> T"
        by (simp only: bt(1))
      then show ?thesis by (simp only: u' inst_abs_list Fty_eq)
    qed
    have "closed u'" using r by (auto simp: u' intro!: closed_abs_list)
    then have wte': "wt_env \<rho> env'" using wt_env_update[OF upd conjunct1[OF r]] tu' by blast
    have "vinv \<rho> env1 (X \<union> insert (F, Fty) (vars u'))" using r by (simp add: u' Un_ac)
    then have vi'': "vinv \<rho> env' X" by (rule vinv_update[OF upd])
    have "ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if sol: "solution \<rho> \<sigma> env''" for \<sigma>
    proof -
      note s = solutionD[OF sol]
      have lk: "vt_lookup (tenv env'') F = Some (Fty, u')"
        using ok_update(2)[OF upd] by (intro extends_lookup[OF ext']) simp
      have js: "e \<tturnstile> map Bound is : map e is" by (rule typings_Bounds) (use is0 in auto)
      have tu: "e \<turnstile> ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is : T"
        using typing_ap[OF tu' s(3)] Fty_eq js by (auto intro: list_app_typeI)
      have "ap \<rho> \<sigma> (app (Var F Fty) is) = \<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is"
        by (simp add: app_apps ap_apps comp_def)
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is"
      proof (rule conv_apps)
        show "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map Bound is) (map Bound is)" by (simp add: list_all2_refl)
        show "wt (\<sigma> F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is)"
          using wt_ap[OF tyF s(3)] by (simp add: app_apps ap_apps comp_def)
        show "wt (ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is)" using tu by (auto simp: wt_def)
        show "\<sigma> F (tsubst \<rho> Fty) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" by (rule s(4)[OF lk])
      qed
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (ap \<rho> \<sigma> u)"
      proof (rule conv_beta_eta)
        show "wt (ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is)" using tu by (auto simp: wt_def)
        show "ap \<rho> \<sigma> u' \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev is)) 0 (ap \<rho> \<sigma> u)"
          using beta_abs_list_apps[of "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)" "is"] is0
          by (simp add: u' ap_abs_list)
      qed
      also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" using r sol by (blast intro: conv_sym)
      finally show ?thesis .
    qed
    with wte' vi'' show ?thesis by blast
  qed
  ultimately show ?thesis unfolding step_ok_def by blast
qed

lemma ok_trans_inj:
  assumes "ok (trans xs d z1) l" "ok (trans xs d z2) l" "0 \<le> d" "0 \<le> z1" "0 \<le> z2"
  shows "z1 = z2"
proof (cases "l < d")
  case True
  with ok_trans(2)[OF assms(1,3,4)] ok_trans(2)[OF assms(2,3,5)] show ?thesis by simp
next
  case False
  with ok_trans(3)[OF assms(1,3,4)] ok_trans(3)[OF assms(2,3,5)] show ?thesis by simp
qed

lemma map_filter_id_simps:
  "List.map_filter id [] = []"
  "List.map_filter id (None # os) = List.map_filter id os"
  "List.map_filter id (Some l # os) = l # List.map_filter id os"
  by (simp_all add: List.map_filter_def)

lemma try_trans_distinct:
  "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) zs os \<Longrightarrow> distinct zs \<Longrightarrow> \<forall>z\<in>set zs. 0 \<le> z \<Longrightarrow>
    0 \<le> d \<Longrightarrow> distinct (List.map_filter id os) \<and>
    (\<forall>l\<in>set (List.map_filter id os). \<exists>z\<in>set zs. ok (trans xs d z) l)"
  unfolding id_def
proof (induction zs arbitrary: os)
  note mf = map_filter_id_simps[unfolded id_def]
  case Nil
  then show ?case by (simp add: mf)
next
  case (Cons z zs)
  from Cons.prems(1) obtain opt os' where os: "os = opt # os'" "ok (try_trans xs d z) opt"
    "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) zs os'"
    by (cases os) auto
  note mf = map_filter_id_simps[unfolded id_def]
  from Cons.IH[OF os(3)] Cons.prems(2-4) have IH: "distinct (List.map_filter (\<lambda>x. x) os')"
    "\<forall>l\<in>set (List.map_filter (\<lambda>x. x) os'). \<exists>z\<in>set zs. ok (trans xs d z) l" by simp_all
  show ?case
  proof (cases opt)
    case None
    then show ?thesis using IH os by (simp add: mf)
  next
    case (Some l)
    have tl: "ok (trans xs d z) l" using os(2) Some by (simp add: ok_try_trans)
    have "l \<notin> set (List.map_filter (\<lambda>x. x) os')"
    proof
      assume "l \<in> set (List.map_filter (\<lambda>x. x) os')"
      with IH(2) obtain z' where "z' \<in> set zs" "ok (trans xs d z') l" by blast
      with ok_trans_inj[OF tl _ Cons.prems(4)] Cons.prems(2,3) show False by auto
    qed
    with IH tl Some os show ?thesis by (auto simp: mf)
  qed
qed

lemma mk_proj_list_aux_sorted:
  "sorted_wrt (>) (mk_proj_list_aux os j) \<and> (\<forall>k\<in>set (mk_proj_list_aux os j). k \<le> j)"
proof (induction os j rule: mk_proj_list_aux.induct)
  case (1 i "is" j)
  then have IH: "sorted_wrt (>) (mk_proj_list_aux is (j - 1))"
    "\<forall>k\<in>set (mk_proj_list_aux is (j - 1)). k \<le> j - 1" by (cases i; simp)+
  then have "\<forall>k\<in>set (mk_proj_list_aux is (j - 1)). k < j \<and> k \<le> j" by (auto simp: integer_arith)
  with IH show ?case by auto
qed simp


end

end
