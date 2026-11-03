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


subsection \<open>Iteration with a state\<close>

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
  "pr_ok xs s env d bs u env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> \<sigma> env'' e T X. solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> s : T \<longrightarrow> vinv \<rho> env (X \<union> vars s) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> vars u) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T) \<and>
      ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u))"

definition prs_ok :: "integer list \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> integer \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> env \<Rightarrow> bool" where
  "prs_ok xs ss env d bs us env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> \<sigma> env'' e Ts X. solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow>
      bs_env \<rho> e bs \<longrightarrow> e \<tturnstile> map (inst \<rho>) ss : Ts \<longrightarrow> vinv \<rho> env (X \<union> \<Union> (vars ` set ss)) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> \<Union> (vars ` set us)) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us : Ts) \<and>
      list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) ss us)"

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
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' (X \<union> \<Union> (vars ` set us)) \<and>
      (\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us : Ts) \<and>
      list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) (s # ss) us"
    if sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and ty: "e \<tturnstile> map (inst \<rho>) (s # ss) : Ts"
      and vi: "vinv \<rho> env (X \<union> \<Union> (vars ` set (s # ss)))"
    for \<rho> \<sigma> env'' e Ts X
  proof -
    from ty obtain T Ts' where Ts: "Ts = T # Ts'" and ts: "e \<turnstile> inst \<rho> s : T" "e \<tturnstile> map (inst \<rho>) ss : Ts'"
      by (cases Ts) auto
    have ext1: "extends env1 env''"
      using p2 ext' by (auto simp: prs_ok_def intro: extends_trans)
    have "vinv \<rho> env ((X \<union> \<Union> (vars ` set ss)) \<union> vars s)" using vi by (simp add: Un_ac)
    with p1 sol ext1 wte bs ts(1) have r1: "wt_env \<rho> env1"
      "vinv \<rho> env1 ((X \<union> \<Union> (vars ` set ss)) \<union> vars u)"
      "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<turnstile> inst \<rho> u : T"
      "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)"
      unfolding pr_ok_def by blast+
    have "vinv \<rho> env1 ((X \<union> vars u) \<union> \<Union> (vars ` set ss))" using r1(2) by (simp add: Un_ac)
    with p2 sol ext' r1(1) bs ts(2) have r2: "wt_env \<rho> env'"
      "vinv \<rho> env' ((X \<union> vars u) \<union> \<Union> (vars ` set us'))"
      "\<forall>e'. penv e' (map (\<lambda>x. e (x + d)) xs) d e \<tturnstile> map (inst \<rho>) us' : Ts'"
      "list_all2 (\<lambda>s u. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev xs)) d (ap \<rho> \<sigma> u)) ss us'"
      unfolding prs_ok_def by blast+
    from r1 r2 show ?thesis by (simp add: us Ts Un_ac)
  qed
  ultimately show ?case unfolding prs_ok_def by blast
qed

end

end
