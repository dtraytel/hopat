section \<open>Soundness of Pattern Unification\<close>

theory Pattern_Sound
  imports Pattern_Proj
begin

context pure_sig
begin

subsection \<open>Head normalization keeps the loose bound variables\<close>

lemma head_norm_loose:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar t' k"
  using assms
proof (induction env t r arbitrary: t' k rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and wte = "1.prems"(2) and k = "1.prems"(3)
    and lb = "1.prems"(4)
  have IH: "\<not> loose_bvar u' k'" if "ok (hn env u) u'" "0 \<le> k'" "\<not> loose_bvar u k'" for u u' k'
    using "1.IH"[OF that(1) refl wte that(2,3)] .
  have redex: "\<not> loose_bvar t' k"
    if "ok (hn env (subst_bound u body)) t'" "\<not> loose_bvar (Abs b U0 body $ u) k" for b U0 body u
  proof -
    from that(2) k have "\<not> loose_bvar (body[u/0]) k" by (intro loose_bvar_subst) simp_all
    with IH[OF that(1)[unfolded subst_bound_subst] k] show ?thesis by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with lr obtain U where "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      with wte k have "\<not> loose_bvar u k" by (simp add: wt_env_closed closed_loose_bvar)
      with IH[of u t' k] rest Some k show ?thesis by simp
    qed (use rest lb in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (hn env body) body'" "t' = Abs a T body'" by auto
    with IH[of body body' "k + 1"] lb k Abs show ?thesis by (simp add: integer_arith)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (hn env (subst_bound u body)) t'" by simp
      from redex[OF this] lb App f show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from lb App have lf: "\<not> loose_bvar f k" "\<not> loose_bvar u k" by simp_all
      from IH[OF hf k lf(1)] have nf: "\<not> loose_bvar nf k" .
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this] nf lf(2) Abs show ?thesis by simp
      qed (use rest nf lf in auto)
    qed
  qed (use h lb in auto)
qed

lemma ints_of'_loose:
  assumes "ok (ints_of' env ts) is" "wt_env \<rho> env" "0 \<le> k" "\<forall>t\<in>set ts. \<not> loose_bvar t k"
  shows "\<forall>i\<in>set is. i < k"
proof -
  from assms(1) obtain ts' where hn: "list_all2 (\<lambda>t t'. ok (head_norm env t) t') ts ts'"
    and ints: "ok (ints_of ts') is"
    by (auto simp: ints_of'_def ok_mapM)
  from ints have ts': "ts' = map Bound is" by (simp add: ok_ints_of)
  have "\<forall>t'\<in>set ts'. \<not> loose_bvar t' k"
    using hn assms(4) head_norm_loose[OF _ refl assms(2,3)]
    by (induction rule: list_all2_induct) auto
  with ts' show ?thesis by (auto simp: not_le)
qed


subsection \<open>Composing steps\<close>

lemma step_okI:
  assumes "extends env env'"
    and "\<And>\<rho> \<sigma> env'' e T X. solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow>
      bs_env \<rho> e bs \<Longrightarrow> e \<turnstile> inst \<rho> s : T \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars s \<union> vars t) \<Longrightarrow>
      \<not> loose_bvar s (ilength bs) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "step_ok env bs s t env'"
  using assms unfolding step_ok_def by blast

lemma step_okD:
  assumes "step_ok env bs s t env'"
  shows "extends env env'"
    and "solution \<rho> \<sigma> env'' \<Longrightarrow> extends env' env'' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow>
      bs_env \<rho> e bs \<Longrightarrow> e \<turnstile> inst \<rho> s : T \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow> vinv \<rho> env (X \<union> vars s \<union> vars t) \<Longrightarrow>
      \<not> loose_bvar s (ilength bs) \<Longrightarrow> \<not> loose_bvar t (ilength bs) \<Longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  using assms unfolding step_ok_def by blast+

text \<open>A step on head normal forms is a step on the original problem:\<close>

lemma step_ok_head_norm:
  assumes hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'"
    and st: "step_ok env bs s' t' env'"
  shows "step_ok env bs s t env'"
proof (rule step_okI)
  show ext: "extends env env'" by (rule step_okD(1)[OF st])
  fix \<rho> \<sigma> env'' e T X
  assume sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> s : T" and tyt: "e \<turnstile> inst \<rho> t : T"
    and vi: "vinv \<rho> env (X \<union> vars s \<union> vars t)"
    and lbs: "\<not> loose_bvar s (ilength bs)" and lbt: "\<not> loose_bvar t (ilength bs)"
  have sol0: "solution \<rho> \<sigma> env" using solution_extends[OF sol extends_trans[OF ext ext']] .
  note s1 = head_norm_sound[OF hs refl sol0 wte tys] and t1 = head_norm_sound[OF ht refl sol0 wte tyt]
  have v0: "vinv \<rho> env ((X \<union> vars t) \<union> vars s)" using vi by (simp add: Un_ac)
  have v1: "vinv \<rho> env ((X \<union> vars t) \<union> vars s')"
    by (rule vinv_hn[OF v0]) (use head_norm_vars[OF hs refl] in blast)
  have v1': "vinv \<rho> env ((X \<union> vars s') \<union> vars t)" using v1 by (simp add: Un_ac)
  have "vinv \<rho> env ((X \<union> vars s') \<union> vars t')"
    by (rule vinv_hn[OF v1']) (use head_norm_vars[OF ht refl] in blast)
  moreover have "\<not> loose_bvar s' (ilength bs)" "\<not> loose_bvar t' (ilength bs)"
    using head_norm_loose[OF hs refl wte _ lbs] head_norm_loose[OF ht refl wte _ lbt] by simp_all
  ultimately have r: "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    using step_okD(2)[OF st sol ext' wte bs conjunct1[OF s1] conjunct1[OF t1]] by blast
  then show "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    using s1 t1 by (meson conv_sym conv_trans)
qed

text \<open>A flex term can be replaced by the flex term on the bound variables its arguments reduce to:\<close>

lemma step_ok_flex:
  assumes is_ok: "ok (ints_of' env ss) is" and st: "step_ok env bs (app (Var F Fty) is) t env'"
  shows "step_ok env bs (Var F Fty \<degree>\<degree> ss) t env'"
proof (rule step_okI)
  show ext: "extends env env'" by (rule step_okD(1)[OF st])
  fix \<rho> \<sigma> env'' e T X
  assume sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (Var F Fty \<degree>\<degree> ss) : T" and tyt: "e \<turnstile> inst \<rho> t : T"
    and vi: "vinv \<rho> env (X \<union> vars (Var F Fty \<degree>\<degree> ss) \<union> vars t)"
    and lbs: "\<not> loose_bvar (Var F Fty \<degree>\<degree> ss) (ilength bs)" and lbt: "\<not> loose_bvar t (ilength bs)"
  have sol0: "solution \<rho> \<sigma> env" using solution_extends[OF sol extends_trans[OF ext ext']] .
  note f = flex_sound[OF is_ok sol0 wte tys]
  have "vinv \<rho> env (X \<union> vars (app (Var F Fty) is) \<union> vars t)"
    using vi by (rule vinv_mono) (auto simp: vars_apps)
  moreover have "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    using ints_of'_loose[OF is_ok wte _ ] lbs by (auto simp: app_apps loose_bvar_apps not_le)
  ultimately have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (app (Var F Fty) is) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    using step_okD(2)[OF st sol ext' wte bs f(1) tyt] lbt by blast
  then show "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    using f(2) by (meson conv_trans)
qed


subsection \<open>Unification of the types of binders and constants\<close>

lemma unify_types_sound:
  assumes "ok (unify_types alg T U env) env'"
  shows "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
proof -
  have nh: False if "ok (case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U)) | _ \<Rightarrow> raise e) y"
    for e and y :: env
    using that by (cases e) auto
  have "tenv env' = tenv env \<and> extends env env' \<and>
    (tsol (tyenv env') \<rho> \<longrightarrow> wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"
  proof (cases "T = U")
    case True
    with assms show ?thesis by (simp add: unify_types_def)
  next
    case False
    with assms obtain tye' n' where tu: "ok (type_unify alg U T (tyenv env, maxidx env)) (tye', n')"
      and env': "env' = Envir n' (tenv env) tye'"
      by (auto simp: unify_types_def ok_handle split: prod.splits dest: nh)
    note s = type_unify_sound[OF tu] and c = type_unify_counter[OF tu]
    have "extends env env'" using s(1) c by (simp add: extends_def env')
    with env' s(2)[where \<rho> = \<rho> and ar = ar] show ?thesis by auto
  qed
  then show "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by blast+
qed

lemma wt_env_tenv: "tenv env' = tenv env \<Longrightarrow> wt_env \<rho> env' \<longleftrightarrow> wt_env \<rho> env"
  by (simp add: wt_env_def)

lemma vinv_tenv:
  "tenv env' = tenv env \<Longrightarrow> extends env env' \<Longrightarrow> vinv \<rho> env X \<Longrightarrow> vinv \<rho> env' X"
  unfolding vinv_def extends_def evars_def bnds_def by (auto intro: below_mono)


subsection \<open>\<open>\<eta>\<close>-expansion\<close>

lemma incr_aux_lift: "incr_aux d t = incr_bv 1 d t"
  by (induction d t rule: incr_aux.induct) auto

lemma eta_lift: "Abs a T (lift u 0 $ Bound 0) \<rightarrow>\<^sub>\<eta> u"
proof -
  have "\<not> loose_bvar1 (lift u 0) 0" by simp
  from eta.eta[OF this, of a T u] show ?thesis by simp
qed


subsection \<open>Abstractions\<close>

lemma step_ok_Abs:
  assumes ut: "ok (unify_types alg Ts Tt env) env1" and st: "step_ok env1 ((a, Ts) # bs) ts tt env'"
  shows "step_ok env bs (Abs ns Ts ts) (Abs nt Tt tt) env'"
proof (rule step_okI)
  note u = unify_types_sound[OF ut]
  show ext: "extends env env'" using extends_trans[OF u(2) step_okD(1)[OF st]] .
  fix \<rho> \<sigma> env'' e T X
  assume sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" and tyt: "e \<turnstile> inst \<rho> (Abs nt Tt tt) : T"
    and vi: "vinv \<rho> env (X \<union> vars (Abs ns Ts ts) \<union> vars (Abs nt Tt tt))"
    and lbs: "\<not> loose_bvar (Abs ns Ts ts) (ilength bs)" and lbt: "\<not> loose_bvar (Abs nt Tt tt) (ilength bs)"
  from tys tyt obtain U where TT: "tsubst \<rho> Tt = tsubst \<rho> Ts" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and ts: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U" and tt: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> tt : U"
    by auto
  have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> tt"
  proof (rule step_okD(2)[OF st sol ext'])
    show "wt_env \<rho> env1" using wte by (simp add: wt_env_tenv[OF u(1)])
    show "bs_env \<rho> (e\<langle>0:tsubst \<rho> Ts\<rangle>) ((a, Ts) # bs)" by (rule bs_env_Cons[OF bs c])
    show "vinv \<rho> env1 (X \<union> vars ts \<union> vars tt)" using vinv_tenv[OF u(1,2)] vi by simp
    show "\<not> loose_bvar ts (ilength ((a, Ts) # bs))" "\<not> loose_bvar tt (ilength ((a, Ts) # bs))"
      using lbs lbt by (simp_all add: algebra_simps)
  qed (rule ts, rule tt)
  moreover have "ap \<rho> \<sigma> (Abs ns Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs nt Tt tt)" if "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> tt"
    using conv_Abs[OF _ _ that] wt_ap[OF tys solutionD(3)[OF sol]] wt_ap[OF tyt solutionD(3)[OF sol]] TT
    by simp
  ultimately show "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (Abs ns Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs nt Tt tt)"
    by blast
qed

lemma step_ok_eta:
  assumes st: "step_ok env ((a, Ts) # bs) ts (incr t' $ Bound 0) env'"
  shows "step_ok env bs (Abs a Ts ts) t' env'"
proof (rule step_okI)
  show ext: "extends env env'" by (rule step_okD(1)[OF st])
  fix \<rho> \<sigma> env'' e T X
  assume sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (Abs a Ts ts) : T" and tyt: "e \<turnstile> inst \<rho> t' : T"
    and vi: "vinv \<rho> env (X \<union> vars (Abs a Ts ts) \<union> vars t')"
    and lbs: "\<not> loose_bvar (Abs a Ts ts) (ilength bs)" and lbt: "\<not> loose_bvar t' (ilength bs)"
  note \<sigma> = solutionD(3)[OF sol]
  from tys obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and ts: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U"
    by auto
  have te: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> (incr t' $ Bound 0) : U"
    using tyt T by (auto simp: incr_def incr_aux_lift intro!: lift_type)
  have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (incr t' $ Bound 0)"
  proof (rule step_okD(2)[OF st sol ext' wte bs_env_Cons[OF bs c] ts te])
    show "vinv \<rho> env (X \<union> vars ts \<union> vars (incr t' $ Bound 0))" using vi by (simp add: incr_def)
    show "\<not> loose_bvar ts (ilength ((a, Ts) # bs))" using lbs by (simp add: algebra_simps)
    show "\<not> loose_bvar (incr t' $ Bound 0) (ilength ((a, Ts) # bs))"
      using lbt loose_bvar_lift[of 0 "ilength bs" t'] ilength_nonneg[of bs]
      by (simp add: incr_def incr_aux_lift integer_arith)
  qed
  moreover have "ap \<rho> \<sigma> (Abs a Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    if cv: "ap \<rho> \<sigma> ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (incr t' $ Bound 0)"
  proof -
    have ap_e: "ap \<rho> \<sigma> (incr t') = lift (ap \<rho> \<sigma> t') 0"
      using \<sigma> by (simp add: incr_def incr_aux_lift ap_lift)
    have "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> lift (ap \<rho> \<sigma> t') 0 $ Bound 0 : U"
      using typing_ap[OF te \<sigma>] by (simp add: ap_e)
    from typing.Abs[OF c this]
    have "e \<turnstile> Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0) : tsubst \<rho> Ts \<rightarrow>\<^sub>T U" .
    then have "wt (Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0))" by (auto simp: wt_def)
    then have "ap \<rho> \<sigma> (Abs a Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0)"
      using conv_Abs[OF _ _ cv[simplified, unfolded ap_e]] wt_ap[OF tys \<sigma>] by simp
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
      using \<open>wt (Abs a (tsubst \<rho> Ts) (lift (ap \<rho> \<sigma> t') 0 $ Bound 0))\<close> eta_lift
      by (intro beta_eta_conv) auto
    finally show ?thesis .
  qed
  ultimately show "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (Abs a Ts ts) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    by blast
qed


subsection \<open>Rigid heads\<close>

lemma typing_unique: "e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t : T' \<Longrightarrow> T = T'"
proof (induction arbitrary: T' rule: typing.induct)
  case (App e s T U t)
  from App.prems obtain T0 where "e \<turnstile> s : T0 \<rightarrow>\<^sub>T T'" "e \<turnstile> t : T0" by auto
  with App.IH show ?case by blast
next
  case (Abs T e t U a)
  from Abs.prems obtain U' where "T' = T \<rightarrow>\<^sub>T U'" "e\<langle>0:T\<rangle> \<turnstile> t : U'" by auto
  with Abs.IH show ?case by simp
qed auto

definition steps_ok :: "env \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> env \<Rightarrow> bool" where
  "steps_ok env bs ps env' \<longleftrightarrow> extends env env' \<and>
    (\<forall>\<rho> \<sigma> env'' e X. solution \<rho> \<sigma> env'' \<longrightarrow> extends env' env'' \<longrightarrow> wt_env \<rho> env \<longrightarrow> bs_env \<rho> e bs \<longrightarrow>
      (\<forall>(s, t)\<in>set ps. \<exists>T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T) \<longrightarrow>
      vinv \<rho> env (X \<union> (\<Union>(s, t)\<in>set ps. vars s \<union> vars t)) \<longrightarrow>
      (\<forall>(s, t)\<in>set ps. \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs)) \<longrightarrow>
      wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> (\<forall>(s, t)\<in>set ps. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t))"

lemma foldM_steps_ok:
  assumes "ok (foldM (\<lambda>(s, t) env. f s t env) ps env) env'"
    and "\<And>s t env env'. (s, t) \<in> set ps \<Longrightarrow> ok (f s t env) env' \<Longrightarrow> step_ok env bs s t env'"
  shows "steps_ok env bs ps env'"
  using assms
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (simp add: steps_ok_def)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by (cases p)
  with Cons.prems(1) obtain env1 where f: "ok (f s t env) env1"
    and rest: "ok (foldM (\<lambda>(s, t) env. f s t env) ps env1) env'"
    by auto
  have s1: "step_ok env bs s t env1" using Cons.prems(2)[OF _ f] p by simp
  have s2: "steps_ok env1 bs ps env'" using Cons.IH[OF rest] Cons.prems(2) by simp
  have ext: "extends env env'" using step_okD(1)[OF s1] s2 by (auto simp: steps_ok_def intro: extends_trans)
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> (\<forall>(s, t)\<in>set (p # ps). ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    if sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and ty: "\<forall>(s, t)\<in>set (p # ps). \<exists>T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
      and vi: "vinv \<rho> env (X \<union> (\<Union>(s, t)\<in>set (p # ps). vars s \<union> vars t))"
      and lb: "\<forall>(s, t)\<in>set (p # ps). \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs)"
    for \<rho> \<sigma> env'' e X
  proof -
    let ?Y = "\<Union>(s, t)\<in>set ps. vars s \<union> vars t"
    from ty p obtain T where "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" by auto
    moreover have "vinv \<rho> env ((X \<union> ?Y) \<union> vars s \<union> vars t)" using vi p by (simp add: Un_ac)
    moreover have ext1: "extends env1 env''"
      using s2 ext' by (auto simp: steps_ok_def intro: extends_trans)
    ultimately have r1: "wt_env \<rho> env1 \<and> vinv \<rho> env1 (X \<union> ?Y) \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
      using step_okD(2)[OF s1 sol ext1 wte bs] lb p by auto
    have ty': "\<forall>(s, t)\<in>set ps. \<exists>T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T" using ty by simp
    have lb': "\<forall>(s, t)\<in>set ps. \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs)" using lb by simp
    have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> (\<forall>(s, t)\<in>set ps. ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
      using s2 sol ext' r1 bs ty' lb' unfolding steps_ok_def by blast
    with r1 show ?thesis by (simp add: p)
  qed
  ultimately show ?case unfolding steps_ok_def by blast
qed

lemma typings_nth: "e \<tturnstile> ts : Ts \<Longrightarrow> length ts = length Ts \<and> (\<forall>i<length ts. e \<turnstile> ts ! i : Ts ! i)"
  by (induction ts arbitrary: Ts) (auto split: list.splits simp: nth_Cons')

lemma step_ok_rigid:
  assumes ext1: "extends env env1" and tenv1: "tenv env1 = tenv env"
    and heads: "\<And>\<rho> \<sigma> env'' e U U'. solution \<rho> \<sigma> env'' \<Longrightarrow> extends env1 env'' \<Longrightarrow>
      e \<turnstile> inst \<rho> h : U \<Longrightarrow> e \<turnstile> inst \<rho> h' : U' \<Longrightarrow> inst \<rho> h = inst \<rho> h'"
    and vh: "vars h = {}" "vars h' = {}" and len: "length ss = length ts"
    and st: "steps_ok env1 bs (zip ss ts) env'"
  shows "step_ok env bs (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) env'"
proof (rule step_okI)
  show ext: "extends env env'" using extends_trans[OF ext1] st by (simp add: steps_ok_def)
  fix \<rho> \<sigma> env'' e T X
  assume sol: "solution \<rho> \<sigma> env''" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
    and bs: "bs_env \<rho> e bs" and tys: "e \<turnstile> inst \<rho> (h \<degree>\<degree> ss) : T" and tyt: "e \<turnstile> inst \<rho> (h' \<degree>\<degree> ts) : T"
    and vi: "vinv \<rho> env (X \<union> vars (h \<degree>\<degree> ss) \<union> vars (h' \<degree>\<degree> ts))"
    and lbs: "\<not> loose_bvar (h \<degree>\<degree> ss) (ilength bs)" and lbt: "\<not> loose_bvar (h' \<degree>\<degree> ts) (ilength bs)"
  note \<sigma> = solutionD(3)[OF sol]
  have ext1': "extends env1 env''" using st ext' by (auto simp: steps_ok_def intro: extends_trans)
  from tys obtain Us where th: "e \<turnstile> inst \<rho> h : Us \<Rrightarrow> T" and tss: "e \<tturnstile> map (inst \<rho>) ss : Us"
    by (auto simp: inst_apps elim: list_app_typeE)
  from tyt obtain Us' where th': "e \<turnstile> inst \<rho> h' : Us' \<Rrightarrow> T" and tts: "e \<tturnstile> map (inst \<rho>) ts : Us'"
    by (auto simp: inst_apps elim: list_app_typeE)
  have hh: "inst \<rho> h = inst \<rho> h'" by (rule heads[OF sol ext1' th th'])
  from typings_nth[OF tss] typings_nth[OF tts] len have lens: "length Us = length Us'" by simp
  from typing_unique[OF th th'[folded hh]] funs_eq[OF lens] have UU: "Us = Us'" by simp
  have wte1: "wt_env \<rho> env1" using wte by (simp add: wt_env_tenv[OF tenv1])
  have A: "\<forall>(s, t)\<in>set (zip ss ts). \<exists>T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
    using typings_nth[OF tss] typings_nth[OF tts] UU len by (fastforce simp: set_zip)
  have sub: "X \<union> (\<Union>(s, t)\<in>set (zip ss ts). vars s \<union> vars t) \<subseteq> X \<union> vars (h \<degree>\<degree> ss) \<union> vars (h' \<degree>\<degree> ts)"
    by (auto simp: vars_apps dest: set_zip_leftD set_zip_rightD)
  have B: "vinv \<rho> env1 (X \<union> (\<Union>(s, t)\<in>set (zip ss ts). vars s \<union> vars t))"
    using vinv_mono[OF vinv_tenv[OF tenv1 ext1 vi] sub] .
  have C: "\<forall>(s, t)\<in>set (zip ss ts). \<not> loose_bvar s (ilength bs) \<and> \<not> loose_bvar t (ilength bs)"
    using lbs lbt by (auto simp: loose_bvar_apps dest: set_zip_leftD set_zip_rightD)
  have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> (\<forall>(s, t)\<in>set (zip ss ts). ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    using st sol ext' wte1 bs A B C unfolding steps_ok_def by blast
  moreover have "ap \<rho> \<sigma> (h \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (h' \<degree>\<degree> ts)"
    if "\<forall>(s, t)\<in>set (zip ss ts). ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  proof -
    have "ap \<rho> \<sigma> h = ap \<rho> \<sigma> h'" using hh by (simp add: ap_def)
    moreover have "list_all2 (\<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta>) (map (ap \<rho> \<sigma>) ss) (map (ap \<rho> \<sigma>) ts)"
      using that len by (simp add: list_all2_iff zip_map_map split_def)
    ultimately show ?thesis
      using conv_apps wt_ap[OF tys \<sigma>] wt_ap[OF tyt \<sigma>] by (simp add: ap_apps)
  qed
  ultimately show "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and> ap \<rho> \<sigma> (h \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (h' \<degree>\<degree> ts)"
    by blast
qed

lemma heads_types:
  assumes "ok (unify_types alg Ta Tb env) env1" "solution \<rho> \<sigma> env''" "extends env1 env''"
    "e \<turnstile> inst \<rho> (c Ta) : U" "e \<turnstile> inst \<rho> (c Tb) : U'"
    and c: "c = Const a \<or> c = Free a"
  shows "inst \<rho> (c Ta) = inst \<rho> (c Tb)"
proof -
  from assms(4,5) c have "cert_typ alg ar (tsubst \<rho> Ta)" "cert_typ alg ar (tsubst \<rho> Tb)" by auto
  then have "tsubst \<rho> Ta = tsubst \<rho> Tb"
    using unify_types_sound(3)[OF assms(1) tsol_extends[OF assms(2,3)]] by (simp add: cert_typ_def)
  with c show ?thesis by auto
qed

end

end
