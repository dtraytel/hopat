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

end

end
