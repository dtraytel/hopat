section \<open>Soundness of the Base Operations of \<open>unify.ML\<close>\<close>

theory Unify_Base_Sound
  imports Unify_Semantics "Pattern_Correctness.Match_Lemmas"
begin

context pure_sig_gen
begin

subsection \<open>Type unification\<close>

lemma cunify_types_ok: "okW (cunify_types alg' T U env) env' \<longleftrightarrow> ok (unify_types alg' T U env) env'"
  by (auto simp: cunify_types_def raiseW_def emit_def bindW_def returnW_def
      split: option.splits xres.splits exn.splits)

lemma cunify_types_sound:
  assumes "okW (cunify_types alg' T U env) env'"
  shows "tenv env' = tenv env" "extends env env'"
    and "tsol (tyenv env') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  using unify_types_sound[OF assms[unfolded cunify_types_ok]] by blast+

lemma test_unify_types_ok: "okW (test_unify_types alg' T U env) env' \<longleftrightarrow> okW (cunify_types alg' T U env) env'"
  by (auto simp: test_unify_types_def okW_whenW)

lemmas test_unify_types_sound = cunify_types_sound[folded test_unify_types_ok]

text \<open>An extension that keeps the term environment is a step on any pairs:\<close>

lemma dstep_tenv:
  assumes tenv: "tenv env' = tenv env" and ext: "extends env env'"
  shows "dstep env dps env' dps"
proof (rule dstepI[OF ext])
  fix \<rho> env'' X assume "wt_env \<rho> env" "dtyped \<rho> dps" "vinv \<rho> env (X \<union> dvars dps)"
  then show "wt_env \<rho> env' \<and> dtyped \<rho> dps \<and> vinv \<rho> env' (X \<union> dvars dps) \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps) \<rho> dps"
    using wt_env_tenv[OF tenv] vinv_tenv[OF tenv ext] deqv_self[of \<rho> dps] by blast
qed

lemma cunify_types_dstep: "okW (cunify_types alg' T U env) env' \<Longrightarrow> dstep env dps env' dps"
  using dstep_tenv cunify_types_sound(1,2) by blast


subsection \<open>Types of terms\<close>

text \<open>The type computed by \<^const>\<open>fastype\<close>, instantiated by a solution of the type environment,
  is the type of the instantiated term:\<close>

lemma env_fastype_sound:
  "ok (env_fastype env Ts t) T \<Longrightarrow> Ts = map snd bs \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow>
    e \<turnstile> inst \<rho> t : U \<Longrightarrow> tsubst \<rho> T = U"
proof (induction env Ts t arbitrary: T bs e U rule: env_fastype.induct)
  case (1 env Ts f u)
  from "1.prems"(1) obtain T0 T' where f: "ok (env_fastype env Ts f) T0"
    and dv: "ok (devar (tyenv env) T0) T'"
    and rest: "ok (case T' of
      Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
        else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by auto
  from "1.prems"(5) obtain A where tf: "e \<turnstile> inst \<rho> f : A \<rightarrow>\<^sub>T U" by auto
  have "tsubst \<rho> T0 = A \<rightarrow>\<^sub>T U" by (rule "1.IH"[OF f "1.prems"(2-4) tf])
  moreover have "tsubst \<rho> T' = tsubst \<rho> T0" by (rule devar_sound[OF dv refl "1.prems"(3)])
  moreover from rest obtain T1 where "T' = T1 \<rightarrow>\<^sub>T T"
    by (auto split: ptyp.splits list.splits if_splits)
  ultimately show ?case by simp
next
  case (4 env Ts i)
  have "ok (nth Ts i) T"
  proof -
    have nh: False if "ok (case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound i])
        | _ \<Rightarrow> raise e) y" for e and y :: ptyp
      using that by (cases e) auto
    from "4.prems"(1) show ?thesis by (auto simp: ok_handle dest: nh)
  qed
  then have i: "0 \<le> i" "i < ilength bs" "T = snd (bs ! nat_of_integer i)"
    using "4.prems"(2) nat_of_integer_less_ilength[of i bs] by (auto simp: ok_nth)
  with "4.prems"(4,5) show ?case by (auto simp: bs_env_def)
next
  case (6 env Ts a T0 u)
  from "6.prems"(1) obtain U0 where u: "ok (env_fastype env (T0 # Ts) u) U0" and T: "T = T0 \<rightarrow>\<^sub>T U0"
    by auto
  from "6.prems"(5) obtain W where c: "cert_typ alg ar (tsubst \<rho> T0)"
    and tu: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> u : W" and U: "U = tsubst \<rho> T0 \<rightarrow>\<^sub>T W"
    by auto
  have "tsubst \<rho> U0 = W"
    by (rule "6.IH"[OF u _ "6.prems"(3) bs_env_Cons[OF "6.prems"(4) c] tu, of a]) (simp add: "6.prems"(2))
  with T U show ?case by simp
qed auto

lemma fastype_sound:
  "ok (fastype env bs t) T \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> bs_env \<rho> e bs \<Longrightarrow> e \<turnstile> inst \<rho> t : U \<Longrightarrow>
    tsubst \<rho> T = U"
  unfolding fastype_def by (erule env_fastype_sound) simp_all

text \<open>\<^const>\<open>binder_types\<close> and \<^const>\<open>body_type\<close> split a type, modulo the type environment:\<close>

lemma binder_body_type_sound:
  assumes "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> ok (body_type env T) B \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow>
    tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> B"
  using assms
proof (induction env T r arbitrary: Ts B rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases T)
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" using Type by auto
      from h T obtain Ts' where r: "ok (bt env U) Ts'" and Ts: "Ts = T1 # Ts'" by auto
      from "1.prems"(2) T have b: "ok (body_type env U) B" by (subst (asm) body_type.simps) simp
      from "1.IH"[OF r refl b "1.prems"(3)] Ts T show ?thesis by simp
    next
      case False
      with h Type have "Ts = []" by (auto split: list.splits if_splits)
      moreover from "1.prems"(2) Type False have "B = T"
        by (subst (asm) body_type.simps) (auto split: list.splits if_splits)
      ultimately show ?thesis by simp
    qed
  next
    case (TVar v S)
    from h TVar obtain lr where lr: "ok (type_lookup (tyenv env) v S) lr"
      and rest: "ok (case lr of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    from "1.prems"(2) TVar obtain lr' where lr': "ok (type_lookup (tyenv env) v S) lr'"
      and rest': "ok (case lr' of None \<Rightarrow> return T | Some T' \<Rightarrow> body_type env T') B"
      by (subst (asm) body_type.simps) auto
    from lr lr' have ll: "lr' = lr" by simp
    show ?thesis
    proof (cases lr)
      case (Some T')
      with rest rest' ll have r: "ok (bt env T') Ts" and b: "ok (body_type env T') B" by simp_all
      from "1.IH"[OF r refl b "1.prems"(3)] ok_type_lookup_sound[OF lr[unfolded Some] "1.prems"(3)] TVar
      show ?thesis by simp
    qed (use rest rest' ll in simp)
  next
    case (TFree a S)
    with h "1.prems"(2) show ?thesis by (subst (asm) body_type.simps) simp
  qed
qed

lemma strip_type_sound:
  "ok (strip_type env T) (Ts, B) \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> tsubst \<rho> T = map (tsubst \<rho>) Ts \<Rrightarrow> tsubst \<rho> B"
  by (auto simp: strip_type_def intro: binder_body_type_sound[OF _ refl])

text \<open>Terms whose loose bound variables are bound by the binders have certified types:\<close>

text \<open>A binding of a closed term is an equation in every environment:\<close>

lemma eqv_bind_closed:
  assumes "(Var x U, u) \<in> E" "closed u" "\<And>e. e \<turnstile> u : U"
  shows "eqv E e (Var x U) u"
proof -
  have "cert_typ alg ar U"
    by (rule typing_cert[OF assms(3)[of e]]) (use assms(2) loose_bvar1_imp closed_loose_bvar in blast)
  then show ?thesis using eqv_ax[OF assms(1) _ assms(3)] by auto
qed

lemma bs_env_cert:
  assumes "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> t : T" "\<not> loose_bvar t (ilength bs)"
  shows "cert_typ alg ar T"
proof (rule typing_cert[OF assms(2)], intro allI impI)
  fix i assume i: "0 \<le> i" "loose_bvar1 (inst \<rho> t) i"
  then have "loose_bvar t i" using loose_bvar1_imp by simp
  with assms(3) have "i < ilength bs" using loose_bvar_mono[of t i "ilength bs"] by fastforce
  then have "bs ! nat_of_integer i \<in> set bs" "e i = tsubst \<rho> (snd (bs ! nat_of_integer i))"
    using assms(1) i(1) nat_of_integer_less_ilength[OF i(1) \<open>i < ilength bs\<close>]
    by (auto simp: bs_env_def)
  then show "cert_typ alg ar (e i)" using assms(1) by (auto simp: bs_env_def)
qed

subsection \<open>\<open>\<eta>\<close>-normal form\<close>

lemma etif_sound:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' = vars t \<and> (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar t k \<longrightarrow> \<not> loose_bvar t' k) \<and>
    (\<forall>\<rho> e. tsol tye \<rho> \<longrightarrow> cert_typ alg ar (tsubst \<rho> T) \<longrightarrow> e \<turnstile> inst \<rho> t : tsubst \<rho> T \<longrightarrow>
      e \<turnstile> inst \<rho> t' : tsubst \<rho> T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t))"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    from h T obtain u where hu: "ok (ef tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u"
      by auto
    have lt: "incr_boundvars 1 t = lift t 0" by (simp add: incr_boundvars_def)
    note IH = "1.IH"[OF hu refl, unfolded lt]
    have "vars t' = vars t" using IH t' by simp
    moreover have "\<not> loose_bvar t' k" if "0 \<le> k" "\<not> loose_bvar t k" for k
    proof -
      have "\<not> loose_bvar (lift t 0 $ Bound 0) (k + 1)"
        using that loose_bvar_lift[of 0 k t] by (simp add: integer_arith)
      with IH that(1) t' show ?thesis by (simp add: integer_arith)
    qed
    moreover have "e \<turnstile> inst \<rho> t' : tsubst \<rho> T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
      if tsol: "tsol tye \<rho>" and c: "cert_typ alg ar (tsubst \<rho> T)" and ty: "e \<turnstile> inst \<rho> t : tsubst \<rho> T"
      for \<rho> e
    proof -
      from c T have c1: "cert_typ alg ar (tsubst \<rho> T1)" and c2: "cert_typ alg ar (tsubst \<rho> U)"
        by (simp_all add: cert_typ_fun)
      have te: "e\<langle>0:tsubst \<rho> T1\<rangle> \<turnstile> inst \<rho> (lift t 0 $ Bound 0) : tsubst \<rho> U"
        using ty T by auto
      from IH tsol c2 te have tu: "e\<langle>0:tsubst \<rho> T1\<rangle> \<turnstile> inst \<rho> u : tsubst \<rho> U"
        and cu: "\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (lift t 0 $ Bound 0)"
        by blast+
      have ty': "e \<turnstile> inst \<rho> t' : tsubst \<rho> T" using c1 tu t' T by auto
      moreover have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t" if \<sigma>: "wt_subst \<sigma>" for \<sigma>
      proof -
        have ap_e: "ap \<rho> \<sigma> (lift t 0) = lift (ap \<rho> \<sigma> t) 0" using \<sigma> by (simp add: ap_lift)
        have "e\<langle>0:tsubst \<rho> T1\<rangle> \<turnstile> lift (ap \<rho> \<sigma> t) 0 $ Bound 0 : tsubst \<rho> U"
          using typing_ap[OF te \<sigma>] by (simp add: ap_e)
        from typing.Abs[OF c1 this]
        have w: "wt (Abs STR '''' (tsubst \<rho> T1) (lift (ap \<rho> \<sigma> t) 0 $ Bound 0))" by (auto simp: wt_def)
        have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs STR '''' (tsubst \<rho> T1) (lift (ap \<rho> \<sigma> t) 0 $ Bound 0)"
          using conv_Abs[OF _ w cu[rule_format, OF \<sigma>, unfolded ap_simps ap_e]] wt_ap[OF ty' \<sigma>] t'
          by simp
        also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
          using w eta_lift_Bound0 by (intro beta_eta_conv) auto
        finally show ?thesis .
      qed
      ultimately show ?thesis by blast
    qed
    ultimately show ?thesis by blast
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from h TVar obtain lr where lr: "ok (type_lookup tye v S) lr"
        and rest: "ok (case lr of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by auto
      show ?thesis
      proof (cases lr)
        case (Some T')
        with rest have r: "ok (ef tye T' t) t'" by simp
        note IH = "1.IH"[OF r refl]
        have "tsubst \<rho> T = tsubst \<rho> T'" if "tsol tye \<rho>" for \<rho>
          using ok_type_lookup_sound[OF lr[unfolded Some] that] TVar by simp
        with IH show ?thesis by metis
      qed (use rest in simp)
    next
      case (Type a Ts)
      with nf h have "t' = t" by (auto split: list.splits if_splits)
      then show ?thesis by simp
    qed (use h in simp)
  qed
qed

lemma eta_norm_nonAbs: "\<not> is_Abs t \<Longrightarrow> eta_norm env bs t = do {T \<leftarrow> fastype env bs t; etif (tyenv env) T t}"
  by (cases t) simp_all

lemma eta_norm_nonAbs_sound:
  assumes "ok (eta_norm env bs t) t'" "\<not> is_Abs t"
  shows "vars t' = vars t \<and> (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar t k \<longrightarrow> \<not> loose_bvar t' k) \<and>
    (\<forall>\<rho> e T. tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow> \<not> loose_bvar t (ilength bs) \<longrightarrow>
      e \<turnstile> inst \<rho> t' : T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t))"
proof -
  from assms obtain T0 where T0: "ok (fastype env bs t) T0" and et: "ok (etif (tyenv env) T0 t) t'"
    by (auto simp: eta_norm_nonAbs)
  note E = etif_sound[OF et refl]
  have "e \<turnstile> inst \<rho> t' : T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
    if tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> t : T"
      and lb: "\<not> loose_bvar t (ilength bs)" for \<rho> e T
  proof -
    have T: "tsubst \<rho> T0 = T" by (rule fastype_sound[OF T0 tsol bs ty])
    have "cert_typ alg ar T" by (rule bs_env_cert[OF bs ty lb])
    with E tsol ty T show ?thesis by blast
  qed
  with E show ?thesis by blast
qed

lemma eta_norm_sound:
  "ok (eta_norm env bs t) t' \<Longrightarrow> vars t' = vars t \<and> (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar t k \<longrightarrow> \<not> loose_bvar t' k) \<and>
    (\<forall>\<rho> e T. tsol (tyenv env) \<rho> \<longrightarrow> bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow> \<not> loose_bvar t (ilength bs) \<longrightarrow>
      e \<turnstile> inst \<rho> t' : T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t))"
proof (induction t arbitrary: bs t')
  case (Abs a T0 body)
  from Abs.prems obtain b' where b': "ok (eta_norm env ((a, T0) # bs) body) b'"
    and t': "t' = Abs a T0 b'" by auto
  note IH = Abs.IH[OF b']
  have "vars t' = vars (Abs a T0 body)" using IH t' by simp
  moreover have "\<not> loose_bvar t' k" if "0 \<le> k" "\<not> loose_bvar (Abs a T0 body) k" for k
    using IH that t' by (simp add: integer_arith)
  moreover have "e \<turnstile> inst \<rho> t' : T \<and> (\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a T0 body))"
    if tsol: "tsol (tyenv env) \<rho>" and bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> (Abs a T0 body) : T"
      and lb: "\<not> loose_bvar (Abs a T0 body) (ilength bs)"
    for \<rho> e T
  proof -
    from ty obtain W where c: "cert_typ alg ar (tsubst \<rho> T0)"
      and tb: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> body : W" and T: "T = tsubst \<rho> T0 \<rightarrow>\<^sub>T W"
      by auto
    have lb': "\<not> loose_bvar body (ilength ((a, T0) # bs))" using lb by (simp add: algebra_simps)
    from IH tsol bs_env_Cons[OF bs c] tb lb'
    have tb': "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> b' : W"
      and cb: "\<forall>\<sigma>. wt_subst \<sigma> \<longrightarrow> ap \<rho> \<sigma> b' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body"
      by blast+
    have ty': "e \<turnstile> inst \<rho> t' : T" using c tb' T t' by auto
    moreover have "ap \<rho> \<sigma> t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (Abs a T0 body)" if \<sigma>: "wt_subst \<sigma>" for \<sigma>
      using conv_Abs[OF _ _ cb[rule_format, OF \<sigma>]] wt_ap[OF ty' \<sigma>] wt_ap[OF ty \<sigma>] t' by simp
    ultimately show ?thesis by blast
  qed
  ultimately show ?case by blast
qed (rule eta_norm_nonAbs_sound; simp)+

subsection \<open>Normalization of disagreement pairs\<close>

text \<open>Replacing a term of a pair by an equivalent one, in the same environment:\<close>

definition tconv :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "tconv env bs t t' \<longleftrightarrow> vars t' \<subseteq> vars t \<union> evars env \<and>
    (\<forall>\<rho> e T. tsol (tyenv env) \<rho> \<longrightarrow> wt_env \<rho> env \<longrightarrow> bs_env \<rho> e bs \<longrightarrow> e \<turnstile> inst \<rho> t : T \<longrightarrow>
      \<not> loose_bvar t (ilength bs) \<longrightarrow>
      e \<turnstile> inst \<rho> t' : T \<and> \<not> loose_bvar t' (ilength bs) \<and> eqv (binds \<rho> env) e (inst \<rho> t) (inst \<rho> t'))"

lemma tconv_ap:
  assumes "tconv env bs t t'" "tsol (tyenv env) \<rho>" "wt_env \<rho> env" "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> t : T"
    "\<not> loose_bvar t (ilength bs)" "solution \<rho> \<sigma> env"
  shows "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
proof -
  from assms(1-6) have "eqv (binds \<rho> env \<union> {}) e (inst \<rho> t) (inst \<rho> t')" unfolding tconv_def by simp
  from eqv_ap[OF this assms(7)] show ?thesis by simp
qed

lemma tconv_trans:
  assumes "tconv env bs t1 t2" "tconv env bs t2 t3"
  shows "tconv env bs t1 t3"
  unfolding tconv_def
proof (intro conjI allI impI)
  show "vars t3 \<subseteq> vars t1 \<union> evars env" using assms unfolding tconv_def by blast
  fix \<rho> e T assume a: "tsol (tyenv env) \<rho>" "wt_env \<rho> env" "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> t1 : T"
    "\<not> loose_bvar t1 (ilength bs)"
  from assms(1) a have r1: "e \<turnstile> inst \<rho> t2 : T" "\<not> loose_bvar t2 (ilength bs)"
    "eqv (binds \<rho> env) e (inst \<rho> t1) (inst \<rho> t2)"
    unfolding tconv_def by blast+
  from assms(2) a(1-3) r1(1,2) have r2: "e \<turnstile> inst \<rho> t3 : T" "\<not> loose_bvar t3 (ilength bs)"
    "eqv (binds \<rho> env) e (inst \<rho> t2) (inst \<rho> t3)"
    unfolding tconv_def by blast+
  show "e \<turnstile> inst \<rho> t3 : T" "\<not> loose_bvar t3 (ilength bs)" by (fact r2(1), fact r2(2))
  show "eqv (binds \<rho> env) e (inst \<rho> t1) (inst \<rho> t3)" by (rule eqv.eqv_trans[OF r1(3) r2(3)])
qed

lemma head_norm_tconv: "ok (head_norm env t) t' \<Longrightarrow> tconv env bs t t'"
  unfolding tconv_def
  using head_norm_vars[OF _ refl] head_norm_eqv[OF _ refl] head_norm_loose[OF _ refl] ilength_nonneg
  by blast

lemma eta_norm_tconv: "ok (eta_norm env bs t) t' \<Longrightarrow> tconv env bs t t'"
proof -
  assume a: "ok (eta_norm env bs t) t'"
  note E = eta_norm_sound[OF a]
  show ?thesis unfolding tconv_def
  proof (intro conjI allI impI)
    show "vars t' \<subseteq> vars t \<union> evars env" using E by blast
    fix \<rho> e T assume b: "tsol (tyenv env) \<rho>" "wt_env \<rho> env" "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> t : T"
      "\<not> loose_bvar t (ilength bs)"
    with E have r: "e \<turnstile> inst \<rho> t' : T" "\<not> loose_bvar t' (ilength bs)"
      "ap \<rho> (\<lambda>x T. Var x T) t' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (\<lambda>x T. Var x T) t"
      using wt_subst_Var by auto
    show "e \<turnstile> inst \<rho> t' : T" "\<not> loose_bvar t' (ilength bs)" by (fact r(1), fact r(2))
    from conv_sym[OF r(3)[unfolded ap_Var]] b(4) r(1)
    show "eqv (binds \<rho> env) e (inst \<rho> t) (inst \<rho> t')" by (rule eqv_conv)
  qed
qed

lemma tconv_dstep:
  assumes ct: "tconv env bs t t'" and cu: "tconv env bs u u'"
  shows "dstep env [(bs, t, u)] env [(bs, t', u')]"
proof (rule dstepI[OF extends_refl])
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext: "extends env env''"
    and wte: "wt_env \<rho> env" and d: "dtyped \<rho> [(bs, t, u)]" and v: "vinv \<rho> env (X \<union> dvars [(bs, t, u)])"
  have tsol: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF tsol'' ext])
  from d obtain e T where bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T"
    and lb: "\<not> loose_bvar t (ilength bs)" "\<not> loose_bvar u (ilength bs)"
    by auto
  from ct tsol wte bs ty(1) lb(1) have rt: "e \<turnstile> inst \<rho> t' : T" "\<not> loose_bvar t' (ilength bs)"
    unfolding tconv_def by blast+
  from cu tsol wte bs ty(2) lb(2) have ru: "e \<turnstile> inst \<rho> u' : T" "\<not> loose_bvar u' (ilength bs)"
    unfolding tconv_def by blast+  have "dtyped \<rho> [(bs, t', u')]" using bs rt ru by auto
  moreover have "vinv \<rho> env (X \<union> dvars [(bs, t', u')])"
  proof (rule vinv_hn)
    show "vinv \<rho> env (X \<union> (vars t \<union> vars u))" using v by (simp add: Un_ac)
    show "dvars [(bs, t', u')] \<subseteq> vars t \<union> vars u \<union> evars env" using ct cu by (auto simp: tconv_def)
  qed
  moreover have "deqv (binds \<rho> env \<union> dp_eqs \<rho> [(bs, t', u')]) \<rho> [(bs, t, u)]"
    unfolding deqv_single
  proof (intro allI impI)
    fix e' T' assume a: "bs_env \<rho> e' bs" "e' \<turnstile> inst \<rho> t : T'" "e' \<turnstile> inst \<rho> u : T'"
    let ?E = "binds \<rho> env \<union> dp_eqs \<rho> [(bs, t', u')]"
    from ct tsol wte a(1,2) lb(1) have t1: "e' \<turnstile> inst \<rho> t' : T'" "eqv (binds \<rho> env) e' (inst \<rho> t) (inst \<rho> t')"
      unfolding tconv_def by blast+
    from cu tsol wte a(1,3) lb(2) have u1: "e' \<turnstile> inst \<rho> u' : T'" "eqv (binds \<rho> env) e' (inst \<rho> u) (inst \<rho> u')"
      unfolding tconv_def by blast+
    have "eqv ?E e' (inst \<rho> t') (inst \<rho> u')"
      by (rule dp_eqs_use[OF _ _ a(1) t1(1) u1(1) rt(2) ru(2)]) auto
    from eqv.eqv_trans[OF eqv.eqv_trans[OF eqv_mono[OF t1(2)] this] eqv.eqv_sym[OF eqv_mono[OF u1(2)]]]
    show "eqv ?E e' (inst \<rho> t) (inst \<rho> u)" by blast
  qed
  ultimately show "wt_env \<rho> env \<and> dtyped \<rho> [(bs, t', u')] \<and> vinv \<rho> env (X \<union> dvars [(bs, t', u')]) \<and>
      deqv (binds \<rho> env \<union> dp_eqs \<rho> [(bs, t', u')]) \<rho> [(bs, t, u)]"
    using wte by blast
qed

text \<open>Stripping common abstractions:\<close>

lemma dstep_Abs:
  assumes tenv: "tenv env1 = tenv env" and ext: "extends env env1"
  shows "dstep env [(bs, Abs a T s, Abs b U t)] env1 [((c, T) # bs, s, t)]"
proof (rule dstepI[OF ext])
  fix \<rho> env'' X assume tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env1 env''"
    and wte: "wt_env \<rho> env" and d: "dtyped \<rho> [(bs, Abs a T s, Abs b U t)]"
    and v: "vinv \<rho> env (X \<union> dvars [(bs, Abs a T s, Abs b U t)])"
  from d[unfolded dtyped_simps] obtain e V where bs: "bs_env \<rho> e bs" and ty: "e \<turnstile> inst \<rho> (Abs a T s) : V" "e \<turnstile> inst \<rho> (Abs b U t) : V"
    and lb: "\<not> loose_bvar (Abs a T s) (ilength bs)" "\<not> loose_bvar (Abs b U t) (ilength bs)"
    by blast
  have body: "\<exists>W. e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W \<and> e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t : W \<and>
      cert_typ alg ar (tsubst \<rho> T) \<and> tsubst \<rho> U = tsubst \<rho> T"
    if "e' \<turnstile> inst \<rho> (Abs a T s) : V'" "e' \<turnstile> inst \<rho> (Abs b U t) : V'" for e' V'
  proof -
    from that(1) obtain W where V: "V' = tsubst \<rho> T \<rightarrow>\<^sub>T W" and c: "cert_typ alg ar (tsubst \<rho> T)"
      and ts: "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W"
      by auto
    from that(2) obtain W' where V': "V' = tsubst \<rho> U \<rightarrow>\<^sub>T W'" and tt': "e'\<langle>0:tsubst \<rho> U\<rangle> \<turnstile> inst \<rho> t : W'"
      by auto
    from V V' have TU: "tsubst \<rho> U = tsubst \<rho> T" and WW: "W' = W" by simp_all
    from tt' have tt: "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t : W" by (simp only: TU WW)
    with ts c TU show ?thesis by blast
  qed
  from body[OF ty] obtain W where ts: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W"
    and tt: "e\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t : W" and c: "cert_typ alg ar (tsubst \<rho> T)" by blast
  have lb': "\<not> loose_bvar s (ilength ((c, T) # bs))" "\<not> loose_bvar t (ilength ((c, T) # bs))"
    using lb by (auto simp: algebra_simps)
  have "dtyped \<rho> [((c, T) # bs, s, t)]"
    using bs_env_Cons[OF bs c, of c] ts tt lb' by auto
  moreover have "vinv \<rho> env1 (X \<union> dvars [((c, T) # bs, s, t)])" using vinv_tenv[OF tenv ext v] by simp
  moreover have "wt_env \<rho> env1" using wte by (simp add: wt_env_tenv[OF tenv])
  moreover have "deqv (binds \<rho> env1 \<union> dp_eqs \<rho> [((c, T) # bs, s, t)]) \<rho> [(bs, Abs a T s, Abs b U t)]"
    unfolding deqv_single
  proof (intro allI impI)
    fix e' V' assume a: "bs_env \<rho> e' bs" "e' \<turnstile> inst \<rho> (Abs a T s) : V'" "e' \<turnstile> inst \<rho> (Abs b U t) : V'"
    let ?E = "binds \<rho> env1 \<union> dp_eqs \<rho> [((c, T) # bs, s, t)]"
    from body[OF a(2,3)] obtain W' where s1: "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> s : W'"
      and t1: "e'\<langle>0:tsubst \<rho> T\<rangle> \<turnstile> inst \<rho> t : W'" and TU: "tsubst \<rho> U = tsubst \<rho> T" by blast
    have "eqv ?E (e'\<langle>0:tsubst \<rho> T\<rangle>) (inst \<rho> s) (inst \<rho> t)"
      by (rule dp_eqs_use[OF _ _ bs_env_Cons[OF a(1) c, of c] s1 t1 lb']) auto
    from eqv.eqv_abs[OF this c, of a b] TU show "eqv ?E e' (inst \<rho> (Abs a T s)) (inst \<rho> (Abs b U t))" by simp
  qed
  ultimately show "wt_env \<rho> env1 \<and> dtyped \<rho> [((c, T) # bs, s, t)] \<and> vinv \<rho> env1 (X \<union> dvars [((c, T) # bs, s, t)]) \<and>
      deqv (binds \<rho> env1 \<union> dp_eqs \<rho> [((c, T) # bs, s, t)]) \<rho> [(bs, Abs a T s, Abs b U t)]"
    by blast
qed

lemma new_dpair_sound:
  "okW (new_dpair alg' bs t u env) (dp', env') \<Longrightarrow> tenv env' = tenv env \<and> dstep env [(bs, t, u)] env' [dp']"
proof (induction alg' bs t u env rule: new_dpair.induct)
  case (1 alg' bs a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems" obtain env1 where cu: "okW (cunify_types alg' T U env) env1"
    and r: "okW (new_dpair alg' ((c, T) # bs) body1 body2 env1) (dp', env')"
    by (auto simp: c_def Let_def)
  note IH = "1.IH"[OF cu c_def r] and cs = cunify_types_sound[OF cu]
  from IH cs have "tenv env' = tenv env" by simp
  moreover have "dstep env [(bs, Abs a T body1, Abs b U body2)] env' [dp']"
    using dstep_trans[OF dstep_Abs[OF cs(1,2)] conjunct2[OF IH]] .
  ultimately show ?case by blast
qed (auto simp: dstep_refl)

lemma head_norm_dpair_sound:
  assumes "okW (head_norm_dpair alg' env dp) (dp', env')"
  shows "tenv env' = tenv env" "dstep env [dp] env' [dp']"
proof -
  obtain bs t u where dp: "dp = (bs, t, u)" by (cases dp)
  from assms obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env bs t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env bs u1) u2" and
    nd: "okW (new_dpair alg' bs t2 u2 env) (dp', env')"
    by (auto simp: head_norm_dpair_def dp)
  have "tconv env bs t t2" by (rule tconv_trans[OF head_norm_tconv[OF ht] eta_norm_tconv[OF et]])
  moreover have "tconv env bs u u2" by (rule tconv_trans[OF head_norm_tconv[OF hu] eta_norm_tconv[OF eu]])
  ultimately have "dstep env [(bs, t, u)] env [(bs, t2, u2)]" by (rule tconv_dstep)
  with new_dpair_sound[OF nd] show "tenv env' = tenv env" "dstep env [dp] env' [dp']"
    by (auto simp: dp intro: dstep_trans)
qed

subsection \<open>Assignments\<close>

lemma get_eta_var_app:
  "okW (get_eta_var bs n t) (v, T) \<Longrightarrow> t = app (Var v T) (rev (map (\<lambda>j. n + integer_of_nat j) [0..<length bs]))"
proof (induction bs arbitrary: n t)
  case Nil
  then show ?case by (cases t) (auto simp: app_apps)
next
  case (Cons b bs)
  from Cons.prems obtain f where t: "t = f $ Bound n" and r: "okW (get_eta_var bs (n + 1) f) (v, T)"
    by (cases "(b # bs, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  have m: "map (\<lambda>j. n + integer_of_nat j) [0..<Suc (length bs)] =
      n # map (\<lambda>j. n + 1 + integer_of_nat j) [0..<length bs]"
    by (simp add: map_upt_Suc integer_of_nat_eq_of_nat algebra_simps del: upt_Suc)
  show ?case using Cons.IH[OF r] by (simp add: t m app_apps del: upt_Suc)
qed

lemma downto0_upt: "downto0 (rev (map integer_of_nat [0..<k])) (integer_of_nat k - 1)"
  by (induction k) (simp_all add: integer_of_nat_eq_of_nat)

lemma rlist_abs_abs_list: "rlist_abs bs t = abs_list (rev bs) t"
  by (induction bs t rule: rlist_abs.induct) simp_all

text \<open>Solving a pair whose left-hand side is \<open>\<eta>\<close>-equivalent to a variable by assignment:\<close>

lemma eta_var_step:
  assumes gev: "okW (get_eta_var bs 0 s) (F, Fty)" and upd: "ok (update (F, Fty) (rlist_abs bs t) env) env'"
  shows "step_ok env bs s t env'"
proof -
  define "is" where "is = rev (map integer_of_nat [0..<length bs])"
  have s: "s = app (Var F Fty) is" using get_eta_var_app[OF gev] by (simp add: is_def)
  have is_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    by (auto simp: is_def ilength_eq integer_of_nat_eq_of_nat)
  have mb: "map (\<lambda>i. bs ! nat_of_integer i) is = rev bs"
    by (simp add: is_def rev_map[symmetric] map_nth comp_def)
  define u' where "u' = rlist_abs bs t"
  have u': "u' = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t"
    by (simp add: u'_def mb rlist_abs_abs_list)
  have pj: "ok (proj t env bs is) (t, env)"
    using downto0_upt[of "length bs"] by (simp add: proj_def is_def ilength_eq)
  note upd = upd[folded u'_def]
  note ps = proj_sound[OF pj] and is_nonneg = is_ok[THEN bspec, THEN conjunct1]
  have ext: "extends env env'" using extends_update[OF upd] .
  moreover have "wt_env \<rho> env' \<and> vinv \<rho> env' X \<and>
      eqv (binds \<rho> env') e (inst \<rho> (app (Var F Fty) is)) (inst \<rho> t)"
    if tsol'': "tsol (tyenv env'') \<rho>" and ext': "extends env' env''" and wte: "wt_env \<rho> env"
      and bs: "bs_env \<rho> e bs" and tyF: "e \<turnstile> inst \<rho> (app (Var F Fty) is) : T" and tyt: "e \<turnstile> inst \<rho> t : T"
      and vi: "vinv \<rho> env (X \<union> vars (app (Var F Fty) is) \<union> vars t)"
      and lbt: "\<not> loose_bvar t (ilength bs)"
    for \<rho> env'' e T X
  proof -
    have ext1: "extends env env''" using extends_trans[OF extends_update[OF upd] ext'] .
    have vi': "vinv \<rho> env ((X \<union> {(F, Fty)}) \<union> vars t)" using vi by (simp add: Un_ac)
    have is0: "\<forall>i\<in>set is. 0 \<le> i" using is_ok by blast
    note r = proj_sound(2)[OF pj is0 tsol'' ext1 wte bs tyt vi' lbt]
    from tyF obtain Fty_eq: "tsubst \<rho> Fty = map e is \<Rrightarrow> T" by (rule typing_appE)
    note bt = bs_types[OF bs is_ok]
    let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (map (\<lambda>i. bs ! nat_of_integer i) is)"
    have tu': "e' \<turnstile> inst \<rho> u' : tsubst \<rho> Fty" for e'
    proof -
      from r have "pushes e' (map e is) \<turnstile> inst \<rho> t : T" by blast
      then have "pushes e' (map snd ?bs) \<turnstile> inst \<rho> t : T" by (simp only: bt(1))
      from typing_abs_list[OF this bt(2)] have "e' \<turnstile> abs_list ?bs (inst \<rho> t) : map e is \<Rrightarrow> T"
        by (simp only: bt(1))
      then show ?thesis by (simp only: u' inst_abs_list Fty_eq)
    qed
    have "closed u'" using r by (auto simp: u' intro!: closed_abs_list)
    then have wte': "wt_env \<rho> env'" using wt_env_update[OF upd conjunct1[OF r]] tu' by blast
    have "vinv \<rho> env (X \<union> insert (F, Fty) (vars u'))" using r by (simp add: u' Un_ac)
    then have vi'': "vinv \<rho> env' X" by (rule vinv_update[OF upd])
    let ?E = "binds \<rho> env'"
    have lk: "vt_lookup (tenv env') F = Some (Fty, u')" using ok_update(2)[OF upd] by simp
    have Fe: "inst \<rho> (app (Var F Fty) is) = Var F (tsubst \<rho> Fty) \<degree>\<degree> map Bound is"
      by (simp add: app_apps inst_apps comp_def)
    have js: "e \<tturnstile> map Bound is : map e is" by (rule typings_Bounds) (use is0 in auto)
    have tyV: "e \<turnstile> Var F (tsubst \<rho> Fty) : tsubst \<rho> Fty"
      using tyF unfolding Fe by (auto elim!: list_app_typeE simp: Fty_eq dest: typings_BoundsD)
    have tu: "e \<turnstile> inst \<rho> u' \<degree>\<degree> map Bound is : T"
      using tu'[of e] Fty_eq js by (auto intro: list_app_typeI)
    have "(Var F (tsubst \<rho> Fty), inst \<rho> u') \<in> ?E" unfolding binds_def using lk by blast
    from eqv_ax[OF this tyV tu'] have "eqv ?E e (Var F (tsubst \<rho> Fty)) (inst \<rho> u')" .
    from eqv_apps_head[OF this _ tu] tyF
    have e1: "eqv ?E e (inst \<rho> (app (Var F Fty) is)) (inst \<rho> u' \<degree>\<degree> map Bound is)" unfolding Fe by simp
    from r have e3: "eqv (binds \<rho> env) e (inst \<rho> t) (rename (bren (rev is)) 0 (inst \<rho> t))" by blast
    from eqv_typing[OF e3] tyt obtain "e \<turnstile> rename (bren (rev is)) 0 (inst \<rho> t) : T"
      by (metis typing_unique)
    moreover have "inst \<rho> u' \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> rename (bren (rev is)) 0 (inst \<rho> t)"
    proof (rule conv_beta_eta)
      show "wt (inst \<rho> u' \<degree>\<degree> map Bound is)" using tu by (auto simp: wt_def)
      show "inst \<rho> u' \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* rename (bren (rev is)) 0 (inst \<rho> t)"
        using beta_abs_list_apps[of ?bs "is"] is0 by (simp add: u' inst_abs_list)
    qed
    ultimately have e2: "eqv ?E e (inst \<rho> u' \<degree>\<degree> map Bound is) (rename (bren (rev is)) 0 (inst \<rho> t))"
      using tu by (blast intro: eqv_conv)
    have e3': "eqv ?E e (rename (bren (rev is)) 0 (inst \<rho> t)) (inst \<rho> t)"
      using eqv.eqv_sym[OF eqv_mono[OF e3 binds_extends[OF extends_update[OF upd]]]] .
    from eqv.eqv_trans[OF eqv.eqv_trans[OF e1 e2] e3'] wte' vi'' show ?thesis by blast
  qed
  ultimately show ?thesis unfolding step_ok_def s by blast
qed

text \<open>
  An assignment solves the pair. Its occurs check is not needed for soundness: the update fails
  if the variable is already bound, and the semantics does not require acyclic environments.
  Neither is the unification of the types: the typing of the pair already makes the types equal.
\<close>

theorem assignment_sound:
  assumes "okW (assignment alg' bs t u env) env'"
  shows "dstep env [(bs, t, u)] env' []"
proof -
  have "\<exists>v T T1 T2 env1. okW (get_eta_var bs 0 t) (v, T) \<and> okW (cunify_types alg' T1 T2 env) env1 \<and>
      ok (update (v, T) (rlist_abs bs u) env1) env'"
    using assms by (auto simp: assignment_def split: occ.split_asm) (metis occ.exhaust)
  then obtain v T T1 T2 env1 where gev: "okW (get_eta_var bs 0 t) (v, T)"
    and cu: "okW (cunify_types alg' T1 T2 env) env1" and upd: "ok (update (v, T) (rlist_abs bs u) env1) env'"
    by blast
  have "dstep env1 [(bs, t, u)] env' []" by (rule step_ok_dstep[OF eta_var_step[OF gev upd]])
  with cunify_types_dstep[OF cu] show ?thesis by (rule dstep_trans)
qed

subsection \<open>Combining steps\<close>

text \<open>The sides of a pair can be swapped, in the problem and in the result:\<close>

lemma dstep_swap_in:
  assumes s: "dstep env ((bs, u, t) # dps) env' dps'"
  shows "dstep env ((bs, t, u) # dps) env' dps'"
proof (rule dstepI[OF dstepD(1)[OF s]])
  fix \<rho> env'' X assume a: "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env"
    and d: "dtyped \<rho> ((bs, t, u) # dps)" and v: "vinv \<rho> env (X \<union> dvars ((bs, t, u) # dps))"
    and nf: "nfree env''"
  have d': "dtyped \<rho> ((bs, u, t) # dps)" using d by auto
  have v': "vinv \<rho> env (X \<union> dvars ((bs, u, t) # dps))" using v by (simp add: Un_ac)
  let ?E = "binds \<rho> env' \<union> dp_eqs \<rho> dps'"
  note r = dstepD(2,3)[OF s a d' v' nf]
  then have "deqv ?E \<rho> [(bs, u, t)]" "deqv ?E \<rho> dps" using deqv_Cons[of ?E \<rho> "(bs, u, t)" dps] by blast+
  then have "deqv ?E \<rho> ((bs, t, u) # dps)"
    using deqv_Cons[of ?E \<rho> "(bs, t, u)" dps] deqv_single_sym by blast
  with r show "wt_env \<rho> env' \<and> dtyped \<rho> dps' \<and> vinv \<rho> env' (X \<union> dvars dps') \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> dps') \<rho> ((bs, t, u) # dps)"
    by blast
qed

lemma dstep_swap_out:
  assumes s: "dstep env dps env' ((bs, u, t) # dps')"
  shows "dstep env dps env' ((bs, t, u) # dps')"
proof (rule dstepI[OF dstepD(1)[OF s]])
  fix \<rho> env'' X assume a: "tsol (tyenv env'') \<rho>" "extends env' env''" "wt_env \<rho> env"
    "dtyped \<rho> dps" "vinv \<rho> env (X \<union> dvars dps)" "nfree env''"
  note r = dstepD(2,3)[OF s a]
  have d: "dtyped \<rho> ((bs, t, u) # dps')" using r by auto
  let ?A = "binds \<rho> env' \<union> dp_eqs \<rho> ((bs, t, u) # dps')"
  have "deqv ?A \<rho> dps"
  proof (rule deqv_eqs[of "binds \<rho> env'" "dp_eqs \<rho> ((bs, u, t) # dps')"])
    show "deqv (binds \<rho> env' \<union> dp_eqs \<rho> ((bs, u, t) # dps')) \<rho> dps" using r by blast
    fix l r e assume "(l, r) \<in> dp_eqs \<rho> ((bs, u, t) # dps')"
    then have "(r, l) \<in> dp_eqs \<rho> ((bs, t, u) # dps') \<or> (l, r) \<in> dp_eqs \<rho> ((bs, t, u) # dps')"
      by (auto simp: dp_eqs_Cons)
    with dp_eqs_eqv[OF d, of ?A] show "eqv ?A e l r" by (blast intro: eqv.eqv_sym)
  qed blast
  with r d show "wt_env \<rho> env' \<and> dtyped \<rho> ((bs, t, u) # dps') \<and> vinv \<rho> env' (X \<union> dvars ((bs, t, u) # dps')) \<and>
      deqv (binds \<rho> env' \<union> dp_eqs \<rho> ((bs, t, u) # dps')) \<rho> dps"
    by (auto simp: Un_ac)
qed

text \<open>A step on some pairs, followed by a step on one more pair:\<close>

lemma dstep_seq:
  assumes s1: "dstep env dps env1 (a1 @ b1)" and s2: "dstep env1 [p] env' (a2 @ b2)"
    and D: "set D = set (p # dps)"
  shows "dstep env D env' ((a2 @ a1) @ (b2 @ b1))"
proof -
  have "dstep env (dps @ [p]) env1 ((a1 @ b1) @ [p])" by (rule dstep_frame[OF s1])
  then have "dstep env D env1 ([p] @ (a1 @ b1))" by (rule dstep_set) (use D in auto)
  moreover have "dstep env1 ([p] @ (a1 @ b1)) env' ((a2 @ b2) @ (a1 @ b1))" by (rule dstep_frame[OF s2])
  ultimately have "dstep env D env' ((a2 @ b2) @ (a1 @ b1))" by (rule dstep_trans)
  then show ?thesis by (rule dstep_set) auto
qed

subsection \<open>Auxiliary facts\<close>

lemma head_of_apps: "head_of (s \<degree>\<degree> ts) = head_of s"
  by (induction ts arbitrary: s) simp_all

lemma vars_rlist_abs [simp]: "vars (rlist_abs rb t) = vars t"
  by (simp add: rlist_abs_abs_list)

lemma get_eta_var_head: "okW (get_eta_var bs n t) (v, T) \<Longrightarrow> head_of t = Var v T"
  using get_eta_var_app[of bs n t v T] by (simp add: app_apps head_of_apps)

lemma okW_ASSIGN_return: "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> y = x"
  by (cases e) auto

end

end
