section \<open>Soundness of Head Normalization\<close>

theory Pattern_Head_Norm
  imports Pattern_Semantics Pattern_Types
begin

context pure_sig
begin

text \<open>
  The soundness proofs fix a solution \<open>(\<rho>, \<sigma>)\<close> of the final environment. The problems are
  well-typed after instantiating their types by \<open>\<rho>\<close>, and so are the bindings of the environment:
\<close>

definition wt_env :: "tinst \<Rightarrow> env \<Rightarrow> bool" where
  "wt_env \<rho> env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> (\<forall>e. e \<turnstile> inst \<rho> u : tsubst \<rho> U))"

lemma wt_envD: "wt_env \<rho> env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> e \<turnstile> inst \<rho> u : tsubst \<rho> U"
  unfolding wt_env_def by blast


subsection \<open>Instances\<close>

lemma ap_simps [simp]:
  "ap \<rho> \<sigma> (Var x T) = \<sigma> x (tsubst \<rho> T)"
  "ap \<rho> \<sigma> (Const c T) = Const c (tsubst \<rho> T)"
  "ap \<rho> \<sigma> (Free y T) = Free y (tsubst \<rho> T)"
  "ap \<rho> \<sigma> (Bound i) = Bound i"
  "ap \<rho> \<sigma> (Abs a T t) = Abs a (tsubst \<rho> T) (ap \<rho> \<sigma> t)"
  "ap \<rho> \<sigma> (s $ t) = ap \<rho> \<sigma> s $ ap \<rho> \<sigma> t"
  by (simp_all add: ap_def)

lemma ap_subst: "wt_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> ap \<rho> \<sigma> (t[s/k]) = (ap \<rho> \<sigma> t)[ap \<rho> \<sigma> s/k]"
  by (simp add: ap_def wt_subst_def)

lemma ap_lift: "wt_subst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> ap \<rho> \<sigma> (incr_bv n k t) = incr_bv n k (ap \<rho> \<sigma> t)"
  by (simp add: ap_def wt_subst_def)

lemma typing_ap: "e \<turnstile> inst \<rho> t : T \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> e \<turnstile> ap \<rho> \<sigma> t : T"
  unfolding ap_def by (rule typing_vsubst)

lemma wt_ap: "e \<turnstile> inst \<rho> t : T \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> wt (ap \<rho> \<sigma> t)"
  unfolding wt_def using typing_ap by blast

lemma conv_beta: "wt s \<Longrightarrow> s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  by (rule beta_eta_conv) auto

lemma conv_refl [simp]: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
  by (simp add: conv_def)

lemma conv_sym: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s"
  unfolding conv_def by (rule equivclp_sym)

lemma conv_trans [trans]: "r \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> s \<Longrightarrow> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> r \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  unfolding conv_def by (rule equivclp_trans)

text \<open>The \<open>\<beta>\<close>-redexes of the instance of a term:\<close>

lemma inst_beta: "inst \<rho> (Abs a T s $ t) \<rightarrow>\<^sub>\<beta> inst \<rho> (s[t/0])"
  by simp

lemma ap_beta: "wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> (Abs a T s $ t) \<rightarrow>\<^sub>\<beta> ap \<rho> \<sigma> (s[t/0])"
  by (simp add: ap_subst)


subsection \<open>Lookup\<close>

lemma ok_lookup_None: "ok (lookup env x T) None \<Longrightarrow> vt_lookup (tenv env) x = None"
  by (auto simp: lookup_def var_clash_def split: option.splits if_splits)

lemma ok_lookup_Some:
  assumes "ok (lookup env x T) (Some u)"
  obtains U where "vt_lookup (tenv env) x = Some (U, u)" "ok (unified (tyenv env) T U) True"
  using assms by (auto simp: lookup_def var_clash_def split: option.splits if_splits)

text \<open>A variable bound by the environment is equivalent to its binding in every solution.\<close>

lemma lookup_sound:
  assumes "ok (lookup env x T) (Some u)" "solution \<rho> \<sigma> env" "wt_env \<rho> env"
  shows "ap \<rho> \<sigma> (Var x T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" and "e \<turnstile> inst \<rho> u : tsubst \<rho> T"
proof -
  obtain U where U: "vt_lookup (tenv env) x = Some (U, u)" "ok (unified (tyenv env) T U) True"
    using assms(1) by (rule ok_lookup_Some)
  note s = solutionD[OF assms(2)]
  from unified_sound[OF U(2) s(2)] have "tsubst \<rho> T = tsubst \<rho> U" .
  with s(4)[OF U(1)] show "ap \<rho> \<sigma> (Var x T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by simp
  from wt_envD[OF assms(3) U(1)] \<open>tsubst \<rho> T = tsubst \<rho> U\<close>
  show "e \<turnstile> inst \<rho> u : tsubst \<rho> T" by simp
qed


subsection \<open>Head normalization\<close>

text \<open>Head normalization preserves the type and the meaning of a term in every solution.\<close>

lemma head_norm_sound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow>
    e \<turnstile> inst \<rho> t' : T \<and> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
  using assms
proof (induction env t r arbitrary: t' e T rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note sol = "1.prems"(2) and wte = "1.prems"(3) and ty = "1.prems"(4)
  note \<sigma> = solutionD(3)[OF sol]
  have IH: "e' \<turnstile> inst \<rho> u' : U \<and> ap \<rho> \<sigma> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
    if "ok (hn env u) u'" "e' \<turnstile> inst \<rho> u : U" for u u' e' U
    using "1.IH"[OF that(1) refl sol wte that(2)] .
  show ?case
  proof (cases t)
    case (Var x T0)
    with h obtain lr where lr: "ok (lookup env x T0) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with rest have hu: "ok (hn env u) t'" by simp
      from ty Var have T: "T = tsubst \<rho> T0" by auto
      note l = lookup_sound[OF lr[unfolded Some] sol wte]
      from IH[OF hu l(2)[of e, folded T]] l(1) Var show ?thesis by (blast intro: conv_trans)
    qed (use rest ty in simp)
  next
    case (Abs a T0 body)
    with h obtain body' where hb: "ok (hn env body) body'" and t': "t' = Abs a T0 body'" by auto
    from ty Abs obtain U where ok: "cert_typ alg ar (tsubst \<rho> T0)"
      and tb: "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> body : U" and T: "T = tsubst \<rho> T0 \<rightarrow>\<^sub>T U"
      by auto
    from IH[OF hb tb] have tb': "e\<langle>0:tsubst \<rho> T0\<rangle> \<turnstile> inst \<rho> body' : U"
      and c: "ap \<rho> \<sigma> body \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> body'"
      by blast+
    from ok tb' T t' have "e \<turnstile> inst \<rho> t' : T" by auto
    moreover have "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
    proof -
      have "wt (Abs a (tsubst \<rho> T0) (ap \<rho> \<sigma> body))" using wt_ap[OF ty \<sigma>] Abs by simp
      moreover have "wt (Abs a (tsubst \<rho> T0) (ap \<rho> \<sigma> body'))"
        using wt_ap[OF \<open>e \<turnstile> inst \<rho> t' : T\<close> \<sigma>] t' by simp
      ultimately show ?thesis using conv_Abs c by (simp add: Abs t')
    qed
    ultimately show ?thesis by blast
  next
    case (App f u)
    text \<open>A \<open>\<beta>\<close>-redex at the head is contracted, and normalization continues with the result.\<close>
    have redex: "e \<turnstile> inst \<rho> t' : T \<and> ap \<rho> \<sigma> (Abs b U0 body $ u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
      if hr: "ok (hn env (subst_bound u body)) t'" and tr: "e \<turnstile> inst \<rho> (Abs b U0 body $ u) : T"
      for b U0 body
    proof -
      have tr': "e \<turnstile> inst \<rho> (body[u/0]) : T"
        using subject_reduction_beta[OF tr inst_beta] .
      from IH[OF hr[unfolded subst_bound_subst] tr'] have "e \<turnstile> inst \<rho> t' : T"
        and c: "ap \<rho> \<sigma> (body[u/0]) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'"
        by blast+
      moreover have "ap \<rho> \<sigma> (Abs b U0 body $ u) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (body[u/0])"
        by (rule conv_beta[OF wt_ap[OF tr \<sigma>] ap_beta[OF \<sigma>]])
      ultimately show ?thesis using c by (blast intro: conv_trans)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (hn env (subst_bound u body)) t'" by simp
      from redex[OF this ty[unfolded App f]] App f show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from ty App obtain U where tf: "e \<turnstile> inst \<rho> f : U \<rightarrow>\<^sub>T T" and tu: "e \<turnstile> inst \<rho> u : U" by auto
      from IH[OF hf tf] have tnf: "e \<turnstile> inst \<rho> nf : U \<rightarrow>\<^sub>T T"
        and c: "ap \<rho> \<sigma> f \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> nf"
        by blast+
      have tnfu: "e \<turnstile> inst \<rho> (nf $ u) : T" using tnf tu by auto
      have c': "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (nf $ u)"
      proof -
        have "wt (ap \<rho> \<sigma> f $ ap \<rho> \<sigma> u)" using wt_ap[OF ty \<sigma>] App by simp
        moreover have "wt (ap \<rho> \<sigma> nf $ ap \<rho> \<sigma> u)" using wt_ap[OF tnfu \<sigma>] by simp
        ultimately show ?thesis using conv_App c conv_refl by (simp add: App)
      qed
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this tnfu[unfolded nf]] c' nf show ?thesis by (blast intro: conv_trans)
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with tnfu c' show ?thesis by simp
      qed
    qed
  qed (use h ty in simp_all)
qed

end

end
