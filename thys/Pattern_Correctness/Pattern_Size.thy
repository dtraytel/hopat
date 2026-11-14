section \<open>A Size Measure for Unification Problems\<close>

theory Pattern_Size
  imports Pattern_Acyclic Pattern_Normal
begin

text \<open>
  Unification problems are measured by the size of the \<open>\<beta>\<close>-normal form of their instance under
  the environment. A flexible term \<open>F t\<^sub>1 \<dots> t\<^sub>k\<close> counts as the \<open>\<eta>\<close>-expansion of \<open>F\<close> to its
  arity, without its arguments, so that pruning bindings do not change the size (after Grobauer).
\<close>

context pure_sig_gen
begin

subsection \<open>\<open>\<beta>\<close>-normal forms\<close>

definition bnorm :: "pterm \<Rightarrow> pterm" where
  "bnorm t = (THE u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> no_redex u)"

lemma no_redex_reds: "u \<rightarrow>\<^sub>\<beta>\<^sup>* v \<Longrightarrow> no_redex u \<Longrightarrow> v = u"
  by (induction rule: converse_rtranclp_induct) (auto simp: no_redex_iff)

lemma bnorm_eqI: "t \<rightarrow>\<^sub>\<beta>\<^sup>* u \<Longrightarrow> no_redex u \<Longrightarrow> bnorm t = u"
  unfolding bnorm_def
proof (rule the_equality)
  fix v assume tu: "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" and u: "no_redex u" and "t \<rightarrow>\<^sub>\<beta>\<^sup>* v \<and> no_redex v"
  then have tv: "t \<rightarrow>\<^sub>\<beta>\<^sup>* v" and v: "no_redex v" by blast+
  from beta_confluent tu tv obtain w where "u \<rightarrow>\<^sub>\<beta>\<^sup>* w" "v \<rightarrow>\<^sub>\<beta>\<^sup>* w"
    unfolding diamond_def commute_def square_def by blast
  with u v show "v = u" using no_redex_reds by metis
qed simp

lemma bnorm: "termip beta t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t \<and> no_redex (bnorm t)"
  using beta_normal_ex[of t] bnorm_eqI by metis

lemma bnorm_reds: "termip beta t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> bnorm t' = bnorm t"
proof -
  assume sn: "termip beta t" and tt': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'"
  have "termip beta t'" by (rule termip_reds[OF tt' sn])
  from bnorm[OF this] have "t' \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t'" "no_redex (bnorm t')" by blast+
  with tt' have "bnorm t = bnorm t'" by (intro bnorm_eqI) (blast intro: rtranclp_trans)+
  then show ?thesis by simp
qed

lemma termip_Abs: "termip beta (Abs a T t) \<Longrightarrow> termip beta t"
proof (induction "Abs a T t" arbitrary: t rule: accp_induct_rule)
  case 1
  have step: "termip beta t'" if "t \<rightarrow>\<^sub>\<beta> t'" for t'
    using "1.hyps"(2)[of t'] that by blast
  show ?case by (rule accp.accI) (blast intro: step)
qed

lemma bnorm_Abs: "termip beta (Abs a T t) \<Longrightarrow> bnorm (Abs a T t) = Abs a T (bnorm t)"
proof (rule bnorm_eqI)
  assume "termip beta (Abs a T t)"
  from bnorm[OF termip_Abs[OF this]] have "t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t" "no_redex (bnorm t)" by blast+
  then show "Abs a T t \<rightarrow>\<^sub>\<beta>\<^sup>* Abs a T (bnorm t)" "no_redex (Abs a T (bnorm t))"
    by (simp_all add: rtrancl_beta_Abs)
qed

text \<open>Well-typed terms have \<open>\<beta>\<close>-normal forms:\<close>

lemma bnorm_typed: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t \<and> no_redex (bnorm t)"
  using bnorm[OF type_implies_termi] .

lemma bnorm_typed_reds: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> bnorm t' = bnorm t"
  using bnorm_reds[OF type_implies_termi] .

lemma typing_args: "e \<turnstile> h \<degree>\<degree> ts : T \<Longrightarrow> t \<in> set ts \<Longrightarrow> \<exists>U. e \<turnstile> t : U"
proof -
  assume "e \<turnstile> h \<degree>\<degree> ts : T" "t \<in> set ts"
  then obtain Ts where "e \<tturnstile> ts : Ts" using list_app_typeD by blast
  with \<open>t \<in> set ts\<close> show ?thesis
    by (induction ts arbitrary: Ts) (auto split: list.splits)
qed

lemma beta_reds_args: "list_all2 (\<lambda>t u. t \<rightarrow>\<^sub>\<beta>\<^sup>* u) ts us \<Longrightarrow> h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* h \<degree>\<degree> us"
proof (induction ts us arbitrary: h rule: list_all2_induct)
  case (Cons t ts u us)
  have "h $ t \<rightarrow>\<^sub>\<beta>\<^sup>* h $ u" by (rule rtrancl_beta_AppR[OF Cons.hyps(1)])
  then have "(h $ t) \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* (h $ u) \<degree>\<degree> ts" by (rule apps_preserves_beta2)
  with Cons.IH[of "h $ u"] show ?case by (simp add: rtranclp_trans)
qed simp

lemma bnorm_atom_apps:
  assumes "atom h" "e \<turnstile> h \<degree>\<degree> ts : T"
  shows "bnorm (h \<degree>\<degree> ts) = h \<degree>\<degree> map bnorm ts"
proof (rule bnorm_eqI)
  have n: "t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t \<and> no_redex (bnorm t)" if "t \<in> set ts" for t
    using typing_args[OF assms(2) that] bnorm_typed by blast
  then show "h \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta>\<^sup>* h \<degree>\<degree> map bnorm ts"
    by (intro beta_reds_args) (simp add: list_all2_conv_all_nth)
  have "\<not> is_Abs h" "no_redex h" using assms(1) by (cases h; simp)+
  with n show "no_redex (h \<degree>\<degree> map bnorm ts)" by (simp add: no_redex_apps)
qed

lemma bnorm_Abs_typed: "e \<turnstile> Abs a U t : T \<Longrightarrow> bnorm (Abs a U t) = Abs a U (bnorm t)"
  by (rule bnorm_Abs[OF type_implies_termi])

lemma bnorm_lift: "e \<turnstile> t : T \<Longrightarrow> 0 \<le> k \<Longrightarrow> bnorm (lift t k) = lift (bnorm t) k"
proof (rule bnorm_eqI)
  assume "e \<turnstile> t : T" "0 \<le> k"
  then have "t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t" "no_redex (bnorm t)" using bnorm_typed by blast+
  have "lift t k \<rightarrow>\<^sub>\<beta>\<^sup>* lift u k" if "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" for u
    using that by (induction rule: rtranclp_induct)
      (auto intro: rtranclp.rtrancl_into_rtrancl simp: \<open>0 \<le> k\<close>)
  with \<open>t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t\<close> \<open>no_redex (bnorm t)\<close>
  show "lift t k \<rightarrow>\<^sub>\<beta>\<^sup>* lift (bnorm t) k" "no_redex (lift (bnorm t) k)"
    by (simp_all add: no_redex_incr_bv)
qed


subsection \<open>The size of \<open>\<beta>\<close>-normal forms\<close>

fun arity :: "ptyp \<Rightarrow> nat" where
  "arity (Type a [T, U]) = (if a = STR ''fun'' then Suc (arity U) else 0)"
| "arity _ = 0"

lemma arity_fun [simp]: "arity (T \<rightarrow>\<^sub>T U) = Suc (arity U)"
  by simp

lemma arity_funs: "arity (Ts \<Rrightarrow> T) = length Ts + arity T"
  by (induction Ts) auto

fun dhd :: "pterm \<Rightarrow> pterm" where
  "dhd (s $ t) = dhd s"
| "dhd t = t"

fun dnargs :: "pterm \<Rightarrow> nat" where
  "dnargs (s $ t) = Suc (dnargs s)"
| "dnargs t = 0"

lemma dhd_apps [simp]: "dhd (h \<degree>\<degree> ts) = dhd h"
  by (induction ts rule: rev_induct) (simp_all add: app_last[symmetric])

lemma dnargs_apps [simp]: "dnargs (h \<degree>\<degree> ts) = dnargs h + length ts"
  by (induction ts rule: rev_induct) (simp_all add: app_last[symmetric])

text \<open>A flexible term counts as the \<open>\<eta>\<close>-expansion of its head, without its arguments.\<close>

fun msz :: "pterm \<Rightarrow> nat" where
  "msz (Abs a T t) = msz t + 2"
| "msz (s $ t) = (case dhd s of Var x T \<Rightarrow> 2 * (arity T - Suc (dnargs s)) + 1 | _ \<Rightarrow> msz s + msz t)"
| "msz (Var x T) = 2 * arity T + 1"
| "msz _ = 1"

lemma msz_rigid_apps: "rigid h \<Longrightarrow> msz (h \<degree>\<degree> ts) = 1 + sum_list (map msz ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) (simp_all add: rigid_iff)
next
  case (snoc t ts)
  have "\<not> is_Var (dhd h)" using snoc.prems by (cases h) (simp_all add: rigid_iff)
  then have "(case dhd (h \<degree>\<degree> ts) of Var x T \<Rightarrow> 2 * (arity T - Suc (dnargs (h \<degree>\<degree> ts))) + 1
      | _ \<Rightarrow> msz (h \<degree>\<degree> ts) + msz t) = msz (h \<degree>\<degree> ts) + msz t"
    by (cases "dhd h") simp_all
  with snoc show ?case by (simp add: app_last[symmetric])
qed

lemma msz_flex_apps: "msz (Var x T \<degree>\<degree> ts) = 2 * (arity T - length ts) + 1"
  by (induction ts rule: rev_induct) (simp_all add: app_last[symmetric])

lemma dhd_lift: "dhd (lift t k) = lift (dhd t) k"
  by (induction t arbitrary: k rule: dhd.induct) simp_all

lemma dnargs_lift [simp]: "dnargs (lift t k) = dnargs t"
  by (induction t arbitrary: k rule: dnargs.induct) simp_all

lemma msz_lift [simp]: "msz (lift t k) = msz t"
proof (induction t arbitrary: k rule: msz.induct)
  case (2 s t)
  then show ?case by (cases "dhd s") (simp_all add: dhd_lift split: if_splits)
qed simp_all

subsection \<open>Unfolding closed and well-typed bindings\<close>

definition closed_env :: "env \<Rightarrow> bool" where
  "closed_env env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> closed u)"

lemma wt_env_closed_env: "wt_env \<rho> env \<Longrightarrow> closed_env env"
  unfolding closed_env_def using wt_env_closed by blast

lemma loose_bvar_vsubst_on:
  "(\<And>x T. (x, T) \<in> vars t \<Longrightarrow> closed (\<sigma> x T)) \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (vsubst \<sigma> t) k \<longleftrightarrow> loose_bvar t k"
proof (induction t arbitrary: k)
  case (Var x T)
  then show ?case using closed_loose_bvar by auto
next
  case (Abs a T t)
  then show ?case by (simp add: integer_arith)
qed auto

abbreviation usubst :: "env \<Rightarrow> vsubst" where
  "usubst env \<equiv> \<lambda>x T. case uval env x of Some v \<Rightarrow> v | None \<Rightarrow> Var x T"

lemma closed_usubst:
  assumes ac: "acyc env" and cl: "closed_env env"
  shows "closed_subst (usubst env)"
proof -
  have "closed (unf env u)" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using that
  proof (induction x arbitrary: U u rule: dep_induct[OF ac])
    case (1 x)
    have "closed (usubst env y T)" if "(y, T) \<in> vars u" for y T
    proof (cases "vt_lookup (tenv env) y")
      case (Some b)
      obtain U' u' where b: "b = (U', u')" by force
      have "(y, x) \<in> dep env" by (rule depI[OF "1.prems" that])
      from "1.IH"[OF this Some[unfolded b]] Some b show ?thesis by (simp add: uval_eq[OF ac])
    qed (simp add: uval_eq[OF ac] closed_def)
    moreover have "closed u" using cl "1.prems" unfolding closed_env_def by blast
    ultimately show ?case
      unfolding unf_def closed_def by (subst loose_bvar_vsubst_on) (simp_all add: closed_def)
  qed
  then show ?thesis
    by (auto simp: closed_subst_def uval_eq[OF ac] closed_def split: option.splits)
qed

lemma unf_subst:
  "acyc env \<Longrightarrow> closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> unf env (t[s/k]) = (unf env t)[unf env s/k]"
  unfolding unf_def using closed_usubst by simp

lemma unf_lift:
  "acyc env \<Longrightarrow> closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> unf env (incr_bv n k t) = incr_bv n k (unf env t)"
  unfolding unf_def using closed_usubst by simp

text \<open>Head normalization reduces the unfolding:\<close>

lemma head_norm_unf:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow> unf env t \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note ac = "1.prems"(2) and cl = "1.prems"(3)
  have IH: "unf env u \<rightarrow>\<^sub>\<beta>\<^sup>* unf env u'" if "ok (hn env u) u'" for u u'
    using "1.IH"[OF that refl ac cl] .
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
      with IH[of u t'] rest Some Var show ?thesis by (simp add: unf_Var[OF ac])
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (hn env body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    have redex: "unf env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
    proof -
      have "unf env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta> unf env (body[u/0])"
        by (simp add: unf_subst[OF ac cl])
      with IH[OF that[unfolded subst_bound_subst]] show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
    qed
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have fu: "unf env (f $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unf env (nf $ u)" using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded Abs] redex[OF this]] App show ?thesis by simp
      qed (use rest fu App in auto)
    qed
  qed (use h in auto)
qed

text \<open>Unfolding well-typed bindings preserves types:\<close>

lemma typing_unf_gen:
  assumes ac: "acyc env"
    and b: "\<And>x T U u. (x, T) \<in> vars t \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
      tsubst \<rho> T = tsubst \<rho> U \<and> (\<forall>e. e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U)"
  shows "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unf env t) : T"
  using b
proof (induction t arbitrary: e T)
  case (Var x T')
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case (Some p)
    obtain U u where p: "p = (U, u)" by force
    from Var.prems(2)[of x T' U u] Some p have "tsubst \<rho> T' = tsubst \<rho> U" "e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U"
      by auto
    with Var.prems(1) Some p show ?thesis by (auto simp: unf_Var[OF ac])
  qed (use Var.prems in \<open>simp add: unf_Var[OF ac]\<close>)
next
  case (Abs a U t)
  then show ?case by fastforce
next
  case (App s t)
  from App.prems(1) obtain U where "e \<turnstile> inst \<rho> s : U \<rightarrow>\<^sub>T T" "e \<turnstile> inst \<rho> t : U" by auto
  with App.IH App.prems(2) show ?case by fastforce
qed auto

lemma typing_unf:
  assumes ac: "acyc env" and wte: "wt_env \<rho> env" and vc: "vcons \<rho> (vars t \<union> evars env)"
    and nf: "nfree env"
  shows "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unf env t) : T"
proof -
  have bnd: "\<forall>e. e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using that
  proof (induction x arbitrary: U u rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof
      fix e
      show "e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U"
      proof (rule typing_unf_gen[OF ac])
        show "e \<turnstile> inst \<rho> u : tsubst \<rho> U" by (rule wt_envD[OF wte "1.prems"])
        fix y T U' u' assume y: "(y, T) \<in> vars u" and y': "vt_lookup (tenv env) y = Some (U', u')"
        have "(y, T) \<in> evars env" "(y, U') \<in> evars env"
          using evarsI2[OF "1.prems"] y evarsI[OF y'] by blast+
        then have "tsubst \<rho> T = tsubst \<rho> U'" using vconsD[OF vc nfreeD[OF nf y']] by blast
        with "1.IH"[OF depI[OF "1.prems" y] y']
        show "tsubst \<rho> T = tsubst \<rho> U' \<and> (\<forall>e. e \<turnstile> inst \<rho> (unf env u') : tsubst \<rho> U')" by blast
      qed
    qed
  qed
  show "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unf env t) : T"
  proof (rule typing_unf_gen[OF ac])
    fix x T' U u assume "(x, T') \<in> vars t" "vt_lookup (tenv env) x = Some (U, u)"
    moreover from this have "tsubst \<rho> T' = tsubst \<rho> U"
      using vconsD[OF vc nfreeD[OF nf]] evarsI by blast
    ultimately show "tsubst \<rho> T' = tsubst \<rho> U \<and> (\<forall>e. e \<turnstile> inst \<rho> (unf env u) : tsubst \<rho> U)"
      using bnd by blast
  qed
qed


subsection \<open>The measure\<close>

definition M :: "tinst \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> nat" where
  "M \<rho> env t = msz (bnorm (inst \<rho> (unf env t)))"

lemma inst_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> inst \<rho> s \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_inst)

text \<open>The measure is invariant under head normalization:\<close>

lemma M_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "e \<turnstile> inst \<rho> (unf env t) : T"
  shows "M \<rho> env t' = M \<rho> env t"
  unfolding M_def
  using bnorm_typed_reds[OF assms(4) inst_reds[OF head_norm_unf[OF assms(1) refl assms(2,3)]]] by simp

lemma M_Abs: "e \<turnstile> inst \<rho> (unf env (Abs a U t)) : T \<Longrightarrow> M \<rho> env (Abs a U t) = M \<rho> env t + 2"
  unfolding M_def by (simp add: bnorm_Abs_typed)

lemma inst_rigid: "rigid h \<Longrightarrow> rigid (inst \<rho> h)"
  by (cases h) simp_all

lemma unf_rigid: "rigid h \<Longrightarrow> unf env h = h"
  by (cases h) simp_all

lemma M_rigid:
  assumes "rigid h" "e \<turnstile> inst \<rho> (unf env (h \<degree>\<degree> ts)) : T"
  shows "M \<rho> env (h \<degree>\<degree> ts) = 1 + sum_list (map (M \<rho> env) ts)"
proof -
  have i: "inst \<rho> (unf env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> map (inst \<rho> \<circ> unf env) ts"
    using assms(1) by (simp add: unf_apps inst_apps unf_rigid)
  have r: "rigid (inst \<rho> h)" by (rule inst_rigid[OF assms(1)])
  then have at: "atom (inst \<rho> h)" by (simp add: rigid_iff)
  have "M \<rho> env (h \<degree>\<degree> ts) = msz (inst \<rho> h \<degree>\<degree> map (bnorm \<circ> inst \<rho> \<circ> unf env) ts)"
    using bnorm_atom_apps[OF at assms(2)[unfolded i]] by (simp add: M_def i comp_def)
  also have "\<dots> = 1 + sum_list (map msz (map (bnorm \<circ> inst \<rho> \<circ> unf env) ts))"
    by (rule msz_rigid_apps[OF r])
  also have "\<dots> = 1 + sum_list (map (M \<rho> env) ts)" by (simp add: M_def[abs_def] comp_def)
  finally show ?thesis .
qed

lemma M_flex:
  assumes ac: "acyc env" and "vt_lookup (tenv env) x = None" "e \<turnstile> inst \<rho> (unf env (Var x U \<degree>\<degree> ts)) : T"
  shows "M \<rho> env (Var x U \<degree>\<degree> ts) = 2 * (arity (tsubst \<rho> U) - length ts) + 1"
proof -
  have i: "inst \<rho> (unf env (Var x U \<degree>\<degree> ts)) = Var x (tsubst \<rho> U) \<degree>\<degree> map (inst \<rho> \<circ> unf env) ts"
    using assms(2) by (simp add: unf_apps inst_apps unf_Var[OF ac])
  from bnorm_atom_apps[of _ e _ T, OF _ assms(3)[unfolded i]] msz_flex_apps
  show ?thesis by (simp add: M_def i)
qed

lemma M_lift:
  assumes "acyc env" "closed_env env" "0 \<le> k" "e \<turnstile> inst \<rho> (unf env t) : T"
  shows "M \<rho> env (lift t k) = M \<rho> env t"
  unfolding M_def using bnorm_lift[OF assms(4,3)]
  by (simp add: unf_lift[OF assms(1-3)] inst_lift)

subsection \<open>Pruning\<close>

text \<open>
  A pruning binding \<open>G := \<lambda>x\<^sub>1 \<dots> x\<^sub>m. H x\<^sub>i\<^sub>1 \<dots> x\<^sub>i\<^sub>k\<close>, where \<open>G\<close> and \<open>H\<close> have the same arity
  up to the dropped arguments, does not change the size of normal forms.
\<close>

lemma vsubst_apps: "vsubst \<sigma> (s \<degree>\<degree> ts) = vsubst \<sigma> s \<degree>\<degree> map (vsubst \<sigma>) ts"
  by (induction ts arbitrary: s) simp_all

lemma size_apps_ge: "size r \<le> size (r \<degree>\<degree> rs)"
  by simp

lemma size_apps_arg: "t \<in> set ts \<Longrightarrow> size t < size (h \<degree>\<degree> ts)"
proof (induction ts arbitrary: h)
  case (Cons a ts)
  show ?case
  proof (cases "t = a")
    case True
    have "size a < size (h $ a)" by simp
    also have "\<dots> \<le> size ((h $ a) \<degree>\<degree> ts)" by (rule size_apps_ge)
    finally show ?thesis using True by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    from Cons.IH[OF this, of "h $ a"] show ?thesis by (simp del: size_apps)
  qed
qed simp

lemma msz_abs_list [simp]: "msz (abs_list bs t) = msz t + 2 * length bs"
  by (induction bs) auto

lemma bnorm_abs_list:
  "e \<turnstile> abs_list bs t : U \<Longrightarrow> \<exists>e' U'. e' \<turnstile> t : U' \<and> bnorm (abs_list bs t) = abs_list bs (bnorm t)"
proof (induction bs arbitrary: e U)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  with Cons.prems obtain U' where "e\<langle>0:T\<rangle> \<turnstile> abs_list bs t : U'" by auto
  from Cons.IH[OF this] obtain e' U'' where "e' \<turnstile> t : U''" "bnorm (abs_list bs t) = abs_list bs (bnorm t)"
    by blast
  with bnorm_Abs_typed[of e x T "abs_list bs t" U] Cons.prems b show ?case by auto
qed auto

lemma subst_abs_list_ex: "\<exists>s' k'. (abs_list bs t)[s/k] = abs_list bs (t[s'/k'])"
proof (induction bs arbitrary: s k)
  case (Cons b bs)
  obtain x T where b: "b = (x, T)" by force
  from Cons.IH[of "lift s 0" "k + 1"] b show ?case by auto
qed (auto intro: exI[of _ s] exI[of _ k])

lemma msz_flex_redex:
  "e \<turnstile> abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> vs : U \<Longrightarrow>
    msz (bnorm (abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> vs)) = 2 * (length bs + (arity Hty - length ws) - length vs) + 1"
proof (induction vs arbitrary: bs ws)
  case Nil
  from bnorm_abs_list[of e bs "Var H Hty \<degree>\<degree> ws" U] Nil obtain e' U' where
    ty: "e' \<turnstile> Var H Hty \<degree>\<degree> ws : U'"
    and b: "bnorm (abs_list bs (Var H Hty \<degree>\<degree> ws)) = abs_list bs (bnorm (Var H Hty \<degree>\<degree> ws))"
    by auto
  from bnorm_atom_apps[OF _ ty] b show ?case by (simp add: msz_flex_apps)
next
  case (Cons v vs)
  show ?case
  proof (cases bs)
    case Nil
    have eq: "abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> (v # vs) = Var H Hty \<degree>\<degree> (ws @ v # vs)"
      using Nil by simp
    have bn: "bnorm (Var H Hty \<degree>\<degree> (ws @ v # vs)) = Var H Hty \<degree>\<degree> map bnorm (ws @ v # vs)"
      by (rule bnorm_atom_apps) (use Cons.prems[unfolded eq] in simp_all)
    have "msz (bnorm (abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> (v # vs))) =
        2 * (arity Hty - length (map bnorm (ws @ v # vs))) + 1"
      unfolding eq bn by (rule msz_flex_apps)
    then show ?thesis using Nil by simp
  next
    case (Cons b bs')
    obtain x T where b: "b = (x, T)" by force
    obtain s' k' where sub: "(abs_list bs' (Var H Hty \<degree>\<degree> ws))[v/0] = abs_list bs' ((Var H Hty \<degree>\<degree> ws)[s'/k'])"
      using subst_abs_list_ex by blast
    let ?ws = "map (\<lambda>w. w[s'/k']) ws"
    have e1: "abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> (v # vs) = (Abs x T (abs_list bs' (Var H Hty \<degree>\<degree> ws)) $ v) \<degree>\<degree> vs"
      using Cons b by simp
    have e2: "(abs_list bs' (Var H Hty \<degree>\<degree> ws))[v/0] = abs_list bs' (Var H Hty \<degree>\<degree> ?ws)"
      using sub by simp
    have red: "abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> (v # vs) \<rightarrow>\<^sub>\<beta> abs_list bs' (Var H Hty \<degree>\<degree> ?ws) \<degree>\<degree> vs"
      unfolding e1 e2[symmetric] by (rule apps_preserves_beta) (rule beta.beta)
    note ty' = subject_reduction_beta[OF "Cons.prems" red]
    have "bnorm (abs_list bs' (Var H Hty \<degree>\<degree> ?ws) \<degree>\<degree> vs) = bnorm (abs_list bs (Var H Hty \<degree>\<degree> ws) \<degree>\<degree> (v # vs))"
      by (rule bnorm_typed_reds[OF "Cons.prems" r_into_rtranclp[of beta, OF red]])
    with "Cons.IH"[OF ty'] Cons show ?thesis by simp
  qed
qed

lemma no_redex_Abs_apps: "no_redex (Abs a U u \<degree>\<degree> ts) \<Longrightarrow> ts = []"
proof (induction ts rule: rev_induct)
  case (snoc y ys)
  then have "\<not> is_Abs (Abs a U u \<degree>\<degree> ys)" "no_redex (Abs a U u \<degree>\<degree> ys)" by simp_all
  with snoc.IH show ?case by simp
qed simp

definition psubst :: "indexname \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> vsubst" where
  "psubst G TG b = (\<lambda>x T. if x = G \<and> T = TG then b else Var x T)"

lemma wt_psubst: "closed b \<Longrightarrow> (\<And>e. e \<turnstile> b : TG) \<Longrightarrow> wt_subst (psubst G TG b)"
  by (auto simp: wt_subst_def closed_subst_def psubst_def closed_def)

lemma typing_Var_apps_arity: "e \<turnstile> Var x T \<degree>\<degree> ts : U \<Longrightarrow> length ts \<le> arity T"
proof -
  assume "e \<turnstile> Var x T \<degree>\<degree> ts : U"
  then obtain Ts where "e \<turnstile> Var x T : Ts \<Rrightarrow> U" "e \<tturnstile> ts : Ts" by (blast dest: list_app_typeD)
  then have "T = Ts \<Rrightarrow> U" "length ts = length Ts" using typings_nth by auto
  then show ?thesis by (simp add: arity_funs)
qed

lemma msz_prune:
  assumes b: "b = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)" "closed b" "\<And>e. e \<turnstile> b : TG"
    and ar: "arity TG = length bs + a" "arity Hty = length ks + a"
  shows "e \<turnstile> Y : T \<Longrightarrow> no_redex Y \<Longrightarrow> msz (bnorm (vsubst (psubst G TG b) Y)) = msz Y"
proof (induction Y arbitrary: e T rule: measure_induct_rule[of size])
  case (less Y)
  let ?\<pi> = "psubst G TG b"
  note wt = wt_psubst[OF b(2,3)]
  have tyY: "e \<turnstile> vsubst ?\<pi> Y : T" by (rule typing_vsubst[OF less.prems(1) wt])
  obtain h ts where Y: "Y = h \<degree>\<degree> ts" and h: "atom h \<or> (\<exists>a U u. h = Abs a U u)"
    using ex_head_tail by blast
  from h show ?case
  proof
    assume at: "atom h"
    have IH: "msz (bnorm (vsubst ?\<pi> t)) = msz t" if tin: "t \<in> set ts" for t
    proof -
      obtain U where "e \<turnstile> t : U" using typing_args[OF less.prems(1)[unfolded Y] tin] by blast
      moreover have "\<not> is_Abs h" using at by (cases h) simp_all
      then have "no_redex t" using less.prems(2) Y tin by (simp add: no_redex_apps)
      moreover have "size t < size Y" using Y tin size_apps_arg by blast
      ultimately show ?thesis using less.IH by blast
    qed
    have IHs: "map (\<lambda>t. msz (bnorm (vsubst ?\<pi> t))) ts = map msz ts"
      by (rule map_cong[OF refl]) (rule IH)
    show ?thesis
    proof (cases "rigid h")
      case True
      have v: "vsubst ?\<pi> (h \<degree>\<degree> ts) = h \<degree>\<degree> map (vsubst ?\<pi>) ts"
        using True by (cases h) (simp_all add: vsubst_apps)
      have "bnorm (vsubst ?\<pi> (h \<degree>\<degree> ts)) = h \<degree>\<degree> map bnorm (map (vsubst ?\<pi>) ts)"
        unfolding v by (rule bnorm_atom_apps[OF at]) (use tyY Y v in simp)
      then have "msz (bnorm (vsubst ?\<pi> (h \<degree>\<degree> ts))) = 1 + sum_list (map msz (map bnorm (map (vsubst ?\<pi>) ts)))"
        by (simp only: msz_rigid_apps[OF True])
      also have "\<dots> = msz (h \<degree>\<degree> ts)" by (simp only: map_map comp_def IHs msz_rigid_apps[OF True])
      finally show ?thesis using Y by simp
    next
      case False
      with at obtain x U where hx: "h = Var x U" by (cases h) simp_all
      show ?thesis
      proof (cases "x = G \<and> U = TG")
        case True
        have v: "vsubst ?\<pi> (h \<degree>\<degree> ts) = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks) \<degree>\<degree> map (vsubst ?\<pi>) ts"
          using True hx b(1) by (simp add: vsubst_apps psubst_def)
        have ty: "e \<turnstile> abs_list bs (Var H Hty \<degree>\<degree> map Bound ks) \<degree>\<degree> map (vsubst ?\<pi>) ts : T"
          using tyY Y v by simp
        have "length ts \<le> arity TG" using typing_Var_apps_arity less.prems(1) Y hx True by blast
        moreover have "msz (bnorm (vsubst ?\<pi> (h \<degree>\<degree> ts))) =
            2 * (length bs + (arity Hty - length (map Bound ks)) - length (map (vsubst ?\<pi>) ts)) + 1"
          unfolding v by (rule msz_flex_redex[OF ty])
        ultimately show ?thesis using ar Y hx True by (simp add: msz_flex_apps)
      next
        case False
        have v: "vsubst ?\<pi> (h \<degree>\<degree> ts) = Var x U \<degree>\<degree> map (vsubst ?\<pi>) ts"
          using False hx by (auto simp: vsubst_apps psubst_def)
        have "bnorm (vsubst ?\<pi> (h \<degree>\<degree> ts)) = Var x U \<degree>\<degree> map bnorm (map (vsubst ?\<pi>) ts)"
          unfolding v by (rule bnorm_atom_apps) (use tyY Y v in simp_all)
        then show ?thesis using Y hx by (simp only: msz_flex_apps length_map)
      qed
    qed
  next
    assume "\<exists>a U u. h = Abs a U u"
    then obtain a U u where hu: "h = Abs a U u" by blast
    with less.prems(2) Y have ts: "ts = []" using no_redex_Abs_apps by blast
    with less.prems(1) Y hu obtain V where "e\<langle>0:U\<rangle> \<turnstile> u : V" by auto
    moreover have "no_redex u" using less.prems(2) Y hu ts by simp
    moreover have "size u < size Y" using Y hu ts by simp
    ultimately have "msz (bnorm (vsubst ?\<pi> u)) = msz u" using less.IH by blast
    moreover have "e \<turnstile> Abs a U (vsubst ?\<pi> u) : T" using tyY Y hu ts by simp
    ultimately show ?thesis using Y hu ts by (simp add: bnorm_Abs_typed)
  qed
qed

lemma vsubst_vsubst: "vsubst \<sigma> (vsubst \<tau> t) = vsubst (\<lambda>x T. vsubst \<sigma> (\<tau> x T)) t"
  by (induction t) simp_all

lemma vars_unf_sub: "acyc env \<Longrightarrow> vars (unf env t) \<subseteq> vars t \<union> evars env"
proof -
  assume ac: "acyc env"
  have "vars (unf env (Var x T)) \<subseteq> insert (x, T) (evars env)" for x T
  proof (induction x arbitrary: T rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have IH: "vars (unf env (Var y T')) \<subseteq> insert (y, T') (evars env)" if "(y, T') \<in> vars u" for y T'
        using "1.IH"[OF depI[OF Some[unfolded p] that]] .
      have vu: "vars u \<subseteq> evars env" using evarsI2[OF Some[unfolded p]] .
      have eq: "vars (unf env (Var x T)) = (\<Union>(y, T')\<in>vars u. vars (unf env (Var y T')))"
        by (subst unf_Var[OF ac]) (simp add: Some p vars_unf[of env u])
      show ?thesis
      proof
        fix q assume "q \<in> vars (unf env (Var x T))"
        with eq obtain y T' where yu: "(y, T') \<in> vars u" and q: "q \<in> vars (unf env (Var y T'))" by blast
        from IH[OF yu] q have "q \<in> insert (y, T') (evars env)" by blast
        with yu vu show "q \<in> insert (x, T) (evars env)" by blast
      qed
    qed (simp add: unf_Var[OF ac])
  qed
  then show ?thesis by (auto simp: vars_unf[of env t])
qed

lemma beta_reds_vsubst: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> closed_subst \<sigma> \<Longrightarrow> vsubst \<sigma> s \<rightarrow>\<^sub>\<beta>\<^sup>* vsubst \<sigma> t"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_vsubst)

text \<open>A single pruning binding:\<close>

lemma unf_prune:
  assumes upd: "ok (update (G, Gty) b env) env1" and ac: "acyc env" "acyc env1"
    and b: "unf env1 b = b"
  shows "unf env1 t = vsubst (\<lambda>x T. if x = G then b else Var x T) (unf env t)"
proof -
  let ?\<pi> = "\<lambda>x T. if x = G then b else Var x T"
  note u = ok_update[OF upd]
  have lk1: "vt_lookup (tenv env1) x = (if x = G then Some (Gty, b) else vt_lookup (tenv env) x)" for x
    using u(2) by simp
  have Var: "unf env1 (Var x T) = vsubst ?\<pi> (unf env (Var x T))" for x T
  proof (induction x arbitrary: T rule: dep_induct[OF ac(1)])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have xG: "x \<noteq> G" using u(1) Some by auto
      have "unf env1 u = vsubst (\<lambda>y T'. vsubst ?\<pi> (unf env (Var y T'))) u"
        unfolding unf_def
        by (rule vsubst_cong) (use "1.IH"[OF depI[OF Some[unfolded p]]] in \<open>simp add: unf_def\<close>)
      also have "\<dots> = vsubst ?\<pi> (unf env u)" by (simp add: unf_def vsubst_vsubst)
      finally show ?thesis using Some p xG by (simp add: unf_Var[OF ac(2)] unf_Var[OF ac(1)] lk1)
    next
      case None
      then show ?thesis using b by (simp add: unf_Var[OF ac(2)] unf_Var[OF ac(1)] lk1)
    qed
  qed
  have "usubst env1 x T = vsubst ?\<pi> (usubst env x T)" for x T using Var[of x T] by (simp add: unf_def)
  then show ?thesis by (simp add: unf_def vsubst_vsubst)
qed

lemma inst_vsubst_prune:
  "(\<And>T. (G, T) \<in> vars X \<Longrightarrow> tsubst \<rho> T = TG) \<Longrightarrow>
    inst \<rho> (vsubst (\<lambda>x T. if x = G then b else Var x T) X) = vsubst (psubst G TG (inst \<rho> b)) (inst \<rho> X)"
  by (induction X) (auto simp: psubst_def)

lemma M_prune:
  assumes upd: "ok (update (G, Gty) b env) env1"
    and b: "b = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)"
    and ac: "acyc env" "acyc env1" and cl: "closed_env env" "closed b"
    and H: "vt_lookup (tenv env1) H = None"
    and tyb: "\<And>e. e \<turnstile> inst \<rho> b : tsubst \<rho> Gty"
    and ar: "arity (tsubst \<rho> Gty) = length bs + a" "arity (tsubst \<rho> Hty) = length ks + a"
    and wte: "wt_env \<rho> env" and vc: "vcons \<rho> (vars t \<union> evars env1)" and ty: "e \<turnstile> inst \<rho> t : T"
    and nf: "nfree env1"
  shows "M \<rho> env1 t = M \<rho> env t"
proof -
  let ?TG = "tsubst \<rho> Gty" and ?b = "inst \<rho> b"
  let ?\<pi> = "psubst G ?TG ?b"
  have ub: "unf env1 b = b" using H b by (simp add: unf_def vsubst_abs_list vsubst_apps uval_eq[OF ac(2)] comp_def)
  have Gin: "(G, Gty) \<in> evars env1" using evars_update[OF upd] by simp
  have ev: "evars env \<subseteq> evars env1" using evars_update[OF upd] by blast
  have Gl: "G \<notin> loose" using nfreeD[OF nf, of G] ok_update(2)[OF upd] by simp
  have nf0: "nfree env" unfolding nfree_def
  proof (intro allI impI)
    fix x b' assume x: "vt_lookup (tenv env) x = Some b'"
    with ok_update(1)[OF upd] have "x \<noteq> G" by auto
    with x ok_update(2)[OF upd] have "vt_lookup (tenv env1) x = Some b'" by simp
    then show "x \<notin> loose" by (rule nfreeD[OF nf])
  qed
  have G: "tsubst \<rho> T' = ?TG" if "(G, T') \<in> vars (unf env t)" for T'
  proof -
    have "(G, T') \<in> vars t \<union> evars env1" using vars_unf_sub[OF ac(1)] that ev by blast
    with Gin show ?thesis using vconsD[OF vc Gl] by blast
  qed
  have Y: "inst \<rho> (unf env1 t) = vsubst ?\<pi> (inst \<rho> (unf env t))"
    by (simp add: unf_prune[OF upd ac ub] inst_vsubst_prune[OF G])
  have tyY: "e \<turnstile> inst \<rho> (unf env t) : T"
    by (rule typing_unf[OF ac(1) wte vcons_mono[OF vc] nf0 ty]) (use ev in blast)
  have wt: "wt_subst ?\<pi>" by (rule wt_psubst) (use cl(2) tyb in \<open>simp_all add: closed_def\<close>)
  note n = bnorm_typed[OF tyY]
  have cs: "closed_subst ?\<pi>" using wt by (simp add: wt_subst_def)
  have "bnorm (vsubst ?\<pi> (bnorm (inst \<rho> (unf env t)))) = bnorm (vsubst ?\<pi> (inst \<rho> (unf env t)))"
    by (rule bnorm_typed_reds[OF typing_vsubst[OF tyY wt] beta_reds_vsubst[OF conjunct1[OF n] cs]])
  moreover have "msz (bnorm (vsubst ?\<pi> (bnorm (inst \<rho> (unf env t))))) = msz (bnorm (inst \<rho> (unf env t)))"
  proof (rule msz_prune)
    show "?b = abs_list (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) (Var H (tsubst \<rho> Hty) \<degree>\<degree> map Bound ks)"
      by (simp add: b inst_abs_list inst_apps comp_def)
    show "closed ?b" using cl(2) by (simp add: closed_def)
    show "e' \<turnstile> ?b : ?TG" for e' by (rule tyb)
    show "arity ?TG = length (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) + a" using ar by simp
    show "arity (tsubst \<rho> Hty) = length ks + a" by (rule ar(2))
    show "e \<turnstile> bnorm (inst \<rho> (unf env t)) : T" by (rule subject_reduction_beta'[OF conjunct1[OF n] tyY])
    show "no_redex (bnorm (inst \<rho> (unf env t)))" using n by blast
  qed
  ultimately show ?thesis by (simp add: M_def Y)
qed

text \<open>Environments and their extensions:\<close>

lemma wt_env_extends: "wt_env \<rho> env' \<Longrightarrow> extends env env' \<Longrightarrow> wt_env \<rho> env"
  unfolding wt_env_def extends_def by blast

lemma evars_extends: "extends env env' \<Longrightarrow> evars env \<subseteq> evars env'"
  unfolding evars_def bnds_def extends_def by blast

end

subsection \<open>Without loose names\<close>

context pure_sig
begin

lemma typing_unf:
  assumes ac: "acyc env" and wte: "wt_env \<rho> env" and vc: "vcons \<rho> (vars t \<union> evars env)"
  shows "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unf env t) : T"
  by (rule typing_unf[OF assms nfree0])

lemma M_prune:
  assumes upd: "ok (update (G, Gty) b env) env1"
    and b: "b = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)"
    and ac: "acyc env" "acyc env1" and cl: "closed_env env" "closed b"
    and H: "vt_lookup (tenv env1) H = None"
    and tyb: "\<And>e. e \<turnstile> inst \<rho> b : tsubst \<rho> Gty"
    and ar: "arity (tsubst \<rho> Gty) = length bs + a" "arity (tsubst \<rho> Hty) = length ks + a"
    and wte: "wt_env \<rho> env" and vc: "vcons \<rho> (vars t \<union> evars env1)" and ty: "e \<turnstile> inst \<rho> t : T"
  shows "M \<rho> env1 t = M \<rho> env t"
  by (rule M_prune[OF assms nfree0])

end

end
