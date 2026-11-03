section \<open>A Size Measure for Unification Problems\<close>

theory Pattern_Size
  imports Pattern_Acyclic Pattern_Normal
begin

text \<open>
  Unification problems are measured by the size of the \<open>\<beta>\<close>-normal form of their instance under
  the environment. A flexible term \<open>F t\<^sub>1 \<dots> t\<^sub>k\<close> counts as the \<open>\<eta>\<close>-expansion of \<open>F\<close> to its
  arity, without its arguments, so that pruning bindings do not change the size (after Grobauer).
\<close>

context pure_sig
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

lemma no_redex_lift: "no_redex (lift t k) \<longleftrightarrow> no_redex t"
proof (induction t arbitrary: k)
  case (App s t)
  then show ?case by (cases s) auto
qed auto

lemma bnorm_lift: "e \<turnstile> t : T \<Longrightarrow> 0 \<le> k \<Longrightarrow> bnorm (lift t k) = lift (bnorm t) k"
proof (rule bnorm_eqI)
  assume "e \<turnstile> t : T" "0 \<le> k"
  then have "t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t" "no_redex (bnorm t)" using bnorm_typed by blast+
  have "lift t k \<rightarrow>\<^sub>\<beta>\<^sup>* lift u k" if "t \<rightarrow>\<^sub>\<beta>\<^sup>* u" for u
    using that by (induction rule: rtranclp_induct)
      (auto intro: rtranclp.rtrancl_into_rtrancl simp: \<open>0 \<le> k\<close>)
  with \<open>t \<rightarrow>\<^sub>\<beta>\<^sup>* bnorm t\<close> \<open>no_redex (bnorm t)\<close>
  show "lift t k \<rightarrow>\<^sub>\<beta>\<^sup>* lift (bnorm t) k" "no_redex (lift (bnorm t) k)"
    by (simp_all add: no_redex_lift)
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

definition rigid :: "pterm \<Rightarrow> bool" where
  "rigid h \<longleftrightarrow> atom h \<and> \<not> is_Var h"

lemma rigid_simps [simp]:
  "rigid (Const c T)" "rigid (Free y T)" "rigid (Bound i)" "\<not> rigid (Var x T)"
  "\<not> rigid (Abs a T t)" "\<not> rigid (s $ t)"
  by (simp_all add: rigid_def)

lemma msz_rigid_apps: "rigid h \<Longrightarrow> msz (h \<degree>\<degree> ts) = 1 + sum_list (map msz ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) (simp_all add: rigid_def)
next
  case (snoc t ts)
  have "\<not> is_Var (dhd h)" using snoc.prems by (cases h) (simp_all add: rigid_def)
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
        then have "tsubst \<rho> T = tsubst \<rho> U'" using vconsD[OF vc] by blast
        with "1.IH"[OF depI[OF "1.prems" y] y']
        show "tsubst \<rho> T = tsubst \<rho> U' \<and> (\<forall>e. e \<turnstile> inst \<rho> (unf env u') : tsubst \<rho> U')" by blast
      qed
    qed
  qed
  show "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unf env t) : T"
  proof (rule typing_unf_gen[OF ac])
    fix x T' U u assume "(x, T') \<in> vars t" "vt_lookup (tenv env) x = Some (U, u)"
    moreover from this have "tsubst \<rho> T' = tsubst \<rho> U"
      using vconsD[OF vc] evarsI by blast
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
  then have at: "atom (inst \<rho> h)" by (simp add: rigid_def)
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

end

end
