section \<open>Unfolding with Type Checks\<close>

theory Pattern_Unfc
  imports Pattern_Term_Unif
begin


text \<open>
  The termination proofs measure terms by their unfolding (\<open>unf\<close>), which applies the
  bindings to every occurrence of a bound name, whatever its type. With names at two types, the
  occurrences at another type make the unfolding ill-typed; but \<open>lookup\<close> follows a binding only
  if the types agree modulo the type environment, and raises otherwise. \<open>unfc\<close> unfolds exactly
  those occurrences (\<open>unified\<close>, as \<open>lookup\<close>), so its results are well-typed at every solution of the type environment,
  with no hypothesis on the names.
\<close>

context pure_sig_gen
begin

definition cval :: "env \<Rightarrow> (indexname \<Rightarrow> (ptyp \<times> pterm) option) \<Rightarrow> vsubst" where
  "cval env f y T = (case f y of
     Some (U, v) \<Rightarrow> if ok (unified (tyenv env) T U) True then v else Var y T
   | None \<Rightarrow> Var y T)"

definition uvalc_step :: "env \<Rightarrow> (indexname \<Rightarrow> (ptyp \<times> pterm) option) \<Rightarrow> indexname \<Rightarrow> (ptyp \<times> pterm) option" where
  "uvalc_step env f x = (case vt_lookup (tenv env) x of
     Some (U, u) \<Rightarrow> Some (U, vsubst (cval env f) u)
   | None \<Rightarrow> None)"

definition uvalc :: "env \<Rightarrow> indexname \<Rightarrow> (ptyp \<times> pterm) option" where
  "uvalc env = wfrec (dep env) (uvalc_step env)"

definition unfc :: "env \<Rightarrow> pterm \<Rightarrow> pterm" where
  "unfc env = vsubst (cval env (uvalc env))"

lemma adm_uvalc_step: "adm_wf (dep env) (uvalc_step env)"
  unfolding adm_wf_def
proof (intro allI impI)
  fix f g :: "indexname \<Rightarrow> (ptyp \<times> pterm) option" and x
  assume eq: "\<forall>y. (y, x) \<in> dep env \<longrightarrow> f y = g y"
  show "uvalc_step env f x = uvalc_step env g x"
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    have "vsubst (cval env f) u = vsubst (cval env g) u"
    proof (rule vsubst_cong)
      fix y T' assume "(y, T') \<in> vars u"
      then have "f y = g y" using eq depI[OF Some[unfolded b]] by blast
      then show "cval env f y T' = cval env g y T'" by (simp add: cval_def)
    qed
    with Some b show ?thesis by (simp add: uvalc_step_def)
  qed (simp add: uvalc_step_def)
qed

lemma unfc_simps [simp]:
  "unfc env (Abs a T t) = Abs a T (unfc env t)"
  "unfc env (s $ t) = unfc env s $ unfc env t"
  "unfc env (Const c T) = Const c T"
  "unfc env (Free y T) = Free y T"
  "unfc env (Bound i) = Bound i"
  by (simp_all add: unfc_def)

lemma unfc_apps: "unfc env (h \<degree>\<degree> ts) = unfc env h \<degree>\<degree> map (unfc env) ts"
  by (induction ts arbitrary: h) simp_all

context
  fixes env assumes ac: "acyc env"
begin

lemma uvalc_eq:
  "uvalc env x = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> Some (U, unfc env u) | None \<Rightarrow> None)"
  unfolding uvalc_def
  by (subst wfrec_fixpoint[OF wf_dep[OF ac] adm_uvalc_step])
    (simp add: uvalc_step_def unfc_def uvalc_def split: option.splits)

lemma unfc_Var:
  "unfc env (Var x T) = (case vt_lookup (tenv env) x of
     Some (U, u) \<Rightarrow> if ok (unified (tyenv env) T U) True then unfc env u else Var x T
   | None \<Rightarrow> Var x T)"
  by (simp add: unfc_def cval_def uvalc_eq[unfolded unfc_def] split: option.splits)

lemma unfc_Var_bound:
  "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ok (unified (tyenv env) T U) True \<Longrightarrow>
    unfc env (Var x T) = unfc env u"
  by (simp add: unfc_Var)

lemma unfc_Var_other:
  "(\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> \<not> ok (unified (tyenv env) T U) True) \<Longrightarrow>
    unfc env (Var x T) = Var x T"
  by (auto simp: unfc_Var split: option.splits)

text \<open>The values are closed if the bindings are:\<close>

lemma closed_cval:
  assumes cl: "closed_env env"
  shows "closed_subst (cval env (uvalc env))"
proof -
  have "closed (unfc env u)" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using that
  proof (induction x arbitrary: U u rule: dep_induct[OF ac])
    case (1 x)
    have "closed (cval env (uvalc env) y T)" if "(y, T) \<in> vars u" for y T
    proof (cases "vt_lookup (tenv env) y")
      case (Some b)
      obtain U' u' where b: "b = (U', u')" by force
      have "(y, x) \<in> dep env" by (rule depI[OF "1.prems" that])
      from "1.IH"[OF this Some[unfolded b]] Some b show ?thesis
        by (simp add: cval_def uvalc_eq closed_def)
    qed (simp add: cval_def uvalc_eq closed_def)
    moreover have "closed u" using cl "1.prems" unfolding closed_env_def by blast
    ultimately show ?case
      unfolding unfc_def closed_def by (subst loose_bvar_vsubst_on) (simp_all add: closed_def)
  qed
  then show ?thesis
    by (auto simp: closed_subst_def cval_def uvalc_eq closed_def split: option.splits)
qed

lemma unfc_subst:
  "closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> unfc env (t[s/k]) = (unfc env t)[unfc env s/k]"
  unfolding unfc_def using closed_cval by simp

lemma unfc_lift:
  "closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> unfc env (incr_bv n k t) = incr_bv n k (unfc env t)"
  unfolding unfc_def using closed_cval by simp

lemma loose_bvar_unfc:
  "closed_env env \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (unfc env t) k \<longleftrightarrow> loose_bvar t k"
  unfolding unfc_def by (rule loose_bvar_vsubst_on) (use closed_cval in \<open>auto simp: closed_subst_def\<close>)

text \<open>Typing, at every solution of the type environment and with no hypothesis on the names:\<close>


lemma typing_unfc:
  assumes wte: "wt_env \<rho> env" and ts: "tsol (tyenv env) \<rho>"
  shows "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unfc env t) : T"
proof -
  have bnd: "\<forall>e. e \<turnstile> inst \<rho> (unfc env u) : tsubst \<rho> U" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using that
  proof (induction x arbitrary: U u rule: dep_induct[OF ac])
    case (1 x)
    have tm: "e \<turnstile> inst \<rho> (unfc env s) : S" if "e \<turnstile> inst \<rho> s : S" "vars s \<subseteq> vars u" for e s S
      using that
    proof (induction s arbitrary: e S)
      case (Var y T')
      show ?case
      proof (cases "vt_lookup (tenv env) y")
        case (Some b)
        obtain U' u' where b: "b = (U', u')" by force
        show ?thesis
        proof (cases "ok (unified (tyenv env) T' U') True")
          case True
          have "(y, x) \<in> dep env" using depI[OF "1.prems"] Var.prems(2) by auto
          from "1.IH"[OF this Some[unfolded b]] have "e \<turnstile> inst \<rho> (unfc env u') : tsubst \<rho> U'" by blast
          moreover have "S = tsubst \<rho> T'" using Var.prems(1) by auto
          moreover have "tsubst \<rho> T' = tsubst \<rho> U'" by (rule unified_sound[OF True ts])
          ultimately show ?thesis using Some b True by (simp add: unfc_Var)
        qed (use Some b Var.prems in \<open>simp add: unfc_Var\<close>)
      qed (use Var.prems in \<open>simp add: unfc_Var\<close>)
    next
      case (App s1 s2)
      then show ?case by fastforce
    qed fastforce+
    from wt_envD[OF wte "1.prems"] show ?case by (blast intro: tm)
  qed
  show "e \<turnstile> inst \<rho> t : T \<Longrightarrow> e \<turnstile> inst \<rho> (unfc env t) : T"
  proof (induction t arbitrary: e T)
    case (Var y T')
    show ?case
    proof (cases "vt_lookup (tenv env) y")
      case (Some b)
      obtain U' u' where b: "b = (U', u')" by force
      show ?thesis
      proof (cases "ok (unified (tyenv env) T' U') True")
        case True
        have "T = tsubst \<rho> T'" using Var.prems by auto
        moreover have "tsubst \<rho> T' = tsubst \<rho> U'" by (rule unified_sound[OF True ts])
        ultimately show ?thesis using bnd[OF Some[unfolded b]] Some b True by (simp add: unfc_Var)
      qed (use Some b Var.prems in \<open>simp add: unfc_Var\<close>)
    qed (use Var.prems in \<open>simp add: unfc_Var\<close>)
  next
    case (App s1 s2)
    then show ?case by fastforce
  qed fastforce+
qed

end


subsection \<open>Head normalization\<close>

lemma ok_lookup_Some_unified:
  assumes "ok (lookup env x T) (Some u)"
  obtains U where "vt_lookup (tenv env) x = Some (U, u)" "ok (unified (tyenv env) T U) True"
  using assms by (rule ok_lookup_Some)

lemma head_norm_unfc:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow> unfc env t \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  note ac = "1.prems"(2) and cl = "1.prems"(3)
  have IH: "unfc env u \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env u'" if "ok (hn env u) u'" for u u'
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
      with lr obtain U where "vt_lookup (tenv env) x = Some (U, u)" "ok (unified (tyenv env) T U) True"
        by (auto elim: ok_lookup_Some_unified)
      with IH[of u t'] rest Some Var show ?thesis by (simp add: unfc_Var_bound[OF ac])
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (hn env body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    have redex: "unfc env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env t'"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
    proof -
      have "unfc env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta> unfc env (body[u/0])"
        by (simp add: unfc_subst[OF ac cl])
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
      have fu: "unfc env (f $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env (nf $ u)" using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded Abs] redex[OF this]] App show ?thesis by simp
      qed (use rest fu App in auto)
    qed
  qed (use h in auto)
qed

text \<open>
  Head normalization is defined (it returns or raises) if the unfolding with type checks is
  strongly normalizing and the types are consistent with the type environment; no hypothesis on
  the names. An occurrence of a bound name at another type raises.
\<close>

definition tok :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "tok env X \<longleftrightarrow> (\<forall>(x, T)\<in>X. tcons (tyenv env) T \<and>
    (x \<notin> loose \<longrightarrow> (\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> tnorm (tyenv env) T = tnorm (tyenv env) U)))"

lemma tok_mono: "tok env X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> tok env Y"
  unfolding tok_def by blast

lemma tok_tcons: "tok env X \<Longrightarrow> (x, T) \<in> X \<Longrightarrow> tcons (tyenv env) T"
  unfolding tok_def by blast

text \<open>A lookup at a type that differs from that of the binding is a lookup of a loose name:\<close>

lemma tok_clash_loose:
  assumes "tok env X" "(x, T) \<in> X" "vt_lookup (tenv env) x = Some (U, u)"
    and "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U"
  shows "x \<in> loose"
  using assms unfolding tok_def by blast

lemma tok_clash_ne:
  assumes "tok env X" "(x, T) \<in> X" "vt_lookup (tenv env) x = Some (U, u)"
    and "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U"
  shows "loose \<noteq> {}"
  using tok_clash_loose[OF assms] by blast

text \<open>
  The condition holds for the variables that have one type in the most general solution of the
  type environment, together with the variables of the bindings:
\<close>

lemma tokI:
  assumes "\<And>x T. (x, T) \<in> X \<Longrightarrow> tcons (tyenv env) T" and "vcons (tnorm_inst (tyenv env)) (X \<union> evars env)"
  shows "tok env X"
proof -
  have "tnorm (tyenv env) T = tnorm (tyenv env) U"
    if xT: "(x, T) \<in> X" and x: "x \<notin> loose" and b: "vt_lookup (tenv env) x = Some (U, u)" for x T U u
  proof -
    have "(x, U) \<in> evars env" using b unfolding evars_def bnds_def by (cases x) blast
    then have eq: "tsubst (tnorm_inst (tyenv env)) T = tsubst (tnorm_inst (tyenv env)) U"
      using assms(2) xT x unfolding vcons_def by blast
    show ?thesis by (subst (1 2) tnorm_tsubst) (rule eq)
  qed
  then show ?thesis using assms(1) unfolding tok_def by blast
qed

lemma lookup_def_tok:
  assumes tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)" and t: "tok env ({(x, T)} \<union> evars env)"
  shows "lookup env x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
    | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
proof (cases "vt_lookup (tenv env) x")
  case (Some b)
  obtain U u where b: "b = (U, u)" by force
  have "(x, U) \<in> evars env" using Some b unfolding evars_def bnds_def by (cases x) blast
  then have "tcons (tyenv env) T" "tcons (tyenv env) U" using t by (auto dest: tok_tcons)
  from unified_ok[OF tac tc this] Some b show ?thesis
    by (simp add: lookup_def return_def bindM_def var_clash_def raise_def)
qed (simp add: lookup_def)

subsection \<open>Definedness\<close>

text \<open>
  \<open>dfd m\<close>: the computation \<open>m\<close> terminates, and if it raises an exception, then the
  exception is the one of \<open>var_clash\<close> (an occurrence of a bound name at a type that differs
  from that of the binding).
\<close>

definition clashx :: "exn \<Rightarrow> bool" where
  "clashx e \<longleftrightarrow> loose \<noteq> {} \<and> (\<exists>ts. e = Type_Error (STR ''Variable has two distinct types'') [] ts)"

definition dfd :: "'a M \<Rightarrow> bool" where
  "dfd m \<longleftrightarrow> m \<noteq> None \<and> (\<forall>e. m = Some (Err e) \<longrightarrow> clashx e)"

lemma clashxI: "loose \<noteq> {} \<Longrightarrow> clashx (Type_Error (STR ''Variable has two distinct types'') [] ts)"
  by (simp add: clashx_def)

lemma clashx_loose: "clashx e \<Longrightarrow> loose \<noteq> {}"
  by (simp add: clashx_def)

lemma dfd_Ok [simp]: "dfd (Some (Ok x))" and dfd_Err [simp]: "dfd (Some (Err e)) \<longleftrightarrow> clashx e"
  and dfd_None [simp]: "\<not> dfd None"
  by (simp_all add: dfd_def)

lemma dfd_return [simp]: "dfd (return x)"
  by (simp add: return_def)

lemma dfd_raise [simp]: "dfd (raise e) \<longleftrightarrow> clashx e"
  by (simp add: raise_def)

lemma dfd_cases: "dfd m \<Longrightarrow> (\<And>x. m = Some (Ok x) \<Longrightarrow> P) \<Longrightarrow> (\<And>e. m = Some (Err e) \<Longrightarrow> clashx e \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding dfd_def by (cases m) (auto, metis xres.exhaust)

lemma dfd_bindM: "dfd m \<Longrightarrow> (\<And>x. m = Some (Ok x) \<Longrightarrow> dfd (f x)) \<Longrightarrow> dfd (bindM m f)"
  by (erule dfd_cases) (auto simp: bindM_def)

lemma dfd_var_clash: "x \<in> loose \<Longrightarrow> dfd (var_clash x T U)"
  by (auto simp: var_clash_def clashx_def)

lemma head_norm_def:
  assumes ac: "acyc env" and cl: "closed_env env"
    and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfd (head_norm env t)"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_sn_less wf_less_than],
    of "\<lambda>t. (unfc env t, hrk env t)"]])
  case (1 t)
  have sn: "termip (sup beta subt) u" if "(sup beta subt)\<^sup>*\<^sup>* (unfc env t) u" for u
    by (rule termip_sup_reds[OF that "1.prems"(2)])
  have IH: "dfd (head_norm env u)"
    if "tok env (vars u \<union> evars env)" "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t) (unfc env u)" for u
  proof (rule "1.IH"[OF _ that(1)])
    have "(unfc env u, unfc env t) \<in> sn_less"
      by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use that(2) "1.prems"(2) in blast)
    then show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unfc env t, hrk env t))"
      by simp
    show "termip (sup beta subt) (unfc env u)" by (rule sn[OF tranclp_into_rtranclp[OF that(2)]])
  qed
  have IH': "dfd (head_norm env u)"
    if "tok env (vars u \<union> evars env)" "unfc env u = unfc env t" "hrk env u < hrk env t" for u
  proof (rule "1.IH"[OF _ that(1)])
    show "(u, t) \<in> inv_image (sn_less <*lex*> less_than) (\<lambda>t. (unfc env t, hrk env t))"
      using that(2,3) by simp
    show "termip (sup beta subt) (unfc env u)" by (subst that(2)) (rule "1.prems"(2))
  qed
  have vk: "tok env (vars u \<union> evars env)" if "vars u \<subseteq> vars t \<union> evars env" for u
    using "1.prems"(1) that by (auto intro: tok_mono)
  have redex: "dfd (head_norm env (subst_bound u body))"
    if "(sup beta subt)\<^sup>*\<^sup>* (unfc env t) (unfc env (Abs b U body $ u))" "vars body \<union> vars u \<subseteq> vars t \<union> evars env"
    for b U body u
  proof (subst subst_bound_subst, rule IH)
    have r: "unfc env (Abs b U body $ u) \<rightarrow>\<^sub>\<beta> unfc env (body[u/0])"
      by (simp add: unfc_subst[OF ac cl])
    then show "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t) (unfc env (body[u/0]))"
      using that(1) by (meson rtranclp_into_tranclp1 sup2I1)
    show "tok env (vars (body[u/0]) \<union> evars env)"
      using vk vars_subst[of body u 0] that(2) by blast
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    have lk: "lookup env x T = (case vt_lookup (tenv env) x of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash x T U)"
      by (rule lookup_def_tok[OF tac tc tok_mono[OF "1.prems"(1)]]) (auto simp: Var)
    have cl: "loose \<noteq> {}" if "vt_lookup (tenv env) x = Some (U, u)" "tnorm (tyenv env) T \<noteq> tnorm (tyenv env) U" for U u
      by (rule tok_clash_ne[OF "1.prems"(1) _ that]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have tcU: "tcons (tyenv env) T" "tcons (tyenv env) U"
      proof -
        have "(x, U) \<in> evars env" using Some p unfolding evars_def bnds_def by (cases x) blast
        then show "tcons (tyenv env) T" "tcons (tyenv env) U" using "1.prems"(1) Var by (auto simp: tok_def)
      qed
      have ue: "ok (unified (tyenv env) T U) True \<longleftrightarrow> tnorm (tyenv env) T = tnorm (tyenv env) U"
        using unified_ok[OF tac tc tcU] by (simp add: return_def)
      show ?thesis
      proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
        case True
        have u: "unfc env u = unfc env t" using Some p Var True ue by (simp add: unfc_Var_bound[OF ac])
        have "hrk env u < hrk env t"
        proof (cases u)
          case (Var y U')
          have "(y, x) \<in> dep env" using depI[OF Some[unfolded p], of y U'] Var by simp
          then show ?thesis using rk_less[OF ac] Var \<open>t = Var x T\<close> by (simp add: hrk_def)
        qed (simp_all add: hrk_def \<open>t = Var x T\<close>)
        moreover have "vars u \<subseteq> vars t \<union> evars env" using evarsI2[OF Some[unfolded p]] by blast
        ultimately have "dfd (head_norm env u)"
          using IH'[of u] vk u by blast
        then show ?thesis using lk Var Some p True by (subst head_norm.simps) (simp add: return_def bindM_def)
      next
        case False
        then show ?thesis using lk Var Some p cl[OF Some[unfolded p] False]
          by (subst head_norm.simps) (simp add: var_clash_def raise_def bindM_def clashx_def)
      qed
    qed (use lk Var in \<open>subst head_norm.simps, simp add: return_def bindM_def\<close>)
  next
    case (Abs a T body)
    have "subt (unfc env t) (unfc env body)" using Abs by (simp add: subt_def)
    then have "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t) (unfc env body)" by blast
    moreover have "tok env (vars body \<union> evars env)" by (rule vk) (use Abs in simp)
    ultimately have rb: "dfd (head_norm env body)" using IH[of body] by blast
    show "dfd (head_norm env t)"
      using rb Abs by (subst head_norm.simps) (auto intro!: dfd_bindM)
  next
    case (App f u)
    have vfu: "vars f \<union> vars u \<subseteq> vars t \<union> evars env" using App by auto
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      from redex[of b U body u] f App vfu show ?thesis by (subst head_norm.simps) simp
    next
      case False
      have "subt (unfc env t) (unfc env f)" using App by (simp add: subt_def)
      then have tf: "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t) (unfc env f)" by blast
      moreover have "tok env (vars f \<union> evars env)" using vk vfu by blast
      ultimately have df: "dfd (head_norm env f)" using IH[of f] by blast
      have hn: "head_norm env t = bindM (head_norm env f)
          (\<lambda>nf. case nf of Abs _ _ body \<Rightarrow> head_norm env (subst_bound u body) | _ \<Rightarrow> return (nf $ u))"
        using App False by (subst head_norm.simps) (cases f; simp)
      show ?thesis
      proof (rule dfd_cases[OF df])
        fix e assume "head_norm env f = Some (Err e)" "clashx e"
        then show ?thesis using hn by (simp add: bindM_def)
      next
        fix nf assume "head_norm env f = Some (Ok nf)"
        then have nf: "head_norm env f = return nf" by (simp add: return_def)
        have fnf: "unfc env f \<rightarrow>\<^sub>\<beta>\<^sup>* unfc env nf"
          by (rule head_norm_unfc[OF nf[unfolded return_def] refl ac cl])
        show ?thesis
        proof (cases nf)
          case (Abs b U body)
          have "(sup beta subt)\<^sup>*\<^sup>* (unfc env t) (unfc env (Abs b U body $ u))"
            using App Abs beta_reds_sup[OF rtrancl_beta_AppL[OF fnf, of "unfc env u"]] by simp
          moreover have "vars nf \<subseteq> vars f \<union> evars env"
            by (rule head_norm_vars[OF nf[unfolded return_def] refl])
          then have "vars body \<union> vars u \<subseteq> vars t \<union> evars env" using vfu Abs by auto
          ultimately have "dfd (head_norm env (subst_bound u body))" using redex[of b U body u] by blast
          then show ?thesis using hn nf Abs by (simp add: bindM_def return_def)
        qed (use hn nf in \<open>simp_all add: bindM_def return_def\<close>)
      qed
    qed
  qed (subst head_norm.simps, simp add: return_def)+
qed

abbreviation rho0 :: "env \<Rightarrow> tinst" where
  "rho0 env \<equiv> tnorm_inst (tyenv env)"

lemma allM_dfd: "(\<And>x. x \<in> set xs \<Longrightarrow> dfd (P x)) \<Longrightarrow> dfd (allM P xs)"
  by (induction xs) (auto intro!: dfd_bindM)

subsection \<open>Typing and definedness of the unfolding under the invariants\<close>

lemma unfc_same:
  assumes "tenv env1 = tenv env" "tyenv env1 = tyenv env"
  shows "unfc env1 = unfc env"
  unfolding unfc_def[abs_def] cval_def[abs_def] uvalc_def uvalc_step_def[abs_def] dep_def by (simp only: assms)

lemma unfc_rigid: "rigid h \<Longrightarrow> unfc env h = h"
  by (cases h) simp_all

lemma tok_einv:
  assumes ei: "einv A K env" and wi: "winv env X" and X: "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tok env (X \<union> evars env)"
proof (rule tokI)
  fix x T assume xT: "(x, T) \<in> X \<union> evars env"
  note e = einvD[OF ei]
  have "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  proof (cases "(x, T) \<in> X")
    case True
    with X show ?thesis by (auto simp: vtvars_def)
  next
    case False
    with xT obtain y U u where yb: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
      by (auto simp: evars_def bnds_def)
    moreover have "tvars T \<subseteq> ttvars u" if "(x, T) \<in> vars u" using that
      by (induction u) (auto simp: ttvars_def)
    ultimately show ?thesis using tvinvD(2)[OF e(1) yb(1)] by blast
  qed
  then show "tcons (tyenv env) T" by (rule tinv_tcons[OF e(2)])
next
  have "vinv (tnorm_inst (tyenv env)) env X" using winvD[OF wi einv_rho0[OF ei]] by blast
  then show "vcons (tnorm_inst (tyenv env)) (X \<union> evars env \<union> evars env)" by (simp add: vinv_def)
qed

lemma typing_unfc0:
  assumes "einv A K env" "winv env X" "e \<turnstile> inst (rho0 env) t : T"
  shows "e \<turnstile> inst (rho0 env) (unfc env t) : T"
proof -
  note r0 = einv_rho0[OF assms(1)]
  have "wt_env (rho0 env) env" using winvD[OF assms(2) r0] by blast
  from typing_unfc[OF einvD(3)[OF assms(1)] this r0(1) assms(3)] show ?thesis .
qed

lemma termip_unfc0:
  assumes "einv A K env" "winv env X" "e \<turnstile> inst (rho0 env) t : T"
  shows "termip (sup beta subt) (unfc env t)"
  using termip_inst[OF type_implies_termi[OF typing_unfc0[OF assms]] refl] by (rule termip_beta_subt)

text \<open>Head normalization of a well-formed pair terminates, and raises at most a clash:\<close>

lemma hn_dfd:
  assumes ei: "einv A K env" and wi: "winv env X" and p: "upok A env bs X s t"
  shows "dfd (head_norm env s)" "dfd (head_norm env t)"
    "ok (head_norm env s) s' \<Longrightarrow> ok (head_norm env t) t' \<Longrightarrow> upok A env bs X s' t'"
proof -
  let ?\<rho> = "rho0 env"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei] and pd = upokD[OF p]
  have tk: "tok env (X \<union> evars env)" by (rule tok_einv[OF ei wi pd(6)])
  obtain e0 T0 where ty0: "bs_env ?\<rho> e0 bs" "e0 \<turnstile> inst ?\<rho> s : T0" "e0 \<turnstile> inst ?\<rho> t : T0"
    using pd(9)[OF r0] by blast
  have hn: "dfd (head_norm env u)" if "vars u \<subseteq> X \<union> evars env" "e0 \<turnstile> inst ?\<rho> u : T0" for u
  proof (rule head_norm_def[OF e(3,4,6,7)])
    show "tok env (vars u \<union> evars env)" using tk that(1) by (auto intro: tok_mono)
    show "termip (sup beta subt) (unfc env u)" by (rule termip_unfc0[OF ei wi that(2)])
  qed
  show "dfd (head_norm env s)" "dfd (head_norm env t)" using hn[OF pd(1) ty0(2)] hn[OF pd(2) ty0(3)] by simp_all
  assume s'': "head_norm env s = Some (Ok s')" and t'': "head_norm env t = Some (Ok t')"
  have w0: "wt_env ?\<rho> env" using winvD[OF wi r0] by blast
  show "upok A env bs X s' t'"
    unfolding upok_def
  proof (intro conjI allI impI)
    show "vars s' \<union> vars t' \<subseteq> X \<union> evars env"
      using head_norm_vars[OF s'' refl] head_norm_vars[OF t'' refl] pd(1,2) by blast
    show "ttvars s' \<union> ttvars t' \<union> btvars bs \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
      using head_norm_ttvars[OF s'' refl] head_norm_ttvars[OF t'' refl] pd(3-6) tvinv_etvars[OF e(1)] by blast
    show "\<not> loose_bvar s' (ilength bs)" by (rule head_norm_loose[OF s'' refl w0 ilength_nonneg pd(7)])
    show "\<not> loose_bvar t' (ilength bs)" by (rule head_norm_loose[OF t'' refl w0 ilength_nonneg pd(8)])
    fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
    obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" using pd(9)[OF \<rho>] by blast
    have wr: "wt_env \<rho> env" using winvD[OF wi \<rho>] by blast
    show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s' : T \<and> e \<turnstile> inst \<rho> t' : T"
      using ty head_norm_sound[OF s'' refl \<rho>(1) wr ty(2)] head_norm_sound[OF t'' refl \<rho>(1) wr ty(3)] by blast
  qed
qed

text \<open>Soundness gives the typing invariant of the results of a step:\<close>

lemma winv_stepg:
  assumes st: "step_okg env bs s t env'" and wi: "winv env X" and p: "upok A env bs X s t"
  shows "winv env' X"
  unfolding winv_def
proof (intro allI impI)
  fix \<rho> assume \<rho>: "tsol (tyenv env') \<rho>" "cert_inst \<rho>"
  have ext: "extends env env'" using st unfolding step_okg_def by blast
  have \<rho>0: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF \<rho>(1) ext])
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
    using upokD(9)[OF p \<rho>0 \<rho>(2)] by blast
  have w: "wt_env \<rho> env" "vinv \<rho> env X" using winvD[OF wi \<rho>0 \<rho>(2)] by blast+
  have "vinv \<rho> env (X \<union> vars s \<union> vars t)" using w(2) vinv_evars[of s t X env \<rho>] upokD(1,2)[OF p] by simp
  with st \<rho>(1) w(1) ty upokD(7,8)[OF p] show "wt_env \<rho> env' \<and> vinv \<rho> env' X"
    unfolding step_okg_def by (blast intro: extends_refl)
qed

subsection \<open>Definedness with a postcondition\<close>

definition dfdp :: "'a M \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "dfdp m P \<longleftrightarrow> dfd m \<and> (\<forall>x. m = return x \<longrightarrow> P x)"

lemma dfdp_return [simp]: "dfdp (return x) P \<longleftrightarrow> P x"
  by (auto simp: dfdp_def return_def)

lemma dfdp_Ok [simp]: "dfdp (Some (Ok x)) P \<longleftrightarrow> P x"
  by (auto simp: dfdp_def return_def)

lemma dfdp_var_clash: "x \<in> loose \<Longrightarrow> dfdp (var_clash x T U) P"
  by (auto simp: dfdp_def var_clash_def raise_def return_def clashx_def)

lemma dfdp_dfd: "dfdp m P \<Longrightarrow> dfd m"
  by (simp add: dfdp_def)

lemma dfdp_ok: "dfdp m P \<Longrightarrow> m = return x \<Longrightarrow> P x"
  by (simp add: dfdp_def)

lemma dfdp_mono: "dfdp m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> dfdp m Q"
  by (simp add: dfdp_def)

lemma dfdp_bindM:
  assumes "dfdp m P" "\<And>x. m = return x \<Longrightarrow> P x \<Longrightarrow> dfdp (f x) Q"
  shows "dfdp (bindM m f) Q"
proof (rule dfd_cases[OF dfdp_dfd[OF assms(1)]])
  fix e assume "m = Some (Err e)" "clashx e"
  then show ?thesis by (simp add: dfdp_def bindM_def return_def)
next
  fix x assume m: "m = Some (Ok x)"
  then have "dfdp (f x) Q" using assms dfdp_ok[OF assms(1)] by (simp add: return_def)
  with m show ?thesis by (simp add: bindM_def)
qed

lemma dfdp_cases:
  assumes "dfdp m P"
  obtains (err) e where "m = Some (Err e)" "clashx e" | (ok) x where "m = return x" "P x"
  using assms by (auto simp: dfdp_def return_def elim: dfd_cases)

lemma tok_bnd: "tok env (evars env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tok env (vars u \<union> evars env)"
  using evarsI2[of env x U u] by (auto intro: tok_mono)

end

end
