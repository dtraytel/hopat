section \<open>Termination of Pattern Unification with Names at Two Types\<close>

theory Unify_Pattern_Dfd
  imports Unify_Pull_Dfd
begin

text \<open>
  The counterpart of the termination proof of pattern unification (theories
  \<^theory>\<open>Pattern_Correctness.Pattern_Termination\<close> to
  \<^theory>\<open>Pattern_Correctness.Pattern_Term_Unif\<close>) without a hypothesis on the names: the
  measure uses \<open>unfc\<close>, and unification may in addition raise the exception of
  \<^const>\<open>var_clash\<close>. The statements are about the computations themselves (no \<open>cut\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>The measure\<close>

definition Mc :: "tinst \<Rightarrow> env \<Rightarrow> pterm \<Rightarrow> nat" where
  "Mc \<rho> env t = msz (bnorm (inst \<rho> (unfc env t)))"

lemma Mc_head_norm:
  assumes "ok (head_norm env t) t'" "acyc env" "closed_env env" "e \<turnstile> inst \<rho> (unfc env t) : T"
  shows "Mc \<rho> env t' = Mc \<rho> env t"
  unfolding Mc_def
  using bnorm_typed_reds[OF assms(4) inst_reds[OF head_norm_unfc[OF assms(1) refl assms(2,3)]]] by simp

lemma Mc_Abs: "e \<turnstile> inst \<rho> (unfc env (Abs a U t)) : T \<Longrightarrow> Mc \<rho> env (Abs a U t) = Mc \<rho> env t + 2"
  unfolding Mc_def by (simp add: bnorm_Abs_typed)

lemma Mc_rigid:
  assumes "rigid h" "e \<turnstile> inst \<rho> (unfc env (h \<degree>\<degree> ts)) : T"
  shows "Mc \<rho> env (h \<degree>\<degree> ts) = 1 + sum_list (map (Mc \<rho> env) ts)"
proof -
  have i: "inst \<rho> (unfc env (h \<degree>\<degree> ts)) = inst \<rho> h \<degree>\<degree> map (inst \<rho> \<circ> unfc env) ts"
    using assms(1) by (simp add: unfc_apps inst_apps unfc_rigid)
  have r: "rigid (inst \<rho> h)" by (rule inst_rigid[OF assms(1)])
  then have at: "atom (inst \<rho> h)" by (simp add: rigid_iff)
  have "Mc \<rho> env (h \<degree>\<degree> ts) = msz (inst \<rho> h \<degree>\<degree> map (bnorm \<circ> inst \<rho> \<circ> unfc env) ts)"
    using bnorm_atom_apps[OF at assms(2)[unfolded i]] by (simp add: Mc_def i comp_def)
  also have "\<dots> = 1 + sum_list (map msz (map (bnorm \<circ> inst \<rho> \<circ> unfc env) ts))"
    by (rule msz_rigid_apps[OF r])
  also have "\<dots> = 1 + sum_list (map (Mc \<rho> env) ts)" by (simp add: Mc_def[abs_def] comp_def)
  finally show ?thesis .
qed

lemma Mc_flex:
  assumes ac: "acyc env" and "vt_lookup (tenv env) x = None" "e \<turnstile> inst \<rho> (unfc env (Var x U \<degree>\<degree> ts)) : T"
  shows "Mc \<rho> env (Var x U \<degree>\<degree> ts) = 2 * (arity (tsubst \<rho> U) - length ts) + 1"
proof -
  have i: "inst \<rho> (unfc env (Var x U \<degree>\<degree> ts)) = Var x (tsubst \<rho> U) \<degree>\<degree> map (inst \<rho> \<circ> unfc env) ts"
    using assms(2) by (simp add: unfc_apps inst_apps unfc_Var[OF ac])
  from bnorm_atom_apps[of _ e _ T, OF _ assms(3)[unfolded i]] msz_flex_apps
  show ?thesis by (simp add: Mc_def i)
qed

lemma Mc_lift:
  assumes "acyc env" "closed_env env" "0 \<le> k" "e \<turnstile> inst \<rho> (unfc env t) : T"
  shows "Mc \<rho> env (lift t k) = Mc \<rho> env t"
  unfolding Mc_def using bnorm_lift[OF assms(4,3)]
  by (simp add: unfc_lift[OF assms(1-3)] inst_lift)

lemma Mc_same:
  assumes "tenv env1 = tenv env" "tyenv env1 = tyenv env"
  shows "Mc \<rho> env1 = Mc \<rho> env"
proof -
  have "unfc env1 = unfc env" by (rule unfc_same[OF assms])
  then show ?thesis by (simp only: Mc_def[abs_def])
qed

subsection \<open>Pruning\<close>

lemma unfc_vsubst: "unfc env t = vsubst (\<lambda>y T. unfc env (Var y T)) t"
  unfolding unfc_def by (induction t) simp_all

text \<open>
  A pruning binding of \<open>G\<close> replaces the occurrences of \<open>G\<close> whose type unifies with the type of
  the binding:
\<close>

lemma unfc_prune:
  assumes upd: "ok (update (G, Gty) b env) env1" and ac: "acyc env" "acyc env1"
    and b: "unfc env1 b = b"
  shows "unfc env1 t = vsubst (\<lambda>x T. if x = G \<and> ok (unified (tyenv env) T Gty) True then b else Var x T) (unfc env t)"
proof -
  let ?\<pi> = "\<lambda>x T. if x = G \<and> ok (unified (tyenv env) T Gty) True then b else Var x T"
  note u = ok_update[OF upd]
  have lk1: "vt_lookup (tenv env1) x = (if x = G then Some (Gty, b) else vt_lookup (tenv env) x)" for x
    using u(2) by simp
  have th: "tyenv env1 = tyenv env" by (rule u(3))
  have Var: "unfc env1 (Var x T) = vsubst ?\<pi> (unfc env (Var x T))" for x T
  proof (induction x arbitrary: T rule: dep_induct[OF ac(1)])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have xG: "x \<noteq> G" using u(1) Some by auto
      have "unfc env1 u = vsubst (\<lambda>y T'. vsubst ?\<pi> (unfc env (Var y T'))) u"
        by (subst unfc_vsubst) (rule vsubst_cong, use "1.IH"[OF depI[OF Some[unfolded p]]] in simp)
      also have "\<dots> = vsubst ?\<pi> (unfc env u)" by (subst (2) unfc_vsubst) (simp add: vsubst_vsubst)
      finally show ?thesis using Some p xG
        by (simp add: unfc_Var[OF ac(2)] unfc_Var[OF ac(1)] lk1 th)
    next
      case None
      then show ?thesis using b by (simp add: unfc_Var[OF ac(2)] unfc_Var[OF ac(1)] lk1 th)
    qed
  qed
  show ?thesis by (subst (1 2) unfc_vsubst) (simp add: Var vsubst_vsubst)
qed

lemma inst_vsubst_prunec:
  "(\<And>T. (G, T) \<in> vars X \<Longrightarrow> ok (unified \<theta> T Gty) True \<longleftrightarrow> tsubst \<rho> T = TG) \<Longrightarrow>
    inst \<rho> (vsubst (\<lambda>x T. if x = G \<and> ok (unified \<theta> T Gty) True then b else Var x T) X) =
      vsubst (psubst G TG (inst \<rho> b)) (inst \<rho> X)"
  by (induction X) (auto simp: psubst_def)

lemma vars_unfc_sub: "acyc env \<Longrightarrow> vars (unfc env t) \<subseteq> vars t \<union> evars env"
proof -
  assume ac: "acyc env"
  have "vars (unfc env (Var x T)) \<subseteq> insert (x, T) (evars env)" for x T
  proof (induction x arbitrary: T rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv env) x")
      case (Some p)
      obtain U u where p: "p = (U, u)" by force
      have "vars (unfc env u) \<subseteq> evars env"
      proof
        fix z assume "z \<in> vars (unfc env u)"
        then obtain y T' where yT: "(y, T') \<in> vars u" "z \<in> vars (unfc env (Var y T'))"
          by (subst (asm) unfc_vsubst) (auto simp: vars_vsubst)
        from "1.IH"[OF depI[OF Some[unfolded p] yT(1)]] yT(2) evarsI2[OF Some[unfolded p]] yT(1)
        show "z \<in> evars env" by blast
      qed
      then show ?thesis using Some p by (auto simp: unfc_Var[OF ac] split: if_splits)
    qed (simp add: unfc_Var[OF ac])
  qed
  then show "vars (unfc env t) \<subseteq> vars t \<union> evars env"
    by (subst unfc_vsubst) (fastforce simp: vars_vsubst)
qed

lemma Mc_prune:
  assumes upd: "ok (update (G, Gty) b env) env1"
    and b: "b = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)"
    and ac: "acyc env" "acyc env1" and cl: "closed_env env" "closed b"
    and H: "vt_lookup (tenv env1) H = None"
    and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
    and tk: "tok env (vars t \<union> evars env1)"
    and tyb: "\<And>e. e \<turnstile> inst (rho0 env) b : tsubst (rho0 env) Gty"
    and ar: "arity (tsubst (rho0 env) Gty) = length bs + a" "arity (tsubst (rho0 env) Hty) = length ks + a"
    and wte: "wt_env (rho0 env) env" and ty: "e \<turnstile> inst (rho0 env) t : T"
  shows "Mc (rho0 env) env1 t = Mc (rho0 env) env t"
proof -
  let ?\<rho> = "rho0 env"
  let ?TG = "tsubst ?\<rho> Gty" and ?b = "inst ?\<rho> b"
  let ?\<pi> = "psubst G ?TG ?b"
  have ub: "unfc env1 b = b" using H b
    by (simp add: unfc_def vsubst_abs_list vsubst_apps cval_def uvalc_eq[OF ac(2)] comp_def)
  have Gin: "(G, Gty) \<in> evars env1" using evars_update[OF upd] by simp
  have ev: "evars env \<subseteq> evars env1" using evars_update[OF upd] by blast
  have tGty: "tcons (tyenv env) Gty" using tk Gin by (auto simp: tok_def)
  have G: "ok (unified (tyenv env) T' Gty) True \<longleftrightarrow> tsubst ?\<rho> T' = ?TG" if "(G, T') \<in> vars (unfc env t)" for T'
  proof -
    have "(G, T') \<in> vars t \<union> evars env1" using vars_unfc_sub[OF ac(1)] that ev by blast
    then have "tcons (tyenv env) T'" using tk by (auto simp: tok_def)
    from unified_ok[OF tac tc this tGty] show ?thesis by (simp add: return_def)
  qed
  have Y: "inst ?\<rho> (unfc env1 t) = vsubst ?\<pi> (inst ?\<rho> (unfc env t))"
    by (simp add: unfc_prune[OF upd ac ub] inst_vsubst_prunec[OF G])
  have tyY: "e \<turnstile> inst ?\<rho> (unfc env t) : T"
    by (rule typing_unfc[OF ac(1) wte tsol_tnorm[OF tac] ty])
  have wt: "wt_subst ?\<pi>" by (rule wt_psubst) (use cl(2) tyb in \<open>simp_all add: closed_def\<close>)
  note n = bnorm_typed[OF tyY]
  have cs: "closed_subst ?\<pi>" using wt by (simp add: wt_subst_def)
  have "bnorm (vsubst ?\<pi> (bnorm (inst ?\<rho> (unfc env t)))) = bnorm (vsubst ?\<pi> (inst ?\<rho> (unfc env t)))"
    by (rule bnorm_typed_reds[OF typing_vsubst[OF tyY wt] beta_reds_vsubst[OF conjunct1[OF n] cs]])
  moreover have "msz (bnorm (vsubst ?\<pi> (bnorm (inst ?\<rho> (unfc env t))))) = msz (bnorm (inst ?\<rho> (unfc env t)))"
  proof (rule msz_prune)
    show "?b = abs_list (map (\<lambda>(x, T). (x, tsubst ?\<rho> T)) bs) (Var H (tsubst ?\<rho> Hty) \<degree>\<degree> map Bound ks)"
      by (simp add: b inst_abs_list inst_apps comp_def)
    show "closed ?b" using cl(2) by (simp add: closed_def)
    show "e' \<turnstile> ?b : ?TG" for e' by (rule tyb)
    show "arity ?TG = length (map (\<lambda>(x, T). (x, tsubst ?\<rho> T)) bs) + a" using ar by simp
    show "arity (tsubst ?\<rho> Hty) = length ks + a" by (rule ar(2))
    show "e \<turnstile> bnorm (inst ?\<rho> (unfc env t)) : T" by (rule subject_reduction_beta'[OF conjunct1[OF n] tyY])
    show "no_redex (bnorm (inst ?\<rho> (unfc env t)))" using n by blast
  qed
  ultimately show ?thesis by (simp add: Mc_def Y)
qed


subsection \<open>Pruning extensions\<close>

text \<open>
  An extension prunes if it keeps the type environment and the measure, at the most general
  solution of the type environment, of the problems whose variables have consistent types.
\<close>

definition prunesc :: "env \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "prunesc env env' X \<longleftrightarrow> tyenv env' = tyenv env \<and>
    (\<forall>e t T. wt_env (rho0 env) env' \<longrightarrow> tok env' (X \<union> evars env') \<longrightarrow> vars t \<subseteq> X \<union> evars env \<longrightarrow>
      e \<turnstile> inst (rho0 env) t : T \<longrightarrow> Mc (rho0 env) env' t = Mc (rho0 env) env t)"

lemma prunesc_same: "tenv env' = tenv env \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> prunesc env env' X"
  unfolding prunesc_def using Mc_same[of env' env] by simp

lemma tok_tyenv: "tyenv env' = tyenv env \<Longrightarrow> tok env' X = tok env X"
  by (simp add: tok_def)

lemma prunesc_trans:
  assumes "prunesc env env1 X" "prunesc env1 env2 X" "extends env1 env2" "extends env env1"
  shows "prunesc env env2 X"
  unfolding prunesc_def
proof (intro conjI allI impI)
  have th: "tyenv env1 = tyenv env" "tyenv env2 = tyenv env1" using assms(1,2) by (simp_all add: prunesc_def)
  then show "tyenv env2 = tyenv env" by simp
  fix e t T assume a: "wt_env (rho0 env) env2" "tok env2 (X \<union> evars env2)" "vars t \<subseteq> X \<union> evars env"
    "e \<turnstile> inst (rho0 env) t : T"
  have "wt_env (rho0 env) env1" by (rule wt_env_extends[OF a(1) assms(3)])
  moreover have "tok env1 (X \<union> evars env1)"
    using a(2) evars_extends[OF assms(3)] th tok_tyenv[of env2 env1] by (auto simp: tok_def)
  ultimately have "Mc (rho0 env) env1 t = Mc (rho0 env) env t" using assms(1) a(3,4) unfolding prunesc_def by blast
  moreover have "evars env \<subseteq> evars env1" by (rule evars_extends[OF assms(4)])
  then have "vars t \<subseteq> X \<union> evars env1" using a(3) by blast
  then have "Mc (rho0 env) env2 t = Mc (rho0 env) env1 t"
    using assms(2) a(1,2,4) th unfolding prunesc_def by auto
  ultimately show "Mc (rho0 env) env2 t = Mc (rho0 env) env t" by simp
qed

lemma prunesc_update:
  assumes upd: "ok (update (G, Gty) b env) env1"
    and b: "b = abs_list bs (Var H Hty \<degree>\<degree> map Bound ks)"
    and ac: "acyc env" "acyc env1" and cl: "closed_env env" "closed b"
    and H: "vt_lookup (tenv env1) H = None"
    and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "prunesc env env1 X"
  unfolding prunesc_def
proof (intro conjI allI impI)
  note u = ok_update[OF upd]
  show "tyenv env1 = tyenv env" by (rule u(3))
  fix e t T assume a: "wt_env (rho0 env) env1" "tok env1 (X \<union> evars env1)" "vars t \<subseteq> X \<union> evars env"
    "e \<turnstile> inst (rho0 env) t : T"
  have lk: "vt_lookup (tenv env1) G = Some (Gty, b)" using u(2) by simp
  have tyb: "e' \<turnstile> inst (rho0 env) b : tsubst (rho0 env) Gty" for e' by (rule wt_envD[OF a(1) lk])
  obtain c where ar: "arity (tsubst (rho0 env) Gty) = length bs + c" "arity (tsubst (rho0 env) Hty) = length ks + c"
    using prune_arity[OF tyb[of e, unfolded b]] by blast
  have wte: "wt_env (rho0 env) env" by (rule wt_env_extends[OF a(1) extends_update[OF upd]])
  have "vars t \<union> evars env1 \<subseteq> X \<union> evars env1" using a(3) evars_extends[OF extends_update[OF upd]] by blast
  then have tk: "tok env (vars t \<union> evars env1)" using a(2) u(3) by (auto simp: tok_def)
  show "Mc (rho0 env) env1 t = Mc (rho0 env) env t"
    by (rule Mc_prune[OF upd b ac cl H tac tc tk tyb ar wte a(4)])
qed

lemma prunesc_genvar: "genvar a env T = (env', G) \<Longrightarrow> prunesc env env' X"
  by (rule prunesc_same) (simp_all add: genvar_simps)

subsection \<open>The occurs checks\<close>

context
  fixes env assumes ac: "acyc env" and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
begin

text \<open>
  The occurs check of pattern unification terminates; if it does not raise the clash, its answer
  is the occurrence in the type-blind unfolding (a lookup that does not raise follows the binding).
\<close>

lemma occurs_dfdp:
  "tok env (vars t \<union> evars env) \<Longrightarrow> dfdp (occurs F t env) (\<lambda>b. b = (F \<in> fst ` vars (unf env t)))"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than],
    of "\<lambda>t. (size (unf env t), case t of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0)"]])
  case (1 t)
  note IH = "1.IH"[simplified, rule_format]
  show ?case
  proof (cases t)
    case (Var G T)
    have lk: "lookup env G T = (case vt_lookup (tenv env) G of None \<Rightarrow> return None
      | Some (U, u) \<Rightarrow> if tnorm (tyenv env) T = tnorm (tyenv env) U then return (Some u) else var_clash G T U)"
      by (rule lookup_def_tok[OF tac tc tok_mono[OF "1.prems"]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) G")
      case None
      then show ?thesis using lk Var by (subst occurs.simps) (simp add: unf_Var[OF ac] bindM_def return_def)
    next
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      show ?thesis
      proof (cases "tnorm (tyenv env) T = tnorm (tyenv env) U")
        case True
        have u: "unf env (Var G T) = unf env u" using Some b by (simp add: unf_Var[OF ac])
        have "rank": "(case u of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0) < Suc (rk env G)"
        proof (cases u)
          case (Var y U')
          have "(y, G) \<in> dep env" using depI[OF Some[unfolded b], of y U'] Var by simp
          then show ?thesis using rk_less[OF ac] Var by simp
        qed simp_all
        have "dfdp (occurs F u env) (\<lambda>b. b = (F \<in> fst ` vars (unf env u)))"
        proof (rule IH)
          have "tok env (evars env)" using "1.prems" by (rule tok_mono) blast
          from tok_bnd[OF this Some[unfolded b]] show "tok env (vars u \<union> evars env)" .
        qed (use u "rank" Var in simp_all)
        then show ?thesis using lk Var Some b u True by (subst occurs.simps) (simp add: bindM_def return_def)
      next
        case False
        then show ?thesis using lk Var Some b
          by (subst occurs.simps) (simp add: bindM_def var_clash_def raise_def dfdp_def return_def)
      qed
    qed
  next
    case (App t1 t2)
    have d1: "dfdp (occurs F t1 env) (\<lambda>b. b = (F \<in> fst ` vars (unf env t1)))"
      by (rule IH) (use "1.prems" App in \<open>auto intro: tok_mono\<close>)
    have d2: "dfdp (occurs F t2 env) (\<lambda>b. b = (F \<in> fst ` vars (unf env t2)))"
      by (rule IH) (use "1.prems" App in \<open>auto intro: tok_mono\<close>)
    have eq: "occurs F t env = bindM (occurs F t1 env) (\<lambda>b. if b then return True else occurs F t2 env)"
      using App by (subst occurs.simps) simp
    show ?thesis unfolding eq
    proof (rule dfdp_bindM[OF d1])
      fix b1 assume b1: "b1 = (F \<in> fst ` vars (unf env t1))"
      show "dfdp (if b1 then return True else occurs F t2 env) (\<lambda>b. b = (F \<in> fst ` vars (unf env t)))"
      proof (cases b1)
        case True
        then show ?thesis using b1 App by (auto simp: image_Un)
      next
        case False
        then show ?thesis using b1 App by (auto simp: image_Un intro: dfdp_mono[OF d2])
      qed
    qed
  next
    case (Abs a T u)
    have "dfdp (occurs F u env) (\<lambda>b. b = (F \<in> fst ` vars (unf env u)))"
      by (rule IH) (use "1.prems" Abs in \<open>auto intro: tok_mono\<close>)
    then show ?thesis using Abs by (subst occurs.simps) simp
  qed (subst occurs.simps, simp)+
qed

end



context
  fixes env assumes ac: "acyc env" and cl: "closed_env env"
    and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
begin

lemma mapM_dfd: "(\<And>x. x \<in> set xs \<Longrightarrow> dfd (f x)) \<Longrightarrow> dfd (mapM f xs)"
proof (induction xs)
  case Nil
  then show ?case by (simp add: return_def)
next
  case (Cons x xs)
  then show ?case by (auto intro!: dfd_bindM)
qed

lemma existsM_dfd0: "(\<And>x. x \<in> set xs \<Longrightarrow> dfd (P x)) \<Longrightarrow> dfd (existsM P xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (auto intro!: dfd_bindM)
qed

lemma ints_of'_dfd:
  assumes "tok env (\<Union> (vars ` set ts) \<union> evars env)" "\<And>t. t \<in> set ts \<Longrightarrow> termip (sup beta subt) (unfc env t)"
  shows "(\<exists>is. ints_of' env ts = return is) \<or> ints_of' env ts = raise Pattern \<or>
    (\<exists>x. ints_of' env ts = raise x \<and> clashx x)"
proof -
  have "dfd (head_norm env t)" if "t \<in> set ts" for t
    by (rule head_norm_def[OF ac cl tac tc]) (use assms that in \<open>auto intro: tok_mono\<close>)
  then have d: "dfd (mapM (head_norm env) ts)" by (rule mapM_dfd)
  show ?thesis
  proof (rule dfd_cases[OF d])
    fix x assume "mapM (head_norm env) ts = Some (Err x)" "clashx x"
    then show ?thesis by (auto simp: ints_of'_def bindM_def raise_def)
  next
    fix ts' assume "mapM (head_norm env) ts = Some (Ok ts')"
    then show ?thesis using ints_of_result[of ts'] by (auto simp: ints_of'_def bindM_def return_def)
  qed
qed

lemma rigid_occurs_dfd:
  shows "tok env (vars t \<union> evars env) \<Longrightarrow> termip (sup beta subt) (unfc env t) \<Longrightarrow>
    dfd (rigid_occurs F t env)"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_sn_less, of "unfc env"]])
  case (1 t)
  have dh: "dfd (head_norm env t)" by (rule head_norm_def[OF ac cl tac tc "1.prems"])
  show ?case
  proof (rule dfd_cases[OF dh])
    fix x assume "head_norm env t = Some (Err x)" "clashx x"
    then show ?thesis by (subst rigid_occurs.simps) (simp add: bindM_def)
  next
    fix t' assume hn0: "head_norm env t = Some (Ok t')"
    then have hn: "head_norm env t = return t'" by (simp add: return_def)
    have tt': "(sup beta subt)\<^sup>*\<^sup>* (unfc env t) (unfc env t')"
      by (rule beta_reds_sup[OF head_norm_unfc[OF hn0 refl ac cl]])
    have vt': "vars t' \<subseteq> vars t \<union> evars env" by (rule head_norm_vars[OF hn0 refl])
    have IH: "dfd (rigid_occurs F u env)"
      if "vars u \<subseteq> vars t' \<union> evars env" "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t') (unfc env u)" for u
    proof (rule "1.IH"[rule_format])
      have tu: "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t) (unfc env u)" using tt' that(2) by (rule rtranclp_tranclp_tranclp)
      have "(unfc env u, unfc env t) \<in> sn_less"
        by (simp only: sn_less_def mem_Collect_eq case_prod_conv) (use tu "1.prems"(2) in blast)
      then show "(u, t) \<in> inv_image sn_less (unfc env)" by simp
      show "tok env (vars u \<union> evars env)" using "1.prems"(1) that(1) vt' by (auto intro: tok_mono)
      show "termip (sup beta subt) (unfc env u)" by (rule termip_sup_reds[OF tranclp_into_rtranclp[OF tu] "1.prems"(2)])
    qed
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain a T u where Abs: "t' = Abs a T u" by (cases t') auto
      have "subt (unfc env t') (unfc env u)" using Abs by (simp add: subt_def)
      then have "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t') (unfc env u)" by blast
      then have "dfd (rigid_occurs F u env)" using IH[of u] Abs by auto
      then show ?thesis using hn Abs by (subst rigid_occurs.simps) (simp add: bindM_def return_def)
    next
      case False
      obtain h ts where st: "strip_comb t' = (h, ts)" by force
      have t': "t' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF st])
      have sub: "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t') (unfc env u)" if "u \<in> set ts" for u
        unfolding t' unfc_apps using sup_subt_apps[of "unfc env u" "map (unfc env) ts"] that by simp
      have args: "dfd (rigid_occurs F u env)" if "u \<in> set ts" for u
      proof (rule IH)
        show "vars u \<subseteq> vars t' \<union> evars env" using that t' by (auto simp: vars_apps)
        show "(sup beta subt)\<^sup>+\<^sup>+ (unfc env t') (unfc env u)" by (rule sub[OF that])
      qed
      have ex: "dfd (existsM (\<lambda>u. rigid_occurs F u env) ts)" by (rule existsM_dfd0[OF args])
      have rh: "dfd (rigid_head env u)" if u: "u \<in> set ts" for u
      proof -
        have "tok env (vars u \<union> evars env)"
          using "1.prems"(1) vt' t' u by (auto simp: vars_apps intro: tok_mono)
        moreover have "termip (sup beta subt) (unfc env u)"
          by (rule termip_sup_reds[OF rtranclp_trans[OF tt' tranclp_into_rtranclp[OF sub[OF u]]] "1.prems"(2)])
        ultimately have "dfd (head_norm env u)" by (rule head_norm_def[OF ac cl tac tc])
        then show ?thesis unfolding rigid_head_def by (rule dfd_bindM) simp
      qed
      have al: "dfd (allM (rigid_head env) ts)" by (rule allM_dfd[OF tac tc ac cl rh])
      show ?thesis using hn False ex al st
        by (subst rigid_occurs.simps) (auto simp: pterm_case_nonAbs bindM_def return_def split: pterm.splits)
    qed
  qed
qed

end


subsection \<open>Computations without cut\<close>

text \<open>
  The statements of the original termination proof are about \<open>cut f m\<close>; here the
  counterpart \<open>dcut f m\<close> is \<open>m\<close> itself, with the same introduction rules.
\<close>

definition dcut :: "('a \<Rightarrow> env) \<Rightarrow> 'a M \<Rightarrow> 'a M" where
  "dcut f m = m"

lemma dcut_OkD: "dcut f m = Some (Ok a) \<Longrightarrow> m = Some (Ok a)"
  by (simp add: dcut_def)

lemma dcut_okI: "m = Some (Ok a) \<Longrightarrow> P (Ok a) \<Longrightarrow> P (Err Pattern) \<Longrightarrow> \<exists>r. dcut f m = Some r \<and> P r"
  by (simp add: dcut_def)

lemma dcut_errI: "m = Some (Err e) \<Longrightarrow> P (Err e) \<Longrightarrow> P (Err Pattern) \<Longrightarrow> \<exists>r. dcut f m = Some r \<and> P r"
  by (simp add: dcut_def)

lemma dcut_raiseI: "m = raise e \<Longrightarrow> P (Err e) \<Longrightarrow> P (Err Pattern) \<Longrightarrow> \<exists>r. dcut f m = Some r \<and> P r"
  by (simp add: dcut_def raise_def)

lemma dcut_returnI: "m = return a \<Longrightarrow> P (Ok a) \<Longrightarrow> P (Err Pattern) \<Longrightarrow> \<exists>r. dcut f m = Some r \<and> P r"
  by (simp add: dcut_def return_def)

lemma dcut_bind_errI:
  assumes "dcut f m = Some (Err e)" "\<And>a b. ok m a \<Longrightarrow> ok (k a) b \<Longrightarrow> nfree (g b) \<Longrightarrow> nfree (f a)"
    "P (Err e)" "P (Err Pattern)"
  shows "\<exists>r. dcut g (m \<bind> k) = Some r \<and> P r"
  using assms by (simp add: dcut_def bindM_def)

lemma dcut_handle_bind_errI:
  assumes c: "dcut f m = Some (Err e)"
    and anti: "\<And>a b. ok m a \<Longrightarrow> ok (k a) b \<Longrightarrow> nfree (g b) \<Longrightarrow> nfree (f a)"
    and hr: "\<And>e. \<exists>e'. h e = raise e'" and hP: "\<And>e e'. P (Err e) \<Longrightarrow> h e = raise e' \<Longrightarrow> P (Err e')"
    and Pe: "P (Err e)" "P (Err Pattern)"
  shows "\<exists>r. dcut g (handle (m \<bind> k) h) = Some r \<and> P r"
proof -
  obtain e' where e': "h e = raise e'" using hr by blast
  have "handle (m \<bind> k) h = raise e'" using c e' by (simp add: dcut_def bindM_def handle_def raise_def)
  then show ?thesis using hP[OF Pe(1) e'] by (simp add: dcut_def raise_def)
qed

subsection \<open>Results of projection\<close>

definition prpostc :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    pterm \<Rightarrow> (pterm \<times> env) res \<Rightarrow> bool" where
  "prpostc A K env X s r \<longleftrightarrow> (case r of
      Ok (u, env') \<Rightarrow> einv A K env' \<and> winv env' X \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        prunesc env env' X \<and> card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
        (\<forall>x b. vt_lookup (tenv env') x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow>
           x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}) \<and>
        fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y} \<and>
        ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and> vars u \<subseteq> X \<union> evars env'
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern \<or> clashx e)"

lemma prpostc_Err [simp]: "prpostc A K env X s (Err e) \<longleftrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern \<or> clashx e"
  by (simp add: prpostc_def)

lemma prpostc_OkD:
  assumes "prpostc A K env X s (Ok (u, env'))"
  shows "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunesc env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
      x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "vars u \<subseteq> X \<union> evars env'"
  using assms by (simp_all only: prpostc_def xres.case case_prod_conv)

lemma prpostc_OkI:
  assumes "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunesc env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "\<And>x b. vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
      x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
    "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "vars u \<subseteq> X \<union> evars env'"
  shows "prpostc A K env X s (Ok (u, env'))"
  by (simp only: prpostc_def xres.case case_prod_conv) (use assms in blast)

text \<open>Results of projecting a list of arguments, with names in \<open>N\<close>:\<close>

definition prspostc :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    indexname set \<Rightarrow> (pterm list \<times> env) res \<Rightarrow> bool" where
  "prspostc A K env X N r \<longleftrightarrow> (case r of
      Ok (us, env') \<Rightarrow> einv A K env' \<and> winv env' X \<and> tyenv env' = tyenv env \<and> extends env env' \<and>
        prunesc env env' X \<and> card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
        (\<forall>x b. vt_lookup (tenv env') x = Some b \<longrightarrow> vt_lookup (tenv env) x = None \<longrightarrow> x \<in> N) \<and>
        (\<forall>u\<in>set us. fst ` vars (unf env' u) \<subseteq> N \<and> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A \<and>
          vars u \<subseteq> X \<union> evars env')
    | Err e \<Rightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern \<or> clashx e)"

lemma prspostc_Err [simp]: "prspostc A K env X N (Err e) \<longleftrightarrow> (\<exists>v. e = Unif v) \<or> e = Pattern \<or> clashx e"
  by (simp add: prspostc_def)

lemma prspostc_OkD:
  assumes "prspostc A K env X N (Ok (us, env'))"
  shows "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunesc env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> N"
    "u \<in> set us \<Longrightarrow> fst ` vars (unf env' u) \<subseteq> N"
    "u \<in> set us \<Longrightarrow> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    "u \<in> set us \<Longrightarrow> vars u \<subseteq> X \<union> evars env'"
  using assms by (simp_all only: prspostc_def xres.case case_prod_conv)

lemma prspostc_OkI:
  assumes "einv A K env'" "winv env' X" "tyenv env' = tyenv env" "extends env env'" "prunesc env env' X"
    "card (ubv env' X) \<le> card (ubv env X)" "newb env env'"
    "\<And>x b. vt_lookup (tenv env') x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> x \<in> N"
    "\<And>u. u \<in> set us \<Longrightarrow> fst ` vars (unf env' u) \<subseteq> N"
    "\<And>u. u \<in> set us \<Longrightarrow> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<And>u. u \<in> set us \<Longrightarrow> vars u \<subseteq> X \<union> evars env'"
  shows "prspostc A K env X N (Ok (us, env'))"
  by (simp only: prspostc_def xres.case case_prod_conv) (use assms in blast)

text \<open>The well-typedness invariant after projection follows from soundness:\<close>

text \<open>Projecting the arguments of a rigid head, threading the environment:\<close>

lemma mapAccM_pr_dfd:
  assumes ei0: "einv A K env0" and d: "0 \<le> d" and xs0: "\<forall>x\<in>set xs. 0 \<le> x"
    and "einv A K env" "winv env X" "tyenv env = tyenv env0" "extends env0 env" "prunesc env0 env X"
      "newb env0 env"
    and N0: "{y. maxidx env0 < snd y} \<subseteq> N"
    and "\<forall>t\<in>set ts. fst ` vars (unf env0 t) \<subseteq> N"
    and "\<And>t env. t \<in> set ts \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> tyenv env = tyenv env0 \<Longrightarrow>
      extends env0 env \<Longrightarrow> prunesc env0 env X \<Longrightarrow> newb env0 env \<Longrightarrow>
      \<exists>r. dcut snd (pr xs t env d bs) = Some r \<and> prpostc A K env X t r"
  shows "\<exists>r. dcut snd (mapAccM (\<lambda>s env. pr xs s env d bs) ts env) = Some r \<and> prspostc A K env X N r"
  using assms(4-)
proof (induction ts arbitrary: env)
  case Nil
  have "prspostc A K env X N (Ok ([], env))"
    by (rule prspostc_OkI) (use Nil.prems(1,2) in \<open>simp_all add: prunesc_same\<close>)
  then show ?case by (intro dcut_okI[of _ "([], env)"]) (simp_all add: return_def)
next
  case (Cons t ts)
  note ei = Cons.prems(1) and wi = Cons.prems(2) and th = Cons.prems(3) and ext0 = Cons.prems(4)
    and pr0 = Cons.prems(5) and nb0 = Cons.prems(6) and Nt = Cons.prems(8)
    and IH = Cons.prems(9)
  let ?f = "\<lambda>s env. pr xs s env d bs"
  let ?k = "\<lambda>(y, s1). mapAccM ?f ts s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))"
  have st: "mapAccM ?f (t # ts) env = pr xs t env d bs \<bind> ?k" by simp
  have anti: "nfree (snd a)" if "ok (pr xs t env d bs) a" "ok (?k a) b" "nfree (snd b)" for a b
  proof -
    obtain u env1 where a: "a = (u, env1)" by force
    from that(2) obtain us env' where m: "ok (mapAccM ?f ts env1) (us, env')" "snd b = env'"
      by (auto simp: a)
    have "extends env1 env'" by (rule mapAccM_pr_extends[OF m(1) d xs0])
    then show ?thesis using that(3) m(2) by (auto simp: a intro: nfree_extends)
  qed
  obtain r where r: "dcut snd (pr xs t env d bs) = Some r" "prpostc A K env X t r"
    using IH[of t env] ei wi th ext0 pr0 nb0 by auto
  have nm: "fst ` vars (unf env t) \<union> {y. maxidx env < snd y} \<subseteq> N"
  proof -
    have "fst ` vars (unf env t) \<subseteq> fst ` vars (unf env0 t) \<union> {y. maxidx env0 < snd y}"
      by (rule names_newb[OF einvD(3)[OF ei0] einvD(3)[OF ei] nb0 einvD(5)[OF ei0]])
    moreover have "{y. maxidx env < snd y} \<subseteq> {y. maxidx env0 < snd y}"
      using extends_maxidx[OF ext0] by auto
    moreover have "fst ` vars (unf env0 t) \<subseteq> N" using Nt by simp
    ultimately show ?thesis using N0 by blast
  qed
  show ?case
  proof (cases r)
    case (Err e)
    show ?thesis unfolding st
      by (rule dcut_bind_errI[OF r(1)[unfolded Err] anti]) (use r(2) Err in simp_all)
  next
    case (Ok p)
    obtain u env1 where p: "p = (u, env1)" by force
    note po = prpostc_OkD[OF r(2)[unfolded Ok p]]
    note r1 = dcut_OkD[OF r(1)[unfolded Ok p]]
    have th1: "tyenv env1 = tyenv env0" using po(3) th by simp
    have ext1: "extends env0 env1" by (rule extends_trans[OF ext0 po(4)])
    have pr1: "prunesc env0 env1 X" by (rule prunesc_trans[OF pr0 po(5) po(4) ext0])
    have nb1: "newb env0 env1" by (rule newb_trans[OF nb0 po(7)])
    obtain r' where r': "dcut snd (mapAccM ?f ts env1) = Some r'" "prspostc A K env1 X N r'"
    proof -
      have "\<forall>t\<in>set ts. fst ` vars (unf env0 t) \<subseteq> N" using Nt by simp
      from Cons.IH[OF po(1,2) th1 ext1 pr1 nb1 Cons.prems(7) this IH[OF list.set_intros(2)]]
      show ?thesis using that by blast
    qed
    have m1: "mapAccM ?f (t # ts) env = mapAccM ?f ts env1 \<bind> (\<lambda>(us, env'). return (u # us, env'))"
      using r1(1) by (simp add: return_def[symmetric])
    show ?thesis
    proof (cases r')
      case (Err e)
      show ?thesis unfolding m1
        by (rule dcut_bind_errI[OF r'(1)[unfolded Err]]) (use r'(2) Err in auto)
    next
      case (Ok p')
      obtain us env' where p': "p' = (us, env')" by force
      note qo = prspostc_OkD[OF r'(2)[unfolded Ok p']]
      note r2 = dcut_OkD[OF r'(1)[unfolded Ok p']]
      have m: "mapAccM ?f (t # ts) env = return (u # us, env')"
        using m1 r2(1) by (simp add: return_def[symmetric])
      have "prspostc A K env X N (Ok (u # us, env'))"
      proof (rule prspostc_OkI)
        show "einv A K env'" "winv env' X" by (rule qo(1), rule qo(2))
        show "tyenv env' = tyenv env" using qo(3) po(3) by simp
        show "extends env env'" by (rule extends_trans[OF po(4) qo(4)])
        show "prunesc env env' X" by (rule prunesc_trans[OF po(5) qo(5) qo(4) po(4)])
        show "card (ubv env' X) \<le> card (ubv env X)" using qo(6) po(6) by simp
        show "newb env env'" by (rule newb_trans[OF po(7) qo(7)])
      next
        fix x b assume x': "vt_lookup (tenv env') x = Some b" and x0: "vt_lookup (tenv env) x = None"
        show "x \<in> N"
        proof (cases "vt_lookup (tenv env1) x")
          case None
          from qo(8)[OF x' None] show ?thesis .
        next
          case (Some b1)
          from po(8)[OF Some x0] nm show ?thesis by blast
        qed
      next
        fix u' assume u': "u' \<in> set (u # us)"
        show "fst ` vars (unf env' u') \<subseteq> N"
        proof (cases "u' = u")
          case True
          have "fst ` vars (unf env' u) \<subseteq> fst ` vars (unf env1 u) \<union> {y. maxidx env1 < snd y}"
            by (rule names_newb[OF einvD(3)[OF po(1)] einvD(3)[OF qo(1)] qo(7) einvD(5)[OF po(1)]])
          moreover have "{y. maxidx env1 < snd y} \<subseteq> {y. maxidx env < snd y}"
            using extends_maxidx[OF po(4)] by auto
          ultimately show ?thesis using po(9) nm True by blast
        next
          case False
          with u' have "u' \<in> set us" by simp
          from qo(9)[OF this] show ?thesis .
        qed
        show "ttvars u' \<subseteq> tvars_env (tyenv env) \<union> A"
          using u' po(10) qo(10) po(3) by auto
        show "vars u' \<subseteq> X \<union> evars env'"
          using u' po(11) qo(11) evars_extends[OF qo(4)] by auto
      qed
      from dcut_okI[where P = "prspostc A K env X N" and f = snd, OF m[unfolded return_def] this]
      show ?thesis by simp
    qed
  qed
qed


subsection \<open>Termination of projection\<close>

lemma pr_dfd_aux:
  "Mc (tnorm_inst (tyenv env)) env s = n \<Longrightarrow> einv A K env \<Longrightarrow> winv env X \<Longrightarrow> finite X \<Longrightarrow>
    vtvars X \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> vars s \<subseteq> X \<union> evars env \<Longrightarrow>
    ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> \<not> loose_bvar s (ilength bs) \<Longrightarrow>
    (\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T) \<Longrightarrow>
    0 \<le> d \<Longrightarrow> \<forall>x\<in>set xs. 0 \<le> x \<Longrightarrow>
    \<exists>r. dcut snd (pr xs s env d bs) = Some r \<and> prpostc A K env X s r"
proof (induction n arbitrary: s env d bs rule: less_induct)
  case (less n)
  note Mn = less.prems(1) and ei = less.prems(2) and wi = less.prems(3) and fin = less.prems(4)
    and vX = less.prems(5) and vs = less.prems(6) and tvs = less.prems(7) and lb = less.prems(8)
    and ty = less.prems(9) and d = less.prems(10) and xs0 = less.prems(11)
  have PE: "prpostc A K env X s (Err Pattern)" by simp
  let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  have w0: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi r0] by blast+
  have vcX: "vcons ?\<rho> (X \<union> evars env)" using w0(2) by (simp add: vinv_def)
  have vcons: "vcons ?\<rho> (vars t \<union> evars env)" if "vars t \<subseteq> X \<union> evars env" for t
    by (rule vcons_mono[OF vcX]) (use that in blast)
  have vok: "tok env (vars t \<union> evars env)" if "vars t \<subseteq> X \<union> evars env" for t
    by (rule tok_mono[OF tok_einv[OF ei vX]]) (use that in blast)
  obtain e0 T0 where ty0: "e0 \<turnstile> inst ?\<rho> s : T0" using ty[OF r0] by blast
  have tyu: "e0 \<turnstile> inst ?\<rho> (unfc env s) : T0" by (rule typing_unfc[OF e(3) w0(1) r0(1) ty0])
  have sn: "termip (sup beta subt) (unfc env s)" by (rule termip_unfc0[OF ei wi ty0])
  have dh: "dfd (head_norm env s)" by (rule head_norm_def[OF e(3,4,6,7) vok[OF vs] sn])
  show ?case
  proof (rule dfd_cases[OF dh])
    fix x assume hx: "head_norm env s = Some (Err x)" "clashx x"
    then have "pr xs s env d bs = Some (Err x)" by (simp add: pr_unfold bindM_def)
    then show ?thesis by (intro dcut_errI[where e = x]) (simp_all add: hx(2))
  next
  fix s' assume hn0: "head_norm env s = Some (Ok s')"
  have hn: "head_norm env s = return s'" using hn0 by (simp add: return_def)
  note hn' = hn[unfolded return_def]
  have pr_s: "pr xs s env d bs = pr_step pr xs s' env d bs" by (simp add: pr_unfold hn)
  have vs': "vars s' \<subseteq> X \<union> evars env" using head_norm_vars[OF hn' refl] vs by blast
  have tvs': "ttvars s' \<subseteq> tvars_env ?\<theta> \<union> A"
    using head_norm_ttvars[OF hn' refl] tvs tvinv_etvars[OF e(1)] by blast
  have tvbs: "btvars bs \<subseteq> tvars_env ?\<theta> \<union> A" using tvs by blast
  have lb': "\<not> loose_bvar s' (ilength bs)" by (rule head_norm_loose[OF hn' refl w0(1) ilength_nonneg lb])
  have ty': "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s' : T" if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    from ty[OF that] obtain e T where "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> s : T" by blast
    moreover have "wt_env \<rho> env" using winvD[OF wi that] by blast
    ultimately show ?thesis using head_norm_sound[OF hn' refl that(1)] by blast
  qed
  have nm': "fst ` vars (unf env s') \<subseteq> fst ` vars (unf env s)"
    using beta_reds_vars[OF head_norm_unf[OF hn' refl e(3,4)]] by blast
  have Ms': "Mc ?\<rho> env s' = n" using Mc_head_norm[OF hn' e(3,4) tyu] Mn by simp
  obtain e1 T1 where ty1: "e1 \<turnstile> inst ?\<rho> s' : T1" using ty'[OF r0] by blast
  have tyu': "e1 \<turnstile> inst ?\<rho> (unfc env s') : T1" by (rule typing_unfc[OF e(3) w0(1) r0(1) ty1])
  have W: "winv env' X" if "pr xs s env d bs = Some (Ok (u, env'))" "tyenv env' = ?\<theta>" for u env'
    by (rule pr_winv[OF that(1) wi vs ty that(2) d xs0])
  show ?case
  proof (cases "is_Abs s'")
    case True
    then obtain a U t where s': "s' = Abs a U t" by (cases s') auto
    have Mt: "Mc ?\<rho> env t < n" using Mc_Abs[OF tyu'[unfolded s']] Ms' s' by simp
    have tyt: "\<exists>e T. bs_env \<rho> e ((a, U) # bs) \<and> e \<turnstile> inst \<rho> t : T" if "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for \<rho>
    proof -
      from ty'[OF that] obtain e T where bs: "bs_env \<rho> e bs" and tA: "e \<turnstile> inst \<rho> s' : T" by blast
      from tA s' obtain V where c: "cert_typ alg ar (tsubst \<rho> U)" and tt: "e\<langle>0:tsubst \<rho> U\<rangle> \<turnstile> inst \<rho> t : V"
        by auto
      from bs_env_Cons[OF bs c] tt show ?thesis by blast
    qed
    have vt: "vars t \<subseteq> X \<union> evars env" using vs' s' by simp
    have "btvars ((a, U) # bs) = tvars U \<union> btvars bs" by (simp add: btvars_def)
    then have tvt: "ttvars t \<union> btvars ((a, U) # bs) \<subseteq> tvars_env ?\<theta> \<union> A" using tvs' tvbs s' by auto
    have lbt: "\<not> loose_bvar t (ilength ((a, U) # bs))" using lb' s' by simp
    have d1: "0 \<le> d + 1" using d by simp
    obtain r where r: "dcut snd (pr xs t env (d + 1) ((a, U) # bs)) = Some r" "prpostc A K env X t r"
      using less.IH[OF Mt refl ei wi fin vX vt tvt lbt tyt d1 xs0] by blast
    have unfAbs: "unf env s' = Abs a U (unf env t)" by (simp add: s')
    have st: "pr xs s env d bs =
        pr xs t env (d + 1) ((a, U) # bs) \<bind> (\<lambda>(t', env'). return (Abs a U t', env'))"
      using pr_s s' by (simp add: pr_step_def)
    show ?thesis
    proof (cases r)
      case (Err ex)
      show ?thesis unfolding st
        by (rule dcut_bind_errI[OF r(1)[unfolded Err]]) (use r(2) Err in auto)
    next
      case (Ok p)
      obtain t' env' where p: "p = (t', env')" by force
      note po = prpostc_OkD[OF r(2)[unfolded Ok p]]
      have pe: "pr xs s env d bs = return (Abs a U t', env')"
        using st dcut_OkD(1)[OF r(1)[unfolded Ok p]] by (simp add: return_def[symmetric])
      have "prpostc A K env X s (Ok (Abs a U t', env'))"
      proof (rule prpostc_OkI[OF po(1) W[OF pe[unfolded return_def] po(3)] po(3-7)])
        fix x b assume "vt_lookup (tenv env') x = Some b" "vt_lookup (tenv env) x = None"
        from po(8)[OF this] nm' unfAbs
        show "x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by auto
      next
        show "fst ` vars (unf env' (Abs a U t')) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
          using po(9) nm' unfAbs by auto
        show "ttvars (Abs a U t') \<subseteq> tvars_env (tyenv env) \<union> A" using po(10) tvs' s' by auto
        show "vars (Abs a U t') \<subseteq> X \<union> evars env'" using po(11) by simp
      qed
      from dcut_okI[OF pe[unfolded return_def] this PE] show ?thesis .
    qed
  next
    case nAbs: False
    obtain h ts where hts: "strip_comb s' = (h, ts)" by force
    have s': "s' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF hts])
    have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
    have vts: "vars t \<subseteq> X \<union> evars env" if "t \<in> set ts" for t
      using vs' that unfolding s' vars_apps by blast
    have tvts: "ttvars t \<subseteq> tvars_env ?\<theta> \<union> A" if "t \<in> set ts" for t
      using tvs' that unfolding s' ttvars_apps by blast
    have lbts: "\<not> loose_bvar t (ilength bs)" if "t \<in> set ts" for t
      using lb' that unfolding s' loose_bvar_apps by blast
    have tyts: "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t : T" if tin: "t \<in> set ts" and tr: "tsol ?\<theta> \<rho>" "cert_inst \<rho>" for t \<rho>
    proof -
      from ty'[OF tr] obtain e T where bs: "bs_env \<rho> e bs" and tA: "e \<turnstile> inst \<rho> s' : T" by blast
      from tA have "e \<turnstile> inst \<rho> h \<degree>\<degree> map (inst \<rho>) ts : T" by (simp add: s' inst_apps)
      then obtain U where "e \<turnstile> inst \<rho> t : U"
        using typing_args[of e "inst \<rho> h" "map (inst \<rho>) ts" T "inst \<rho> t"] tin by auto
      with bs show ?thesis by blast
    qed
    show ?thesis
    proof (cases "is_Var h")
      case True
      then obtain F Fty where h: "h = Var F Fty" by (cases h) auto
      have F0: "vt_lookup (tenv env) F = None" using head_norm_Var_head[OF hn' refl] hts h by simp
      have Fin: "(F, Fty) \<in> X \<union> evars env" using vs' unfolding s' h vars_apps by simp
      have Fb: "snd F \<le> maxidx env" using w0(2) Fin unfolding vinv_def by (blast dest: belowD)
      have tvF: "tvars Fty \<subseteq> tvars_env ?\<theta> \<union> A" using tvs' unfolding s' h ttvars_apps by simp
      have io3: "(\<exists>js. ints_of' env ts = return js) \<or> ints_of' env ts = raise Pattern \<or>
          (\<exists>x. ints_of' env ts = raise x \<and> clashx x)"
      proof (rule ints_of'_dfd[OF e(3,4,6,7)])
        show "tok env (\<Union> (vars ` set ts) \<union> evars env)"
          by (rule tok_mono[OF tok_einv[OF ei vX]]) (use vts in blast)
        show "termip (sup beta subt) (unfc env t)" if tin: "t \<in> set ts" for t
        proof -
          from tyts[OF tin r0] obtain e T where "e \<turnstile> inst ?\<rho> t : T" by blast
          then show ?thesis by (rule termip_unfc0[OF ei wi])
        qed
      qed
      from io3 consider (cl) x where "ints_of' env ts = raise x" "clashx x"
        | (io) "(\<exists>js. ints_of' env ts = return js) \<or> ints_of' env ts = raise Pattern" by blast
      then show ?thesis
      proof cases
        case cl
        then have "pr xs s env d bs = raise x" using pr_s nAbs hts h by (simp add: pr_step_def)
        then show ?thesis by (intro dcut_errI[where e = x]) (simp_all add: raise_def cl(2))
      next
      case io
      then show ?thesis
      proof
        assume "ints_of' env ts = raise Pattern"
        then have "pr xs s env d bs = raise Pattern" using pr_s nAbs hts h by (simp add: pr_step_def)
        then show ?thesis by (intro dcut_errI[where e = Pattern]) (simp_all add: raise_def)
      next
        assume "\<exists>js. ints_of' env ts = return js"
        then obtain js where js: "ints_of' env ts = return js" by blast
        obtain js' where js': "mapM (try_trans xs d) js = return js'"
          using mapM_return[of js "try_trans xs d"] try_trans_return by blast
        let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
        have l2: "list_all2 (\<lambda>z opt. ok (try_trans xs d z) opt) js js'"
          using js' unfolding return_def by (simp only: ok_mapM)
        then have len: "length js = length js'" by (rule list_all2_lengthD)
        have ks: "\<forall>k\<in>set ?ks. 0 \<le> k \<and> k < ilength js" by (rule mk_proj_list_bren(1)[OF len])
        have tyF: "e1 \<turnstile> inst ?\<rho> (app (Var F Fty) js) : T1"
          by (rule flex_sound(1)[OF js[unfolded return_def] r0(1) w0(1) ty1[unfolded s' h]])
        from tyF obtain Fty_eq: "tsubst ?\<rho> Fty = map e1 js \<Rrightarrow> T1" and js0: "\<forall>i\<in>set js. 0 \<le> i"
          by (rule typing_appE)
        have Fn: "tnorm ?\<theta> Fty = map e1 js \<Rrightarrow> T1" using Fty_eq by simp
        have tc: "tcons ?\<theta> Fty" by (rule tinv_tcons[OF e(2) tvF])
        have ks': "\<forall>k\<in>set ?ks. 0 \<le> k \<and> k < ilength (map e1 js)" using ks by (simp add: ilength_eq)
        obtain Hty where tg: "type_of_G env Fty (ilength (map e1 js)) ?ks = return Hty"
          using type_of_G_ok[OF e(6,7) tc Fn ks'] by blast
        have tg': "type_of_G env Fty (ilength js) ?ks = return Hty" using tg by (simp add: ilength_eq)
        have tvH: "tvars Hty \<subseteq> tvars_env ?\<theta> \<union> A" by (rule type_of_G_tvars[OF tg'[unfolded return_def] e(1) tvF])
        obtain env1 H where gv: "genvar (fst F) env Hty = (env1, H)" by force
        have "\<forall>i\<in>set js. i < ilength bs"
          by (rule ints_of'_loose[OF js[unfolded return_def] w0(1) ilength_nonneg]) (use lbts in blast)
        with js0 have xsb: "\<forall>i\<in>set js. 0 \<le> i \<and> i < ilength bs" by blast
        from bind_new_term[OF ei fin F0 Fin Fb gv xsb ks tvF tvbs tvH]
        obtain env'' where bn: "(mk_hnf bs js H ?ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env''"
          and post: "einv A K env''" "tyenv env'' = ?\<theta>" "extends env env''" "prunes env env'' X"
            "card (ubv env'' X) \<le> card (ubv env X)" "newb env env''"
          and lkF: "vt_lookup (tenv env'') F = Some (Fty, abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (app H ?ks))"
          by blast
        let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (app H ?ks)"
        note g = genvar_simps[OF gv]
        have mk: "mk_hnf bs js H ?ks = return ?u" by (simp add: mk_hnf_def mkabs_ok[OF xsb])
        have upd: "update (F, Fty) ?u env1 = return env''" using bn mk by simp
        have pe: "pr xs s env d bs = return (app H ?ls, env'')"
          using pr_s nAbs hts h js js' tg' gv mk upd by (simp add: pr_step_def Let_def)
        note u = ok_update[OF upd[unfolded return_def]]
        let ?H = "(fst F, maxidx env + 1)"
        have H: "H = Var ?H Hty" by (rule g(4))
        have lk'': "vt_lookup (tenv env'') x = (if x = F then Some (Fty, ?u) else vt_lookup (tenv env) x)" for x
          using u(2) g(1) by simp
        have H0: "vt_lookup (tenv env) ?H = None"
        proof (rule ccontr)
          assume "vt_lookup (tenv env) ?H \<noteq> None"
          then obtain b where "vt_lookup (tenv env) ?H = Some b" by blast
          from bbelowD[OF e(5) this] show False by simp
        qed
        have FH: "?H \<noteq> F" using Fb by (simp add: prod_eq_iff)
        have H'': "vt_lookup (tenv env'') ?H = None" using lk''[of ?H] H0 FH by simp
        have prc: "prunesc env env'' X"
        proof (rule prunesc_trans[OF prunesc_genvar[OF gv] _ extends_update[OF upd[unfolded return_def]] extends_genvar[OF gv]])
          have ei1: "einv A K env1" by (rule einv_genvar[OF gv ei])
          note e1 = einvD[OF ei1] and e2 = einvD[OF post(1)]
          have cu: "closed ?u" using e2(4) lkF unfolding closed_env_def by blast
          show "prunesc env1 env'' X"
          proof (rule prunesc_update[OF upd[unfolded return_def] _ e1(3) e2(3) e1(4) cu H'' e1(6,7)])
            show "?u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) js) (Var ?H Hty \<degree>\<degree> map Bound ?ks)"
              by (simp add: app_apps H)
          qed
        qed
        have "prpostc A K env X s (Ok (app H ?ls, env''))"
        proof (rule prpostc_OkI[OF post(1) W[OF pe[unfolded return_def] post(2)] post(2,3) prc post(5,6)])
          fix x b assume x'': "vt_lookup (tenv env'') x = Some b" and x0: "vt_lookup (tenv env) x = None"
          have "x = F" using lk''[of x] x'' x0 by (cases "x = F") simp_all
          moreover have "F \<in> fst ` vars (unf env s')"
          proof -
            have "(F, Fty) \<in> vars (unf env s')"
              using F0 by (simp add: s' h unf_apps vars_apps unf_Var[OF e(3)])
            then show ?thesis by force
          qed
          ultimately show "x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" using nm' by blast
        next
          have "unf env'' (app H ?ls) = app H ?ls"
            using H'' by (simp add: app_apps unf_apps H unf_Var[OF einvD(3)[OF post(1)]] comp_def)
          then show "fst ` vars (unf env'' (app H ?ls)) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
            by (simp add: H)
          show "ttvars (app H ?ls) \<subseteq> tvars_env (tyenv env) \<union> A" using tvH by (simp add: H)
          show "vars (app H ?ls) \<subseteq> X \<union> evars env''" using evarsI2[OF lkF] by (simp add: H)
        qed
        from dcut_okI[OF pe[unfolded return_def] this PE] show ?thesis .
      qed
      qed
    next
      case nVar: False
      show ?thesis
      proof (cases "is_Abs h")
        case True
        then have "pr xs s env d bs = raise Pattern" using pr_s nAbs nVar hts by (simp add: pr_step_def)
        then show ?thesis by (intro dcut_errI[where e = Pattern]) (simp_all add: raise_def)
      next
        case nAbs_h: False
        have rh: "rigid h" using nVar nAbs_h nApp by (cases h) auto
        have Mc_ts: "Mc ?\<rho> env t < n" if tin: "t \<in> set ts" for t
        proof -
          have "Mc ?\<rho> env s' = 1 + sum_list (map (Mc ?\<rho> env) ts)"
            using Mc_rigid[OF rh tyu'[unfolded s']] s' by simp
          moreover have "Mc ?\<rho> env t \<le> sum_list (map (Mc ?\<rho> env) ts)"
            using tin by (simp add: member_le_sum_list)
          ultimately show ?thesis using Ms' by simp
        qed
        let ?hc = "case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h"
        have hd: "(\<exists>h''. ?hc = return h'' \<and> vars h'' = {} \<and> ttvars h'' \<subseteq> ttvars h \<and> rigid h'') \<or>
            (\<exists>v. ?hc = raise (Unif v))"
        proof (cases h)
          case (Bound i)
          then show ?thesis using trans_result[of xs d i] by auto
        qed (use rh in auto)
        then show ?thesis
        proof
          assume "\<exists>v. ?hc = raise (Unif v)"
          then obtain v where hv: "?hc = raise (Unif v)" by blast
          have "pr xs s env d bs = raise (Unif v)"
            using pr_s nAbs nVar nAbs_h hts hv by (simp add: pr_step_def)
          then show ?thesis by (intro dcut_errI[where e = "Unif v"]) (simp_all add: raise_def)
        next
          assume "\<exists>h''. ?hc = return h'' \<and> vars h'' = {} \<and> ttvars h'' \<subseteq> ttvars h \<and> rigid h''"
          then obtain h'' where hh: "?hc = return h''" "vars h'' = {}" "ttvars h'' \<subseteq> ttvars h" "rigid h''"
            by blast
          let ?N = "fst ` vars (unf env s) \<union> {y. maxidx env < snd y}"
          have Nts: "\<forall>t\<in>set ts. fst ` vars (unf env t) \<subseteq> ?N"
          proof
            fix t assume tin: "t \<in> set ts"
            have "vars (unf env t) \<subseteq> vars (unf env s')"
              using tin unfolding s' unf_apps vars_apps by auto
            then have "fst ` vars (unf env t) \<subseteq> fst ` vars (unf env s')" by (rule image_mono)
            with nm' show "fst ` vars (unf env t) \<subseteq> ?N" by blast
          qed
          have "\<exists>r. dcut snd (mapAccM (\<lambda>s env. pr xs s env d bs) ts env) = Some r \<and> prspostc A K env X ?N r"
          proof (rule mapAccM_pr_dfd[OF ei d xs0 ei wi refl extends_refl prunesc_same[OF refl refl] newb_refl _ Nts])
            show "{y. maxidx env < snd y} \<subseteq> ?N" by blast
          next
            fix t env2 assume tin: "t \<in> set ts" and ei2: "einv A K env2" and wi2: "winv env2 X"
              and th2: "tyenv env2 = ?\<theta>" and ext2: "extends env env2" and pr2: "prunesc env env2 X"
              and nb2: "newb env env2"
            show "\<exists>r. dcut snd (pr xs t env2 d bs) = Some r \<and> prpostc A K env2 X t r"
            proof (rule less.IH[OF _ refl ei2 wi2 fin _ _ _ lbts[OF tin] _ d xs0])
              have r2: "tsol (tyenv env2) ?\<rho>" "cert_inst ?\<rho>" using einv_rho0[OF ei2] th2 by simp_all
              have w2: "wt_env ?\<rho> env2" "vinv ?\<rho> env2 X" using winvD[OF wi2 r2] by blast+
              have vc2: "vcons ?\<rho> (X \<union> evars env2)" using w2(2) by (simp add: vinv_def)
              obtain e T where tyt: "e \<turnstile> inst ?\<rho> t : T" using tyts[OF tin r0] by blast
              have "Mc ?\<rho> env2 t = Mc ?\<rho> env t"
                using pr2 w2(1) tok_einv[OF ei2, of X] vX th2 vts[OF tin] tyt unfolding prunesc_def by auto
              then show "Mc (tnorm_inst (tyenv env2)) env2 t < n" using Mc_ts[OF tin] th2 by simp
              show "vtvars X \<subseteq> tvars_env (tyenv env2) \<union> A" using vX th2 by simp
              show "vars t \<subseteq> X \<union> evars env2" using vts[OF tin] evars_extends[OF ext2] by blast
              show "ttvars t \<union> btvars bs \<subseteq> tvars_env (tyenv env2) \<union> A" using tvts[OF tin] tvbs th2 by simp
            next
              fix \<rho> assume "tsol (tyenv env2) \<rho>" "cert_inst \<rho>"
              then show "\<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> t : T" using tyts[OF tin] th2 by simp
            qed
          qed
          then obtain r where r: "dcut snd (mapAccM (\<lambda>s env. pr xs s env d bs) ts env) = Some r"
            "prspostc A K env X ?N r"
            by blast
          have st: "pr xs s env d bs = mapAccM (\<lambda>s env. pr xs s env d bs) ts env \<bind>
              (\<lambda>(us, env'). return (h'' \<degree>\<degree> us, env'))"
            using pr_s nAbs nVar nAbs_h hts hh(1) by (simp add: pr_step_def list_comb_apps)
          show ?thesis
          proof (cases r)
            case (Err ex)
            show ?thesis unfolding st
              by (rule dcut_bind_errI[OF r(1)[unfolded Err]]) (use r(2) Err in auto)
          next
            case (Ok p)
            obtain us env' where p: "p = (us, env')" by force
            note qo = prspostc_OkD[OF r(2)[unfolded Ok p]]
            have pe: "pr xs s env d bs = return (h'' \<degree>\<degree> us, env')"
              using st dcut_OkD(1)[OF r(1)[unfolded Ok p]] by (simp add: return_def[symmetric])
            have "prpostc A K env X s (Ok (h'' \<degree>\<degree> us, env'))"
            proof (rule prpostc_OkI[OF qo(1) W[OF pe[unfolded return_def] qo(3)] qo(3-7)])
              fix x b assume "vt_lookup (tenv env') x = Some b" "vt_lookup (tenv env) x = None"
              from qo(8)[OF this] show "x \<in> ?N" .
            next
              show "fst ` vars (unf env' (h'' \<degree>\<degree> us)) \<subseteq> ?N"
              proof
                fix x assume "x \<in> fst ` vars (unf env' (h'' \<degree>\<degree> us))"
                then obtain q where q: "q \<in> vars (unf env' (h'' \<degree>\<degree> us))" "x = fst q" by blast
                from q(1) have "q \<in> vars (unf env' h'' \<degree>\<degree> map (unf env') us)" by (simp only: unf_apps)
                then obtain u where u: "u \<in> set us" "q \<in> vars (unf env' u)"
                  using hh(2) unf_rigid[OF hh(4)] unfolding vars_apps by auto
                from u(2) q(2) have "x \<in> fst ` vars (unf env' u)" by blast
                with qo(9)[OF u(1)] show "x \<in> ?N" by blast
              qed
              have "ttvars h \<subseteq> ttvars s'" by (simp add: s' ttvars_apps)
              then show "ttvars (h'' \<degree>\<degree> us) \<subseteq> tvars_env (tyenv env) \<union> A"
                unfolding ttvars_apps using hh(3) tvs' qo(10) by blast
              show "vars (h'' \<degree>\<degree> us) \<subseteq> X \<union> evars env'"
                unfolding vars_apps using hh(2) qo(11) by blast
            qed
            from dcut_okI[OF pe[unfolded return_def] this PE] show ?thesis .
          qed
        qed
      qed
    qed
  qed
  qed
qed


theorem pr_dfd:
  assumes "einv A K env" "winv env X" "finite X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vars s \<subseteq> X \<union> evars env" "ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and "\<not> loose_bvar s (ilength bs)"
    and "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and "0 \<le> d" "\<forall>x\<in>set xs. 0 \<le> x"
  shows "\<exists>r. dcut snd (pr xs s env d bs) = Some r \<and> prpostc A K env X s r"
  by (rule pr_dfd_aux[OF refl assms])

corollary proj_dfd:
  assumes "einv A K env" "winv env X" "finite X" "vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    and "vars s \<subseteq> X \<union> evars env" "ttvars s \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    and "\<not> loose_bvar s (ilength bs)"
    and "\<And>\<rho>. tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>e T. bs_env \<rho> e bs \<and> e \<turnstile> inst \<rho> s : T"
    and "\<forall>x\<in>set is. 0 \<le> x"
  shows "\<exists>r. dcut snd (proj s env bs is) = Some r \<and> prpostc A K env X s r"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  have "prpostc A K env X s (Ok (s, env))"
  proof (rule prpostc_OkI[OF assms(1,2) refl extends_refl prunesc_same[OF refl refl] order_refl newb_refl])
    show "\<And>x b. vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow>
        x \<in> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by simp
    show "fst ` vars (unf env s) \<subseteq> fst ` vars (unf env s) \<union> {y. maxidx env < snd y}" by blast
    show "ttvars s \<subseteq> tvars_env (tyenv env) \<union> A" using assms(6) by blast
    show "vars s \<subseteq> X \<union> evars env" by (rule assms(5))
  qed
  then show ?thesis using True by (intro dcut_okI[of _ "(s, env)"]) (simp_all add: proj_def return_def)
next
  case False
  with pr_dfd[OF assms(1-8) order_refl assms(9)] show ?thesis by (simp add: proj_def)
qed


subsection \<open>Flex-flex problems\<close>

lemma bind_new_dfd:
  assumes ei: "einv A K env" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env" "snd F \<le> maxidx env"
    and gv: "genvar a env Hty = (env1, H)"
    and xs: "\<forall>i\<in>set xs. 0 \<le> i \<and> i < ilength bs" and ks: "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength xs"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
      "tvars Hty \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "\<exists>env'. (mk_hnf bs xs H ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env' \<and>
    einv A K env' \<and> tyenv env' = tyenv env \<and> extends env env' \<and> prunesc env env' X \<and>
    card (ubv env' X) \<le> card (ubv env X) \<and> newb env env' \<and>
    vt_lookup (tenv env') F = Some (Fty, abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app H ks))"
proof -
  note e = einvD[OF ei] and g = genvar_simps[OF gv]
  let ?H = "(a, maxidx env + 1)" and ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (app H ks)"
  have H: "H = Var ?H Hty" by (rule g(4))
  have mk: "mk_hnf bs xs H ks = return ?u" by (simp add: mk_hnf_def mkabs_ok[OF xs])
  have F1: "vt_lookup (tenv env1) F = None" using F(1) g(1) by simp
  obtain env' where upd: "update (F, Fty) ?u env1 = return env'" using update_ok[OF F1] by blast
  note u = ok_update[OF upd[unfolded return_def]]
  have FH: "F \<noteq> ?H" using F(3) by auto
  have H1: "vt_lookup (tenv env1) ?H = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env1) ?H \<noteq> None"
    then obtain b where "vt_lookup (tenv env) ?H = Some b" using g(1) by auto
    from bbelowD[OF e(5) this] show False by simp
  qed
  have H': "vt_lookup (tenv env') ?H = None" using H1 FH u(2) by simp
  have vu: "vars ?u = {(?H, Hty)}" by (simp add: H)
  have cl: "closed ?u"
    by (rule closed_abs_list) (use ks in \<open>simp add: H loose_bvar_app_Var ilength_eq\<close>)
  have ei1: "einv A K env1" by (rule einv_genvar[OF gv ei])
  have ei': "einv A K env'"
  proof (rule einv_update[OF ei1 upd[unfolded return_def] _ cl])
    fix y U assume "(y, U) \<in> vars ?u"
    with vu have "y = ?H" by simp
    then show "(F, y) \<notin> (dep env1)\<^sup>*" using not_dep_unbound[OF H1 FH] by simp
  next
    show "snd F \<le> maxidx env1" using F(3) g(3) by simp
  next
    have "btvars (map (\<lambda>i. bs ! nat_of_integer i) xs) \<subseteq> btvars bs" by (rule btvars_nths[OF xs])
    then show "tvars Fty \<union> ttvars ?u \<subseteq> tvars_env (tyenv env1) \<union> A"
      using tv by (auto simp: ttvars_abs_list H g(2))
  qed
  have ext1: "extends env env1" by (rule extends_genvar[OF gv])
  have ext': "extends env1 env'" by (rule extends_update[OF upd[unfolded return_def]])
  have pr: "prunesc env env' X"
  proof (rule prunesc_trans[OF prunesc_genvar[OF gv] _ ext' ext1])
    note e1 = einvD[OF ei1] and e' = einvD[OF ei']
    show "prunesc env1 env' X"
    proof (rule prunesc_update[OF upd[unfolded return_def] _ e1(3) e'(3) e1(4) cl H' e1(6,7)])
      show "?u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) xs) (Var ?H Hty \<degree>\<degree> map Bound ks)"
        by (simp add: H app_apps)
    qed
  qed
  have Fin: "F \<in> fst ` (X \<union> evars env1)" using F(2) evars_genvar[OF gv] by (metis fst_conv image_eqI)
  have "card (ubv env' X) \<le> card (ubv env1 X)"
    by (rule card_ubv_update(2)[OF fin upd[unfolded return_def] Fin, of ?H Hty]) (use vu in simp)
  then have card: "card (ubv env' X) \<le> card (ubv env X)" by (simp add: ubv_genvar[OF gv])
  have nb: "newb env env'"
    by (rule newb_update[OF upd[unfolded return_def] _ newb_genvar[OF gv]]) (use vu in simp)
  show ?thesis using mk upd ei' u(2,3) g(2) extends_trans[OF ext1 ext'] pr card nb by auto
qed



lemma mk_ff_list_aux_Failure:
  "length is \<noteq> length js \<Longrightarrow> mk_ff_list_aux is js k = raise (Failure (STR ''mk_ff_list''))"
  by (induction "is" js k rule: mk_ff_list_aux.induct) (auto simp: bindM_def raise_def)

text \<open>
  With one name at two types on both sides, the numbers of arguments may differ, and
  \<open>flexflex1\<close> fails with \<open>Failure "mk_ff_list"\<close> (as \<open>Pattern.flexflex1\<close> raises
  \<open>Fail "mk_ff_list"\<close>).
\<close>

lemma flexflex1_dfd:
  assumes ei: "einv A K env" and wi: "winv env X" and fin: "finite X"
    and F: "vt_lookup (tenv env) F = None" "(F, Fty) \<in> X \<union> evars env"
    and tyF: "e \<turnstile> inst (tnorm_inst (tyenv env)) (app (Var F Fty) is) : T"
    and lF: "\<not> loose_bvar (app (Var F Fty) is) (ilength bs)"
    and tv: "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "(\<exists>env'. flexflex1 env bs F Fty is js = return env' \<and> einv A K env' \<and> tyenv env' = tyenv env \<and>
    extends env env' \<and> prunesc env env' X \<and> card (ubv env' X) \<le> card (ubv env X)) \<or>
    flexflex1 env bs F Fty is js = raise (Failure (STR ''mk_ff_list''))"
proof (cases "is = js")
  case True
  then show ?thesis using ei by (auto simp: flexflex1_def intro: prunesc_same)
next
  case False
  show ?thesis
  proof (cases "length is = length js")
    case len: False
    then have "mk_ff_list is js = raise (Failure (STR ''mk_ff_list''))"
      by (simp add: mk_ff_list_def mk_ff_list_aux_Failure)
    then show ?thesis using False by (simp add: flexflex1_def bindM_def raise_def)
  next
    case len: True
    let ?\<theta> = "tyenv env" let ?\<rho> = "tnorm_inst ?\<theta>"
    note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
    have vi: "vinv ?\<rho> env X" using winvD[OF wi r0] by blast
    from tyF obtain F1: "tsubst ?\<rho> Fty = map e is \<Rrightarrow> T" and is0: "\<forall>i\<in>set is. 0 \<le> i" by (rule typing_appE)
    from len have "length (map e is) = length (map e js)" by simp
    then obtain ks where ks: "mk_ff_list is js = return ks" using mk_ff_list_ok by force
    have ks': "\<forall>k\<in>set ks. 0 \<le> k \<and> k < ilength (map e is)"
      using ok_mk_ff_list(2)[OF ks[unfolded return_def]] by (simp add: ilength_eq)
    have tc: "tcons ?\<theta> Fty" by (rule tinv_tcons[OF e(2) tv(1)])
    obtain Hty where tg: "type_of_G env Fty (ilength (map e is)) ks = return Hty"
      using type_of_G_ok[OF e(6,7) tc _ ks'] F1 by force
    have tvH: "tvars Hty \<subseteq> tvars_env ?\<theta> \<union> A"
      by (rule type_of_G_tvars[OF tg[unfolded return_def] e(1) tv(1)])
    obtain env1 H where gv: "genvar (fst F) env Hty = (env1, H)" by force
    have xs: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs" using is0 app_Bounds_less[OF lF] by blast
    have Fb: "snd F \<le> maxidx env" using vi F(2) unfolding vinv_def by (blast dest: belowD)
    from bind_new_dfd[OF ei fin F(1,2) Fb gv xs ks'[simplified ilength_eq length_map, folded ilength_eq] tv tvH]
    obtain env' where r: "(mk_hnf bs is H ks \<bind> (\<lambda>t. update (F, Fty) t env1)) = return env'"
      and post: "einv A K env'" "tyenv env' = tyenv env" "extends env env'" "prunesc env env' X"
        "card (ubv env' X) \<le> card (ubv env X)"
      by blast
    have "flexflex1 env bs F Fty is js = return env'"
      using False ks tg gv r by (simp add: flexflex1_def mk_new_hnf_def ilength_eq)
    with post show ?thesis by blast
  qed
qed

end

end
