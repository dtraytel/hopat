section \<open>Completeness of Pattern Unification\<close>

theory Pattern_Complete
  imports Pattern_Occurs
begin

context pure_sig
begin

subsection \<open>Head normal forms\<close>

text \<open>The head of a head normal form that is not an abstraction is not an abstraction:\<close>

lemma head_norm_head:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t' \<Longrightarrow> \<not> is_Abs (fst (strip_comb t'))"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "\<not> is_Abs (fst (strip_comb u'))" if "ok (hn env u) u'" "\<not> is_Abs u'" for u u'
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    then show ?thesis using IH "1.prems"(2) Var by (cases lr) (auto simp: strip_comb_def)
  next
    case (Abs a T body)
    with h "1.prems"(2) show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with h App IH "1.prems"(2) show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest IH "1.prems"(2) show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) simp_all
        with IH[OF nf nA] show ?thesis by (simp add: strip_comb_App)
      qed
    qed
  qed (use h "1.prems"(2) in \<open>auto simp: strip_comb_def\<close>)
qed


subsection \<open>Composing the steps\<close>

lemma step_cp_None: "step_cp env bs s t None"
  by (simp add: step_cp_def ccon_def)

lemma step_cp_hn_bind:
  assumes "\<And>s' t'. ok (head_norm env s) s' \<Longrightarrow> ok (head_norm env t) t' \<Longrightarrow> step_cp env bs s' t' (g s' t')"
  shows "step_cp env bs s t (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. g s' t')))"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume h: "cinv \<rho> \<sigma> env e bs X A" "vars s \<union> vars t \<subseteq> X" "cterm \<rho> env e bs A s T"
    "cterm \<rho> env e bs A t T" "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  show "ccon \<rho> \<sigma> env e bs X A (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. g s' t')))"
  proof (rule ccon_bindM[OF no_unif_head_norm'])
    fix s' assume hs: "ok (head_norm env s) s'"
    show "ccon \<rho> \<sigma> env e bs X A (head_norm env t \<bind> (\<lambda>t'. g s' t'))"
    proof (rule ccon_bindM[OF no_unif_head_norm'])
      fix t' assume ht: "ok (head_norm env t) t'"
      show "ccon \<rho> \<sigma> env e bs X A (g s' t')"
        by (rule step_cpD[OF step_cp_head_norm[OF hs ht assms[OF hs ht]] h])
    qed
  qed
qed

lemma step_cp_flex_bind:
  assumes "\<And>is. ok (ints_of' env ss) is \<Longrightarrow> step_cp env bs (app (Var F Fty) is) t (r is)"
  shows "step_cp env bs (Var F Fty \<degree>\<degree> ss) t (ints_of' env ss \<bind> r)"
proof (rule step_cpI)
  fix \<rho> \<sigma> e X A T
  assume h: "cinv \<rho> \<sigma> env e bs X A" "vars (Var F Fty \<degree>\<degree> ss) \<union> vars t \<subseteq> X"
    "cterm \<rho> env e bs A (Var F Fty \<degree>\<degree> ss) T" "cterm \<rho> env e bs A t T"
    "ap \<rho> \<sigma> (Var F Fty \<degree>\<degree> ss) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  show "ccon \<rho> \<sigma> env e bs X A (ints_of' env ss \<bind> r)"
  proof (rule ccon_bindM[OF no_unif_ints_of'])
    fix "is" assume is_ok: "ok (ints_of' env ss) is"
    show "ccon \<rho> \<sigma> env e bs X A (r is)" by (rule step_cpD[OF step_cp_flex[OF is_ok assms[OF is_ok]] h])
  qed
qed

lemma step_cp_flex_bind_r:
  assumes "\<And>js. ok (ints_of' env ts) js \<Longrightarrow> step_cp env bs s (app (Var G Gty) js) (r js)"
  shows "step_cp env bs s (Var G Gty \<degree>\<degree> ts) (ints_of' env ts \<bind> r)"
proof -
  have "step_cp env bs (Var G Gty \<degree>\<degree> ts) s (ints_of' env ts \<bind> r)"
    by (rule step_cp_flex_bind) (rule step_cp_sym, rule assms)
  then show ?thesis by (rule step_cp_sym)
qed

lemma step_cp_unif_step:
  assumes IH: "\<And>bs1 s1 t1 env1. step_cp env1 bs1 s1 t1 (uni alg bs1 s1 t1 env1)"
    and occ: "\<And>F Fty is t h ts. strip_comb t = (h, ts) \<Longrightarrow> rigid h \<Longrightarrow> rocc_ok env bs F Fty is t"
    and hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'"
  shows "step_cp env bs s' t' (unif_step uni alg bs s' t' env)"
proof (cases "is_Abs s'")
  case sAbs: True
  then obtain ns Ts ts where s': "s' = Abs ns Ts ts" by (cases s') auto
  show ?thesis
  proof (cases "is_Abs t'")
    case True
    then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
    have eq: "unif_step uni alg bs s' t' env =
        unify_types alg Ts Tt env \<bind> uni alg ((if ns = STR '''' then nt else ns, Ts) # bs) ts tt"
      by (simp add: unif_step_def s' t' Let_def)
    show ?thesis unfolding eq unfolding s' t' by (rule step_cp_Abs[OF IH])
  next
    case False
    then show ?thesis unfolding s' unif_step_def by simp (rule step_cp_eta[OF IH])
  qed
next
  case nsAbs: False
  show ?thesis
  proof (cases "is_Abs t'")
    case True
    then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
    show ?thesis unfolding t' unif_step_def using nsAbs
      by simp (rule step_cp_sym[OF step_cp_eta[OF step_cp_sym[OF IH]]])
  next
    case ntAbs: False
    obtain hs ss where shs: "strip_comb s' = (hs, ss)" by force
    obtain ht ts where sht: "strip_comb t' = (ht, ts)" by force
    have s': "s' = hs \<degree>\<degree> ss" and t': "t' = ht \<degree>\<degree> ts"
      by (rule strip_comb_apps[OF shs], rule strip_comb_apps[OF sht])
    have nAh: "\<not> is_Abs hs" "\<not> is_Abs ht"
      using head_norm_head[OF hs refl nsAbs] head_norm_head[OF ht refl ntAbs] shs sht by simp_all
    have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
      using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
    have rig: "rigid h" if "\<not> is_Var h" "\<not> is_Abs h" "\<not> (\<exists>f u. h = f $ u)" for h
      using that by (cases h) auto
    have body: "unif_step uni alg bs s' t' env =
        (if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (Var F Fty, Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env bs F Fty is t'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env bs F Fty is s'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht))"
      using nsAbs ntAbs shs sht by (simp add: unif_step_def)
    show ?thesis
    proof (cases "is_Var hs")
      case sVar: True
      then obtain F Fty where hsF: "hs = Var F Fty" by (cases hs) auto
      show ?thesis
      proof (cases "is_Var ht")
        case True
        then obtain G Gty where htG: "ht = Var G Gty" by (cases ht) auto
        have "step_cp env bs (Var F Fty \<degree>\<degree> ss) (Var G Gty \<degree>\<degree> ts)
            (ints_of' env ss \<bind> (\<lambda>is. ints_of' env ts \<bind> (\<lambda>js.
              if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js)))"
        proof (rule step_cp_flex_bind, rule step_cp_flex_bind_r)
          fix "is" js assume is_ok: "ok (ints_of' env ss) is" and js_ok: "ok (ints_of' env ts) js"
          show "step_cp env bs (app (Var F Fty) is) (app (Var G Gty) js)
              (if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js)"
          proof (cases "F = G")
            case True
            then show ?thesis using step_cp_flexflex1[of env bs F Fty "is" Gty js] by simp
          next
            case False
            then show ?thesis
              using step_cp_flexflex2[OF ints_of'_distinct[OF is_ok] ints_of'_distinct[OF js_ok]] by simp
          qed
        qed
        then show ?thesis using body by (simp add: s' t' hsF htG)
      next
        case ntVar: False
        have rh: "rigid ht" by (rule rig[OF ntVar nAh(2) nApp(2)])
        have "step_cp env bs (Var F Fty \<degree>\<degree> ss) t' (ints_of' env ss \<bind> (\<lambda>is. flexrigid env bs F Fty is t'))"
        proof (rule step_cp_flex_bind)
          fix "is" assume is_ok: "ok (ints_of' env ss) is"
          show "step_cp env bs (app (Var F Fty) is) t' (flexrigid env bs F Fty is t')"
            by (rule step_cp_flexrigid'[OF ints_of'_distinct[OF is_ok] occ[OF sht rh]])
        qed
        then show ?thesis using body sVar ntVar by (simp add: s' hsF)
      qed
    next
      case nsVar: False
      have rhs: "rigid hs" by (rule rig[OF nsVar nAh(1) nApp(1)])
      show ?thesis
      proof (cases "is_Var ht")
        case True
        then obtain F Fty where htF: "ht = Var F Fty" by (cases ht) auto
        have "step_cp env bs (Var F Fty \<degree>\<degree> ts) s' (ints_of' env ts \<bind> (\<lambda>is. flexrigid env bs F Fty is s'))"
        proof (rule step_cp_flex_bind)
          fix "is" assume is_ok: "ok (ints_of' env ts) is"
          show "step_cp env bs (app (Var F Fty) is) s' (flexrigid env bs F Fty is s')"
            by (rule step_cp_flexrigid'[OF ints_of'_distinct[OF is_ok] occ[OF shs rhs]])
        qed
        from step_cp_sym[OF this] show ?thesis using body nsVar by (simp add: t' htF)
      next
        case ntVar: False
        have rht: "rigid ht" by (rule rig[OF ntVar nAh(2) nApp(2)])
        have body': "unif_step uni alg bs s' t' env = (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)"
          using body nsVar ntVar nAh by simp
        have clash: "step_cp env bs (hs \<degree>\<degree> ss) (ht \<degree>\<degree> ts) r" if "\<And>\<rho>. inst \<rho> hs \<noteq> inst \<rho> ht" for r
          by (rule step_cp_clash[OF rhs rht that])
        have "step_cp env bs (hs \<degree>\<degree> ss) (ht \<degree>\<degree> ts) (unif_step uni alg bs s' t' env)"
        proof (cases hs)
          case hsC: (Const a Ta)
          show ?thesis
          proof (cases "ht")
            case (Const b Tb)
            show ?thesis
            proof (cases "a = b")
              case True
              then show ?thesis
                by (simp add: body' hsC Const) (rule step_cp_rigid_types[OF IH disjI1[OF refl]])
            qed (use clash hsC Const in \<open>auto simp: body'\<close>)
          qed (use clash hsC rht in \<open>auto simp: rigid_def\<close>)
        next
          case hsF: (Free a Ta)
          show ?thesis
          proof (cases "ht")
            case (Free b Tb)
            show ?thesis
            proof (cases "a = b")
              case True
              then show ?thesis
                by (simp add: body' hsF Free) (rule step_cp_rigid_types[OF IH disjI2[OF refl]])
            qed (use clash hsF Free in \<open>auto simp: body'\<close>)
          qed (use clash hsF rht in \<open>auto simp: rigid_def\<close>)
        next
          case hsB: (Bound i)
          show ?thesis
          proof (cases "ht")
            case (Bound j)
            show ?thesis
            proof (cases "i = j")
              case True
              then show ?thesis
                by (simp add: body' hsB Bound) (rule step_cp_rigid_bound[OF IH])
            qed (use clash hsB Bound in \<open>auto simp: body'\<close>)
          qed (use clash hsB rht in \<open>auto simp: rigid_def\<close>)
        qed (use rhs in \<open>auto simp: rigid_def\<close>)
        then show ?thesis by (simp add: s' t')
      qed
    qed
  qed
qed

theorem unif_complete_rel:
  assumes occ: "\<And>env bs F Fty is t h ts. strip_comb t = (h, ts) \<Longrightarrow> rigid h \<Longrightarrow> rocc_ok env bs F Fty is t"
  shows "unif alg' bs s t env = Some r \<Longrightarrow> alg' = alg \<Longrightarrow> step_cp env bs s t (Some r)"
proof (induction alg' bs s t env r rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs s t env r)
  have IH: "step_cp env1 bs1 s1 t1 (uni alg bs1 s1 t1 env1)" for bs1 s1 t1 env1
  proof (cases "uni alg bs1 s1 t1 env1")
    case None
    then show ?thesis by (simp add: step_cp_None)
  next
    case (Some r1)
    then show ?thesis using "1.IH"[OF _ refl] by simp
  qed
  have body: "head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg bs s' t' env)) = Some r"
    using "1.hyps" unfolding unif_step_def "1.prems" .
  have st: "step_cp env bs s' t' (unif_step uni alg bs s' t' env)"
    if "ok (head_norm env s) s'" "ok (head_norm env t) t'" for s' t'
    by (rule step_cp_unif_step[OF _ _ that]) (rule IH, rule occ, assumption+)
  have "step_cp env bs s t (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg bs s' t' env)))"
    by (rule step_cp_hn_bind, rule st)
  then show ?case by (simp only: body)
qed

subsection \<open>Completeness\<close>

theorem unif_complete: "unif alg bs s t env = Some r \<Longrightarrow> step_cp env bs s t (Some r)"
proof -
  have occ: "rocc_ok env bs F Fty is t" if "strip_comb t = (h, ts)" "rigid h" for env bs F Fty "is" t h ts
    by (rule rocc_ok_rigid[OF that])
  show "unif alg bs s t env = Some r \<Longrightarrow> step_cp env bs s t (Some r)"
    by (rule unif_complete_rel[OF occ]) simp_all
qed

text \<open>
  Completeness of \<^const>\<open>unify\<close> for the algebra of the signature: if \<open>(\<rho>, \<sigma>)\<close> is a solution of
  \<open>env\<close> that unifies the closed terms \<open>s\<close> and \<open>t\<close>, which are well-typed with the same type after
  instantiation by \<open>\<rho>\<close>, then \<^const>\<open>unify\<close> does not fail with \<open>Unif\<close>, and every resulting
  environment has a solution that agrees with \<open>(\<rho>, \<sigma>)\<close> on the variables of \<open>env\<close>, \<open>s\<close> and
  \<open>t\<close> (those of index at most \<^const>\<open>maxidx\<close>). The invariants are those of soundness and the type
  invariant: the type variables of \<open>env\<close>, \<open>s\<close> and \<open>t\<close> are known to the type environment or in a
  set \<open>A\<close> of type variables with unique sorts and indices at most \<^const>\<open>maxidx\<close>.
\<close>

theorem unify_complete:
  assumes u: "unify alg s t env = Some r"
    and sol: "solution \<rho> \<sigma> env" and wte: "wt_env \<rho> env" and vi: "vinv \<rho> env (vars s \<union> vars t)"
    and tv: "tvinv A env" and tvs: "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    and ty: "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" and cl: "closed s" "closed t"
    and eq: "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "no_unif (Some r)"
    and "r = Ok env' \<Longrightarrow> \<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and>
      sagree (maxidx env) \<sigma> \<sigma>' \<and> wt_env \<rho>' env' \<and> tvinv A env'"
proof -
  let ?X = "vars s \<union> vars t"
  have "bs_env \<rho> e []" by (simp add: bs_env_def)
  moreover have "vtvars ?X \<subseteq> ttvars s \<union> ttvars t" using vtvars_vars[of s] vtvars_vars[of t] by auto
  ultimately have inv: "cinv \<rho> \<sigma> env e [] ?X A"
    using sol wte vi tv tvs unfolding cinv_def btvars_def by auto
  have cs: "cterm \<rho> env e [] A s T" and ct: "cterm \<rho> env e [] A t T"
    using ty cl tvs closed_loose_bvar[of s 0] closed_loose_bvar[of t 0] by (auto simp: cterm_def)
  have c: "ccon \<rho> \<sigma> env e [] ?X A (Some r)"
    using step_cpD[OF unif_complete[OF u[unfolded unify_def]] inv order_refl cs ct eq] .
  then show "no_unif (Some r)" by (simp add: ccon_def)
  assume "r = Ok env'"
  with c obtain \<rho>' \<sigma>' where "cinv \<rho>' \<sigma>' env' e [] ?X A" "tagree (maxidx env) \<rho> \<rho>'" "sagree (maxidx env) \<sigma> \<sigma>'"
    unfolding ccon_def by blast
  then show "\<exists>\<rho>' \<sigma>'. solution \<rho>' \<sigma>' env' \<and> tagree (maxidx env) \<rho> \<rho>' \<and> sagree (maxidx env) \<sigma> \<sigma>' \<and>
      wt_env \<rho>' env' \<and> tvinv A env'"
    unfolding cinv_def by blast
qed

text \<open>In particular, a \<open>Unif\<close> failure means that there is no solution:\<close>

corollary unify_Unif:
  assumes "unify alg s t env = raise (Unif tr)"
    and "tvinv A env" "ttvars s \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "closed s" "closed t"
  shows "\<not> (\<exists>\<rho> \<sigma> e T. solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> vinv \<rho> env (vars s \<union> vars t) \<and>
    e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t)"
proof
  assume "\<exists>\<rho> \<sigma> e T. solution \<rho> \<sigma> env \<and> wt_env \<rho> env \<and> vinv \<rho> env (vars s \<union> vars t) \<and>
    e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  then obtain \<rho> \<sigma> e T where h: "solution \<rho> \<sigma> env" "wt_env \<rho> env" "vinv \<rho> env (vars s \<union> vars t)"
    "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
    by blast
  have u: "unify alg s t env = Some (Err (Unif tr))" using assms(1) by (simp add: raise_def)
  from unify_complete(1)[OF u h(1-3) assms(2,3) h(4,5) assms(4,5) h(6)] show False by simp
qed

end

end
