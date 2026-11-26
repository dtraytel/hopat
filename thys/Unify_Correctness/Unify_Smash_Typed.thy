section \<open>Smashed Unifiers that Bind Names with Several Types\<close>

theory Unify_Smash_Typed
  imports Unify_Typed_Results Unify_Acyclic
begin

text \<open>
  \<open>Unify.smash_unifiers\<close> binds the heads of the flex-flex pairs of a unifier to constant
  functions over new variables. If a head occurs with two types, the resulting environment can be
  cyclic in the names of its variables, so that it is outside the invariant of environments
  (\<^const>\<open>pure_sig_gen.einv\<close>) and has no solution by unfolding. This theory shows, without a
  hypothesis on the names, that a smashed unifier still has a typed solution: the typed reading
  of its environment (\<^const>\<open>pure_sig_gen.gbody\<close>) has a fixed point (\<open>gfix\<close>), which gives a
  solution of the bindings and of their readings at other types (\<open>gfix_gsolution\<close>). The
  invariant of a smashed unifier (\<open>smash_flexflex_invw\<close>) is \<^const>\<open>pure_sig_gen.einv\<close> with the
  fixed point in place of acyclicity (\<open>einvw\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>Fixed points of the typed reading\<close>

definition gfix :: "tinst \<Rightarrow> env \<Rightarrow> vsubst \<Rightarrow> bool" where
  "gfix \<rho> env g \<longleftrightarrow> wt_subst g \<and>
    (\<forall>x V. g x V = (case gbody \<rho> env x V of Some t \<Rightarrow> vsubst g t | None \<Rightarrow> Var x V))"

lemma gfixD:
  assumes "gfix \<rho> env g"
  shows "wt_subst g" "g x V = (case gbody \<rho> env x V of Some t \<Rightarrow> vsubst g t | None \<Rightarrow> Var x V)"
  using assms unfolding gfix_def by blast+

lemma gfix_None: "gfix \<rho> env g \<Longrightarrow> gbody \<rho> env x V = None \<Longrightarrow> g x V = Var x V"
  using gfixD(2)[of \<rho> env g x V] by simp

lemma gbody_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> gbody \<rho> env x V = None"
  by (simp add: gbody_def)

lemma gfix_unbound: "gfix \<rho> env g \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> g x V = Var x V"
  by (rule gfix_None[OF _ gbody_unbound])

lemma gfix_gsol: "acyc env \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> gfix \<rho> env (gsol \<rho> env)"
  unfolding gfix_def using gsol_unfold[of env \<rho>] wt_subst_gsol[of \<rho> env] by blast

lemma gfix_tenv: "tenv env' = tenv env \<Longrightarrow> gfix \<rho> env' g \<longleftrightarrow> gfix \<rho> env g"
  by (simp add: gfix_def gbody_def)

text \<open>A fixed point, composed with a substitution, solves the bindings and their readings at
  other types:\<close>

lemma gfix_gsolution:
  assumes gf: "gfix \<rho> env g" and wte: "wt_env \<rho> env" and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env) \<rho>"
    and \<sigma>: "wt_subst \<sigma>"
  shows "gsolution \<rho> (\<lambda>x T. vsubst \<sigma> (g x T)) env"
proof -
  let ?\<sigma>' = "\<lambda>x T. vsubst \<sigma> (g x T)"
  note wg = gfixD(1)[OF gf]
  have ws: "wt_subst ?\<sigma>'" by (rule wt_subst_comp[OF \<sigma> wg])
  have "solution \<rho> ?\<sigma>' env"
    unfolding solution_def
  proof (intro conjI allI impI)
    show "wsinst alg \<rho>" "tsol (tyenv env) \<rho>" "wt_subst ?\<sigma>'" using \<rho> ws by simp_all
    fix x U u assume b: "vt_lookup (tenv env) x = Some (U, u)"
    have "g x (tsubst \<rho> U) = vsubst g (inst \<rho> u)"
      using gfixD(2)[OF gf, of x "tsubst \<rho> U"] by (simp add: gbody_binding[OF wte b])
    then show "?\<sigma>' x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> ?\<sigma>' u" by (simp add: ap_def vsubst_vsubst)
  qed
  moreover have "vsubst ?\<sigma>' l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst ?\<sigma>' r"
    if g: "(l, r) \<in> ghosts \<rho> env" and ty: "e \<turnstile> l : T" "e \<turnstile> r : T" for l r e T
  proof -
    from g obtain x V cs b U u ds where l: "l = Var x V" and r: "r = abs_list cs b"
      and lk: "vt_lookup (tenv env) x = Some (U, u)" and iu: "inst \<rho> u = abs_list ds b"
      and len: "length cs = length ds"
      unfolding ghosts_def by blast
    from ty(1) l have TV: "T = V" by auto
    let ?t = "retype (inst \<rho> u) V"
    have a: "aconv_term ?t r" unfolding iu r by (rule ghost_retype[OF ty(2)[unfolded r TV] len])
    have "e \<turnstile> ?t : V" by (rule aconv_typing[OF a ty(2)[unfolded TV]])
    moreover have "closed u" using wte lk unfolding wt_env_def by blast
    then have "closed ?t" by (simp add: closed_def)
    ultimately have "\<forall>e'. e' \<turnstile> ?t : V" using typing_closed by blast
    then have "gbody \<rho> env x V = Some ?t" by (simp add: gbody_def lk)
    then have "g x V = vsubst g ?t" using gfixD(2)[OF gf, of x V] by simp
    then have "vsubst ?\<sigma>' l = vsubst ?\<sigma>' ?t" by (simp add: l vsubst_vsubst)
    moreover have "vsubst ?\<sigma>' ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst ?\<sigma>' r"
      by (rule conv_vsubst[OF aconv_term_conv[OF a] ws])
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis unfolding gsolution_def by blast
qed

text \<open>
  A fixed point extends to a new binding whose variables, at the instantiated types, have no
  well-typed reading in the extended environment: they are unbound, or bound with types at
  which the binding cannot be read.
\<close>

lemma gfix_update:
  assumes gf: "gfix \<rho> env g"
    and lk: "\<And>y. vt_lookup (tenv env2) y = (if y = z then Some (Z, u) else vt_lookup (tenv env) y)"
    and z: "vt_lookup (tenv env) z = None" and cl: "closed u"
    and fr: "\<And>y W. (y, W) \<in> vars (inst \<rho> u) \<Longrightarrow> gbody \<rho> env2 y W = None"
  shows "\<exists>g2. gfix \<rho> env2 g2"
proof -
  define h where "h y W = (if y = z then (case gbody \<rho> env2 z W of Some r \<Rightarrow> r | None \<Rightarrow> Var z W) else Var y W)"
    for y W
  define g2 where "g2 x V = vsubst h (g x V)" for x V
  have gb: "gbody \<rho> env2 x V = gbody \<rho> env x V" if "x \<noteq> z" for x V
    using that by (simp add: gbody_def lk)
  have r: "closed r \<and> (\<forall>e. e \<turnstile> r : V) \<and> vars r = vars (inst \<rho> u)" if "gbody \<rho> env2 z V = Some r" for r V
    using that cl by (auto simp: gbody_def lk closed_def split: if_splits)
  have wh: "wt_subst h"
    unfolding wt_subst_def closed_subst_def h_def using r by (auto simp: closed_def split: option.splits)
  have wg2: "wt_subst (\<lambda>x V. vsubst h (g x V))" by (rule wt_subst_comp[OF wh gfixD(1)[OF gf]])
  have gz: "g z V = Var z V" for V by (rule gfix_unbound[OF gf z])
  have fx: "g2 y W = Var y W" if "gbody \<rho> env2 y W = None" for y W
  proof (cases "y = z")
    case True
    then show ?thesis using that by (simp add: g2_def gz h_def)
  next
    case False
    with that gb have "gbody \<rho> env y W = None" by simp
    from gfix_None[OF gf this] False show ?thesis by (simp add: g2_def h_def)
  qed
  have "g2 x V = (case gbody \<rho> env2 x V of Some t \<Rightarrow> vsubst g2 t | None \<Rightarrow> Var x V)" for x V
  proof (cases "gbody \<rho> env2 x V")
    case None
    with fx show ?thesis by simp
  next
    case (Some t)
    show ?thesis
    proof (cases "x = z")
      case True
      with Some have t: "g2 x V = t" by (simp add: g2_def gz h_def)
      from r Some True have vt: "vars t = vars (inst \<rho> u)" by blast
      have "vsubst g2 t = vsubst Var t" by (rule vsubst_cong) (use fr fx vt in auto)
      also have "\<dots> = t" by (induction t) simp_all
      finally show ?thesis using t Some by simp
    next
      case False
      with Some gb have "gbody \<rho> env x V = Some t" by simp
      then have "g x V = vsubst g t" using gfixD(2)[OF gf, of x V] by simp
      moreover have "g2 = (\<lambda>x V. vsubst h (g x V))" by (simp add: g2_def fun_eq_iff)
      ultimately have "g2 x V = vsubst g2 t" by (simp add: vsubst_vsubst)
      with Some show ?thesis by simp
    qed
  qed
  with wg2 show ?thesis unfolding gfix_def g2_def by blast
qed

text \<open>The case of a binding whose variables are unbound afterwards:\<close>

lemma gfix_update_unbound:
  assumes gf: "\<exists>g. gfix \<rho> env g" and up: "ok (update (z, Z) s env) env2" and cl: "closed s"
    and fr: "\<And>y W. (y, W) \<in> vars s \<Longrightarrow> vt_lookup (tenv env2) y = None"
  shows "\<exists>g. gfix \<rho> env2 g"
proof -
  from gf obtain g where g: "gfix \<rho> env g" by blast
  note u = ok_update[OF up]
  show ?thesis
  proof (rule gfix_update[OF g _ u(1) cl])
    show "vt_lookup (tenv env2) y = (if y = z then Some (Z, s) else vt_lookup (tenv env) y)" for y
      by (simp add: u(2))
    show "gbody \<rho> env2 y W = None" if "(y, W) \<in> vars (inst \<rho> s)" for y W
      using that fr by (auto simp: vars_inst intro: gbody_unbound)
  qed
qed

text \<open>A constant function cannot be read at the type of its value:\<close>

lemma retype_types_abs_typing:
  "e \<turnstile> retype (types_abs Ts (Var x B)) V : V \<Longrightarrow> \<exists>Ds. length Ds = length Ts \<and> V = Ds \<Rrightarrow> B"
proof (induction Ts arbitrary: e V)
  case Nil
  then show ?case by auto
next
  case (Cons T Ts)
  from Cons.prems obtain W e' where V: "V = dom_type V \<rightarrow>\<^sub>T W"
    and b: "e' \<turnstile> retype (types_abs Ts (Var x B)) (rng_type V) : W"
    by auto
  have "rng_type V = W" by (subst V) simp
  with b Cons.IH obtain Ds where "length Ds = length Ts" "W = Ds \<Rrightarrow> B" by metis
  with V have "length (dom_type V # Ds) = length (T # Ts) \<and> V = (dom_type V # Ds) \<Rrightarrow> B" by simp
  then show ?case by blast
qed

lemma funs_neq_self: "Ds \<noteq> [] \<Longrightarrow> Ds \<Rrightarrow> B \<noteq> B"
proof (cases Ds)
  case (Cons D Ds')
  have "size B \<le> size (Ds' \<Rrightarrow> B)" by (rule size_funs)
  then have "size B < size (Ds \<Rrightarrow> B)" using Cons by simp
  then show ?thesis by auto
qed simp

lemma gbody_types_abs_None:
  assumes lk: "vt_lookup (tenv env) v = Some (T, types_abs Ts (Var x B))" and ne: "Ts \<noteq> []"
  shows "gbody \<rho> env v (tsubst \<rho> B) = None"
proof (rule ccontr)
  assume "gbody \<rho> env v (tsubst \<rho> B) \<noteq> None"
  then have "e \<turnstile> retype (types_abs (map (tsubst \<rho>) Ts) (Var x (tsubst \<rho> B))) (tsubst \<rho> B) : tsubst \<rho> B" for e
    by (auto simp: gbody_def lk inst_types_abs split: if_splits)
  from retype_types_abs_typing[OF this] obtain Ds where "length Ds = length Ts" "tsubst \<rho> B = Ds \<Rrightarrow> tsubst \<rho> B"
    by auto
  moreover from this ne have "Ds \<noteq> []" by auto
  ultimately show False using funs_neq_self[of Ds "tsubst \<rho> B"] by simp
qed


subsection \<open>The second update of a variable\<close>

lemma ok_vupdate_Var:
  assumes "ok (vupdate (a, A) (Var n N) env) env'"
  shows "a = n \<and> env' = env \<or>
    a \<noteq> n \<and> indexname_less a n \<and> vt_lookup (tenv env) n = None \<and> ok (update (n, N) (Var a N) env) env' \<or>
    a \<noteq> n \<and> indexname_less a n \<and> (\<exists>N' s. vt_lookup (tenv env) n = Some (N', s) \<and> ok (vupdate (a, A) s env) env') \<or>
    a \<noteq> n \<and> \<not> indexname_less a n \<and> ok (update (a, A) (Var n N) env) env'"
proof -
  have up: "ok (if a = n then return env
      else if indexname_less a n then lookup env n N \<bind> (\<lambda>r.
        case r of None \<Rightarrow> update (n, N) (Var a N) env | Some u \<Rightarrow> vupdate (a, A) u env)
      else update (a, A) (Var n N) env) env'"
    using assms by (subst (asm) vupdate.simps) (simp only: pterm.case fst_conv)
  consider "a = n" | "a \<noteq> n" "indexname_less a n" | "a \<noteq> n" "\<not> indexname_less a n" by blast
  then show ?thesis
  proof cases
    case 1
    with up show ?thesis by (simp add: return_def)
  next
    case 2
    with up obtain lr where lk: "ok (lookup env n N) lr"
      and rest: "ok (case lr of None \<Rightarrow> update (n, N) (Var a N) env | Some u \<Rightarrow> vupdate (a, A) u env) env'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest ok_lookup_None[OF lk[unfolded None]] 2 show ?thesis by simp
    next
      case (Some u)
      from ok_lookup_Some[OF lk[unfolded Some]] obtain N' where "vt_lookup (tenv env) n = Some (N', u)" by blast
      with rest Some 2 show ?thesis by auto
    qed
  next
    case 3
    with up show ?thesis by simp
  qed
qed


subsection \<open>Smashing keeps the fixed point\<close>

text \<open>
  \<^const>\<open>smash_flexflex1\<close> binds the heads \<open>?v :: T\<close> and \<open>?w :: U\<close> of a flex-flex pair to constant
  functions over a new variable \<open>?x :: B\<close>, or binds \<open>?x\<close> to a head without arguments. If the heads
  are one name with two types, and one of them has arguments, the resulting environment is cyclic
  in the names: \<open>?v\<close> is bound to a constant function over \<open>?x\<close>, and \<open>?x\<close> to \<open>?v :: B\<close>. At the type
  \<open>B\<close> the binding of \<open>?v\<close> cannot be read, so that the typed reading still has a fixed point.
\<close>

lemma smash_flexflex1_gfix:
  assumes sm: "okW (smash_flexflex1 (t, u) env) env'"
    and bl: "below (maxidx env) (vars t \<union> vars u \<union> evars env)"
    and gf: "\<exists>g. gfix \<rho> env g"
  shows "\<exists>g. gfix \<rho> env' g"
proof -
  from okW_smash_flexflex1[OF sm] obtain v T w U B env1 var Us env2 Ts
    where hv: "okW (var_head_of env t) (v, T)" and hw: "okW (var_head_of env u) (w, U)"
      and "ok (body_type env T) B" and g: "genvar (fst v) env B = (env1, var)"
      and "ok (binder_types env1 U) Us" and u1: "ok (vupdate (w, U) (types_abs Us var) env1) env2"
      and "ok (binder_types env1 T) Ts"
      and same: "v = w \<and> T = U \<Longrightarrow> env' = env2 \<and> Ts = Us"
      and diff: "\<not> (v = w \<and> T = U) \<Longrightarrow> ok (vupdate (v, T) (types_abs Ts var) env2) env'"
    by blast
  from okW_var_head_of[OF hv] obtain t' where nt: "ok (norm_term env t) t'"
    and ht: "head_of (strip_abs_body t') = Var v T" by blast
  from okW_var_head_of[OF hw] obtain u' where nu: "ok (norm_term env u) u'"
    and hu: "head_of (strip_abs_body u') = Var w U" by blast
  note gs = genvar_simps[OF g]
  define x where "x = (fst v, maxidx env + 1)"
  have var: "var = Var x B" using gs(4) by (simp add: x_def)
  note nvt = norm_term_vars[OF nt] and nvu = norm_term_vars[OF nu]
  have vT: "(v, T) \<in> vars t'" by (rule vars_flex[OF ht])
  have wU: "(w, U) \<in> vars u'" by (rule vars_flex[OF hu])
  have ub: "\<forall>p\<in>vars t'. vt_lookup (tenv env) (fst p) = None" "\<forall>p\<in>vars u'. vt_lookup (tenv env) (fst p) = None"
    using nvt nvu by (simp_all add: nvars_ok_def case_prod_beta)
  have v0: "vt_lookup (tenv env) v = None" using ub(1) vT by fastforce
  have w0: "vt_lookup (tenv env) w = None" using ub(2) wU by fastforce
  from nvt have nmt: "fst ` vars t' \<subseteq> fst ` vars t \<union> fst ` evars env"
    unfolding nvars_ok_def by (rule conjunct2)
  from nvu have nmu: "fst ` vars u' \<subseteq> fst ` vars u \<union> fst ` evars env"
    unfolding nvars_ok_def by (rule conjunct2)
  have "v \<in> fst ` vars t'" by (rule image_eqI[OF _ vT]) simp
  from this nmt have "v \<in> fst ` vars t \<union> fst ` evars env" by (rule set_rev_mp)
  then obtain p where "p \<in> vars t \<union> evars env" "fst p = v" by auto
  with bl have vb: "snd v \<le> maxidx env" unfolding below_def by blast
  have "w \<in> fst ` vars u'" by (rule image_eqI[OF _ wU]) simp
  from this nmu have "w \<in> fst ` vars u \<union> fst ` evars env" by (rule set_rev_mp)
  then obtain q where "q \<in> vars u \<union> evars env" "fst q = w" by auto
  with bl have wb: "snd w \<le> maxidx env" unfolding below_def by blast
  have sx: "snd x = maxidx env + 1" by (simp add: x_def)
  with vb wb have vx: "v \<noteq> x" and wx: "w \<noteq> x" by auto
  have x0: "vt_lookup (tenv env) x = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env) x \<noteq> None"
    then obtain Ux ux where "vt_lookup (tenv env) x = Some (Ux, ux)" by auto
    from evarsI[OF this] have "(x, Ux) \<in> vars t \<union> vars u \<union> evars env" by simp
    from belowD[OF bl this] have "snd x \<le> maxidx env" by simp
    with sx show False by simp
  qed
  have l1: "vt_lookup (tenv env1) y = vt_lookup (tenv env) y" for y by (simp add: gs(1))
  have gf1: "\<exists>g. gfix \<rho> env1 g" using gf by (simp add: gfix_tenv[OF gs(1)])
  let ?tU = "types_abs Us (Var x B)" and ?tT = "types_abs Ts (Var x B)"
  have cx: "closed (Var x B)" by (simp add: closed_def)
  have cU: "closed ?tU" and cT: "closed ?tT"
    by (rule closed_types_abs_closed[OF cx])+
  text \<open>The first binding: of \<open>?w\<close>, or of \<open>?x\<close> to \<open>?w\<close>.\<close>
  have s12: "(Us \<noteq> [] \<or> \<not> indexname_less w x) \<and> ok (update (w, U) ?tU env1) env2 \<or>
      Us = [] \<and> indexname_less w x \<and> ok (update (x, B) (Var w B) env1) env2"
  proof (cases Us)
    case Nil
    with u1 var have "ok (vupdate (w, U) (Var x B) env1) env2" by simp
    from ok_vupdate_Var[OF this] wx x0 l1 Nil show ?thesis by auto
  next
    case (Cons a list)
    then have "vupdate (w, U) ?tU env1 = update (w, U) ?tU env1" by (simp add: ur_vupdate_nonVar)
    with u1 var Cons show ?thesis by simp
  qed
  from s12 consider (S1) "Us \<noteq> [] \<or> \<not> indexname_less w x" "ok (update (w, U) ?tU env1) env2"
    | (S2) "Us = []" "indexname_less w x" "ok (update (x, B) (Var w B) env1) env2"
    by blast
  note sc = this
  have gf2: "\<exists>g. gfix \<rho> env2 g"
  proof (cases rule: sc)
    case S1
    note up = S1(2)
    show ?thesis
      by (rule gfix_update_unbound[OF gf1 up cU])
        (use ok_update(2)[OF up] wx x0 l1 in \<open>simp add: vars_types_abs_mi\<close>)
  next
    case S2
    note up = S2(3)
    show ?thesis
      by (rule gfix_update_unbound[OF gf1 up])
        (use ok_update(2)[OF up] wx w0 l1 in \<open>simp_all add: closed_def\<close>)
  qed
  text \<open>The binding of \<open>?v\<close> to a constant function, or to \<open>?x\<close>. If \<open>?x\<close> is bound to \<open>?w\<close>, the
    binding of \<open>?v\<close> is added first.\<close>
  have updv: "\<exists>g. gfix \<rho> env' g"
    if up: "ok (update (v, T) ?tT env2) env'" and c: "Ts \<noteq> [] \<or> \<not> indexname_less v x"
  proof (cases rule: sc)
    case S1
    note u2 = S1(2)
    show ?thesis
      by (rule gfix_update_unbound[OF gf2 up cT])
        (use ok_update(2)[OF up] ok_update(2)[OF u2] vx wx x0 l1 in \<open>simp add: vars_types_abs_mi\<close>)
  next
    case S2
    note lt = S2(2) and u2 = S2(3)
    note a = ok_update[OF u2] and b = ok_update[OF up]
    from gf1 obtain g1 where g1: "gfix \<rho> env1 g1" by blast
    define envm where "envm = Envir (maxidx env1) (vt_update (v, (T, ?tT)) (tenv env1)) (tyenv env1)"
    have lm: "vt_lookup (tenv envm) y = (if y = v then Some (T, ?tT) else vt_lookup (tenv env1) y)" for y
      by (simp add: envm_def)
    have v1: "vt_lookup (tenv env1) v = None" using v0 l1 by simp
    have "\<exists>g. gfix \<rho> envm g"
    proof (rule gfix_update[OF g1 lm v1 cT])
      fix y W assume "(y, W) \<in> vars (inst \<rho> ?tT)"
      then have "y = x" by (auto simp: vars_inst vars_types_abs_mi)
      then show "gbody \<rho> envm y W = None" using vx x0 l1 by (simp add: gbody_unbound lm)
    qed
    then obtain gm where gm: "gfix \<rho> envm gm" by blast
    have l': "vt_lookup (tenv env') y = (if y = x then Some (B, Var w B) else vt_lookup (tenv envm) y)" for y
      using vx by (auto simp: a(2) b(2) lm)
    have xm: "vt_lookup (tenv envm) x = None" using vx x0 l1 by (simp add: lm)
    show ?thesis
    proof (rule gfix_update[OF gm l' xm])
      show "closed (Var w B)" by (simp add: closed_def)
      fix y W assume "(y, W) \<in> vars (inst \<rho> (Var w B))"
      then have y: "y = w" "W = tsubst \<rho> B" by simp_all
      show "gbody \<rho> env' y W = None"
      proof (cases "w = v")
        case True
        with c lt have "Ts \<noteq> []" by auto
        moreover have "vt_lookup (tenv env') v = Some (T, ?tT)" using vx by (simp add: l' lm)
        ultimately show ?thesis unfolding y True by (rule gbody_types_abs_None[rotated])
      next
        case False
        then have "vt_lookup (tenv env') w = None" using wx w0 l1 by (simp add: l' lm)
        then show ?thesis unfolding y by (rule gbody_unbound)
      qed
    qed
  qed
  show ?thesis
  proof (cases "v = w \<and> T = U")
    case True
    with same gf2 show ?thesis by simp
  next
    case False
    note d = diff[OF False, unfolded var]
    show ?thesis
    proof (cases Ts)
      case (Cons a list)
      then have "vupdate (v, T) ?tT env2 = update (v, T) ?tT env2" by (simp add: ur_vupdate_nonVar)
      with d have "ok (update (v, T) ?tT env2) env'" by simp
      from updv[OF this] Cons show ?thesis by simp
    next
      case Nil
      with d have d': "ok (vupdate (v, T) (Var x B) env2) env'" by simp
      from ok_vupdate_Var[OF d'] vx consider
          (fresh) "indexname_less v x" "vt_lookup (tenv env2) x = None" "ok (update (x, B) (Var v B) env2) env'"
        | (chase) N' s where "indexname_less v x" "vt_lookup (tenv env2) x = Some (N', s)"
            "ok (vupdate (v, T) s env2) env'"
        | (gt) "\<not> indexname_less v x" "ok (update (v, T) (Var x B) env2) env'"
        by (elim disjE conjE exE) auto
      then show ?thesis
      proof cases
        case fresh
        have "\<not> ok (update (x, B) (Var w B) env1) env2"
        proof
          assume "ok (update (x, B) (Var w B) env1) env2"
          from ok_update(2)[OF this] fresh(2) show False by simp
        qed
        with s12 have u2: "ok (update (w, U) ?tU env1) env2" and c2: "Us \<noteq> [] \<or> \<not> indexname_less w x"
          by blast+
        from gf2 obtain g2 where g2: "gfix \<rho> env2 g2" by blast
        note a = ok_update[OF u2] and b = ok_update[OF fresh(3)]
        show ?thesis
        proof (rule gfix_update[OF g2 _ fresh(2)])
          show "vt_lookup (tenv env') y = (if y = x then Some (B, Var v B) else vt_lookup (tenv env2) y)" for y
            by (simp add: b(2))
          show "closed (Var v B)" by (simp add: closed_def)
          fix y W assume "(y, W) \<in> vars (inst \<rho> (Var v B))"
          then have y: "y = v" "W = tsubst \<rho> B" by simp_all
          show "gbody \<rho> env' y W = None"
          proof (cases "v = w")
            case True
            with c2 fresh(1) have "Us \<noteq> []" by auto
            moreover have "vt_lookup (tenv env') v = Some (U, ?tU)" using True wx by (simp add: b(2) a(2))
            ultimately show ?thesis unfolding y by (rule gbody_types_abs_None[rotated])
          next
            case False
            then have "vt_lookup (tenv env') v = None" using vx v0 l1 by (simp add: b(2) a(2))
            then show ?thesis unfolding y by (rule gbody_unbound)
          qed
        qed
      next
        case chase
        have "\<not> ok (update (w, U) ?tU env1) env2"
        proof
          assume "ok (update (w, U) ?tU env1) env2"
          from ok_update(2)[OF this] chase(2) wx x0 l1 show False by simp
        qed
        with s12 have u2: "ok (update (x, B) (Var w B) env1) env2" by blast
        from ok_update(2)[OF u2] chase(2) have s: "s = Var w B" by auto
        note a = ok_update[OF u2]
        from ok_vupdate_Var[OF chase(3)[unfolded s]] show ?thesis
        proof (elim disjE conjE exE)
          assume "env' = env2"
          with gf2 show ?thesis by simp
        next
          assume up: "ok (update (w, B) (Var v B) env2) env'" and vw: "v \<noteq> w"
          show ?thesis
            by (rule gfix_update_unbound[OF gf2 up])
              (use ok_update(2)[OF up] a(2) vx v0 l1 vw in \<open>simp_all add: closed_def\<close>)
        next
          fix N'' s' assume "vt_lookup (tenv env2) w = Some (N'', s')"
          with a(2) wx w0 l1 show ?thesis by simp
        next
          assume up: "ok (update (v, T) (Var w B) env2) env'" and vw: "v \<noteq> w"
          show ?thesis
            by (rule gfix_update_unbound[OF gf2 up])
              (use ok_update(2)[OF up] a(2) wx w0 l1 vw in \<open>simp_all add: closed_def\<close>)
        qed
      next
        case gt
        show ?thesis by (rule updv) (use gt Nil in simp_all)
      qed
    qed
  qed
qed

text \<open>All pairs:\<close>

lemma foldrW_smash_flexflex1_gfix:
  assumes f: "okW (foldrW smash_flexflex1 tps env) env'" and ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
    and gt: "gtyped env (tdps tps)" and ci: "cert_inst (tsol0 (tyenv env))"
    and gf: "\<exists>g. gfix \<rho> env g"
  shows "\<exists>g. gfix \<rho> env' g"
proof -
  let ?\<rho>0 = "tsol0 (tyenv env)"
  have s0: "tsol (tyenv env) ?\<rho>0" by (rule tsol_tsol0[OF ac tc])
  from gt s0 ci have w0: "wt_env ?\<rho>0 env" and d0: "dtyped ?\<rho>0 (tdps tps)" and v0: "vinv ?\<rho>0 env (dvars (tdps tps))"
    unfolding gtyped_def by auto
  have "\<exists>g. gfix \<rho> e' g" if "set xs \<subseteq> set tps" "okW (foldrW smash_flexflex1 xs env) e'" for xs e'
    using that
  proof (induction xs arbitrary: e')
    case Nil
    with gf show ?case by simp
  next
    case (Cons tu xs)
    obtain t u where tu: "tu = (t, u)" by force
    from Cons.prems(2) obtain env1 where f1: "okW (foldrW smash_flexflex1 xs env) env1"
      and s1: "okW (smash_flexflex1 (t, u) env1) e'"
      by (auto simp: tu)
    have sub: "set xs \<subseteq> set tps" and mem: "(t, u) \<in> set tps" using Cons.prems(1) tu by simp_all
    have g1: "\<exists>g. gfix \<rho> env1 g" by (rule Cons.IH[OF sub f1])
    have gtx: "gtyped env (tdps xs)" by (rule gtyped_mono[OF gt]) (use sub in auto)
    from foldrW_smash_flexflex1_sound[OF f1 ac tc gtx ci]
    have ds: "dstep env (tdps xs) env1 []" and ty: "tyenv env1 = tyenv env" by simp_all
    have sx: "set (tdps xs) \<subseteq> set (tdps tps)" using sub by auto
    have dx: "dtyped ?\<rho>0 (tdps xs)" by (rule dtyped_mono[OF d0 sx])
    have "dvars (tdps tps) \<union> dvars (tdps xs) = dvars (tdps tps)" using dvars_mono[OF sx] by blast
    with v0 have vx: "vinv ?\<rho>0 env (dvars (tdps tps) \<union> dvars (tdps xs))" by simp
    have "tsol (tyenv env1) ?\<rho>0" using s0 ty by simp
    from dstepDg(1)[OF ds this extends_refl w0 dx vx]
    have "vinv ?\<rho>0 env1 (dvars (tdps tps) \<union> dvars [])" by blast
    then have "below (maxidx env1) (dvars (tdps tps) \<union> evars env1)" by (simp add: vinv_def)
    moreover have "vars t \<union> vars u \<subseteq> dvars (tdps tps)" using mem by (force simp: dvars_def)
    ultimately have bl: "below (maxidx env1) (vars t \<union> vars u \<union> evars env1)"
      by (auto simp: below_def)
    show ?case by (rule smash_flexflex1_gfix[OF s1 bl g1])
  qed
  from this[OF order_refl f] show ?thesis .
qed

theorem smash_flexflex_gfix:
  assumes "okW (smash_flexflex (env, tps)) env'" "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "gtyped env (tdps tps)" "cert_inst (tsol0 (tyenv env))" "\<exists>g. gfix \<rho> env g"
  shows "\<exists>g. gfix \<rho> env' g"
  using foldrW_smash_flexflex1_gfix[of tps env env'] assms by (simp add: smash_flexflex_def)


subsection \<open>The type variables of a normal form\<close>

text \<open>The type variables of a result of \<^const>\<open>norm_term\<close> are type variables of the term, of the
  bindings or of the type environment; this needs no acyclic term environment.\<close>

lemma ttvars_subst_bound_sub: "ttvars (subst_bound u body) \<subseteq> ttvars body \<union> ttvars u"
  using ttvars_subst[of body u 0] by (simp add: subst_bound_subst)

lemma norm_term1_ttvars:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<forall>x U u. vt_lookup te x = Some (U, u) \<longrightarrow> ttvars u \<subseteq> Q \<Longrightarrow> ttvars t \<subseteq> Q \<Longrightarrow>
    ttvars t' \<subseteq> Q"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and bd = "1.prems"(2) and tv = "1.prems"(3)
  have IH: "ttvars u' \<subseteq> Q" if "ok (nt te u) u'" "ttvars u \<subseteq> Q" for u u'
    using "1.IH"[OF that(1) refl bd that(2)] .
  have sb: "ttvars (subst_bound u body) \<subseteq> Q" if "ttvars body \<subseteq> Q" "ttvars u \<subseteq> Q" for u body
    using ttvars_subst_bound_sub[of u body] that by blast
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest have "t' = t" by simp
      with tv show ?thesis by simp
    next
      case (Some u)
      with ok_lookup1[OF lr] have b: "vt_lookup te x = Some (T, u)" by simp
      from rest Some have "ok (nt te u) t'" by simp
      then show ?thesis by (rule IH) (use bd b in blast)
    qed
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH[OF this(1)] tv Abs show ?thesis by simp
  next
    case (App f u)
    have tvf: "ttvars f \<subseteq> Q" and tvu: "ttvars u \<subseteq> Q" using tv App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      moreover have "ttvars (subst_bound u body) \<subseteq> Q" by (rule sb) (use tvf f tvu in simp_all)
      ultimately show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      note nf = IH[OF hf tvf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        moreover have "ttvars (subst_bound u body) \<subseteq> Q" by (rule sb) (use nf nfA tvu in simp_all)
        ultimately show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        with IH[OF hu tvu] nf show ?thesis by simp
      qed
    qed
  qed (use h tv in auto)
qed

lemma norm_term2_ttvars:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> tvars_env (tyenv env) \<subseteq> Q \<Longrightarrow>
    \<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ttvars u \<subseteq> Q \<Longrightarrow> ttvars t \<subseteq> Q \<Longrightarrow> ttvars t' \<subseteq> Q"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2) and te = "1.prems"(3) and bd = "1.prems"(4)
    and tv = "1.prems"(5)
  have IH: "ttvars u' \<subseteq> Q" if "ok (nt env u) u'" "ttvars u \<subseteq> Q" for u u'
    using "1.IH"[OF that(1) refl ac te bd that(2)] .
  have nT: "tvars T' \<subseteq> Q" if "ok (norm_type_aux (tyenv env) T) T'" "tvars T \<subseteq> Q" for T T'
    using norm_type_aux_tnorm[OF that(1) refl ac] tvars_tnorm[OF ac, of T] that(2) te by blast
  have sb: "ttvars (subst_bound u body) \<subseteq> Q" if "ttvars body \<subseteq> Q" "ttvars u \<subseteq> Q" for u body
    using ttvars_subst_bound_sub[of u body] that by blast
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nT[OF this(1)] tv Var show ?thesis by simp
    next
      case (Some u)
      from ok_lookup_Some[OF lr[unfolded Some]] obtain U where b: "vt_lookup (tenv env) x = Some (U, u)" .
      from rest Some have "ok (nt env u) t'" by simp
      then show ?thesis by (rule IH) (use bd b in blast)
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'" "t' = Abs a T' body'"
      by auto
    with nT[OF this(1)] IH[OF this(2)] tv Abs show ?thesis by simp
  next
    case (App f u)
    have tvf: "ttvars f \<subseteq> Q" and tvu: "ttvars u \<subseteq> Q" using tv App by simp_all
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      moreover have "ttvars (subst_bound u body) \<subseteq> Q" by (rule sb) (use tvf f tvu in simp_all)
      ultimately show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      note nf = IH[OF hf tvf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfA: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        moreover have "ttvars (subst_bound u body) \<subseteq> Q" by (rule sb) (use nf nfA tvu in simp_all)
        ultimately show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        with IH[OF hu tvu] nf show ?thesis by simp
      qed
    qed
  next
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nT[OF this(1)] tv Const show ?thesis by simp
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nT[OF this(1)] tv Free show ?thesis by simp
  next
    case (Bound i)
    with h tv show ?thesis by auto
  qed
qed

theorem norm_term_ttvars:
  assumes nt: "ok (norm_term env t) t'" and ac: "tacyc (tyenv env)" and te: "tvars_env (tyenv env) \<subseteq> Q"
    and bd: "\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ttvars u \<subseteq> Q" and tv: "ttvars t \<subseteq> Q"
  shows "ttvars t' \<subseteq> Q"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "t' = t" using nt by (simp add: norm_term_def)
    with tv show ?thesis by simp
  next
    case n1
    with nt have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_ttvars[OF this refl bd tv] show ?thesis .
  next
    case n2
    with nt have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_ttvars[OF this refl ac te bd tv] show ?thesis .
  qed
qed

corollary norm_term_ttvars_tvinv:
  assumes "ok (norm_term env t) t'" "tvinv A env" "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
proof (rule norm_term_ttvars[OF assms(1) _ _ _ assms(3)])
  show "tacyc (tyenv env)" using tvinvD(1)[OF assms(2)] by (simp add: tinv_def)
  show "\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    using tvinvD(2)[OF assms(2)] by blast
qed simp


subsection \<open>The invariant of the type variables\<close>

lemma vupdate_tvinv:
  assumes "vupdate aU t env = Some r"
  shows "r = Ok env' \<Longrightarrow> tvinv A env \<Longrightarrow> tvars (snd aU) \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A \<Longrightarrow> tvinv A env'"
  using assms
proof (induction aU t env r arbitrary: env' rule: vupdate.raw_induct[rotated, consumes 1])
  case (1 vu aU t env r)
  obtain v T0 where aU: "aU = (v, T0)" by (cases aU)
  have up: "ok (case t of
      Var name' T \<Rightarrow>
        if fst aU = name' then return env
        else if indexname_less (fst aU) name' then lookup env name' T \<bind> (\<lambda>r.
          case r of None \<Rightarrow> update (name', T) (Var (fst aU) T) env | Some u \<Rightarrow> vu aU u env)
        else update aU t env
    | _ \<Rightarrow> update aU t env) env'"
    using "1.hyps" "1.prems" by simp
  note ti = "1.prems"(2) and tv = "1.prems"(3)
  let ?KN = "tvars_env (tyenv env) \<union> A"
  have upd: "tvinv A env'" if "ok (update (z, Z) s env) env'" "tvars Z \<union> ttvars s \<subseteq> ?KN" for z Z s
    by (rule tvinv_update[OF that(1) ti that(2)])
  show ?case
  proof (cases t)
    case (Var name' T)
    consider "v = name'" | "v \<noteq> name'" "indexname_less v name'" | "v \<noteq> name'" "\<not> indexname_less v name'"
      by blast
    then show ?thesis
    proof cases
      case 1
      with up Var aU ti show ?thesis by (simp add: return_def)
    next
      case 2
      with up Var aU obtain lr where lk: "ok (lookup env name' T) lr"
        and rest: "ok (case lr of None \<Rightarrow> update (name', T) (Var v T) env | Some u \<Rightarrow> vu aU u env) env'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest have "ok (update (name', T) (Var v T) env) env'" by simp
        then show ?thesis by (rule upd) (use tv Var in simp)
      next
        case (Some u)
        from ok_lookup_Some[OF lk[unfolded Some]] obtain U where b: "vt_lookup (tenv env) name' = Some (U, u)" .
        have tu: "tvars (snd aU) \<union> ttvars u \<subseteq> ?KN" using tvinvD(2)[OF ti b] tv by blast
        from rest Some have "ok (vu aU u env) env'" by simp
        from "1.IH"[OF this refl ti tu] show ?thesis .
      qed
    next
      case 3
      with up Var aU have "ok (update (v, T0) t env) env'" by simp
      then show ?thesis by (rule upd) (use tv aU in simp)
    qed
  next
    case (Const c T)
    with up aU have "ok (update (v, T0) t env) env'" by simp
    then show ?thesis by (rule upd) (use tv aU in simp)
  next
    case (Free c T)
    with up aU have "ok (update (v, T0) t env) env'" by simp
    then show ?thesis by (rule upd) (use tv aU in simp)
  next
    case (Bound i)
    with up aU have "ok (update (v, T0) t env) env'" by simp
    then show ?thesis by (rule upd) (use tv aU in simp)
  next
    case (Abs a T b)
    with up aU have "ok (update (v, T0) t env) env'" by simp
    then show ?thesis by (rule upd) (use tv aU in simp)
  next
    case (App f u)
    with up aU have "ok (update (v, T0) t env) env'" by simp
    then show ?thesis by (rule upd) (use tv aU in simp)
  qed
qed

lemma smash_flexflex1_tvinv:
  assumes sm: "okW (smash_flexflex1 (t, u) env) env'" and ti: "tvinv A env"
    and tv: "ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvinv A env'"
proof -
  from okW_smash_flexflex1[OF sm] obtain v T w U B env1 var Us env2 Ts
    where hv: "okW (var_head_of env t) (v, T)" and hw: "okW (var_head_of env u) (w, U)"
      and bB: "ok (body_type env T) B" and g: "genvar (fst v) env B = (env1, var)"
      and bU: "ok (binder_types env1 U) Us" and u1: "ok (vupdate (w, U) (types_abs Us var) env1) env2"
      and bT: "ok (binder_types env1 T) Ts"
      and same: "v = w \<and> T = U \<Longrightarrow> env' = env2 \<and> Ts = Us"
      and diff: "\<not> (v = w \<and> T = U) \<Longrightarrow> ok (vupdate (v, T) (types_abs Ts var) env2) env'"
    by blast
  from okW_var_head_of[OF hv] obtain t' where nt: "ok (norm_term env t) t'"
    and ht: "head_of (strip_abs_body t') = Var v T" by blast
  from okW_var_head_of[OF hw] obtain u' where nu: "ok (norm_term env u) u'"
    and hu: "head_of (strip_abs_body u') = Var w U" by blast
  note gs = genvar_simps[OF g]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  note tin = tvinvD(1)[OF ti]
  have "ttvars t' \<subseteq> ?KN" by (rule norm_term_ttvars_tvinv[OF nt ti]) (use tv in simp)
  moreover have "tvars T \<subseteq> ttvars t'" using vars_flex[OF ht] vtvars_vars[of t'] by (auto simp: vtvars_def)
  ultimately have tvT: "tvars T \<subseteq> ?KN" by blast
  have "ttvars u' \<subseteq> ?KN" by (rule norm_term_ttvars_tvinv[OF nu ti]) (use tv in simp)
  moreover have "tvars U \<subseteq> ttvars u'" using vars_flex[OF hu] vtvars_vars[of u'] by (auto simp: vtvars_def)
  ultimately have tvU: "tvars U \<subseteq> ?KN" by blast
  from body_type_term[OF tin refl tvT] bB have tvB: "tvars B \<subseteq> ?KN" by (auto simp: return_def)
  have ti1: "tvinv A env1" by (rule tvinv_genvar[OF g ti])
  note tin1 = tvinvD(1)[OF ti1]
  have KN1: "tvars_env (tyenv env1) \<union> A = ?KN" by (simp add: gs(2))
  from binder_types_tvars[OF tin1 refl, of U] tvU bU have tvUs: "\<forall>P\<in>set Us. tvars P \<subseteq> ?KN"
    by (auto simp: return_def KN1)
  from binder_types_tvars[OF tin1 refl, of T] tvT bT have tvTs: "\<forall>P\<in>set Ts. tvars P \<subseteq> ?KN"
    by (auto simp: return_def KN1)
  have var: "ttvars var = tvars B" using gs(4) by simp
  have ti2: "tvinv A env2"
    by (rule vupdate_tvinv[OF u1 refl ti1]) (use tvU tvUs tvB in \<open>auto simp: KN1 ttvars_types_abs var\<close>)
  have ty2: "tyenv env2 = tyenv env1" by (rule vupdate_tyenv[OF u1 refl])
  show ?thesis
  proof (cases "v = w \<and> T = U")
    case True
    with same ti2 show ?thesis by simp
  next
    case False
    show ?thesis
      by (rule vupdate_tvinv[OF diff[OF False] refl ti2])
        (use tvT tvTs tvB in \<open>auto simp: ty2 KN1 ttvars_types_abs var\<close>)
  qed
qed

lemma foldrW_smash_flexflex1_tvinv:
  assumes "okW (foldrW smash_flexflex1 tps env) env'" "tvinv A env"
    "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvinv A env' \<and> tyenv env' = tyenv env"
  using assms
proof (induction rule: okW_foldrW_induct)
  case (Nil b)
  then show ?case by simp
next
  case (Cons x xs b b1 b')
  obtain t u where x: "x = (t, u)" by force
  from Cons.IH[OF Cons.prems(1)] Cons.prems(2) have t1: "tvinv A b1" and ty1: "tyenv b1 = tyenv b" by simp_all
  have "ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv b1) \<union> A" using Cons.prems(2) x ty1 by simp
  from smash_flexflex1_tvinv[OF Cons.hyps(2)[unfolded x] t1 this] smash_flexflex1_tyenv[OF Cons.hyps(2)] ty1
  show ?case by simp
qed


subsection \<open>The invariant of smashed unifiers\<close>

text \<open>
  The invariant \<^const>\<open>einv\<close> of environments with a fixed point of the typed reading in place of
  acyclicity. An acyclic, well-typed environment has the fixed point \<^const>\<open>gsol\<close>.
\<close>

definition einvw :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "einvw A K env \<longleftrightarrow> tvinv A env \<and> scert alg (tyenv env) \<and> tcert alg (tvars_env (tyenv env) \<union> A) \<and>
    tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A) \<and> closed_env env \<and> bbelow env \<and>
    tsorted alg (tyenv env) \<and> (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>g. gfix \<rho> env g))"

lemma einvwD:
  assumes "einvw A K env"
  shows "tvinv A env" "tinv ar (maxidx env) (tyenv env) A"
    "tsol (tyenv env) \<rho> \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<exists>g. gfix \<rho> env g" "closed_env env" "bbelow env"
    "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "vt_lookup (tyenv env) v = Some (S, U) \<Longrightarrow> sorts_ok alg U"
    "scert alg (tyenv env)" "tcert alg (tvars_env (tyenv env) \<union> A)"
    "tcovered (tyenv env) K (tvars_env (tyenv env) \<union> A)" "tsorted alg (tyenv env)"
  using assms tvinvD(1)[of A env] tinv_tacyc tinv_tcons_env unfolding einvw_def scert_def by blast+

lemma einvw_rho0:
  assumes "einvw A K env"
  shows "tsol (tyenv env) (tnorm_inst (tyenv env))" "cert_inst (tnorm_inst (tyenv env))"
proof -
  note e = einvwD[OF assms]
  show "tsol (tyenv env) (tnorm_inst (tyenv env))" by (rule tsol_tnorm[OF e(6)])
  show "cert_inst (tnorm_inst (tyenv env))"
    by (rule cert_inst_tnorm[OF e(6)]) (use e(2,8) tinv_wft in blast)
qed

lemma einv_einvw:
  assumes ei: "einv A K env" and wi: "winv env X"
  shows "einvw A K env"
proof -
  have "\<exists>g. gfix \<rho> env g" if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
    using gfix_gsol[OF einvD(3)[OF ei]] winvD[OF wi that] by blast
  with ei show ?thesis by (simp add: einv_def einvw_def)
qed

text \<open>
  A smashed unifier: the environment solves the flex-flex pairs, satisfies the invariant with the
  fixed point, and is well-typed with consistent types of the variables that are not loose. No
  hypothesis on the names that the environment binds is needed.
\<close>

theorem smash_flexflex_invw:
  assumes ff: "ffres A K X env tps" and sm: "okW (smash_flexflex (env, tps)) env'"
  shows "dstep env (tdps tps) env' []" "einvw A K env'" "winv env' X" "tyenv env' = tyenv env"
proof -
  have f: "okW (foldrW smash_flexflex1 tps env) env'" using sm by (simp add: smash_flexflex_def)
  note h = ffres_smash[OF ff]
  have ei: "einv A K env" and wi: "winv env X" and pk: "\<forall>(t, u)\<in>set tps. upok A env [] X t u"
    using ff by (simp_all add: ffres_def)
  from foldrW_smash_flexflex1_sound[OF f h(1,2,4,3)] show ds: "dstep env (tdps tps) env' []"
    and th: "tyenv env' = tyenv env" by simp_all
  have pk': "\<forall>(rb, t, u)\<in>set (tdps tps). upok A env rb X t u" using pk by auto
  show wi': "winv env' X" using dstep_winv(1)[OF ds wi pk' th] by (simp add: dvars_def)
  note e = einvD[OF ei]
  have "\<forall>(t, u)\<in>set tps. ttvars t \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
    using pk upokD(3,4) by fast
  from foldrW_smash_flexflex1_tvinv[OF f e(1) this] have tv': "tvinv A env'" by simp
  let ?\<rho>0 = "tsol0 (tyenv env)"
  have s0: "tsol (tyenv env') ?\<rho>0" using tsol_tsol0[OF h(1,2)] th by simp
  from winvD[OF wi' s0 h(3)] have w0: "wt_env ?\<rho>0 env'" and v0: "vinv ?\<rho>0 env' X" by blast+
  have ce: "closed_env env'" by (rule wt_env_closed_env[OF w0])
  have bb: "bbelow env'"
    unfolding bbelow_def
  proof (intro allI impI)
    fix x b assume "vt_lookup (tenv env') x = Some b"
    then obtain U u where "vt_lookup (tenv env') x = Some (U, u)" by (cases b) auto
    from evarsI[OF this] have "(x, U) \<in> X \<union> evars env'" by simp
    with v0 show "snd x \<le> maxidx env'" unfolding vinv_def using belowD by blast
  qed
  have gf: "\<exists>g. gfix \<rho> env' g" if "tsol (tyenv env') \<rho>" "cert_inst \<rho>" for \<rho>
  proof -
    have "tsol (tyenv env) \<rho>" using that(1) th by simp
    from winvD[OF wi this that(2)] have "wt_env \<rho> env" by blast
    from gfix_gsol[OF e(3) this] have "\<exists>g. gfix \<rho> env g" by blast
    from smash_flexflex_gfix[OF sm h(1,2,4,3) this] show ?thesis .
  qed
  show "einvw A K env'"
    unfolding einvw_def using tv' ce bb gf e(9,10,11,12) by (simp add: th)
qed

end

end
