section \<open>A Typed Unifier for Names with Several Types\<close>

theory Pattern_Typed_Unifier
  imports Pattern_Env_Apply
begin

text \<open>
  The unifier identifies the variables of a problem by their names, a typed solution
  (\<open>solution\<close>) gives a value to every pair of a name and a type. If the resulting environment
  binds a name that the problem has with two types, the problem follows from the bindings and
  from the bindings read at the other types (@{thm [source] pure_sig_gen.unify_typed_ghosts}).
  This theory shows that these equations have a common solution: an acyclic, well-typed
  environment is solved by a substitution \<open>gsol\<close> that gives to a variable \<open>(x, V)\<close> whose name
  the environment binds the binding of \<open>x\<close> read at the type \<open>V\<close>, if that is well-typed.
  Unification keeps the environment acyclic without any hypothesis on types
  (\<open>unify_acyc\<close> below). Hence a successful pattern unification has a typed
  unifier that solves the bindings of the resulting environment, whatever the types of the names
  are (\<open>unify_typed_unifier\<close>).
\<close>

subsection \<open>Reading a term at another type\<close>

text \<open>The leading abstractions of a term, with the argument types of a type:\<close>

primrec retype :: "pterm \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "retype (Abs a T b) V = Abs a (dom_type V) (retype b (rng_type V))"
| "retype (Const c T) V = Const c T"
| "retype (Free x T) V = Free x T"
| "retype (Var x T) V = Var x T"
| "retype (Bound i) V = Bound i"
| "retype (s $ t) V = s $ t"

lemma vars_retype [simp]: "vars (retype t V) = vars t"
  by (induction t arbitrary: V) auto

lemma loose_bvar_retype [simp]: "loose_bvar (retype t V) k = loose_bvar t k"
  by (induction t arbitrary: V k) auto

context pure_sig_gen
begin

lemma aconv_retype_abs_list:
  "length cs = length ds \<Longrightarrow> retype b W = b \<Longrightarrow>
    aconv_term (retype (abs_list ds b) (map snd cs \<Rrightarrow> W)) (abs_list cs b)"
proof (induction cs ds rule: list_induct2)
  case (Cons c cs d ds)
  obtain a T where c: "c = (a, T)" by force
  obtain a' T' where d: "d = (a', T')" by force
  from Cons show ?case by (simp add: c d)
qed simp

lemma retype_typed: "e \<turnstile> t : V \<Longrightarrow> retype t V = t"
  by (induction t arbitrary: e V) auto

text \<open>An equation of \<^const>\<open>ghosts\<close> that is well-typed has the binding read at the type as its
  right-hand side, up to the names of the abstractions:\<close>

lemma ghost_retype:
  assumes "e \<turnstile> abs_list cs b : V" "length cs = length ds"
  shows "aconv_term (retype (abs_list ds b) V) (abs_list cs b)"
proof -
  from assms(1) obtain W where V: "V = map snd cs \<Rrightarrow> W" and b: "pushes e (map snd cs) \<turnstile> b : W"
    by (rule typing_abs_listE)
  show ?thesis unfolding V by (rule aconv_retype_abs_list[OF assms(2) retype_typed[OF b]])
qed

lemma aconv_typing: "aconv_term s t \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> s : T"
  using typing_unname_iff[of e s T] typing_unname_iff[of e t T] by (simp add: aconv_term_unname)


subsection \<open>The solution\<close>

text \<open>
  The value of the variable \<open>(x, V)\<close> before the values of the variables of the binding are
  substituted: the binding of \<open>x\<close> read at \<open>V\<close>, if it has the type \<open>V\<close>. At the type of the binding
  this is the binding.
\<close>

definition gbody :: "tinst \<Rightarrow> env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm option" where
  "gbody \<rho> env x V = (case vt_lookup (tenv env) x of
      Some (U, u) \<Rightarrow>
        if (\<forall>e. e \<turnstile> retype (inst \<rho> u) V : V) then Some (retype (inst \<rho> u) V) else None
    | None \<Rightarrow> None)"

text \<open>The substitution, by iteration; it is stable after as many steps as the dependencies
  between the names are deep (\<open>gsol_unfold\<close>).\<close>

primrec git :: "tinst \<Rightarrow> env \<Rightarrow> nat \<Rightarrow> vsubst" where
  "git \<rho> env 0 = Var"
| "git \<rho> env (Suc n) =
    (\<lambda>x V. case gbody \<rho> env x V of Some t \<Rightarrow> vsubst (git \<rho> env n) t | None \<Rightarrow> Var x V)"

definition gsol :: "tinst \<Rightarrow> env \<Rightarrow> vsubst" where
  "gsol \<rho> env = git \<rho> env (Suc (card (Domain (dep env))))"

lemma gbody_binding:
  assumes "wt_env \<rho> env" "vt_lookup (tenv env) x = Some (U, u)"
  shows "gbody \<rho> env x (tsubst \<rho> U) = Some (inst \<rho> u)"
  using wt_envD[OF assms] retype_typed[OF wt_envD[OF assms]] by (simp add: gbody_def assms(2))

lemma gbody_dep:
  assumes "gbody \<rho> env x V = Some t" "(y, W) \<in> vars t"
  shows "(y, x) \<in> dep env"
proof -
  from assms(1) obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)" and t: "t = retype (inst \<rho> u) V"
    by (auto simp: gbody_def split: option.splits if_splits)
  from assms(2) obtain W' where "(y, W') \<in> vars u" by (auto simp: t vars_inst)
  from depI[OF lk this] show ?thesis .
qed

lemma rk_le: "rk env x \<le> card (Domain (dep env))"
proof -
  have "{y. (y, x) \<in> (dep env)\<^sup>+} \<subseteq> Domain (dep env)" by (auto dest: tranclD)
  then show ?thesis unfolding rk_def by (intro card_mono finite_Domain finite_dep)
qed

lemma git_stable:
  assumes ac: "acyc env"
  shows "rk env x < n \<Longrightarrow> git \<rho> env (Suc n) x V = git \<rho> env n x V"
proof (induction n arbitrary: x V)
  case (Suc n)
  show ?case
  proof (cases "gbody \<rho> env x V")
    case (Some t)
    have "vsubst (git \<rho> env (Suc n)) t = vsubst (git \<rho> env n) t"
    proof (rule vsubst_cong)
      fix y W assume "(y, W) \<in> vars t"
      from gbody_dep[OF Some this] have "rk env y < rk env x" by (rule rk_less[OF ac])
      with Suc.prems have "rk env y < n" by simp
      then show "git \<rho> env (Suc n) y W = git \<rho> env n y W" by (rule Suc.IH)
    qed
    with Some show ?thesis by simp
  qed simp
qed simp

text \<open>The substitution is a fixed point: the value of a variable is its body under the
  substitution.\<close>

lemma gsol_unfold:
  assumes ac: "acyc env"
  shows "gsol \<rho> env x V = (case gbody \<rho> env x V of Some t \<Rightarrow> vsubst (gsol \<rho> env) t | None \<Rightarrow> Var x V)"
proof -
  let ?N = "card (Domain (dep env))"
  have "rk env x < Suc ?N" using rk_le[of env x] by simp
  from git_stable[OF ac this, of \<rho> V] have "gsol \<rho> env x V = git \<rho> env (Suc (Suc ?N)) x V"
    by (simp only: gsol_def)
  also have "\<dots> = (case gbody \<rho> env x V of Some t \<Rightarrow> vsubst (git \<rho> env (Suc ?N)) t | None \<Rightarrow> Var x V)"
    by (simp only: git.simps)
  finally show ?thesis by (simp only: gsol_def)
qed

lemma wt_subst_git:
  assumes wte: "wt_env \<rho> env"
  shows "wt_subst (git \<rho> env n)"
proof (induction n)
  case 0
  show ?case unfolding wt_subst_def closed_subst_def by (auto simp: closed_def)
next
  case (Suc n)
  have b: "closed t \<and> (\<forall>e. e \<turnstile> t : V)" if "gbody \<rho> env x V = Some t" for x V t
  proof -
    from that obtain U u where lk: "vt_lookup (tenv env) x = Some (U, u)"
      and t: "t = retype (inst \<rho> u) V" and ty: "\<forall>e. e \<turnstile> t : V"
      by (auto simp: gbody_def split: option.splits if_splits)
    have "closed u" using wte lk unfolding wt_env_def by blast
    with ty show ?thesis by (simp add: t closed_def)
  qed
  have cs: "closed_subst (git \<rho> env n)" using Suc.IH by (simp add: wt_subst_def)
  have cl: "closed (vsubst (git \<rho> env n) t)" if "gbody \<rho> env x V = Some t" for x V t
    using b[OF that] cs by (simp add: closed_def)
  have ty: "e \<turnstile> vsubst (git \<rho> env n) t : V" if "gbody \<rho> env x V = Some t" for e x V t
    using b[OF that] by (blast intro: typing_vsubst[OF _ Suc.IH])
  show ?case
    unfolding wt_subst_def closed_subst_def using cl ty by (auto simp: closed_def split: option.splits)
qed

lemma wt_subst_gsol: "wt_env \<rho> env \<Longrightarrow> wt_subst (gsol \<rho> env)"
  unfolding gsol_def by (rule wt_subst_git)

text \<open>It solves the bindings:\<close>

theorem gsol_solution:
  assumes ac: "acyc env" and wte: "wt_env \<rho> env" and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env) \<rho>"
  shows "solution \<rho> (gsol \<rho> env) env"
proof -
  have "gsol \<rho> env x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (gsol \<rho> env) u"
    if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    by (simp add: gsol_unfold[OF ac] gbody_binding[OF wte that] ap_def)
  with \<rho> wt_subst_gsol[OF wte] show ?thesis by (simp add: solution_def)
qed

text \<open>It solves the bindings read at other types, where they are well-typed:\<close>

theorem gsol_ghosts:
  assumes ac: "acyc env" and wte: "wt_env \<rho> env" and g: "(l, r) \<in> ghosts \<rho> env"
    and ty: "e \<turnstile> l : T" "e \<turnstile> r : T"
  shows "vsubst (gsol \<rho> env) l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst (gsol \<rho> env) r"
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
  then have "vsubst (gsol \<rho> env) l = vsubst (gsol \<rho> env) ?t" by (simp add: l gsol_unfold[OF ac])
  moreover have "vsubst (gsol \<rho> env) ?t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst (gsol \<rho> env) r"
    by (rule conv_vsubst[OF aconv_term_conv[OF a] wt_subst_gsol[OF wte]])
  ultimately show ?thesis by simp
qed

corollary gsol_ebinds:
  assumes "acyc env" "wt_env \<rho> env" "wsinst alg \<rho>" "tsol (tyenv env) \<rho>"
    and "(l, r) \<in> ebinds \<rho> env" "e \<turnstile> l : T" "e \<turnstile> r : T"
  shows "vsubst (gsol \<rho> env) l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst (gsol \<rho> env) r"
  using assms(5) unfolding ebinds_def
proof
  assume "(l, r) \<in> binds \<rho> env"
  then show ?thesis by (rule solution_binds[OF gsol_solution[OF assms(1-4)]])
next
  assume "(l, r) \<in> ghosts \<rho> env"
  then show ?thesis using assms(6,7) by (rule gsol_ghosts[OF assms(1,2)])
qed


subsection \<open>The unifier\<close>

text \<open>Only the well-typed equations are used in a derivation:\<close>

lemma eqv_typed_pairs: "eqv E e s t \<Longrightarrow> eqv {(l, r) \<in> E. \<exists>e T. e \<turnstile> l : T \<and> e \<turnstile> r : T} e s t"
proof (induction rule: eqv.induct)
  case (eqv_ax s t e T)
  then show ?case by (intro eqv.eqv_ax) auto
qed (auto intro: eqv.intros)

text \<open>
  If pattern unification succeeds on closed terms that are well-typed with the same type
  after instantiation by \<open>\<rho>\<close>, and the resulting environment is acyclic, then \<open>gsol\<close> is a solution
  of the resulting environment that unifies the terms. The hypothesis \<open>vinv\<close> asks for one type
  per name for the names that are not loose only.
\<close>

theorem unify_ghost_unifier:
  assumes un: "ok (unify alg' s t env) env'" and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env') \<rho>"
    and wte: "wt_env \<rho> env" and tys: "e \<turnstile> inst \<rho> s : T" and tyt: "e \<turnstile> inst \<rho> t : T"
    and vi: "vinv \<rho> env (vars s \<union> vars t)" and cl: "closed s" "closed t" and ac: "acyc env'"
  shows "solution \<rho> (gsol \<rho> env') env'"
    and "ap \<rho> (gsol \<rho> env') s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (gsol \<rho> env') t"
proof -
  from unify_typed_ghosts[OF un \<rho>(2) wte tys tyt vi cl]
  have wte': "wt_env \<rho> env'" and eq: "eqv (ebinds \<rho> env') e (inst \<rho> s) (inst \<rho> t)" by blast+
  show sol: "solution \<rho> (gsol \<rho> env') env'" by (rule gsol_solution[OF ac wte' \<rho>])
  show "ap \<rho> (gsol \<rho> env') s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> (gsol \<rho> env') t"
    unfolding ap_def
    by (rule eqv_vsubst[OF eqv_typed_pairs[OF eq] solutionD(3)[OF sol]])
      (auto intro: gsol_ebinds[OF ac wte' \<rho>])
qed

end

subsection \<open>Unification keeps the environment acyclic\<close>

text \<open>
  The solution \<open>gsol\<close> needs an acyclic environment. The termination proof
  (theory \<open>Pattern_Termination\<close>, \<open>unify_inv\<close>) gives acyclicity for problems that
  satisfy its invariants, which include typing. The proof below does not use types: a new binding
  is to a new variable, to an unbound variable, or to a term that passed the occurs check.
\<close>

context pure_sig
begin

definition reach :: "env \<Rightarrow> indexname set \<Rightarrow> indexname set" where
  "reach env X = {y. \<exists>x\<in>X. (y, x) \<in> (dep env)\<^sup>*}"

lemma reach_refl: "X \<subseteq> reach env X"
  unfolding reach_def by blast

lemma reach_mono: "X \<subseteq> Y \<Longrightarrow> reach env X \<subseteq> reach env Y"
  unfolding reach_def by blast

lemma reach_reach: "Y \<subseteq> reach env X \<Longrightarrow> reach env Y \<subseteq> reach env X"
  unfolding reach_def by (blast intro: rtrancl_trans)

lemma reach_Un: "reach env (X \<union> Y) = reach env X \<union> reach env Y"
  unfolding reach_def by blast

lemma reach_bound:
  assumes "vt_lookup (tenv env) x = Some (U, u)"
  shows "reach env (fst ` vars u) \<subseteq> reach env {x}"
proof
  fix y assume "y \<in> reach env (fst ` vars u)"
  then obtain z T where z: "(z, T) \<in> vars u" "(y, z) \<in> (dep env)\<^sup>*" unfolding reach_def by auto
  from rtrancl_into_rtrancl[OF z(2) depI[OF assms z(1)]] show "y \<in> reach env {x}"
    by (simp add: reach_def)
qed

lemma ac_below_Un [simp]: "below n (X \<union> Y) \<longleftrightarrow> below n X \<and> below n Y"
  by (auto simp: below_def)

lemma ac_below_insert [simp]: "below n (insert x X) \<longleftrightarrow> snd (fst x) \<le> n \<and> below n X"
  by (auto simp: below_def)

lemma ac_below_sub: "below n X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> below n Y"
  by (rule below_mono[OF _ _ order_refl])

lemma below_bound: "below n (evars env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> snd x \<le> n"
  by (rule belowD[OF _ evarsI])

lemma reach_fresh:
  assumes bl: "below (maxidx env) (evars env)"
  shows "reach env {y. maxidx env < snd y} \<subseteq> {y. maxidx env < snd y}"
proof
  fix y assume "y \<in> reach env {y. maxidx env < snd y}"
  then obtain z where z: "maxidx env < snd z" "(y, z) \<in> (dep env)\<^sup>*" unfolding reach_def by blast
  have "vt_lookup (tenv env) z = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env) z \<noteq> None"
    then obtain U u where "vt_lookup (tenv env) z = Some (U, u)" by auto
    from below_bound[OF bl this] z(1) show False by simp
  qed
  with z(2) have "y = z" using not_dep_unbound[of env z y] by blast
  with z(1) show "y \<in> {y. maxidx env < snd y}" by simp
qed

text \<open>Paths through new bindings start at new variables:\<close>

lemma reach_newb:
  assumes nb: "newb env env1" and bl: "below (maxidx env) (evars env)"
  shows "reach env1 X \<subseteq> reach env X \<union> {y. maxidx env < snd y}"
proof
  fix y assume "y \<in> reach env1 X"
  then obtain x where x: "x \<in> X" and yx: "(y, x) \<in> (dep env1)\<^sup>*" unfolding reach_def by blast
  have "(y, x) \<in> (dep env)\<^sup>* \<or> maxidx env < snd y"
    using yx
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case by simp
  next
    case (step y z)
    from step.hyps(1) obtain U u T where lk: "vt_lookup (tenv env1) z = Some (U, u)"
      and yu: "(y, T) \<in> vars u"
      by (rule depE)
    show ?case
    proof (cases "vt_lookup (tenv env) z")
      case None
      from newbD(2)[OF nb lk None yu] show ?thesis by simp
    next
      case (Some b)
      with lk newbD(1)[OF nb] have lk0: "vt_lookup (tenv env) z = Some (U, u)"
        unfolding extends_def by auto
      have "snd z \<le> maxidx env" by (rule below_bound[OF bl lk0])
      with step.IH have "(z, x) \<in> (dep env)\<^sup>*" by (auto dest: leD)
      with depI[OF lk0 yu] show ?thesis by (blast intro: converse_rtrancl_into_rtrancl)
    qed
  qed
  with x show "y \<in> reach env X \<union> {y. maxidx env < snd y}" unfolding reach_def by blast
qed

subsubsection \<open>Head normalization\<close>

lemma head_norm_reach:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> fst ` vars t' \<subseteq> reach env (fst ` vars t)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "fst ` vars u' \<subseteq> reach env (fst ` vars u)" if "ok (hn env u) u'" for u u'
    using "1.IH"[OF that refl] .
  have redex: "fst ` vars t' \<subseteq> reach env (fst ` vars (Abs b U0 body $ u))"
    if "ok (hn env (subst_bound u body)) t'" for b U0 body u
  proof -
    have "vars (subst_bound u body) \<subseteq> vars (Abs b U0 body $ u)"
      using vars_subst[of body u 0] by (auto simp: subst_bound_subst)
    then have "reach env (fst ` vars (subst_bound u body)) \<subseteq> reach env (fst ` vars (Abs b U0 body $ u))"
      by (intro reach_mono image_mono)
    with IH[OF that] show ?thesis by blast
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
      with lr obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      from rest Some have "ok (hn env u) t'" by simp
      from subset_trans[OF IH[OF this] reach_bound[OF lk]] Var show ?thesis by simp
    qed (use rest in \<open>simp add: reach_refl\<close>)
  next
    case (Abs a T body)
    with h obtain body' where "ok (hn env body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (hn env (subst_bound u body)) t'" by simp
      from redex[OF this] f App show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF hf] have nf: "fst ` vars nf \<subseteq> reach env (fst ` vars f)" .
      have nfu: "fst ` vars (nf $ u) \<subseteq> reach env (fst ` vars (f $ u))"
        using nf reach_refl[of "fst ` vars u" env] by (auto simp: reach_Un image_Un)
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have r: "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF r] have "fst ` vars t' \<subseteq> reach env (fst ` vars (nf $ u))" by (simp add: Abs)
        with reach_reach[OF nfu] App show ?thesis by auto
      qed (use rest nfu App in auto)
    qed
  qed (use h in \<open>auto simp: reach_def\<close>)
qed

lemma head_norm_head_unbound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> strip_comb t' = (Var F T, ts) \<Longrightarrow> vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' ts rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and sc = "1.prems"(2)
  have IH: "vt_lookup (tenv env) F = None" if "ok (hn env u) u'" "strip_comb u' = (Var F T, us)" for u u' us
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x T')
    with h obtain lr where lr: "ok (lookup env x T') lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with rest have "ok (hn env u) t'" by simp
      from IH[OF this sc] show ?thesis .
    next
      case None
      with rest Var have "t' = Var x T'" by simp
      with sc have "x = F" by (simp add: strip_comb_def)
      with ok_lookup_None[OF lr[unfolded None]] show ?thesis by simp
    qed
  next
    case (Abs a T' body)
    with h sc show ?thesis by (auto simp: strip_comb_def)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (hn env (subst_bound u body)) t'" by simp
      from IH[OF this sc] show ?thesis .
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from IH[OF this sc] show ?thesis .
      next
        case nA: False
        with rest have t': "t' = nf $ u" by (cases nf) simp_all
        have "strip_comb nf = (Var F T, snd (strip_comb nf))"
          using sc t' by (cases "strip_comb nf") (simp add: strip_comb_App)
        from IH[OF hf this] show ?thesis .
      qed
    qed
  qed (use h sc in \<open>auto simp: strip_comb_def\<close>)
qed

subsubsection \<open>The occurs check\<close>

lemma occurs_not_occt:
  assumes "occurs F t env = Some r"
  shows "r = Ok False \<Longrightarrow> \<not> occt env F t"
  using assms
proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
  case (1 oc F t env r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "\<not> occt env F u" if "ok (oc F u env) False" for u using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var G T)
    with h obtain lr where lr: "ok (lookup env G T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> oc F u env | None \<Rightarrow> return (F = G)) False"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest lr Var show ?thesis by (simp add: ok_lookup_None occt_Var_unbound)
    next
      case (Some u)
      with lr obtain U where "vt_lookup (tenv env) G = Some (U, u)" by (auto elim: ok_lookup_Some)
      with IH[of u] rest Some Var show ?thesis by (simp add: occt_Var_bound)
    qed
  next
    case (App t1 t2)
    with h obtain b where "ok (oc F t1 env) b" "ok (if b then return True else oc F t2 env) False" by auto
    with IH App show ?thesis by (cases b) auto
  qed (use h IH in auto)
qed

subsubsection \<open>Projection\<close>

definition pr_ac :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "pr_ac env s u env' \<longleftrightarrow> (acyc env \<longrightarrow> below (maxidx env) (vars s \<union> evars env) \<longrightarrow>
    acyc env' \<and> below (maxidx env') (vars u \<union> evars env') \<and> newb env env' \<and>
    fst ` vars u \<subseteq> reach env (fst ` vars s) \<union> {y. maxidx env < snd y})"

lemma genvar_fresh:
  assumes G: "genvar a env T = (env1, G)" and bl: "below (maxidx env) (X \<union> evars env)"
  shows "acyc env1 \<longleftrightarrow> acyc env" "below (maxidx env1) (X \<union> evars env1)"
    "vt_lookup (tenv env1) (a, maxidx env + 1) = None" "maxidx env1 = maxidx env + 1"
    "G = Var (a, maxidx env + 1) T" "maxidx env < maxidx env + 1" "maxidx env \<le> maxidx env1"
proof -
  note g = genvar_simps[OF G]
  show "acyc env1 \<longleftrightarrow> acyc env" by (rule acyc_genvar[OF G])
  show m: "maxidx env1 = maxidx env + 1" "G = Var (a, maxidx env + 1) T" by (fact g(3,4))+
  show lt: "maxidx env < maxidx env + 1" by (simp add: integer_arith)
  then show le: "maxidx env \<le> maxidx env1" by (simp add: m)
  show "below (maxidx env1) (X \<union> evars env1)"
    by (rule below_mono[OF bl _ le]) (simp add: evars_genvar[OF G])
  show "vt_lookup (tenv env1) (a, maxidx env + 1) = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env1) (a, maxidx env + 1) \<noteq> None"
    then obtain U u where "vt_lookup (tenv env) (a, maxidx env + 1) = Some (U, u)" using g(1) by auto
    from below_bound[of "maxidx env", OF _ this] bl have "maxidx env + 1 \<le> maxidx env" by simp
    with lt show False by (auto dest: leD)
  qed
qed

lemma fresh_ne: "snd x \<le> (n :: integer) \<Longrightarrow> x \<noteq> (a, n + 1)"
proof
  assume "snd x \<le> n" "x = (a, n + 1)"
  then have "n + 1 \<le> n" by simp
  moreover have "n < n + 1" by (simp add: integer_arith)
  ultimately show False by (auto dest: leD)
qed

lemma bind_unbound_ac:
  assumes upd: "ok (update (F, Fty) u env) env'" and ac: "acyc env"
    and bl: "below (maxidx env) (X \<union> evars env)" and sF: "snd F \<le> maxidx env"
    and vu: "fst ` vars u \<subseteq> {H}" and bu: "below (maxidx env) (vars u)"
    and Hn: "vt_lookup (tenv env) H = None" and FH: "F \<noteq> H"
  shows "acyc env' \<and> below (maxidx env') (X \<union> evars env')"
proof
  show "acyc env'"
  proof (rule acyc_update[OF upd ac])
    fix y U assume "(y, U) \<in> vars u"
    with vu have "y = H" by force
    then show "(F, y) \<notin> (dep env)\<^sup>*" using not_dep_unbound[OF Hn FH] by simp
  qed
  have "below (maxidx env) (X \<union> evars env')"
    using bl bu sF by (auto simp: evars_update[OF upd] below_def)
  then show "below (maxidx env') (X \<union> evars env')" by (simp add: ok_update(4)[OF upd])
qed

lemma mapAccM_pr_ac:
  assumes "ok (mapAccM f ts env) (us, env')"
    and "\<And>s env u env'. s \<in> set ts \<Longrightarrow> ok (f s env) (u, env') \<Longrightarrow> pr_ac env s u env'"
    and "acyc env" "below (maxidx env) (\<Union>(vars ` set ts) \<union> evars env)"
  shows "acyc env' \<and> below (maxidx env') (\<Union>(vars ` set us) \<union> evars env') \<and> newb env env' \<and>
    fst ` \<Union>(vars ` set us) \<subseteq> reach env (fst ` \<Union>(vars ` set ts)) \<union> {y. maxidx env < snd y}"
  using assms
proof (induction ts arbitrary: env us)
  case Nil
  then show ?case by simp
next
  case (Cons s ts)
  from Cons.prems(1) obtain u env1 us' where f: "ok (f s env) (u, env1)"
    and r: "ok (mapAccM f ts env1) (us', env')" and us: "us = u # us'"
    by (auto split: prod.splits)
  have blE: "below (maxidx env) (evars env)" using Cons.prems(4) by simp
  have bl0: "below (maxidx env) (vars s \<union> evars env)" using Cons.prems(4) by simp
  have "pr_ac env s u env1" using Cons.prems(2)[of s env u env1] f by simp
  then have p: "acyc env1" "below (maxidx env1) (vars u \<union> evars env1)" "newb env env1"
    "fst ` vars u \<subseteq> reach env (fst ` vars s) \<union> {y. maxidx env < snd y}"
    using Cons.prems(3) bl0 unfolding pr_ac_def by blast+
  have le1: "maxidx env \<le> maxidx env1" using newbD(1)[OF p(3)] by (simp add: extends_def)
  have bl1: "below (maxidx env1) (\<Union>(vars ` set ts) \<union> evars env1)"
  proof -
    have "below (maxidx env) (\<Union>(vars ` set ts))" using Cons.prems(4) by simp
    from below_mono[OF this order_refl le1] p(2) show ?thesis by simp
  qed
  have hyp: "\<And>s' env u env'. s' \<in> set ts \<Longrightarrow> ok (f s' env) (u, env') \<Longrightarrow> pr_ac env s' u env'"
    by (rule Cons.prems(2)) simp_all
  note q = Cons.IH[OF r hyp p(1) bl1]
  have le2: "maxidx env1 \<le> maxidx env'" using newbD(1) q by (simp add: extends_def)
  have R: "reach env1 (fst ` \<Union>(vars ` set ts)) \<subseteq> reach env (fst ` \<Union>(vars ` set ts)) \<union> {y. maxidx env < snd y}"
    by (rule reach_newb[OF p(3) blE])
  have Fr: "{y. maxidx env1 < snd y} \<subseteq> {y. maxidx env < snd y}" using le1 by (auto intro: order_le_less_trans)
  have bu: "below (maxidx env') (vars u)" by (rule below_mono[OF p(2) _ le2]) blast
  show ?case
  proof (intro conjI)
    show "acyc env'" using q by blast
    show "below (maxidx env') (\<Union>(vars ` set us) \<union> evars env')" using q bu by (simp add: us)
    show "newb env env'" using newb_trans[OF p(3)] q by blast
    show "fst ` \<Union>(vars ` set us) \<subseteq> reach env (fst ` \<Union>(vars ` set (s # ts))) \<union> {y. maxidx env < snd y}"
      using p(4) q R Fr by (simp add: us image_Un reach_Un) blast
  qed
qed

lemma pr_acyc:
  assumes "pr xs s env d bs = Some r"
  shows "r = Ok (u, env') \<Longrightarrow> pr_ac env s u env'"
  using assms
proof (induction xs s env d bs r arbitrary: u env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  have IH: "pr_ac env1 s1 u1 env2" if "ok (prr xs1 s1 env1 d1 bs1) (u1, env2)" for xs1 s1 env1 d1 bs1 u1 env2
    using "1.IH"[OF that refl] .
  have "ok (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs)) (u, env')"
    using "1.hyps" "1.prems"(1) unfolding pr_step_def by simp
  then obtain s' where hs: "ok (head_norm env s) s'" and st: "ok (pr_step prr xs s' env d bs) (u, env')"
    by auto
  have vs': "vars s' \<subseteq> vars s \<union> evars env" by (rule head_norm_vars[OF hs refl])
  have rs': "fst ` vars s' \<subseteq> reach env (fst ` vars s)" by (rule head_norm_reach[OF hs refl])
  show ?case unfolding pr_ac_def
  proof (intro impI)
    assume ac: "acyc env" and bl: "below (maxidx env) (vars s \<union> evars env)"
    have blE: "below (maxidx env) (evars env)" using bl by simp
    have bls': "below (maxidx env) (vars s' \<union> evars env)" by (rule ac_below_sub[OF bl]) (use vs' in blast)
    show "acyc env' \<and> below (maxidx env') (vars u \<union> evars env') \<and> newb env env' \<and>
        fst ` vars u \<subseteq> reach env (fst ` vars s) \<union> {y. maxidx env < snd y}"
    proof (cases "is_Abs s'")
      case True
      then obtain a T t where s': "s' = Abs a T t" by (cases s') auto
      from st obtain t' where r: "ok (prr xs t env (d + 1) ((a, T) # bs)) (t', env')"
        and u: "u = Abs a T t'"
        by (auto simp: pr_step_def s')
      have "below (maxidx env) (vars t \<union> evars env)" using bls' s' by simp
      with IH[OF r] ac have r': "acyc env'" "below (maxidx env') (vars t' \<union> evars env')" "newb env env'"
        "fst ` vars t' \<subseteq> reach env (fst ` vars t) \<union> {y. maxidx env < snd y}"
        unfolding pr_ac_def by blast+
      have "reach env (fst ` vars t) \<subseteq> reach env (fst ` vars s)" using rs' s' by (intro reach_reach) simp
      with r' show ?thesis by (simp add: u) blast
    next
      case nA: False
      obtain h ts where sc: "strip_comb s' = (h, ts)" by force
      have s'eq: "s' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF sc])
      show ?thesis
      proof (cases "is_Var h")
        case True
        then obtain F Fty where hF: "h = Var F Fty" by (cases h) auto
        from st nA sc hF obtain js js' Hty where
          rest: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow> mk_hnf bs js H (mk_proj_list js') \<bind>
             (\<lambda>t. update (F, Fty) t env1 \<bind> (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (u, env')"
          by (auto simp: pr_step_def Let_def)
        obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
        with rest obtain t where t: "ok (mkabs bs js (app H (mk_proj_list js'))) t"
          and upd: "ok (update (F, Fty) t env1) env'" and u: "u = app H (List.map_filter id js')"
          by (auto simp: mk_hnf_def)
        have Fv: "(F, Fty) \<in> vars s'" using s'eq hF by (simp add: vars_apps)
        have sF: "snd F \<le> maxidx env" using belowD[OF bls'] Fv by blast
        have blF: "below (maxidx env) ({(F, Fty)} \<union> evars env)" using blE sF by (auto simp: below_def)
        note gf = genvar_fresh[OF G blF]
        note bl1 = gf(2)
        have vt: "vars t = {((fst F, maxidx env + 1), Hty)}" using t by (simp add: ok_mkabs gf(5))
        have r: "acyc env' \<and> below (maxidx env') ({(F, Fty)} \<union> evars env')"
        proof (rule bind_unbound_ac[OF upd _ bl1])
          show "acyc env1" using ac gf(1) by simp
          show "snd F \<le> maxidx env1" using sF gf(7) by simp
          show "fst ` vars t \<subseteq> {(fst F, maxidx env + 1)}" by (simp add: vt)
          show "below (maxidx env1) (vars t)" by (simp add: vt gf(4) below_def)
          show "vt_lookup (tenv env1) (fst F, maxidx env + 1) = None" by (rule gf(3))
          show "F \<noteq> (fst F, maxidx env + 1)" by (rule fresh_ne[OF sF])
        qed
        have mx: "maxidx env' = maxidx env + 1" using ok_update(4)[OF upd] gf(4) by simp
        have vu: "vars u = {((fst F, maxidx env + 1), Hty)}" by (simp add: u gf(5))
        have "below (maxidx env') (vars u \<union> evars env')" using r by (simp add: vu mx below_def)
        moreover have "newb env env'"
          by (rule newb_update[OF upd _ newb_genvar[OF G]]) (simp add: vt gf(6))
        moreover have "fst ` vars u \<subseteq> {y. maxidx env < snd y}" by (simp add: vu gf(6))
        ultimately show ?thesis using r by blast
      next
        case nV: False
        show ?thesis
        proof (cases "is_Abs h")
          case True
          with st nA sc nV show ?thesis by (simp add: pr_step_def)
        next
          case nAh: False
          let ?h = "case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h"
          from st nA sc nV nAh obtain h' ts' where hh: "ok ?h h'"
            and m: "ok (mapAccM (\<lambda>s env. prr xs s env d bs) ts env) (ts', env')"
            and u: "u = list_comb h' ts'"
            by (auto simp: pr_step_def)
          have vh: "vars h' = {}"
          proof -
            have "\<not> (\<exists>f v. h = f $ v)" by (rule strip_comb_head[OF sc])
            with nV nAh hh show ?thesis by (cases h) auto
          qed
          have ts_sub: "\<Union>(vars ` set ts) \<subseteq> vars s'" using s'eq by (auto simp: vars_apps)
          have blts: "below (maxidx env) (\<Union>(vars ` set ts) \<union> evars env)"
            by (rule ac_below_sub[OF bls']) (use ts_sub in blast)
          have hyp: "\<And>s1 env1 u1 env2. s1 \<in> set ts \<Longrightarrow> ok (prr xs s1 env1 d bs) (u1, env2) \<Longrightarrow>
              pr_ac env1 s1 u1 env2"
            by (rule IH)
          note m' = mapAccM_pr_ac[OF m hyp ac blts]
          have "fst ` \<Union>(vars ` set ts) \<subseteq> reach env (fst ` vars s)" using rs' ts_sub by blast
          then have rr: "reach env (fst ` \<Union>(vars ` set ts)) \<subseteq> reach env (fst ` vars s)" by (rule reach_reach)
          have vu: "vars u = \<Union>(vars ` set ts')" by (simp add: u list_comb_apps vars_apps vh)
          show ?thesis using m' rr by (simp add: vu) blast
        qed
      qed
    qed
  qed
qed

lemma proj_ac:
  assumes "ok (proj t env bs is) (u, env')"
  shows "pr_ac env t u env'"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  with assms have "u = t" "env' = env" by (simp_all add: proj_def)
  then show ?thesis unfolding pr_ac_def using reach_refl[of "fst ` vars t" env] by auto
next
  case False
  with assms have "ok (pr is t env 0 bs) (u, env')" by (simp add: proj_def)
  from pr_acyc[OF this refl] show ?thesis .
qed

subsubsection \<open>Steps\<close>

definition step_ac :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "step_ac env s t env' \<longleftrightarrow> (\<forall>X. acyc env \<longrightarrow> below (maxidx env) (X \<union> vars s \<union> vars t \<union> evars env) \<longrightarrow>
    acyc env' \<and> below (maxidx env') (X \<union> evars env'))"

lemma step_acI:
  "(\<And>X. acyc env \<Longrightarrow> below (maxidx env) (X \<union> vars s \<union> vars t \<union> evars env) \<Longrightarrow>
    acyc env' \<and> below (maxidx env') (X \<union> evars env')) \<Longrightarrow> step_ac env s t env'"
  unfolding step_ac_def by blast

lemma step_acD:
  "step_ac env s t env' \<Longrightarrow> acyc env \<Longrightarrow> below (maxidx env) (X \<union> vars s \<union> vars t \<union> evars env) \<Longrightarrow>
    acyc env' \<and> below (maxidx env') (X \<union> evars env')"
  unfolding step_ac_def by blast

lemma step_ac_sym: "step_ac env s t env' \<Longrightarrow> step_ac env t s env'"
  unfolding step_ac_def by (simp del: ac_below_Un add: Un_ac)

lemma step_ac_head_norm:
  assumes hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'" and st: "step_ac env s' t' env'"
  shows "step_ac env s t env'"
proof (rule step_acI)
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars s \<union> vars t \<union> evars env)"
  have "below (maxidx env) (X \<union> vars s' \<union> vars t' \<union> evars env)"
    by (rule ac_below_sub[OF bl]) (use head_norm_vars[OF hs refl] head_norm_vars[OF ht refl] in blast)
  from step_acD[OF st ac this] show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" .
qed

lemma step_ac_flex:
  assumes "ok (ints_of' env ss) is" and st: "step_ac env (app (Var F Fty) is) t env'"
  shows "step_ac env (Var F Fty \<degree>\<degree> ss) t env'"
proof (rule step_acI)
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars (Var F Fty \<degree>\<degree> ss) \<union> vars t \<union> evars env)"
  have "below (maxidx env) (X \<union> vars (app (Var F Fty) is) \<union> vars t \<union> evars env)"
    by (rule ac_below_sub[OF bl]) (auto simp: vars_apps)
  from step_acD[OF st ac this] show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" .
qed

lemma step_ac_flex_flex:
  assumes "ok (ints_of' env ss) is" "ok (ints_of' env ts) js"
    and "step_ac env (app (Var F Fty) is) (app (Var G Gty) js) env'"
  shows "step_ac env (Var F Fty \<degree>\<degree> ss) (Var G Gty \<degree>\<degree> ts) env'"
  using step_ac_flex[OF assms(1) step_ac_sym[OF step_ac_flex[OF assms(2) step_ac_sym[OF assms(3)]]]] .

lemma step_ac_Abs:
  assumes ut: "ok (unify_types alg' Ts Tt env) env1" and st: "step_ac env1 ts tt env'"
  shows "step_ac env (Abs ns Ts ts) (Abs nt Tt tt) env'"
proof (rule step_acI)
  note u = unify_types_sound[OF ut]
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars (Abs ns Ts ts) \<union> vars (Abs nt Tt tt) \<union> evars env)"
  have ac1: "acyc env1" using ac u(1) by (simp add: acyc_def dep_def)
  have le: "maxidx env \<le> maxidx env1" using u(2) by (simp add: extends_def)
  have ev: "evars env1 = evars env" by (simp add: evars_def bnds_def u(1))
  have "below (maxidx env1) (X \<union> vars ts \<union> vars tt \<union> evars env1)"
    by (rule below_mono[OF bl _ le]) (auto simp: ev)
  from step_acD[OF st ac1 this] show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" .
qed

lemma step_ac_eta:
  assumes st: "step_ac env ts (incr t' $ Bound 0) env'"
  shows "step_ac env (Abs a Ts ts) t' env'"
proof (rule step_acI)
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars (Abs a Ts ts) \<union> vars t' \<union> evars env)"
  have "vars (incr t' $ Bound 0) = vars t'" by (simp add: incr_def)
  with bl have "below (maxidx env) (X \<union> vars ts \<union> vars (incr t' $ Bound 0) \<union> evars env)" by simp
  from step_acD[OF st ac this] show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" .
qed

definition steps_ac :: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> env \<Rightarrow> bool" where
  "steps_ac env ps env' \<longleftrightarrow> (\<forall>X. acyc env \<longrightarrow>
    below (maxidx env) (X \<union> (\<Union>(s, t)\<in>set ps. vars s \<union> vars t) \<union> evars env) \<longrightarrow>
    acyc env' \<and> below (maxidx env') (X \<union> evars env'))"

lemma foldM_steps_ac:
  assumes "ok (foldM (\<lambda>(s, t) env. f s t env) ps env) env'"
    and "\<And>s t env env'. (s, t) \<in> set ps \<Longrightarrow> ok (f s t env) env' \<Longrightarrow> step_ac env s t env'"
  shows "steps_ac env ps env'"
  using assms
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (simp add: steps_ac_def)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by (cases p)
  with Cons.prems(1) obtain env1 where f: "ok (f s t env) env1"
    and rest: "ok (foldM (\<lambda>(s, t) env. f s t env) ps env1) env'"
    by auto
  have s1: "step_ac env s t env1" using Cons.prems(2)[OF _ f] p by simp
  have s2: "steps_ac env1 ps env'" using Cons.IH[OF rest] Cons.prems(2) by simp
  show ?case unfolding steps_ac_def
  proof (intro allI impI)
    fix X assume ac: "acyc env"
      and bl: "below (maxidx env) (X \<union> (\<Union>(s, t)\<in>set (p # ps). vars s \<union> vars t) \<union> evars env)"
    let ?Y = "\<Union>(s, t)\<in>set ps. vars s \<union> vars t"
    have "below (maxidx env) ((X \<union> ?Y) \<union> vars s \<union> vars t \<union> evars env)" using bl p by simp
    from step_acD[OF s1 ac this] have r1: "acyc env1" "below (maxidx env1) ((X \<union> ?Y) \<union> evars env1)"
      by blast+
    then have "below (maxidx env1) (X \<union> ?Y \<union> evars env1)" by simp
    with s2 r1(1) show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" unfolding steps_ac_def by blast
  qed
qed

lemma step_ac_rigid:
  assumes ext1: "extends env env1" and tenv1: "tenv env1 = tenv env"
    and vh: "vars h = {}" "vars h' = {}" and len: "length ss = length ts"
    and st: "steps_ac env1 (zip ss ts) env'"
  shows "step_ac env (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) env'"
proof (rule step_acI)
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars (h \<degree>\<degree> ss) \<union> vars (h' \<degree>\<degree> ts) \<union> evars env)"
  have ac1: "acyc env1" using ac tenv1 by (simp add: acyc_def dep_def)
  have ev: "evars env1 = evars env" by (simp add: evars_def bnds_def tenv1)
  have le: "maxidx env \<le> maxidx env1" using ext1 by (simp add: extends_def)
  have "below (maxidx env1) (X \<union> (\<Union>(s, t)\<in>set (zip ss ts). vars s \<union> vars t) \<union> evars env1)"
    by (rule below_mono[OF bl _ le]) (auto simp: ev vars_apps vh dest: set_zip_leftD set_zip_rightD)
  with st ac1 show "acyc env' \<and> below (maxidx env') (X \<union> evars env')" unfolding steps_ac_def by blast
qed

lemma flexflex1_ac:
  assumes ff: "ok (flexflex1 env bs F Fty is js) env'"
  shows "step_ac env (app (Var F Fty) is) (app (Var F Gty) js) env'"
proof (rule step_acI)
  fix X assume ac: "acyc env"
    and bl: "below (maxidx env) (X \<union> vars (app (Var F Fty) is) \<union> vars (app (Var F Gty) js) \<union> evars env)"
  have sF: "snd F \<le> maxidx env" using belowD[OF bl, of F Fty] by simp
  have blX: "below (maxidx env) (X \<union> evars env)" using bl by simp
  show "acyc env' \<and> below (maxidx env') (X \<union> evars env')"
  proof (cases "is = js")
    case True
    with ff have "env' = env" by (simp add: flexflex1_def)
    with ac blX show ?thesis by simp
  next
    case False
    with ff obtain ks where hnf: "ok (mk_new_hnf env bs is F Fty ks) env'" by (auto simp: flexflex1_def)
    from hnf obtain Gty' where rest: "ok (let (env1, G) = genvar (fst F) env Gty' in
        mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, Fty) t env1)) env'"
      by (auto simp: mk_new_hnf_def)
    obtain env1 G where G: "genvar (fst F) env Gty' = (env1, G)" by force
    with rest obtain u where u: "ok (mkabs bs is (app G ks)) u" and upd: "ok (update (F, Fty) u env1) env'"
      by (auto simp: mk_hnf_def)
    note gf = genvar_fresh[OF G blX]
    have vu: "vars u = {((fst F, maxidx env + 1), Gty')}" using u by (simp add: ok_mkabs gf(5))
    show ?thesis
    proof (rule bind_unbound_ac[OF upd _ gf(2)])
      show "acyc env1" using ac gf(1) by simp
      show "snd F \<le> maxidx env1" using sF gf(7) by simp
      show "fst ` vars u \<subseteq> {(fst F, maxidx env + 1)}" by (simp add: vu)
      show "below (maxidx env1) (vars u)" by (simp add: vu gf(4) below_def)
      show "vt_lookup (tenv env1) (fst F, maxidx env + 1) = None" by (rule gf(3))
      show "F \<noteq> (fst F, maxidx env + 1)" by (rule fresh_ne[OF sF])
    qed
  qed
qed

lemma ff_ac:
  assumes ff: "ok (ff env bs F Fty is G Gty js) env'" and FG: "F \<noteq> G"
    and Gn: "vt_lookup (tenv env) G = None"
  shows "step_ac env (app (Var F Fty) is) (app (Var G Gty) js) env'"
proof (rule step_acI)
  fix X assume ac: "acyc env"
    and bl: "below (maxidx env) (X \<union> vars (app (Var F Fty) is) \<union> vars (app (Var G Gty) js) \<union> evars env)"
  have sF: "snd F \<le> maxidx env" using belowD[OF bl, of F Fty] by simp
  have sG: "snd G \<le> maxidx env" using belowD[OF bl, of G Gty] by simp
  have blX: "below (maxidx env) (X \<union> evars env)" using bl by simp
  show "acyc env' \<and> below (maxidx env') (X \<union> evars env')"
  proof (cases "subset js is")
    case True
    with ff obtain ks u where u: "ok (mkabs bs is (app (Var G Gty) ks)) u"
      and upd: "ok (update (F, Fty) u env) env'"
      by (auto simp: ff_def)
    have vu: "vars u = {(G, Gty)}" using u by (simp add: ok_mkabs)
    show ?thesis
      by (rule bind_unbound_ac[OF upd ac blX sF _ _ Gn FG]) (use sG in \<open>simp_all add: vu below_def\<close>)
  next
    case False
    let ?ks = "inter js is"
    from False ff obtain ksF Hty where
      rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs bs js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs bs is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain ksG ksF' tG tF env2 where tG: "ok (mkabs bs js (app H ksG)) tG"
      and tF: "ok (mkabs bs is (app H ksF')) tF"
      and upd1: "ok (update (F, Fty) tF env1) env2" and upd2: "ok (update (G, Gty) tG env2) env'"
      by auto
    let ?H = "(fst G, maxidx env + 1)"
    have blX': "below (maxidx env) ((X \<union> {(G, Gty)}) \<union> evars env)" using blX sG by (simp add: below_def)
    note gf = genvar_fresh[OF H blX']
    have vF: "vars tF = {(?H, Hty)}" using tF by (simp add: ok_mkabs gf(5))
    have vG: "vars tG = {(?H, Hty)}" using tG by (simp add: ok_mkabs gf(5))
    have Hne: "x \<noteq> ?H" if "snd x \<le> maxidx env" for x using fresh_ne[OF that] .
    have r1: "acyc env2 \<and> below (maxidx env2) ((X \<union> {(G, Gty)}) \<union> evars env2)"
    proof (rule bind_unbound_ac[OF upd1 _ gf(2)])
      show "acyc env1" using ac gf(1) by simp
      show "snd F \<le> maxidx env1" using sF gf(7) by simp
      show "fst ` vars tF \<subseteq> {?H}" by (simp add: vF)
      show "below (maxidx env1) (vars tF)" by (simp add: vF gf(4) below_def)
      show "vt_lookup (tenv env1) ?H = None" by (rule gf(3))
      show "F \<noteq> ?H" by (rule Hne[OF sF])
    qed
    have m2: "maxidx env2 = maxidx env + 1" using ok_update(4)[OF upd1] gf(4) by simp
    show ?thesis
    proof (rule bind_unbound_ac[OF upd2])
      show "acyc env2" using r1 by blast
      show "below (maxidx env2) (X \<union> evars env2)" using r1 by simp
      show "snd G \<le> maxidx env2" using r1 by (simp add: below_def)
      show "fst ` vars tG \<subseteq> {?H}" by (simp add: vG)
      show "below (maxidx env2) (vars tG)" by (simp add: vG m2 below_def)
      show "vt_lookup (tenv env2) ?H = None" using ok_update(2)[OF upd1] gf(3) Hne[OF sF] by simp
      show "G \<noteq> ?H" by (rule Hne[OF sG])
    qed
  qed
qed

lemma flexflex2_ac:
  assumes "ok (flexflex2 env bs F Fty is G Gty js) env'" "F \<noteq> G"
    "vt_lookup (tenv env) F = None" "vt_lookup (tenv env) G = None"
  shows "step_ac env (app (Var F Fty) is) (app (Var G Gty) js) env'"
  using assms by (cases "indexname_less G F") (auto simp: flexflex2_def intro: ff_ac step_ac_sym)

lemma flexrigid_ac:
  assumes fr: "ok (flexrigid env bs F Fty is t) env'" and Fn: "vt_lookup (tenv env) F = None"
  shows "step_ac env (app (Var F Fty) is) t env'"
proof (rule step_acI)
  fix X assume ac: "acyc env" and bl: "below (maxidx env) (X \<union> vars (app (Var F Fty) is) \<union> vars t \<union> evars env)"
  have nh: False if "ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e) y" for e y
    using that by (cases e) auto
  have oc: "ok (occurs F t env) False"
    and pj: "ok (do {(u, env1) \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env1}) env'"
    using fr by (auto simp: flexrigid_def ok_handle split: if_splits dest: nh)
  then obtain u env1 u' where pj': "ok (proj t env bs is) (u, env1)" and mk: "ok (mkabs bs is u) u'"
    and upd: "ok (update (F, Fty) u' env1) env'"
    by (auto split: prod.splits)
  have vu': "vars u' = vars u" using mk by (simp add: ok_mkabs)
  have sF: "snd F \<le> maxidx env" using belowD[OF bl, of F Fty] by simp
  have blt: "below (maxidx env) (vars t \<union> evars env)" using bl by simp
  have blE: "below (maxidx env) (evars env)" using bl by simp
  have p: "acyc env1" "below (maxidx env1) (vars u \<union> evars env1)" "newb env env1"
    "fst ` vars u \<subseteq> reach env (fst ` vars t) \<union> {y. maxidx env < snd y}"
    using proj_ac[OF pj'] ac blt unfolding pr_ac_def by blast+
  have noc: "F \<notin> reach env (fst ` vars t)"
    using occurs_not_occt[OF oc refl] Fn unfolding occt_def reach_def by blast
  have le1: "maxidx env \<le> maxidx env1" using newbD(1)[OF p(3)] by (simp add: extends_def)
  show "acyc env' \<and> below (maxidx env') (X \<union> evars env')"
  proof
    show "acyc env'"
    proof (rule acyc_update[OF upd p(1)])
      fix y U assume yu: "(y, U) \<in> vars u'"
      show "(F, y) \<notin> (dep env1)\<^sup>*"
      proof
        assume Fy: "(F, y) \<in> (dep env1)\<^sup>*"
        have "y \<in> fst ` vars u" using yu vu' by force
        then have "F \<in> reach env1 (fst ` vars u)" using Fy unfolding reach_def by blast
        also have "\<dots> \<subseteq> reach env1 (reach env (fst ` vars t) \<union> {y. maxidx env < snd y})"
          by (rule reach_mono[OF p(4)])
        also have "\<dots> \<subseteq> reach env (reach env (fst ` vars t) \<union> {y. maxidx env < snd y}) \<union> {y. maxidx env < snd y}"
          by (rule reach_newb[OF p(3) blE])
        also have "\<dots> \<subseteq> reach env (fst ` vars t) \<union> {y. maxidx env < snd y}"
          using reach_reach[OF order_refl, of env "fst ` vars t"] reach_fresh[OF blE] by (auto simp: reach_Un)
        finally show False using noc sF by (auto dest: leD)
      qed
    qed
    have bX: "below (maxidx env1) X" using below_mono[OF bl order_refl le1] by simp
    have "below (maxidx env1) (X \<union> evars env')"
      using bX p(2) order_trans[OF sF le1] by (auto simp: evars_update[OF upd] vu' below_def)
    then show "below (maxidx env') (X \<union> evars env')" by (simp add: ok_update(4)[OF upd])
  qed
qed

theorem unif_acyc:
  assumes "unif alg' bs s t env = Some r"
  shows "r = Ok env' \<Longrightarrow> step_ac env s t env'"
  using assms
proof (induction alg' bs s t env r arbitrary: env' rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs s t env r)
  have IH: "step_ac env1 s1 t1 env2" if "ok (uni alg' bs1 s1 t1 env1) env2" for bs1 s1 t1 env1 env2
    using "1.IH"[OF that refl] .
  have "ok (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg' bs s' t' env))) env'"
    using "1.hyps" "1.prems" unfolding unif_step_def by simp
  then obtain s' t' where hn_s: "ok (head_norm env s) s'" and hn_t: "ok (head_norm env t) t'"
    and body: "ok (unif_step uni alg' bs s' t' env) env'"
    by auto
  have "step_ac env s' t' env'"
  proof (cases "is_Abs s'")
    case sAbs: True
    then obtain ns Ts ts where s': "s' = Abs ns Ts ts" by (cases s') auto
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
      with body s' obtain env1 where ut: "ok (unify_types alg' Ts Tt env) env1"
        and r: "ok (uni alg' ((if ns = STR '''' then nt else ns, Ts) # bs) ts tt env1) env'"
        by (auto simp: unif_step_def Let_def)
      show ?thesis unfolding s' t' by (rule step_ac_Abs[OF ut IH[OF r]])
    next
      case False
      with body s' have r: "ok (uni alg' ((ns, Ts) # bs) ts (incr t' $ Bound 0) env) env'"
        by (simp add: unif_step_def)
      show ?thesis unfolding s' by (rule step_ac_eta[OF IH[OF r]])
    qed
  next
    case nsAbs: False
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
      with body nsAbs have r: "ok (uni alg' ((nt, Tt) # bs) (incr s' $ Bound 0) tt env) env'"
        by (simp add: unif_step_def)
      show ?thesis unfolding t' by (rule step_ac_sym[OF step_ac_eta[OF step_ac_sym[OF IH[OF r]]]])
    next
      case ntAbs: False
      obtain hs ss where shs: "strip_comb s' = (hs, ss)" by force
      obtain ht ts where sht: "strip_comb t' = (ht, ts)" by force
      have s': "s' = hs \<degree>\<degree> ss" and t': "t' = ht \<degree>\<degree> ts"
        by (rule strip_comb_apps[OF shs], rule strip_comb_apps[OF sht])
      have body': "ok (if is_Var hs \<and> is_Var ht then
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
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)) env'"
        using body nsAbs ntAbs shs sht by (simp add: unif_step_def)
      show ?thesis
      proof (cases "is_Var hs")
        case sVar: True
        then obtain F Fty where hs: "hs = Var F Fty" by (cases hs) auto
        have unbF: "vt_lookup (tenv env) F = None"
          using head_norm_head_unbound[OF hn_s refl, of F Fty ss] shs hs by simp
        show ?thesis
        proof (cases "is_Var ht")
          case True
          then obtain G Gty where ht: "ht = Var G Gty" by (cases ht) auto
          have unbG: "vt_lookup (tenv env) G = None"
            using head_norm_head_unbound[OF hn_t refl, of G Gty ts] sht ht by simp
          from body' hs ht obtain "is" js where is_ok: "ok (ints_of' env ss) is"
            and js: "ok (ints_of' env ts) js"
            and r: "ok (if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js) env'"
            by auto
          have "step_ac env (app (Var F Fty) is) (app (Var G Gty) js) env'"
          proof (cases "F = G")
            case True
            with r flexflex1_ac[of env bs F Fty "is" js env' Gty] show ?thesis by simp
          next
            case False
            with r flexflex2_ac[OF _ False unbF unbG] show ?thesis by simp
          qed
          from step_ac_flex_flex[OF is_ok js this] show ?thesis by (simp add: s' t' hs ht)
        next
          case False
          from body' hs False obtain "is" where is_ok: "ok (ints_of' env ss) is"
            and r: "ok (flexrigid env bs F Fty is t') env'"
            by auto
          from step_ac_flex[OF is_ok flexrigid_ac[OF r unbF]] show ?thesis by (simp add: s' hs)
        qed
      next
        case nsVar: False
        show ?thesis
        proof (cases "is_Var ht")
          case True
          then obtain F Fty where ht: "ht = Var F Fty" by (cases ht) auto
          have unbF': "vt_lookup (tenv env) F = None"
            using head_norm_head_unbound[OF hn_t refl, of F Fty ts] sht ht by simp
          from body' nsVar ht obtain "is" where is_ok: "ok (ints_of' env ts) is"
            and r: "ok (flexrigid env bs F Fty is s') env'"
            by auto
          from step_ac_sym[OF step_ac_flex[OF is_ok flexrigid_ac[OF r unbF']]] show ?thesis by (simp add: t' ht)
        next
          case ntVar: False
          have nAbs: "\<not> is_Abs hs" "\<not> is_Abs ht" using body' nsVar ntVar by (auto split: if_splits)
          have body'': "ok (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg' Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht) env'"
            using body' nsVar ntVar nAbs by simp
          have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
            using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
          have rigid: "step_ac env (hs \<degree>\<degree> ss) (ht \<degree>\<degree> ts) env'"
          proof (cases hs)
            case hsC: (Const a Ta)
            show ?thesis
            proof (cases ht)
              case (Const b Tb)
              from body'' hsC Const obtain env1 ps where ab: "a = b"
                and ut: "ok (unify_types alg' Ta Tb env) env1" and ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env1) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              note u = unify_types_sound[OF ut]
              show ?thesis unfolding hsC Const
              proof (rule step_ac_rigid[OF u(2,1) _ _ len])
                show "steps_ac env1 (zip ss ts) env'" using foldM_steps_ac[OF f[unfolded psz]] IH by blast
              qed (use heads_types[OF ut _ _ _ _ disjI1[OF refl]] ab in auto)
            qed (use body'' hsC not_ok_rigid_clash in auto)
          next
            case hsF: (Free a Ta)
            show ?thesis
            proof (cases ht)
              case (Free b Tb)
              from body'' hsF Free obtain env1 ps where ab: "a = b"
                and ut: "ok (unify_types alg' Ta Tb env) env1" and ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env1) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              note u = unify_types_sound[OF ut]
              show ?thesis unfolding hsF Free
              proof (rule step_ac_rigid[OF u(2,1) _ _ len])
                show "steps_ac env1 (zip ss ts) env'" using foldM_steps_ac[OF f[unfolded psz]] IH by blast
              qed (use heads_types[OF ut _ _ _ _ disjI2[OF refl]] ab in auto)
            qed (use body'' hsF not_ok_rigid_clash in auto)
          next
            case hsB: (Bound i)
            show ?thesis
            proof (cases ht)
              case (Bound j)
              from body'' hsB Bound obtain ps where ij: "i = j" and ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg' bs s t env) ps env) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              show ?thesis unfolding hsB Bound
              proof (rule step_ac_rigid[OF extends_refl refl _ _ len])
                show "steps_ac env (zip ss ts) env'" using foldM_steps_ac[OF f[unfolded psz]] IH by blast
              qed (use ij in auto)
            qed (use body'' hsB not_ok_rigid_clash in auto)
          qed (use nsVar nAbs nApp in auto)
          then show ?thesis by (simp add: s' t')
        qed
      qed
    qed
  qed
  then show ?case by (rule step_ac_head_norm[OF hn_s hn_t])
qed


theorem unify_acyc:
  assumes "ok (unify alg' s t env) env'" "acyc env" "below (maxidx env) (vars s \<union> vars t \<union> evars env)"
  shows "acyc env'"
proof -
  have "step_ac env s t env'" using unif_acyc[of alg' "[]" s t env] assms(1) by (simp add: unify_def)
  from step_acD[OF this assms(2), of "{}"] assms(3) show ?thesis by simp
qed

end

subsection \<open>Without a hypothesis on the names\<close>

context pure_sig
begin

text \<open>
  The instance in which every name is loose: no hypothesis on the types of the names of the
  problem and of the given environment is left.
\<close>

theorem unify_typed_unifier:
  assumes un: "ok (unify alg' s t env) env'" and \<rho>: "wsinst alg \<rho>" "tsol (tyenv env') \<rho>"
    and wte: "wt_env \<rho> env" and tys: "e \<turnstile> inst \<rho> s : T" and tyt: "e \<turnstile> inst \<rho> t : T"
    and cl: "closed s" "closed t"
    and bl: "below (maxidx env) (vars s \<union> vars t \<union> evars env)" and ac0: "acyc env"
  shows "\<exists>\<sigma>. solution \<rho> \<sigma> env' \<and> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
proof -
  interpret G: pure_sig_gen alg ar ctab "UNIV :: indexname set"
    by (rule pure_sig_gen_axioms)
  have vi: "G.vinv \<rho> env (vars s \<union> vars t)"
    unfolding G.vinv_def G.vcons_def using bl by simp
  have ac: "acyc env'" by (rule unify_acyc[OF un ac0 bl])
  from G.unify_ghost_unifier[OF un \<rho> wte tys tyt vi cl ac] show ?thesis by blast
qed

end

end
