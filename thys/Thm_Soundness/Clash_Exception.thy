section \<open>The exception for a kept variable at a second type\<close>

theory Clash_Exception
  imports Norm_Clash
begin

text \<open>
  Theory \<open>Norm_Clash\<close> shows that a result of normalization does not depend on the variables
  whose name the environment binds at another type. This theory shows the other half: if such
  a variable is kept, there is no result, and what the code returns is the exception \<open>TYPE\<close>
  of \<open>Envir.lookup\<close>.

  ``Kept'' is made precise with a marker. The clashing variables of a term are replaced by a
  free variable of a name \<open>m\<close> that occurs neither in the term nor in the environment. The marker
  is an atom that normalization does not look up, so the normal form of the marked term
  shows where the clashing variables would end up: one of them is kept if \<open>m\<close> occurs in that
  normal form. The theorem is: if the marked term has a normal form in which \<open>m\<close> occurs, then
  the normalization of the term itself is the exception.

  The converse does not hold: the code may look a clashing variable up, and raise the
  exception, although a later \<open>\<beta>\<close>-reduction would have discarded it (it normalizes the function
  part of an application before it substitutes the argument).
\<close>

subsection \<open>The exception\<close>

text \<open>
  A computation that is the exception \<open>TYPE "Variable has two distinct types"\<close> of
  \<open>Envir.lookup\<close>, in the monad of \<open>Envir\<close> and, with trace events before it, in the monad of
  the rules:
\<close>

definition is_var_clash :: "'a M \<Rightarrow> bool" where
  "is_var_clash m \<longleftrightarrow> (\<exists>x T U. m = var_clash x T U)"

definition is_var_clashT :: "'a T \<Rightarrow> bool" where
  "is_var_clashT m \<longleftrightarrow> (\<exists>evs x T U. m = Some (evs, Err (UExn (PExn
    (Type_Error (STR ''Variable has two distinct types'') [] [Var x U, Var x T])))))"

lemma is_var_clash_iff:
  "is_var_clash m \<longleftrightarrow>
    (\<exists>x T U. m = raise (Type_Error (STR ''Variable has two distinct types'') [] [Var x U, Var x T]))"
  by (simp add: is_var_clash_def var_clash_def)

lemma is_var_clash_var_clash [simp]: "is_var_clash (var_clash x T U)"
  unfolding is_var_clash_def by blast

lemma is_var_clash_bind [simp]: "is_var_clash m \<Longrightarrow> is_var_clash (bindM m f)"
  by (auto simp: is_var_clash_iff raise_def bindM_def)

lemma is_var_clash_bind_ok: "ok m x \<Longrightarrow> is_var_clash (f x) \<Longrightarrow> is_var_clash (bindM m f)"
  by (simp add: bindM_def)

lemma is_var_clashT_liftMT [simp]: "is_var_clash m \<Longrightarrow> is_var_clashT (liftMT m)"
  by (auto simp: is_var_clash_iff is_var_clashT_def raise_def liftMT_def liftM_def liftWT_def)

lemma is_var_clashT_bind [simp]: "is_var_clashT m \<Longrightarrow> is_var_clashT (bindW m f)"
  by (auto simp: is_var_clashT_def bindW_def)

lemma is_var_clashT_bind_ok: "okT m x \<Longrightarrow> is_var_clashT (f x) \<Longrightarrow> is_var_clashT (bindW m f)"
  by (auto simp: is_var_clashT_def bindW_def)


subsection \<open>Variables that raise it\<close>

text \<open>
  A variable clashes strictly if its name is bound and the test of \<open>Envir.lookup\<close> on the two
  types returns false (\<^const>\<open>clash\<close> also holds if that test has no result).
\<close>

definition sclash :: "env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> bool" where
  "sclash env x U \<longleftrightarrow> (\<exists>T u. vt_lookup (tenv env) x = Some (T, u) \<and> ok (unified (tyenv env) U T) False)"

lemma sclash_clash: "sclash env x U \<Longrightarrow> clash env x U"
  by (auto simp: sclash_def clash_def)

lemma sclash_empty: "env_is_empty env \<Longrightarrow> \<not> sclash env x U"
  using clash_empty sclash_clash by blast

lemma lookup_sclash: "sclash env x U \<Longrightarrow> is_var_clash (lookup env x U)"
  by (auto simp: sclash_def lookup_def bindM_def)

lemma lookup1_sclash: "vt_is_empty (tyenv env) \<Longrightarrow> sclash env x U \<Longrightarrow> is_var_clash (lookup1 (tenv env) x U)"
  by (auto simp: sclash_def lookup1_def unified_def return_def)

text \<open>\<open>srel env t s\<close>: the term \<open>s\<close> is \<open>t\<close> with some strictly clashing variables replaced by free variables.\<close>

inductive srel :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" for env where
  Refl [simp, intro!]: "srel env t t"
| Mark: "sclash env x U \<Longrightarrow> srel env (Var x U) (Free m T)"
| Abs: "srel env t s \<Longrightarrow> srel env (Abs a T t) (Abs a T s)"
| App: "srel env t s \<Longrightarrow> srel env u v \<Longrightarrow> srel env (t $ u) (s $ v)"

lemma srel_Var: "srel env (Var x U) s \<Longrightarrow> \<not> sclash env x U \<Longrightarrow> s = Var x U"
  by (auto elim: srel.cases)

lemma srel_AbsE:
  assumes "srel env (Abs a T t) s"
  obtains s' where "s = Abs a T s'" "srel env t s'"
  using assms by (auto elim: srel.cases)

lemma srel_AppE:
  assumes "srel env (t $ u) s"
  obtains t' u' where "s = t' $ u'" "srel env t t'" "srel env u u'"
  using assms by (auto elim: srel.cases)

lemma srel_atom:
  "srel env (Const c T) s \<Longrightarrow> s = Const c T" "srel env (Free c T) s \<Longrightarrow> s = Free c T"
  "srel env (Bound i) s \<Longrightarrow> s = Bound i"
  by (auto elim: srel.cases)

lemma srel_is_Abs: "srel env t s \<Longrightarrow> is_Abs s \<longleftrightarrow> is_Abs t"
  by (cases rule: srel.cases) auto

lemma srel_nosc:
  assumes "srel env t s" "\<And>x U. (x, U) \<in> vars t \<Longrightarrow> \<not> sclash env x U"
  shows "s = t"
  using assms by (induction rule: srel.induct) auto

lemma srel_empty: "env_is_empty env \<Longrightarrow> srel env t s \<Longrightarrow> s = t"
  using srel_nosc[of env t s] by (simp add: sclash_empty)

lemma srel_lift: "srel env t s \<Longrightarrow> srel env (lift t k) (lift s k)"
  by (induction arbitrary: k rule: srel.induct) (auto intro: srel.intros)

lemma srel_subst: "srel env t s \<Longrightarrow> srel env u v \<Longrightarrow> srel env (t[u/k]) (s[v/k])"
proof (induction arbitrary: u v k rule: srel.induct)
  case (Refl t)
  then show ?case
  proof (induction t arbitrary: u v k)
    case (Abs a T t)
    from Abs.IH[OF srel_lift[OF Abs.prems, of 0], of "k + 1"] show ?case by (auto intro: srel.Abs)
  qed (auto intro: srel.App simp: subst_Bound)
next
  case (Abs t s a T)
  from Abs.IH[OF srel_lift[OF Abs.prems, of 0], of "k + 1"] show ?case by (auto intro: srel.Abs)
qed (auto intro: srel.intros)

lemma srel_subst_bound: "srel env t s \<Longrightarrow> srel env u v \<Longrightarrow> srel env (subst_bound u t) (subst_bound v s)"
  by (simp add: subst_bound_subst srel_subst)


subsection \<open>The computation on a term and on a term with replaced variables\<close>

lemma norm_term1_Abs:
  "norm_term1 te (Abs a T b) = do {b' \<leftarrow> norm_term1 te b; return (Abs a T b')}"
  by (subst norm_term1.simps) simp

lemma norm_term1_redex: "norm_term1 te (Abs b U body $ u) = norm_term1 te (subst_bound u body)"
  by (subst norm_term1.simps) simp

lemma norm_term1_App:
  "\<not> is_Abs f \<Longrightarrow> norm_term1 te (f $ u) =
    do {nf \<leftarrow> norm_term1 te f;
      case nf of Abs _ _ body \<Rightarrow> norm_term1 te (subst_bound u body)
      | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 te u; return (nf $ nu)}}"
  by (subst norm_term1.simps) (cases f; simp)

lemma norm_term2_Abs:
  "norm_term2 env (Abs a T b) =
    do {T' \<leftarrow> norm_type_aux (tyenv env) T; b' \<leftarrow> norm_term2 env b; return (Abs a T' b')}"
  by (subst norm_term2.simps) simp

lemma norm_term2_redex: "norm_term2 env (Abs b U body $ u) = norm_term2 env (subst_bound u body)"
  by (subst norm_term2.simps) simp

lemma norm_term2_App:
  "\<not> is_Abs f \<Longrightarrow> norm_term2 env (f $ u) =
    do {nf \<leftarrow> norm_term2 env f;
      case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body)
      | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)}}"
  by (subst norm_term2.simps) (cases f; simp)

text \<open>
  If the term with replaced variables has a normal form, the computation on the term itself
  either has the same result or is the exception: the two computations agree until the first
  strictly clashing variable is looked up.
\<close>

lemma norm_term1_sim:
  assumes "norm_term1 te s = Some r"
  shows "r = Ok s' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> srel env t s \<Longrightarrow>
    ok (norm_term1 te t) s' \<or> is_var_clash (norm_term1 te t)"
  using assms
proof (induction te s r arbitrary: s' t rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te s r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and em = "1.prems"(3) and rel = "1.prems"(4)
  have IH: "ok (norm_term1 te v) u' \<or> is_var_clash (norm_term1 te v)" if "ok (nt te u) u'" "srel env v u" for u u' v
    using "1.IH"[OF that(1) refl te em that(2)] .
  show ?case
  proof (cases t)
    case (Var x U)
    show ?thesis
    proof (cases "sclash env x U")
      case True
      then show ?thesis using lookup1_sclash[OF em] te Var by (simp add: norm_term1_Var)
    next
      case False
      with rel Var have s: "s = Var x U" by (simp add: srel_Var)
      with h obtain lr where lr: "ok (lookup1 te x U) lr"
        and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return s) s'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest lr s Var show ?thesis by (auto simp: norm_term1_Var)
      next
        case (Some u)
        with rest have "ok (nt te u) s'" by simp
        from IH[OF this srel.Refl] lr Some Var show ?thesis by (auto simp: norm_term1_Var bindM_def)
      qed
    qed
  next
    case (Abs a T b)
    with rel obtain sb where s: "s = Abs a T sb" "srel env b sb" by (auto elim: srel_AbsE)
    with h obtain sb' where b: "ok (nt te sb) sb'" "s' = Abs a T sb'" by auto
    from IH[OF b(1) s(2)] b(2) Abs show ?thesis by (auto simp: norm_term1_Abs)
  next
    case (App f u)
    with rel obtain f' u' where s: "s = f' $ u'" and rf: "srel env f f'" and ru: "srel env u u'"
      by (auto elim: srel_AppE)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with rf obtain body' where f': "f' = Abs b U0 body'" "srel env body body'" by (auto elim: srel_AbsE)
      from h s f' have "ok (nt te (subst_bound u' body')) s'" by simp
      from IH[OF this srel_subst_bound[OF f'(2) ru]] App f show ?thesis by (simp add: norm_term1_redex)
    next
      case False
      then have nA: "\<not> is_Abs f'" using srel_is_Abs[OF rf] by simp
      with h s obtain nf where hf: "ok (nt te f') nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u' body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u'; return (nf $ nu)}) s'"
        by (cases f') auto
      from IH[OF hf rf] show ?thesis
      proof
        assume "is_var_clash (norm_term1 te f)"
        then show ?thesis using App False by (simp add: norm_term1_App)
      next
        assume nf: "ok (norm_term1 te f) nf"
        have unfold: "norm_term1 te t = (case nf of Abs _ _ body \<Rightarrow> norm_term1 te (subst_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 te u; return (nf $ nu)})"
          using nf App False by (simp add: norm_term1_App bindM_def)
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain b U0 body where nfa: "nf = Abs b U0 body" by (cases nf) auto
          with rest have "ok (nt te (subst_bound u' body)) s'" by simp
          from IH[OF this srel_subst_bound[OF srel.Refl ru]] nfa unfold show ?thesis by simp
        next
          case nA': False
          with rest obtain nu where hu: "ok (nt te u') nu" and s': "s' = nf $ nu" by (cases nf) auto
          from IH[OF hu ru] s' nA' unfold show ?thesis by (cases nf) auto
        qed
      qed
    qed
  qed (use h rel in \<open>auto dest!: srel_atom simp: norm_term1_atom\<close>)
qed

lemma norm_term2_sim:
  assumes "norm_term2 env s = Some r"
  shows "r = Ok s' \<Longrightarrow> srel env t s \<Longrightarrow> ok (norm_term2 env t) s' \<or> is_var_clash (norm_term2 env t)"
  using assms
proof (induction env s r arbitrary: s' t rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env s r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and rel = "1.prems"(2)
  have IH: "ok (norm_term2 env v) u' \<or> is_var_clash (norm_term2 env v)" if "ok (nt env u) u'" "srel env v u" for u u' v
    using "1.IH"[OF that(1) refl that(2)] .
  show ?case
  proof (cases t)
    case (Var x U)
    show ?thesis
    proof (cases "sclash env x U")
      case True
      then show ?thesis using lookup_sclash Var by (simp add: norm_term2_Var)
    next
      case False
      with rel Var have s: "s = Var x U" by (simp add: srel_Var)
      with h obtain lr where lr: "ok (lookup env x U) lr"
        and rest: "ok (case lr of Some u \<Rightarrow> nt env u
          | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) U; return (Var x T')}) s'"
        by auto
      show ?thesis
      proof (cases lr)
        case None
        with rest lr s Var show ?thesis by (auto simp: norm_term2_Var)
      next
        case (Some u)
        with rest have "ok (nt env u) s'" by simp
        from IH[OF this srel.Refl] lr Some Var show ?thesis by (auto simp: norm_term2_Var bindM_def)
      qed
    qed
  next
    case (Abs a T b)
    with rel obtain sb where s: "s = Abs a T sb" "srel env b sb" by (auto elim: srel_AbsE)
    with h obtain T' sb' where b: "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env sb) sb'" "s' = Abs a T' sb'"
      by auto
    have eq: "norm_term2 env t = do {b' \<leftarrow> norm_term2 env b; return (Abs a T' b')}"
      using b(1) Abs by (simp add: norm_term2_Abs bindM_def)
    from IH[OF b(2) s(2)] b(3) show ?thesis unfolding eq by auto
  next
    case (App f u)
    with rel obtain f' u' where s: "s = f' $ u'" and rf: "srel env f f'" and ru: "srel env u u'"
      by (auto elim: srel_AppE)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with rf obtain body' where f': "f' = Abs b U0 body'" "srel env body body'" by (auto elim: srel_AbsE)
      from h s f' have "ok (nt env (subst_bound u' body')) s'" by simp
      from IH[OF this srel_subst_bound[OF f'(2) ru]] App f show ?thesis by (simp add: norm_term2_redex)
    next
      case False
      then have nA: "\<not> is_Abs f'" using srel_is_Abs[OF rf] by simp
      with h s obtain nf where hf: "ok (nt env f') nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u' body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u'; return (nf $ nu)}) s'"
        by (cases f') auto
      from IH[OF hf rf] show ?thesis
      proof
        assume "is_var_clash (norm_term2 env f)"
        then show ?thesis using App False by (simp add: norm_term2_App)
      next
        assume nf: "ok (norm_term2 env f) nf"
        have unfold: "norm_term2 env t = (case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u; return (nf $ nu)})"
          using nf App False by (simp add: norm_term2_App bindM_def)
        show ?thesis
        proof (cases "is_Abs nf")
          case True
          then obtain b U0 body where nfa: "nf = Abs b U0 body" by (cases nf) auto
          with rest have "ok (nt env (subst_bound u' body)) s'" by simp
          from IH[OF this srel_subst_bound[OF srel.Refl ru]] nfa unfold show ?thesis by simp
        next
          case nA': False
          with rest obtain nu where hu: "ok (nt env u') nu" and s': "s' = nf $ nu" by (cases nf) auto
          from IH[OF hu ru] s' nA' unfold show ?thesis by (cases nf) auto
        qed
      qed
    qed
  qed (use h rel in \<open>auto dest!: srel_atom simp: norm_term2_atom\<close>)
qed

text \<open>\<open>Envir.norm_term\<close>:\<close>

theorem norm_term_sim:
  assumes "ok (norm_term env s) s'" "srel env t s"
  shows "ok (norm_term env t) s' \<or> is_var_clash (norm_term env t)"
proof (cases "env_is_empty env")
  case True
  with assms srel_empty show ?thesis by blast
next
  case False
  show ?thesis
  proof (cases "vt_is_empty (tyenv env)")
    case True
    with assms(1) False have "norm_term1 (tenv env) s = Some (Ok s')" by (simp add: norm_term_def)
    from norm_term1_sim[OF this refl refl True assms(2)] False True show ?thesis
      by (simp add: norm_term_def)
  next
    case em: False
    with assms(1) False have "norm_term2 env s = Some (Ok s')" by (simp add: norm_term_def)
    from norm_term2_sim[OF this refl assms(2)] False em show ?thesis by (simp add: norm_term_def)
  qed
qed


subsection \<open>Free variables of a normal form\<close>

text \<open>The names of the free variables of a normal form come from the term and from the bindings:\<close>

fun fnames :: "pterm \<Rightarrow> name set" where
  "fnames (Free a T) = {a}"
| "fnames (Abs a T t) = fnames t"
| "fnames (t $ u) = fnames t \<union> fnames u"
| "fnames _ = {}"

definition env_fnames :: "env \<Rightarrow> name set" where
  "env_fnames env = (\<Union>u\<in>{u. \<exists>x T. vt_lookup (tenv env) x = Some (T, u)}. fnames u)"

lemma fnames_env: "vt_lookup (tenv env) x = Some (T, u) \<Longrightarrow> fnames u \<subseteq> env_fnames env"
  unfolding env_fnames_def by blast

lemma fnames_incr_bv [simp]: "fnames (incr_bv n k t) = fnames t"
  by (induction n k t rule: incr_bv.induct) auto

lemma fnames_subst: "fnames (t[u/k]) \<subseteq> fnames t \<union> fnames u"
proof (induction t arbitrary: u k)
  case (Abs a T t)
  from Abs[of "lift u 0" "k + 1"] show ?case by simp
next
  case (App t1 t2)
  from App(1)[of u k] App(2)[of u k] show ?case by auto
qed (auto simp: subst_Bound)

lemma fnames_subst_bound: "fnames (subst_bound u t) \<subseteq> fnames t \<union> fnames u"
  by (simp add: subst_bound_subst fnames_subst)

lemma norm_term1_fnames:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> fnames t' \<subseteq> fnames t \<union> env_fnames env"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2)
  have IH: "fnames u' \<subseteq> fnames u \<union> env_fnames env" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest show ?thesis by simp
    next
      case (Some u)
      with ok_lookup1[OF lr] te have "fnames u \<subseteq> env_fnames env" by (auto dest: fnames_env)
      with IH[of u t'] rest Some show ?thesis by auto
    qed
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      from IH[OF this] fnames_subst_bound[of u body] App f show ?thesis by auto
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        from IH[OF this] fnames_subst_bound[of u body] IH[OF hf] nf App show ?thesis by auto
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from IH[OF hf] IH[OF hu] t' App show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma ok_lookup_Some_bound: "ok (lookup env x T) (Some u) \<Longrightarrow> \<exists>U. vt_lookup (tenv env) x = Some (U, u)"
  by (auto simp: lookup_def var_clash_def split: option.splits if_splits)

lemma norm_term2_fnames:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> fnames t' \<subseteq> fnames t \<union> env_fnames env"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "fnames u' \<subseteq> fnames u \<union> env_fnames env" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl] .
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
      with rest show ?thesis by auto
    next
      case (Some u)
      with ok_lookup_Some_bound[of env x T u] lr have "fnames u \<subseteq> env_fnames env" by (auto dest: fnames_env)
      with IH[of u t'] rest Some show ?thesis by auto
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (nt env body) body'" "t' = Abs a T' body'" by auto
    with IH Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      from IH[OF this] fnames_subst_bound[of u body] App f show ?thesis by auto
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        from IH[OF this] fnames_subst_bound[of u body] IH[OF hf] nf App show ?thesis by auto
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from IH[OF hf] IH[OF hu] t' App show ?thesis by auto
      qed
    qed
  qed (use h in auto)
qed

lemma norm_term_fnames: "ok (norm_term env t) t' \<Longrightarrow> fnames t' \<subseteq> fnames t \<union> env_fnames env"
  using norm_term1_fnames[of "tenv env" t "Ok t'" t' env] norm_term2_fnames[of env t "Ok t'" t']
  by (auto simp: norm_term_def split: if_splits)


subsection \<open>A kept variable raises the exception\<close>

text \<open>The term with its strictly clashing variables marked by the name \<open>m\<close>:\<close>

fun mark :: "env \<Rightarrow> name \<Rightarrow> pterm \<Rightarrow> pterm" where
  "mark env m (Var x U) = (if sclash env x U then Free m U else Var x U)"
| "mark env m (Abs a T t) = Abs a T (mark env m t)"
| "mark env m (t $ u) = mark env m t $ mark env m u"
| "mark env m t = t"

lemma srel_mark: "srel env t (mark env m t)"
  by (induction t) (auto intro: srel.intros)

text \<open>
  The marker is kept if it occurs in the normal form of the marked term. Then the
  normalization of the term is the exception.
\<close>

theorem norm_term_kept_clash:
  assumes "ok (norm_term env (mark env m t)) s'" and kept: "m \<in> fnames s'"
    and fresh: "m \<notin> fnames t" "m \<notin> env_fnames env"
  shows "is_var_clash (norm_term env t)"
proof -
  from norm_term_sim[OF assms(1) srel_mark] show ?thesis
  proof
    assume "ok (norm_term env t) s'"
    from norm_term_fnames[OF this] kept fresh show ?thesis by blast
  qed
qed

text \<open>
  Spelled out: the result is \<open>raise (TYPE ("Variable has two distinct types", [], [Var x U, Var x T]))\<close>
  for some variable, and in particular there is no result.
\<close>

corollary norm_term_kept_clash_exn:
  assumes "ok (norm_term env (mark env m t)) s'" "m \<in> fnames s'" "m \<notin> fnames t" "m \<notin> env_fnames env"
  shows "\<exists>x T U. norm_term env t =
    raise (Type_Error (STR ''Variable has two distinct types'') [] [Var x U, Var x T])"
  using norm_term_kept_clash[OF assms] by (simp add: is_var_clash_iff)

text \<open>
  The simplest instance, which also shows that the hypotheses can hold: a strictly clashing
  variable itself. Marked, it is its own normal form (here without type bindings), so it is
  kept; and its normalization is the exception.
\<close>

corollary norm_term_var_clash:
  assumes "sclash env x U"
  shows "is_var_clash (norm_term env (Var x U))"
proof -
  have ne: "\<not> env_is_empty env" using assms sclash_empty by blast
  show ?thesis
  proof (cases "vt_is_empty (tyenv env)")
    case True
    with ne lookup1_sclash[OF True assms] show ?thesis by (simp add: norm_term_def norm_term1_Var)
  next
    case False
    with ne lookup_sclash[OF assms] show ?thesis by (simp add: norm_term_def norm_term2_Var)
  qed
qed

text \<open>
  With \<open>norm_term_clash_rel\<close> this is a dichotomy for a term whose marked version has a normal
  form \<open>s'\<close>: either \<open>m\<close> does not occur in \<open>s'\<close>, and then \<open>s'\<close> is the result for the term itself or
  the term raises the exception earlier; or \<open>m\<close> occurs in \<open>s'\<close>, and the term raises the exception.
\<close>


subsection \<open>The new theorems of the rules\<close>

text \<open>
  The functions that build the new theorem from a unifier (\<^const>\<open>newth\<close> for \<open>assumption\<close>,
  \<^const>\<open>fnewth\<close> for \<open>flexflex_rule\<close>, \<^const>\<open>addth\<close> for composition and resolution) normalize the
  flex-flex pairs first and the proposition after them. If a marker is kept in the theorem
  that they build from the marked arguments, they raise the exception on the arguments
  themselves.
\<close>

definition fnames_list :: "pterm list \<Rightarrow> name set" where
  "fnames_list ts = (\<Union>t\<in>set ts. fnames t)"

definition fnames_tps :: "(pterm \<times> pterm) list \<Rightarrow> name set" where
  "fnames_tps tps = (\<Union>(t, u)\<in>set tps. fnames t \<union> fnames u)"

abbreviation mark_tps :: "env \<Rightarrow> name \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list" where
  "mark_tps env m \<equiv> map (map_prod (mark env m) (mark env m))"

lemma fnames_list_simps [simp]:
  "fnames_list [] = {}" "fnames_list (t # ts) = fnames t \<union> fnames_list ts"
  "fnames_list (ts @ us) = fnames_list ts \<union> fnames_list us"
  by (auto simp: fnames_list_def)

lemma fnames_tps_simps [simp]:
  "fnames_tps [] = {}" "fnames_tps ((t, u) # tps) = fnames t \<union> fnames u \<union> fnames_tps tps"
  by (auto simp: fnames_tps_def)

lemma fnames_list_implies [simp]: "fnames (list_implies As B) = fnames_list As \<union> fnames B"
  by (induction As) (auto simp: implies_def)

lemma srels_mark: "list_all2 (srel env) ts (map (mark env m) ts)"
  by (induction ts) (auto simp: srel_mark)

lemma srelp_mark: "list_all2 (rel_prod (srel env) (srel env)) tps (mark_tps env m tps)"
  by (induction tps) (auto simp: srel_mark)

lemma srels_empty:
  assumes "env_is_empty env" "list_all2 (srel env) ts ss"
  shows "ss = ts"
  using assms(2) by (induction ts ss rule: list_all2_induct) (auto dest: srel_empty[OF assms(1)])

lemma srelp_empty:
  assumes "env_is_empty env" "list_all2 (rel_prod (srel env) (srel env)) ts ss"
  shows "ss = ts"
  using assms(2) by (induction ts ss rule: list_all2_induct) (auto dest: srel_empty[OF assms(1)])

lemma srel_list_implies:
  assumes "list_all2 (srel env) As As'" "srel env B B'"
  shows "srel env (list_implies As B) (list_implies As' B')"
  using assms by (induction As As' rule: list_all2_induct) (auto intro!: srel.App)

text \<open>Lists: the first element that raises the exception ends the computation.\<close>

lemma mapM_sim:
  assumes "list_all2 R ts ss" "ok (mapM f ss) rs"
    and step: "\<And>t s r. R t s \<Longrightarrow> ok (f s) r \<Longrightarrow> ok (f t) r \<or> is_var_clash (f t)"
  shows "ok (mapM f ts) rs \<or> is_var_clash (mapM f ts)"
  using assms(1,2)
proof (induction ts ss arbitrary: rs rule: list_all2_induct)
  case (Cons t ts s ss)
  from Cons.prems obtain r rs' where r: "ok (f s) r" "ok (mapM f ss) rs'" "rs = r # rs'" by auto
  from step[OF Cons.hyps(1) r(1)] show ?case
  proof
    assume "is_var_clash (f t)"
    then show ?thesis by simp
  next
    assume ft: "ok (f t) r"
    from Cons.IH[OF r(2)] show ?thesis
    proof
      assume "ok (mapM f ts) rs'"
      with ft r(3) show ?thesis by simp
    next
      assume "is_var_clash (mapM f ts)"
      then have "is_var_clash (mapM f (t # ts))" using ft by (auto intro: is_var_clash_bind_ok)
      then show ?thesis ..
    qed
  qed
qed simp

lemma norm_tpair_sim:
  assumes "rel_prod (srel env) (srel env) tu su" "ok (norm_tpair env su) r"
  shows "ok (norm_tpair env tu) r \<or> is_var_clash (norm_tpair env tu)"
proof -
  obtain t u s v where tu: "tu = (t, u)" "su = (s, v)" by (cases tu, cases su)
  with assms(1) have rel: "srel env t s" "srel env u v" by simp_all
  from assms(2) tu obtain t' u' where n: "ok (norm_term env s) t'" "ok (norm_term env v) u'" "r = (t', u')"
    by (auto simp: norm_tpair_def)
  from norm_term_sim[OF n(1) rel(1)] show ?thesis
  proof
    assume "is_var_clash (norm_term env t)"
    then show ?thesis by (simp add: norm_tpair_def tu)
  next
    assume a: "ok (norm_term env t) t'"
    from norm_term_sim[OF n(2) rel(2)] show ?thesis
    proof
      assume "ok (norm_term env u) u'"
      with a n(3) show ?thesis by (simp add: norm_tpair_def tu)
    next
      assume "is_var_clash (norm_term env u)"
      then have "is_var_clash (norm_tpair env tu)"
        using a by (auto simp: norm_tpair_def tu intro: is_var_clash_bind_ok)
      then show ?thesis ..
    qed
  qed
qed

lemmas mapM_norm_tpair_sim = mapM_sim[where f = "norm_tpair env" for env, OF _ _ norm_tpair_sim]
lemmas mapM_norm_term_sim = mapM_sim[where f = "norm_term env" for env, OF _ _ norm_term_sim[rotated]]

lemma mapM_norm_tpair_fnames:
  "ok (mapM (norm_tpair env) tps) ntps \<Longrightarrow> fnames_tps ntps \<subseteq> fnames_tps tps \<union> env_fnames env"
proof (induction tps arbitrary: ntps)
  case (Cons tu tps)
  obtain t u where tu: "tu = (t, u)" by (cases tu)
  have e: "norm_tpair env (t, u) = do {t' \<leftarrow> norm_term env t; u' \<leftarrow> norm_term env u; return (t', u')}"
    by (simp add: norm_tpair_def)
  from Cons.prems tu obtain t' u' ns where n: "ok (norm_term env t) t'" "ok (norm_term env u) u'"
    "ok (mapM (norm_tpair env) tps) ns" "ntps = (t', u') # ns"
    by (auto simp: e)
  from norm_term_fnames[OF n(1)] norm_term_fnames[OF n(2)] Cons.IH[OF n(3)] n(4) tu show ?case by auto
qed simp

lemma mapM_norm_term_fnames:
  "ok (mapM (norm_term env) ts) ts' \<Longrightarrow> fnames_list ts' \<subseteq> fnames_list ts \<union> env_fnames env"
proof (induction ts arbitrary: ts')
  case (Cons t ts)
  from Cons.prems obtain t' ns where n: "ok (norm_term env t) t'" "ok (mapM (norm_term env) ts) ns" "ts' = t' # ns"
    by auto
  from norm_term_fnames[OF n(1)] Cons.IH[OF n(2)] n(3) show ?case by auto
qed simp

text \<open>\<open>assumption\<close>:\<close>

lemma newth_sim:
  assumes r: "okT (newth ctx' n (env, tps')) r'"
    and Bs: "list_all2 (srel env) (ac_Bs ctx) (ac_Bs ctx')" and C: "srel env (ac_C ctx) (ac_C ctx')"
    and tps: "list_all2 (rel_prod (srel env) (srel env)) tps tps'"
  shows "okT (newth ctx n (env, tps)) r' \<or> is_var_clashT (newth ctx n (env, tps))"
proof (cases "env_is_empty env")
  case True
  with r srels_empty[OF True Bs] srel_empty[OF True C] srelp_empty[OF True tps]
  show ?thesis by (simp add: newth_def)
next
  case False
  with r obtain ntps P where n: "ok (mapM (norm_tpair env) tps') ntps"
    "ok (norm_term env (list_implies (ac_Bs ctx') (ac_C ctx'))) P"
    and r': "r' = ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P\<rparr>"
    by (auto simp: newth_def)
  let ?body = "do {tps \<leftarrow> mapM (norm_tpair env) tps;
      P \<leftarrow> norm_term env (list_implies (ac_Bs ctx) (ac_C ctx));
      return (ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = tps, th_prop = P\<rparr>)}"
  have eq: "newth ctx n (env, tps) = liftMT ?body" using False by (simp add: newth_def)
  have "ok ?body r' \<or> is_var_clash ?body"
  proof -
    from mapM_norm_tpair_sim[OF tps n(1)] show ?thesis
    proof
      assume "is_var_clash (mapM (norm_tpair env) tps)"
      then show ?thesis by simp
    next
      assume a: "ok (mapM (norm_tpair env) tps) ntps"
      from norm_term_sim[OF n(2) srel_list_implies[OF Bs C]] show ?thesis
      proof
        assume "ok (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx))) P"
        with a r' show ?thesis by simp
      next
        assume "is_var_clash (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx)))"
        then have "is_var_clash ?body" using a by (auto intro: is_var_clash_bind_ok)
        then show ?thesis ..
      qed
    qed
  qed
  then show ?thesis unfolding eq by auto
qed

lemma newth_fnames:
  assumes "okT (newth ctx n (env, tps)) r"
  shows "fnames (th_prop (ar_thm r)) \<union> fnames_tps (th_tpairs (ar_thm r)) \<subseteq>
    fnames_list (ac_Bs ctx) \<union> fnames (ac_C ctx) \<union> fnames_tps tps \<union> env_fnames env"
proof (cases "env_is_empty env")
  case True
  with assms show ?thesis by (auto simp: newth_def)
next
  case False
  with assms obtain ntps P where n: "ok (mapM (norm_tpair env) tps) ntps"
    "ok (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx))) P"
    and r: "r = ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P\<rparr>"
    by (auto simp: newth_def)
  from mapM_norm_tpair_fnames[OF n(1)] norm_term_fnames[OF n(2)] r show ?thesis by auto
qed

theorem newth_kept_clash:
  assumes r: "okT (newth ctx' n (env, mark_tps env m tps)) r'"
    and ctx': "ac_Bs ctx' = map (mark env m) (ac_Bs ctx)" "ac_C ctx' = mark env m (ac_C ctx)"
    and kept: "m \<in> fnames (th_prop (ar_thm r')) \<union> fnames_tps (th_tpairs (ar_thm r'))"
    and fresh: "m \<notin> fnames_list (ac_Bs ctx) \<union> fnames (ac_C ctx) \<union> fnames_tps tps \<union> env_fnames env"
  shows "is_var_clashT (newth ctx n (env, tps))"
proof -
  have "okT (newth ctx n (env, tps)) r' \<or> is_var_clashT (newth ctx n (env, tps))"
    by (rule newth_sim[OF r]) (simp_all add: ctx' srels_mark srel_mark srelp_mark)
  then show ?thesis
  proof
    assume "okT (newth ctx n (env, tps)) r'"
    from newth_fnames[OF this] kept fresh show ?thesis by blast
  qed
qed

text \<open>\<open>flexflex_rule\<close>:\<close>

lemma fnewth_sim:
  assumes r: "ok (fnewth th' env) r"
    and P: "srel env (th_prop th) (th_prop th')" and tps: "list_all2 (rel_prod (srel env) (srel env)) (th_tpairs th) (th_tpairs th')"
    and mx: "th_maxidx th' = th_maxidx th"
  shows "ok (fnewth th env) r \<or> is_var_clash (fnewth th env)"
proof (cases "env_is_empty env")
  case True
  from srel_empty[OF True P] srelp_empty[OF True tps] mx have "th' = th" by simp
  with r show ?thesis by simp
next
  case False
  with r obtain ntps Q where n: "ok (mapM (norm_tpair env) (th_tpairs th')) ntps" "ok (norm_term env (th_prop th')) Q"
    and r': "r = \<lparr>th_maxidx = maxidx_tpairs (filter (\<lambda>(t, u). \<not> aconv_term t u) ntps) (maxidx_of_term Q),
      th_tpairs = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps, th_prop = Q\<rparr>"
    by (auto simp: fnewth_def Let_def)
  let ?body = "do {tps \<leftarrow> mapM (norm_tpair env) (th_tpairs th);
      let tps' = filter (\<lambda>(t, u). \<not> aconv_term t u) tps;
      P \<leftarrow> norm_term env (th_prop th);
      return \<lparr>th_maxidx = maxidx_tpairs tps' (maxidx_of_term P), th_tpairs = tps', th_prop = P\<rparr>}"
  have eq: "fnewth th env = ?body" using False by (simp add: fnewth_def)
  from mapM_norm_tpair_sim[OF tps n(1)] show ?thesis
  proof
    assume "is_var_clash (mapM (norm_tpair env) (th_tpairs th))"
    then show ?thesis unfolding eq by simp
  next
    assume a: "ok (mapM (norm_tpair env) (th_tpairs th)) ntps"
    from norm_term_sim[OF n(2) P] show ?thesis
    proof
      assume "ok (norm_term env (th_prop th)) Q"
      with a r' show ?thesis unfolding eq by (simp add: Let_def)
    next
      assume "is_var_clash (norm_term env (th_prop th))"
      then have "is_var_clash ?body" using a by (auto simp: Let_def intro: is_var_clash_bind_ok)
      then show ?thesis unfolding eq ..
    qed
  qed
qed

lemma fnames_tps_filter: "fnames_tps (filter Q tps) \<subseteq> fnames_tps tps"
  by (auto simp: fnames_tps_def)

lemma fnewth_fnames:
  assumes "ok (fnewth th env) r"
  shows "fnames (th_prop r) \<union> fnames_tps (th_tpairs r) \<subseteq> fnames (th_prop th) \<union> fnames_tps (th_tpairs th) \<union> env_fnames env"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u)")
  case True
  with assms show ?thesis by (auto simp: fnewth_def)
next
  case False
  have eq: "fnewth th env = do {tps \<leftarrow> mapM (norm_tpair env) (th_tpairs th);
      let tps' = filter (\<lambda>(t, u). \<not> aconv_term t u) tps;
      P \<leftarrow> norm_term env (th_prop th);
      return \<lparr>th_maxidx = maxidx_tpairs tps' (maxidx_of_term P), th_tpairs = tps', th_prop = P\<rparr>}"
    using False unfolding fnewth_def by (simp only: if_False)
  from assms[unfolded eq] obtain ntps Q where n: "ok (mapM (norm_tpair env) (th_tpairs th)) ntps" "ok (norm_term env (th_prop th)) Q"
    and r: "th_tpairs r = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop r = Q"
    by (auto simp: Let_def)
  from mapM_norm_tpair_fnames[OF n(1)] norm_term_fnames[OF n(2)] r fnames_tps_filter[of _ ntps]
  show ?thesis by fastforce
qed

theorem fnewth_kept_clash:
  assumes r: "ok (fnewth (th\<lparr>th_tpairs := mark_tps env m (th_tpairs th), th_prop := mark env m (th_prop th)\<rparr>) env) r"
    and kept: "m \<in> fnames (th_prop r) \<union> fnames_tps (th_tpairs r)"
    and fresh: "m \<notin> fnames (th_prop th) \<union> fnames_tps (th_tpairs th) \<union> env_fnames env"
  shows "is_var_clash (fnewth th env)"
proof -
  have "ok (fnewth th env) r \<or> is_var_clash (fnewth th env)"
    by (rule fnewth_sim[OF r]) (simp_all add: srel_mark srelp_mark)
  then show ?thesis
  proof
    assume "ok (fnewth th env) r"
    from fnewth_fnames[OF this] kept fresh show ?thesis by blast
  qed
qed

text \<open>
  Composition and resolution. \<^const>\<open>addth\<close> does not normalize everything: if no variable of the
  proof state can be bound (\<^const>\<open>above\<close>), it copies the premises and the conclusion of the state,
  and of a lifted premise of the rule it copies the assumptions that the rule was lifted over
  (\<^const>\<open>norm_term_skip\<close>). A clashing variable in a copied part would be kept without an
  exception. There is none if the variables of the copied parts have indices up to the bound
  of the test, as the variables of the proof state have (\<open>above_nosc\<close>).
\<close>

definition nosc :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "nosc env t \<longleftrightarrow> (\<forall>(x, U)\<in>vars t. \<not> sclash env x U)"

lemma mark_nosc: "nosc env t \<Longrightarrow> mark env m t = t"
  by (induction t) (auto simp: nosc_def)

lemma nosc_empty: "env_is_empty env \<Longrightarrow> nosc env t"
  by (simp add: nosc_def sclash_empty)

lemma map_mark_nosc: "\<forall>t\<in>set ts. nosc env t \<Longrightarrow> map (mark env m) ts = ts"
  by (induction ts) (simp_all add: mark_nosc)

lemma mark_tps_empty: "env_is_empty env \<Longrightarrow> mark_tps env m tps = tps"
  by (induction tps) (auto simp: mark_nosc nosc_empty)

lemma vt_above_lookup: "vt_above tab lim \<Longrightarrow> vt_lookup tab x = Some v \<Longrightarrow> lim < snd x"
  by transfer auto

lemma above_nosc:
  assumes "above env lim" "\<forall>(x, U)\<in>vars t. snd x \<le> lim"
  shows "nosc env t"
  using assms vt_above_lookup[of "tenv env" lim] by (fastforce simp: nosc_def sclash_def above_def)

text \<open>The assumptions that \<^const>\<open>norm_term_skip\<close> copies:\<close>

function skipped :: "integer \<Rightarrow> pterm \<Rightarrow> pterm list" where
  "skipped n t =
    (if n = 0 then []
     else case dest_all t of
       Some (a, T, b) \<Rightarrow> skipped n b
     | None \<Rightarrow> (case dest_imp t of Some (A, B) \<Rightarrow> A # skipped (n - 1) B | None \<Rightarrow> []))"
  by auto
termination by (relation "measure (\<lambda>(_, t). size t)") (auto dest: dest_size)

declare skipped.simps[simp del]

lemma dest_all_mark:
  "dest_all (mark env m t) = map_option (\<lambda>(a, T, b). (a, T, mark env m b)) (dest_all t)"
  by (cases t rule: dest_all.cases) (auto split: if_splits)

lemma dest_imp_mark:
  "dest_imp (mark env m t) = map_option (map_prod (mark env m) (mark env m)) (dest_imp t)"
  by (cases t rule: dest_imp.cases) (auto split: if_splits)

lemma norm_term_skip_sim:
  "okT (norm_term_skip env n (mark env m t)) s' \<Longrightarrow> \<forall>A\<in>set (skipped n t). nosc env A \<Longrightarrow>
    okT (norm_term_skip env n t) s' \<or> is_var_clashT (norm_term_skip env n t)"
proof (induction env n t arbitrary: s' rule: norm_term_skip.induct)
  case (1 env n t)
  note ok = "1.prems"(1) and sk = "1.prems"(2)
  show ?case
  proof (cases "n = 0")
    case True
    with ok have "ok (norm_term env (mark env m t)) s'" by (subst (asm) norm_term_skip.simps) simp
    from norm_term_sim[OF this srel_mark] True show ?thesis
      by (subst norm_term_skip.simps, subst (2) norm_term_skip.simps) auto
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      obtain a T b where x: "x = (a, T, b)" by (cases x)
      have da: "dest_all (mark env m t) = Some (a, T, mark env m b)" using Some x by (simp add: dest_all_mark)
      from ok False da obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n (mark env m b)) b'" and s': "s' = all_const T' $ Abs a T' b'"
        by (subst (asm) norm_term_skip.simps) auto
      have Tl: "okT (liftMT (norm_type (tyenv env) T)) T'" using T' by simp
      have skb: "\<forall>A\<in>set (skipped n b). nosc env A"
        using sk False Some x by (subst (asm) skipped.simps) simp
      have eq: "norm_term_skip env n t = do {T' \<leftarrow> liftMT (norm_type (tyenv env) T);
          b' \<leftarrow> norm_term_skip env n b; returnW (all_const T' $ Abs a T' b')}"
        using False Some x by (subst norm_term_skip.simps) simp
      from "1.IH"(2)[OF False Some x[symmetric] refl Tl b' skb] show ?thesis
      proof
        assume "okT (norm_term_skip env n b) b'"
        with Tl s' show ?thesis unfolding eq by auto
      next
        assume "is_var_clashT (norm_term_skip env n b)"
        then have "is_var_clashT (norm_term_skip env n t)"
          unfolding eq by (intro is_var_clashT_bind_ok[OF Tl] is_var_clashT_bind)
        then show ?thesis ..
      qed
    next
      case None
      then have da: "dest_all (mark env m t) = None" by (simp add: dest_all_mark)
      show ?thesis
      proof (cases "dest_imp t")
        case N: None
        then have "dest_imp (mark env m t) = None" by (simp add: dest_imp_mark)
        with ok False da show ?thesis by (subst (asm) norm_term_skip.simps) simp
      next
        case (Some y)
        obtain A B where y: "y = (A, B)" by (cases y)
        have sk': "nosc env A" "\<forall>A\<in>set (skipped (n - 1) B). nosc env A"
          using sk False None Some y by (subst (asm) skipped.simps, simp)+
        have di: "dest_imp (mark env m t) = Some (A, mark env m B)"
          using Some y sk'(1) by (simp add: dest_imp_mark mark_nosc)
        from ok False da di obtain B' where B': "okT (norm_term_skip env (n - 1) (mark env m B)) B'"
          and s': "s' = mk_implies A B'"
          by (subst (asm) norm_term_skip.simps) auto
        have eq: "norm_term_skip env n t = do {B' \<leftarrow> norm_term_skip env (n - 1) B; returnW (mk_implies A B')}"
          using False None Some y by (subst norm_term_skip.simps) simp
        from "1.IH"(1)[OF False None Some y[symmetric] B' sk'(2)] show ?thesis
        proof
          assume "okT (norm_term_skip env (n - 1) B) B'"
          with s' show ?thesis unfolding eq by auto
        next
          assume "is_var_clashT (norm_term_skip env (n - 1) B)"
          then show ?thesis unfolding eq by simp
        qed
      qed
    qed
  qed
qed

lemma mapW_norm_term_skip_sim:
  "okT (mapW (norm_term_skip env n) (map (mark env m) ts)) rs \<Longrightarrow>
    \<forall>t\<in>set ts. \<forall>A\<in>set (skipped n t). nosc env A \<Longrightarrow>
    okT (mapW (norm_term_skip env n) ts) rs \<or> is_var_clashT (mapW (norm_term_skip env n) ts)"
proof (induction ts arbitrary: rs)
  case (Cons t ts)
  from Cons.prems(1) obtain r rs' where r: "okT (norm_term_skip env n (mark env m t)) r"
    "okT (mapW (norm_term_skip env n) (map (mark env m) ts)) rs'" "rs = r # rs'"
    by auto
  have sim: "okT (norm_term_skip env n t) r \<or> is_var_clashT (norm_term_skip env n t)"
    by (rule norm_term_skip_sim[OF r(1)]) (use Cons.prems(2) in simp)
  have ih: "okT (mapW (norm_term_skip env n) ts) rs' \<or> is_var_clashT (mapW (norm_term_skip env n) ts)"
    by (rule Cons.IH[OF r(2)]) (use Cons.prems(2) in simp)
  from sim show ?case
  proof
    assume "is_var_clashT (norm_term_skip env n t)"
    then show ?thesis by simp
  next
    assume a: "okT (norm_term_skip env n t) r"
    from ih show ?thesis
    proof
      assume "okT (mapW (norm_term_skip env n) ts) rs'"
      with a r(3) show ?thesis by auto
    next
      assume "is_var_clashT (mapW (norm_term_skip env n) ts)"
      then have "is_var_clashT (mapW (norm_term_skip env n) (t # ts))"
        by (auto intro!: is_var_clashT_bind_ok[OF a])
      then show ?thesis ..
    qed
  qed
qed simp

lemma norm_term_skip_fnames:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> fnames t' \<subseteq> fnames t \<union> env_fnames env"
proof (induction env n t arbitrary: t' rule: norm_term_skip.induct)
  case (1 env n t)
  note ok = "1.prems"
  show ?case
  proof (cases "n = 0")
    case True
    with ok have "ok (norm_term env t) t'" by (subst (asm) norm_term_skip.simps) simp
    then show ?thesis by (rule norm_term_fnames)
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      obtain a T b where x: "x = (a, T, b)" by (cases x)
      from ok False Some x obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (subst (asm) norm_term_skip.simps) auto
      have Tl: "okT (liftMT (norm_type (tyenv env) T)) T'" using T' by simp
      from "1.IH"(2)[OF False Some x[symmetric] refl Tl b'] t' Some x show ?thesis
        by (auto simp: dest_all_Some all_const_def)
    next
      case None
      show ?thesis
      proof (cases "dest_imp t")
        case N: None
        with ok False None show ?thesis by (subst (asm) norm_term_skip.simps) simp
      next
        case (Some y)
        obtain A B where y: "y = (A, B)" by (cases y)
        from ok False None Some y obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
          and t': "t' = mk_implies A B'"
          by (subst (asm) norm_term_skip.simps) auto
        from "1.IH"(1)[OF False None Some y[symmetric] B'] t' Some y show ?thesis
          by (auto simp: dest_imp_Some mk_implies_def implies_def)
      qed
    qed
  qed
qed

lemma mapW_norm_term_skip_fnames:
  "okT (mapW (norm_term_skip env n) ts) ts' \<Longrightarrow> fnames_list ts' \<subseteq> fnames_list ts \<union> env_fnames env"
proof (induction ts arbitrary: ts')
  case (Cons t ts)
  from Cons.prems obtain t' ns where n: "okT (norm_term_skip env n t) t'"
    "okT (mapW (norm_term_skip env n) ts) ns" "ts' = t' # ns"
    by auto
  from norm_term_skip_fnames[OF n(1)] Cons.IH[OF n(2)] n(3) show ?case by auto
qed simp

text \<open>The flex-flex pairs, premises and conclusion that \<^const>\<open>addth\<close> computes:\<close>

definition addth_parts :: "bctx \<Rightarrow> newas \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow>
    ((pterm \<times> pterm) list \<times> pterm list \<times> pterm) T" where
  "addth_parts ctx na env tpairs =
    (if env_is_empty env then returnW (tpairs, bc_Bs ctx @ na_As na, bc_C ctx)
     else do {
       ntps \<leftarrow> liftMT (mapM (norm_tpair env) tpairs);
       if above env (bc_smax ctx) then
         if bc_lifted ctx then do {
           As' \<leftarrow> mapW (norm_term_skip env (bc_nlift ctx)) (na_As na);
           returnW (ntps, bc_Bs ctx @ As', bc_C ctx)}
         else do {
           As' \<leftarrow> liftMT (mapM (norm_term env) (na_As na));
           returnW (ntps, bc_Bs ctx @ As', bc_C ctx)}
       else if bc_match ctx then raiseW COMPOSE
       else do {
         Hs \<leftarrow> liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na));
         C' \<leftarrow> liftMT (norm_term env (bc_C ctx));
         returnW (ntps, Hs, C')}})"

lemma addth_parts:
  "addth ctx A na (env, tps) =
    do {(ntpairs, Hs, C') \<leftarrow> addth_parts ctx na env tps;
      returnW (BRes env ntpairs (list_implies Hs C') A na)}"
  by (simp add: addth_def addth_parts_def)

lemma addth_parts_sim:
  assumes r: "okT (addth_parts ctx' na' env (mark_tps env m tps)) p"
    and marks: "bc_Bs ctx' = map (mark env m) (bc_Bs ctx)" "bc_C ctx' = mark env m (bc_C ctx)"
      "na_As na' = map (mark env m) (na_As na)"
    and same: "bc_match ctx' = bc_match ctx" "bc_lifted ctx' = bc_lifted ctx" "bc_smax ctx' = bc_smax ctx"
      "bc_nlift ctx' = bc_nlift ctx"
    and copied: "above env (bc_smax ctx) \<Longrightarrow> (\<forall>t\<in>set (bc_Bs ctx). nosc env t) \<and> nosc env (bc_C ctx) \<and>
      (bc_lifted ctx \<longrightarrow> (\<forall>t\<in>set (na_As na). \<forall>A\<in>set (skipped (bc_nlift ctx) t). nosc env A))"
  shows "okT (addth_parts ctx na env tps) p \<or> is_var_clashT (addth_parts ctx na env tps)"
proof (cases "env_is_empty env")
  case True
  have "bc_Bs ctx' = bc_Bs ctx" "bc_C ctx' = bc_C ctx" "na_As na' = na_As na" "mark_tps env m tps = tps"
    using True marks by (simp_all add: map_mark_nosc mark_nosc nosc_empty mark_tps_empty)
  with r True show ?thesis by (simp add: addth_parts_def)
next
  case False
  from r False obtain ntps where n: "ok (mapM (norm_tpair env) (mark_tps env m tps)) ntps"
    by (auto simp: addth_parts_def)
  note tp = mapM_norm_tpair_sim[OF srelp_mark n]
  have L: "okT (liftMT (mapM (norm_tpair env) tps)) ntps" if "ok (mapM (norm_tpair env) tps) ntps"
    using that by simp
  show ?thesis
  proof (cases "above env (bc_smax ctx)")
    case ab: True
    from copied[OF ab] marks have Bs: "bc_Bs ctx' = bc_Bs ctx" and C: "bc_C ctx' = bc_C ctx"
      by (simp_all add: map_mark_nosc mark_nosc)
    show ?thesis
    proof (cases "bc_lifted ctx")
      case lf: True
      from r False ab lf same n obtain As' where
        a: "okT (mapW (norm_term_skip env (bc_nlift ctx)) (map (mark env m) (na_As na))) As'"
        and p: "p = (ntps, bc_Bs ctx @ As', bc_C ctx)"
        by (auto simp: addth_parts_def marks(3) Bs C)
      have eq: "addth_parts ctx na env tps = do {ntps \<leftarrow> liftMT (mapM (norm_tpair env) tps);
          As' \<leftarrow> mapW (norm_term_skip env (bc_nlift ctx)) (na_As na);
          returnW (ntps, bc_Bs ctx @ As', bc_C ctx)}"
        using False ab lf by (simp add: addth_parts_def)
      have sk: "\<forall>t\<in>set (na_As na). \<forall>A\<in>set (skipped (bc_nlift ctx) t). nosc env A"
        using copied[OF ab] lf by simp
      from tp show ?thesis
      proof
        assume "is_var_clash (mapM (norm_tpair env) tps)"
        then show ?thesis unfolding eq by simp
      next
        assume t: "ok (mapM (norm_tpair env) tps) ntps"
        from mapW_norm_term_skip_sim[OF a sk] show ?thesis
        proof
          assume "okT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'"
          with t p show ?thesis unfolding eq by auto
        next
          assume "is_var_clashT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na))"
          then have "is_var_clashT (addth_parts ctx na env tps)"
            unfolding eq by (intro is_var_clashT_bind_ok[OF L[OF t]] is_var_clashT_bind)
          then show ?thesis ..
        qed
      qed
    next
      case nl: False
      from r False ab nl same n obtain As' where
        a: "ok (mapM (norm_term env) (map (mark env m) (na_As na))) As'"
        and p: "p = (ntps, bc_Bs ctx @ As', bc_C ctx)"
        by (auto simp: addth_parts_def marks(3) Bs C)
      have eq: "addth_parts ctx na env tps = do {ntps \<leftarrow> liftMT (mapM (norm_tpair env) tps);
          As' \<leftarrow> liftMT (mapM (norm_term env) (na_As na));
          returnW (ntps, bc_Bs ctx @ As', bc_C ctx)}"
        using False ab nl by (simp add: addth_parts_def)
      from tp show ?thesis
      proof
        assume "is_var_clash (mapM (norm_tpair env) tps)"
        then show ?thesis unfolding eq by simp
      next
        assume t: "ok (mapM (norm_tpair env) tps) ntps"
        from mapM_norm_term_sim[OF srels_mark a] show ?thesis
        proof
          assume "ok (mapM (norm_term env) (na_As na)) As'"
          with t p show ?thesis unfolding eq by auto
        next
          assume "is_var_clash (mapM (norm_term env) (na_As na))"
          then have "is_var_clashT (addth_parts ctx na env tps)"
            unfolding eq by (intro is_var_clashT_bind_ok[OF L[OF t]] is_var_clashT_bind is_var_clashT_liftMT)
          then show ?thesis ..
        qed
      qed
    qed
  next
    case na: False
    from r False na same n obtain Hs C' where nm: "\<not> bc_match ctx"
      and h: "ok (mapM (norm_term env) (map (mark env m) (bc_Bs ctx @ na_As na))) Hs"
        "ok (norm_term env (mark env m (bc_C ctx))) C'"
      and p: "p = (ntps, Hs, C')"
      by (auto simp: addth_parts_def marks split: if_splits)
    have eq: "addth_parts ctx na env tps = do {ntps \<leftarrow> liftMT (mapM (norm_tpair env) tps);
        Hs \<leftarrow> liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na));
        C' \<leftarrow> liftMT (norm_term env (bc_C ctx));
        returnW (ntps, Hs, C')}"
      using False na nm by (simp add: addth_parts_def)
    from tp show ?thesis
    proof
      assume "is_var_clash (mapM (norm_tpair env) tps)"
      then show ?thesis unfolding eq by simp
    next
      assume t: "ok (mapM (norm_tpair env) tps) ntps"
      from mapM_norm_term_sim[OF srels_mark h(1)] show ?thesis
      proof
        assume "is_var_clash (mapM (norm_term env) (bc_Bs ctx @ na_As na))"
        then have "is_var_clashT (addth_parts ctx na env tps)"
          unfolding eq by (intro is_var_clashT_bind_ok[OF L[OF t]] is_var_clashT_bind is_var_clashT_liftMT)
        then show ?thesis ..
      next
        assume hs: "ok (mapM (norm_term env) (bc_Bs ctx @ na_As na)) Hs"
        have Lh: "okT (liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na))) Hs" using hs by simp
        from norm_term_sim[OF h(2) srel_mark] show ?thesis
        proof
          assume "ok (norm_term env (bc_C ctx)) C'"
          with t hs p show ?thesis unfolding eq by auto
        next
          assume "is_var_clash (norm_term env (bc_C ctx))"
          then have "is_var_clashT (addth_parts ctx na env tps)"
            unfolding eq
            by (intro is_var_clashT_bind_ok[OF L[OF t]] is_var_clashT_bind_ok[OF Lh] is_var_clashT_bind
              is_var_clashT_liftMT)
          then show ?thesis ..
        qed
      qed
    qed
  qed
qed

lemma addth_parts_fnames:
  assumes "okT (addth_parts ctx na env tps) (ntps, Hs, C')"
  shows "fnames_tps ntps \<union> fnames_list Hs \<union> fnames C' \<subseteq>
    fnames_tps tps \<union> fnames_list (bc_Bs ctx) \<union> fnames_list (na_As na) \<union> fnames (bc_C ctx) \<union> env_fnames env"
proof (cases "env_is_empty env")
  case True
  with assms show ?thesis by (auto simp: addth_parts_def)
next
  case False
  from assms False obtain n: "ok (mapM (norm_tpair env) tps) ntps" by (auto simp: addth_parts_def split: if_splits)
  note tp = mapM_norm_tpair_fnames[OF n]
  show ?thesis
  proof (cases "above env (bc_smax ctx)")
    case ab: True
    show ?thesis
    proof (cases "bc_lifted ctx")
      case True
      with assms False ab obtain As' where "okT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'"
        "Hs = bc_Bs ctx @ As'" "C' = bc_C ctx"
        by (auto simp: addth_parts_def)
      with mapW_norm_term_skip_fnames[OF this(1)] tp show ?thesis by auto
    next
      case False
      with assms \<open>\<not> env_is_empty env\<close> ab obtain As' where "ok (mapM (norm_term env) (na_As na)) As'"
        "Hs = bc_Bs ctx @ As'" "C' = bc_C ctx"
        by (auto simp: addth_parts_def)
      with mapM_norm_term_fnames[OF this(1)] tp show ?thesis by auto
    qed
  next
    case na: False
    with assms False have "ok (mapM (norm_term env) (bc_Bs ctx @ na_As na)) Hs" "ok (norm_term env (bc_C ctx)) C'"
      by (auto simp: addth_parts_def split: if_splits)
    from mapM_norm_term_fnames[OF this(1)] norm_term_fnames[OF this(2)] tp show ?thesis by auto
  qed
qed

theorem addth_kept_clash:
  assumes r: "okT (addth ctx' A na' (env, mark_tps env m tps)) r'"
    and marks: "bc_Bs ctx' = map (mark env m) (bc_Bs ctx)" "bc_C ctx' = mark env m (bc_C ctx)"
      "na_As na' = map (mark env m) (na_As na)"
    and same: "bc_match ctx' = bc_match ctx" "bc_lifted ctx' = bc_lifted ctx" "bc_smax ctx' = bc_smax ctx"
      "bc_nlift ctx' = bc_nlift ctx"
    and copied: "above env (bc_smax ctx) \<Longrightarrow> (\<forall>t\<in>set (bc_Bs ctx). nosc env t) \<and> nosc env (bc_C ctx) \<and>
      (bc_lifted ctx \<longrightarrow> (\<forall>t\<in>set (na_As na). \<forall>A\<in>set (skipped (bc_nlift ctx) t). nosc env A))"
    and kept: "m \<in> fnames (br_prop r') \<union> fnames_tps (br_tpairs r')"
    and fresh: "m \<notin> fnames_tps tps \<union> fnames_list (bc_Bs ctx) \<union> fnames_list (na_As na) \<union> fnames (bc_C ctx) \<union> env_fnames env"
  shows "is_var_clashT (addth ctx A na (env, tps))"
proof -
  from r obtain ntps Hs C' where p: "okT (addth_parts ctx' na' env (mark_tps env m tps)) (ntps, Hs, C')"
    and r': "br_prop r' = list_implies Hs C'" "br_tpairs r' = ntps"
    by (auto simp: addth_parts)
  from addth_parts_sim[OF p marks same copied] show ?thesis
  proof
    assume "okT (addth_parts ctx na env tps) (ntps, Hs, C')"
    from addth_parts_fnames[OF this] kept fresh r' show ?thesis by auto
  next
    assume "is_var_clashT (addth_parts ctx na env tps)"
    then show ?thesis by (simp add: addth_parts)
  qed
qed


subsection \<open>The rules\<close>

text \<open>
  The result sequences of the rules build each result with these functions when it is
  pulled. The exception is not handled: pulling the result raises it.
\<close>

theorem apull_var_clash:
  assumes "okT (bo_pull ops us) (Some ((env, tps), us'))" "is_var_clashT (newth ctx n (env, tps))"
  shows "is_var_clashT (apull ops (AQ_Map ctx n us rest k))"
  by (subst apull.simps) (use assms(2) in \<open>auto intro!: is_var_clashT_bind_ok[OF assms(1)]\<close>)

theorem fpull_var_clash:
  assumes "okT (bo_pull ops us) (Some (et, us'))" "okT (sm et) env" "is_var_clash (fnewth th env)"
  shows "is_var_clashT (fpull ops sm th (FQ us))"
  unfolding fpull_def
  using assms(3) by (auto intro!: is_var_clashT_bind_ok[OF assms(1)] is_var_clashT_bind_ok[OF assms(2)])

lemma is_var_clashT_handle:
  assumes "is_var_clashT m" "\<And>e. e \<noteq> COMPOSE \<Longrightarrow> h e = raiseW e"
  shows "is_var_clashT (handleW m h)"
  using assms by (auto simp: is_var_clashT_def handleW_def raiseW_def)

theorem bpull_var_clash:
  assumes "okT (case xq of UQ_Cell c \<Rightarrow> returnW (Some c) | UQ_Seq us \<Rightarrow> bo_pull ops us) (Some (et, us'))"
    and "is_var_clashT (addth ctx A na et)"
  shows "is_var_clashT (bpull ops (BS_Its ctx A na xq yq))"
  by (subst bpull.simps)
    (use assms(2) in \<open>auto intro!: is_var_clashT_bind_ok[OF assms(1)] is_var_clashT_handle split: texn.splits\<close>)

end
