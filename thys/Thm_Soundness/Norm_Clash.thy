section \<open>Normalization when a bound name occurs at a second type\<close>

theory Norm_Clash
  imports Thm_Rules3
begin

text \<open>
  The rules that unify are proved sound for the results whose environment binds no name of a
  schematic variable that occurs with two types (theory \<open>Thm_Derivable\<close>). This theory describes
  what the models of the code do with an environment that does bind such a name, where the
  new theorem is built: \<open>Envir.lookup\<close> of a variable whose name is bound at a type that does not
  agree with its own raises \<open>TYPE\<close>; \<open>Envir.norm_term\<close> looks a variable up when it reaches it, and
  it does not reach an argument that \<open>\<beta>\<close>-reduction discards. So a result of normalization
  exists only if every occurrence that is reached has the type of its binding, and it does not
  depend on the other occurrences of bound names at other types: they may be replaced by any
  closed terms, for instance by variables of other names. The functions that build the new
  theorems of \<open>assumption\<close> and \<open>flexflex_rule\<close> inherit this.

  This is a description of the code, not a soundness result: it does not say that a result
  whose environment binds such a name is valid.
\<close>

subsection \<open>Occurrences at another type\<close>

text \<open>
  A variable clashes with an environment if its name is bound and the type of the binding is
  not that of the variable under the type environment (the test of \<open>Envir.lookup\<close>).
\<close>

definition clash :: "env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> bool" where
  "clash env x U \<longleftrightarrow> (\<exists>T u. vt_lookup (tenv env) x = Some (T, u) \<and> \<not> ok (unified (tyenv env) U T) True)"

lemma clash_unbound: "vt_lookup (tenv env) x = None \<Longrightarrow> \<not> clash env x U"
  by (simp add: clash_def)

lemma clash_empty: "env_is_empty env \<Longrightarrow> \<not> clash env x U"
  by (simp add: clash_def env_is_empty_def vt_is_empty_lookup)

text \<open>The lookup of a clashing variable has no result; it raises the exception of \<open>Envir\<close>:\<close>

theorem lookup_clash: "clash env x U \<Longrightarrow> \<not> ok (lookup env x U) r"
  by (auto simp: clash_def lookup_def var_clash_def split: option.splits if_splits)

theorem lookup_clash_raises:
  assumes "vt_lookup (tenv env) x = Some (T, u)" "ok (unified (tyenv env) U T) False"
  shows "lookup env x U = raise (Type_Error (STR ''Variable has two distinct types'') [] [Var x T, Var x U])"
  using assms by (simp add: lookup_def var_clash_def bindM_def)

lemma lookup1_clash:
  assumes "vt_is_empty (tyenv env)" "clash env x U"
  shows "\<not> ok (lookup1 (tenv env) x U) r"
proof
  assume "ok (lookup1 (tenv env) x U) r"
  from ok_lookup1[OF this] assms show False by (auto simp: clash_def unified_def)
qed

text \<open>
  \<open>clash_rel env t s\<close>: the term \<open>s\<close> is \<open>t\<close> with some occurrences of clashing variables
  replaced by closed terms.
\<close>

inductive clash_rel :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" for env where
  Refl [simp, intro!]: "clash_rel env t t"
| Clash: "clash env x U \<Longrightarrow> closed w \<Longrightarrow> clash_rel env (Var x U) w"
| Abs: "clash_rel env t s \<Longrightarrow> clash_rel env (Abs a T t) (Abs a T s)"
| App: "clash_rel env t s \<Longrightarrow> clash_rel env u v \<Longrightarrow> clash_rel env (t $ u) (s $ v)"

lemma clash_rel_Var: "clash_rel env (Var x U) s \<Longrightarrow> \<not> clash env x U \<Longrightarrow> s = Var x U"
  by (auto elim: clash_rel.cases)

lemma clash_rel_AbsE:
  assumes "clash_rel env (Abs a T t) s"
  obtains s' where "s = Abs a T s'" "clash_rel env t s'"
  using assms by (auto elim: clash_rel.cases)

lemma clash_rel_AppE:
  assumes "clash_rel env (t $ u) s"
  obtains t' u' where "s = t' $ u'" "clash_rel env t t'" "clash_rel env u u'"
  using assms by (auto elim: clash_rel.cases)

lemma clash_rel_atom:
  "clash_rel env (Const c T) s \<Longrightarrow> s = Const c T" "clash_rel env (Free c T) s \<Longrightarrow> s = Free c T"
  "clash_rel env (Bound i) s \<Longrightarrow> s = Bound i"
  by (auto elim: clash_rel.cases)

text \<open>A term without clashing variables is related to itself only:\<close>

lemma clash_rel_noclash:
  assumes "clash_rel env t s" "\<And>x U. (x, U) \<in> vars t \<Longrightarrow> \<not> clash env x U"
  shows "s = t"
  using assms by (induction rule: clash_rel.induct) auto

lemma clash_rel_empty: "env_is_empty env \<Longrightarrow> clash_rel env t s \<Longrightarrow> s = t"
  using clash_rel_noclash[of env t s] by (simp add: clash_empty)

text \<open>The replacement of all clashing variables by variables that a function chooses:\<close>

fun declash :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp \<Rightarrow> indexname \<times> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "declash env f (Var x U) = (if clash env x U then (case f x U of (y, V) \<Rightarrow> Var y V) else Var x U)"
| "declash env f (Abs a T t) = Abs a T (declash env f t)"
| "declash env f (t $ u) = declash env f t $ declash env f u"
| "declash env f t = t"

lemma clash_rel_declash: "clash_rel env t (declash env f t)"
  by (induction t) (auto intro: clash_rel.intros simp: closed_def split: prod.splits)

text \<open>The relation is kept by lifting and by substitution for a bound variable:\<close>

lemma clash_rel_lift: "clash_rel env t s \<Longrightarrow> 0 \<le> k \<Longrightarrow> clash_rel env (lift t k) (lift s k)"
proof (induction arbitrary: k rule: clash_rel.induct)
  case (Clash x U w)
  then show ?case
    using incr_bv_no_loose[OF closed_loose_bvar[of w k]] by (auto intro: clash_rel.Clash)
next
  case (Abs t s a T)
  from Abs.IH[of "k + 1"] Abs.prems show ?case by (auto intro: clash_rel.Abs simp: integer_arith)
qed (auto intro: clash_rel.App)

lemma clash_rel_subst:
  "clash_rel env t s \<Longrightarrow> clash_rel env u v \<Longrightarrow> 0 \<le> k \<Longrightarrow> clash_rel env (t[u/k]) (s[v/k])"
proof (induction arbitrary: u v k rule: clash_rel.induct)
  case (Refl t)
  then show ?case
  proof (induction t arbitrary: u v k)
    case (Abs a T t)
    from Abs.IH[OF clash_rel_lift[OF Abs.prems(1), of 0], of "k + 1"] Abs.prems(2)
    show ?case by (auto intro: clash_rel.Abs simp: integer_arith)
  qed (auto intro: clash_rel.App simp: subst_Bound)
next
  case (Clash x U w)
  then show ?case
    using subst_no_loose[OF closed_loose_bvar[of w k]] by (auto intro: clash_rel.Clash)
next
  case (Abs t s a T)
  from Abs.IH[OF clash_rel_lift[OF Abs.prems(1), of 0], of "k + 1"] Abs.prems(2)
  show ?case by (auto intro: clash_rel.Abs simp: integer_arith)
qed (auto intro: clash_rel.App)

lemma clash_rel_subst_bound:
  "clash_rel env t s \<Longrightarrow> clash_rel env u v \<Longrightarrow> clash_rel env (subst_bound u t) (subst_bound v s)"
  by (simp add: subst_bound_subst clash_rel_subst)


subsection \<open>Normalization\<close>

text \<open>
  If normalization has a result, it has the same result on every term that is related to its
  argument: it has not looked at the clashing variables that were replaced. The proofs follow
  the computation; a clashing variable that is reached ends it (\<open>lookup_clash\<close>), so it is in an
  argument that a \<open>\<beta>\<close>-reduction has discarded.
\<close>

lemma norm_term1_atom:
  "norm_term1 te (Const c T) = return (Const c T)" "norm_term1 te (Free c T) = return (Free c T)"
  "norm_term1 te (Bound i) = return (Bound i)"
  by (subst norm_term1.simps, simp)+

lemma norm_term1_Var:
  "norm_term1 te (Var x T) =
    do {r \<leftarrow> lookup1 te x T; case r of Some u \<Rightarrow> norm_term1 te u | None \<Rightarrow> return (Var x T)}"
  by (subst norm_term1.simps) simp

lemma norm_term1_clash_rel:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> clash_rel env t s \<Longrightarrow>
    ok (norm_term1 te s) t'"
  using assms
proof (induction te t r arbitrary: t' s rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and em = "1.prems"(3) and rel = "1.prems"(4)
  have IH: "ok (norm_term1 te v) u'" if "ok (nt te u) u'" "clash_rel env u v" for u u' v
    using "1.IH"[OF that(1) refl te em that(2)] .
  have redex: "ok (norm_term1 te (Abs b U0 body' $ v)) t'"
    if "ok (nt te (subst_bound u body)) t'" "clash_rel env body body'" "clash_rel env u v" for b U0 body body' u v
    using IH[OF that(1) clash_rel_subst_bound[OF that(2,3)]] by (subst norm_term1.simps) simp
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    have "\<not> clash env x T" using lookup1_clash[OF em, of x T lr] lr te by auto
    with rel Var have s: "s = Var x T" by (simp add: clash_rel_Var)
    show ?thesis
    proof (cases lr)
      case None
      with rest lr s Var show ?thesis by (subst norm_term1.simps) auto
    next
      case (Some u)
      with rest have "ok (nt te u) t'" by simp
      from IH[OF this clash_rel.Refl] lr Some s show ?thesis by (subst norm_term1.simps) auto
    qed
  next
    case (Abs a T body)
    with h obtain body' where b: "ok (nt te body) body'" "t' = Abs a T body'" by auto
    from rel Abs obtain sb where s: "s = Abs a T sb" "clash_rel env body sb" by (auto elim: clash_rel_AbsE)
    from IH[OF b(1) s(2)] b(2) s(1) show ?thesis by (subst norm_term1.simps) auto
  next
    case (App f u)
    from rel App obtain f' u' where s: "s = f' $ u'" and rf: "clash_rel env f f'" and ru: "clash_rel env u u'"
      by (auto elim: clash_rel_AppE)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with rf obtain body' where f': "f' = Abs b U0 body'" "clash_rel env body body'" by (auto elim: clash_rel_AbsE)
      from h App f have "ok (nt te (subst_bound u body)) t'" by simp
      from redex[OF this f'(2) ru] s f'(1) show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      have nf': "ok (norm_term1 te f') nf" by (rule IH[OF hf rf])
      \<comment> \<open>the head is not a clashing variable, so its replacement is not an abstraction either\<close>
      have nA: "\<not> is_Abs f'"
      proof
        assume A: "is_Abs f'"
        from rf False A obtain x U where fx: "f = Var x U" "clash env x U"
          by (cases rule: clash_rel.cases) auto
        have "ok (norm_term1 te (Var x U)) nf" using IH[OF hf clash_rel.Refl] unfolding fx(1) .
        then obtain lr where "ok (lookup1 te x U) lr" unfolding norm_term1_Var ok_bindM by blast
        with lookup1_clash[OF em fx(2), of lr] te show False by simp
      qed
      have unfold: "norm_term1 te (f' $ u') = (case nf of Abs _ _ body \<Rightarrow> norm_term1 te (subst_bound u' body)
          | _ \<Rightarrow> do {nu \<leftarrow> norm_term1 te u'; return (nf $ nu)})"
        using nA nf' by (subst norm_term1.simps) (cases f'; simp add: bindM_def)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        from IH[OF this clash_rel_subst_bound[OF clash_rel.Refl ru]] nf s unfold show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from IH[OF hu ru] t' False s unfold show ?thesis by (cases nf) auto
      qed
    qed
  qed (use h rel in \<open>auto dest!: clash_rel_atom simp: norm_term1_atom\<close>)
qed

lemma norm_term2_atom:
  "norm_term2 env (Const c T) = do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Const c T')}"
  "norm_term2 env (Free c T) = do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Free c T')}"
  "norm_term2 env (Bound i) = return (Bound i)"
  by (subst norm_term2.simps, simp)+

lemma norm_term2_Var:
  "norm_term2 env (Var x T) =
    do {r \<leftarrow> lookup env x T;
      case r of Some u \<Rightarrow> norm_term2 env u
      | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}}"
  by (subst norm_term2.simps) simp

lemma norm_term2_clash_rel:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> clash_rel env t s \<Longrightarrow> ok (norm_term2 env s) t'"
  using assms
proof (induction env t r arbitrary: t' s rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and rel = "1.prems"(2)
  have IH: "ok (norm_term2 env v) u'" if "ok (nt env u) u'" "clash_rel env u v" for u u' v
    using "1.IH"[OF that(1) refl that(2)] .
  have redex: "ok (norm_term2 env (Abs b U0 body' $ v)) t'"
    if "ok (nt env (subst_bound u body)) t'" "clash_rel env body body'" "clash_rel env u v" for b U0 body body' u v
    using IH[OF that(1) clash_rel_subst_bound[OF that(2,3)]] by (subst norm_term2.simps) simp
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    have "\<not> clash env x T" using lookup_clash[of env x T lr] lr by auto
    with rel Var have s: "s = Var x T" by (simp add: clash_rel_Var)
    show ?thesis
    proof (cases lr)
      case None
      with rest lr s show ?thesis unfolding s norm_term2_Var ok_bindM by auto
    next
      case (Some u)
      with rest have "ok (nt env u) t'" by simp
      from IH[OF this clash_rel.Refl] lr Some show ?thesis unfolding s norm_term2_Var ok_bindM by auto
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where b: "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'"
      "t' = Abs a T' body'" by auto
    from rel Abs obtain sb where s: "s = Abs a T sb" "clash_rel env body sb" by (auto elim: clash_rel_AbsE)
    from IH[OF b(2) s(2)] b(1,3) s(1) show ?thesis by (subst norm_term2.simps) auto
  next
    case (App f u)
    from rel App obtain f' u' where s: "s = f' $ u'" and rf: "clash_rel env f f'" and ru: "clash_rel env u u'"
      by (auto elim: clash_rel_AppE)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with rf obtain body' where f': "f' = Abs b U0 body'" "clash_rel env body body'" by (auto elim: clash_rel_AbsE)
      from h App f have "ok (nt env (subst_bound u body)) t'" by simp
      from redex[OF this f'(2) ru] s f'(1) show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      have nf': "ok (norm_term2 env f') nf" by (rule IH[OF hf rf])
      have nA: "\<not> is_Abs f'"
      proof
        assume A: "is_Abs f'"
        from rf False A obtain x U where fx: "f = Var x U" "clash env x U"
          by (cases rule: clash_rel.cases) auto
        have "ok (norm_term2 env (Var x U)) nf" using IH[OF hf clash_rel.Refl] unfolding fx(1) .
        then obtain lr where "ok (lookup env x U) lr" unfolding norm_term2_Var ok_bindM by blast
        with lookup_clash[OF fx(2), of lr] show False by simp
      qed
      have unfold: "norm_term2 env (f' $ u') = (case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u' body)
          | _ \<Rightarrow> do {nu \<leftarrow> norm_term2 env u'; return (nf $ nu)})"
        using nA nf' by (subst norm_term2.simps) (cases f'; simp add: bindM_def)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        from IH[OF this clash_rel_subst_bound[OF clash_rel.Refl ru]] nf s unfold show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from IH[OF hu ru] t' False s unfold show ?thesis by (cases nf) auto
      qed
    qed
  qed (use h rel in \<open>auto dest!: clash_rel_atom simp: norm_term2_atom\<close>)
qed

text \<open>\<open>Envir.norm_term\<close>:\<close>

theorem norm_term_clash_rel:
  assumes "ok (norm_term env t) t'" "clash_rel env t s"
  shows "ok (norm_term env s) t'"
proof (cases "env_is_empty env")
  case True
  with assms clash_rel_empty show ?thesis by blast
next
  case False
  show ?thesis
  proof (cases "vt_is_empty (tyenv env)")
    case True
    with assms(1) False have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_clash_rel[OF this refl refl True assms(2)] False True show ?thesis
      by (simp add: norm_term_def)
  next
    case em: False
    with assms(1) False have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_clash_rel[OF this refl assms(2)] False em show ?thesis by (simp add: norm_term_def)
  qed
qed

text \<open>In particular with all clashing variables renamed:\<close>

corollary norm_term_declash: "ok (norm_term env t) t' \<Longrightarrow> ok (norm_term env (declash env f t)) t'"
  by (rule norm_term_clash_rel[OF _ clash_rel_declash])

text \<open>A clashing variable itself, or one at the head of an application, has no normal form:\<close>

lemma not_Abs_list_comb_Var: "\<not> is_Abs (list_comb (Var x U) ts)"
  by (cases ts rule: rev_cases) (simp_all add: list_comb_def)

lemma norm_term1_App_fail:
  assumes "\<not> is_Abs f" "\<And>r. \<not> ok (norm_term1 te f) r"
  shows "\<not> ok (norm_term1 te (f $ u)) r"
  using assms by (subst norm_term1.simps) (cases f; auto)

lemma norm_term2_App_fail:
  assumes "\<not> is_Abs f" "\<And>r. \<not> ok (norm_term2 env f) r"
  shows "\<not> ok (norm_term2 env (f $ u)) r"
  using assms by (subst norm_term2.simps) (cases f; auto)

corollary norm_term_clash_head: "clash env x U \<Longrightarrow> \<not> ok (norm_term env (list_comb (Var x U) ts)) t'"
proof
  assume c: "clash env x U" and n: "ok (norm_term env (list_comb (Var x U) ts)) t'"
  have ne: "\<not> env_is_empty env" using c clash_empty by blast
  have A: "\<not> ok (norm_term1 (tenv env) (list_comb (Var x U) ts)) r" if "vt_is_empty (tyenv env)" for r
  proof (induction ts arbitrary: r rule: rev_induct)
    case Nil
    then show ?case using lookup1_clash[OF that c] by (auto simp: norm_term1_Var list_comb_def)
  next
    case (snoc u ts)
    have "list_comb (Var x U) (ts @ [u]) = list_comb (Var x U) ts $ u" by (simp add: list_comb_def)
    with norm_term1_App_fail[OF not_Abs_list_comb_Var snoc.IH] show ?case by simp
  qed
  have B: "\<not> ok (norm_term2 env (list_comb (Var x U) ts)) r" for r
  proof (induction ts arbitrary: r rule: rev_induct)
    case Nil
    then show ?case using lookup_clash[OF c] by (auto simp: norm_term2_Var list_comb_def)
  next
    case (snoc u ts)
    have "list_comb (Var x U) (ts @ [u]) = list_comb (Var x U) ts $ u" by (simp add: list_comb_def)
    with norm_term2_App_fail[OF not_Abs_list_comb_Var snoc.IH] show ?case by simp
  qed
  from n ne A B show False by (auto simp: norm_term_def split: if_splits)
qed


subsection \<open>The new theorems of the rules\<close>

text \<open>
  The functions that build the new theorem from a unifier normalize the parts of their
  arguments with \<^const>\<open>norm_term\<close>: \<^const>\<open>newth\<close> (\<open>assumption\<close>), \<^const>\<open>fnewth\<close> (\<open>flexflex_rule\<close>) and
  \<^const>\<open>addth\<close> (\<open>bicompose_aux\<close>, hence composition and resolution). So if they return a theorem,
  they return it, or a theorem related to it, for arguments in which clashing variables are
  replaced.
\<close>

abbreviation clash_rels :: "env \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> bool" where
  "clash_rels env \<equiv> list_all2 (clash_rel env)"

abbreviation clash_relp :: "env \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> bool" where
  "clash_relp env \<equiv> list_all2 (rel_prod (clash_rel env) (clash_rel env))"

lemma clash_rels_empty:
  assumes "env_is_empty env" "clash_rels env ts ss"
  shows "ss = ts"
  using assms(2) by (induction ts ss rule: list_all2_induct) (auto dest: clash_rel_empty[OF assms(1)])

lemma clash_relp_empty:
  assumes "env_is_empty env" "clash_relp env ts ss"
  shows "ss = ts"
  using assms(2) by (induction ts ss rule: list_all2_induct) (auto dest: clash_rel_empty[OF assms(1)])

lemma clash_rel_list_implies:
  assumes "clash_rels env As As'" "clash_rel env B B'"
  shows "clash_rel env (list_implies As B) (list_implies As' B')"
  using assms by (induction As As' rule: list_all2_induct) (auto intro!: clash_rel.App)

lemma mapM_norm_term_clash_rel:
  assumes "clash_rels env ts ss" "ok (mapM (norm_term env) ts) ts'"
  shows "ok (mapM (norm_term env) ss) ts'"
  using assms unfolding ok_mapM
proof (induction ts ss arbitrary: ts' rule: list_all2_induct)
  case (Cons t ts s ss)
  then show ?case by (cases ts') (auto intro: norm_term_clash_rel)
qed simp

lemma mapM_norm_tpair_clash_rel:
  assumes "clash_relp env tps tps'" "ok (mapM (norm_tpair env) tps) ntps"
  shows "ok (mapM (norm_tpair env) tps') ntps"
  using assms unfolding ok_mapM
proof (induction tps tps' arbitrary: ntps rule: list_all2_induct)
  case (Cons t ts s ss)
  then show ?case
    by (cases ntps) (auto simp: norm_tpair_def split: prod.splits intro: norm_term_clash_rel)
qed simp

text \<open>\<open>assumption\<close>: the same result for the other premises, the conclusion and the flex-flex pairs.\<close>

theorem newth_clash_rel:
  assumes r: "okT (newth ctx n (env, tps)) r"
    and Bs: "clash_rels env (ac_Bs ctx) (ac_Bs ctx')" and C: "clash_rel env (ac_C ctx) (ac_C ctx')"
    and tps: "clash_relp env tps tps'"
  shows "okT (newth ctx' n (env, tps')) r"
proof (cases "env_is_empty env")
  case True
  with r clash_rels_empty[OF True Bs] clash_rel_empty[OF True C] clash_relp_empty[OF True tps]
  show ?thesis by (simp add: newth_def)
next
  case False
  with r obtain ntps P where n: "ok (mapM (norm_tpair env) tps) ntps"
    "ok (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx))) P"
    and r': "r = ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P\<rparr>"
    by (auto simp: newth_def)
  from mapM_norm_tpair_clash_rel[OF tps n(1)] norm_term_clash_rel[OF n(2) clash_rel_list_implies[OF Bs C]]
  show ?thesis using False r' by (simp add: newth_def)
qed

text \<open>\<open>flexflex_rule\<close>: the same result for the proposition and the flex-flex pairs.\<close>

theorem fnewth_clash_rel:
  assumes r: "ok (fnewth th env) th'"
    and P: "clash_rel env (th_prop th) P'" and tps: "clash_relp env (th_tpairs th) tps'"
  shows "ok (fnewth (th\<lparr>th_tpairs := tps', th_prop := P'\<rparr>) env) th'"
proof (cases "env_is_empty env")
  case True
  with r clash_rel_empty[OF True P] clash_relp_empty[OF True tps] show ?thesis by simp
next
  case False
  with r obtain ntps Q where n: "ok (mapM (norm_tpair env) (th_tpairs th)) ntps" "ok (norm_term env (th_prop th)) Q"
    and r': "th' = \<lparr>th_maxidx = maxidx_tpairs (filter (\<lambda>(t, u). \<not> aconv_term t u) ntps) (maxidx_of_term Q),
      th_tpairs = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps, th_prop = Q\<rparr>"
    by (auto simp: fnewth_def Let_def)
  from mapM_norm_tpair_clash_rel[OF tps n(1)] norm_term_clash_rel[OF n(2) P]
  show ?thesis using False r' by (simp add: fnewth_def Let_def)
qed

text \<open>
  \<open>bicompose_aux\<close> normalizes a lifted premise of the rule only behind the assumptions that it
  was lifted over (\<^const>\<open>norm_term_skip\<close>), and it does not normalize the proof state if no variable
  of the state can be bound. What is not normalized is copied, so here the results are
  related, not equal: a replaced variable is replaced in the result where it was copied.
\<close>

lemma clash_rel_dest_all:
  assumes "clash_rel env t s" "dest_all t = Some (a, T, b)"
  obtains b' where "dest_all s = Some (a, T, b')" "clash_rel env b b'"
proof -
  from assms(2) obtain c U where t: "t = Const c U $ Abs a T b" "c = STR ''Pure.all''"
    by (cases t rule: dest_all.cases) (auto split: if_splits)
  from assms(1)[unfolded t(1)] obtain b' where "s = Const c U $ Abs a T b'" "clash_rel env b b'"
    by (auto elim!: clash_rel_AppE clash_rel_AbsE dest!: clash_rel_atom)
  with t(2) that show thesis by simp
qed

lemma clash_rel_dest_imp:
  assumes "clash_rel env t s" "dest_imp t = Some (A, B)"
  obtains A' B' where "dest_imp s = Some (A', B')" "dest_all s = None" "clash_rel env A A'" "clash_rel env B B'"
proof -
  from assms(2) obtain U where t: "t = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: dest_imp_Some)
  from assms(1)[unfolded t] obtain A' B' where "s = Const STR ''Pure.imp'' U $ A' $ B'"
    "clash_rel env A A'" "clash_rel env B B'"
    by (auto elim!: clash_rel_AppE dest!: clash_rel_atom)
  with that show thesis by simp
qed

lemma norm_term_skip_clash_rel:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> clash_rel env t s \<Longrightarrow>
    \<exists>s'. okT (norm_term_skip env n s) s' \<and> clash_rel env t' s'"
proof (induction env n t arbitrary: t' s rule: norm_term_skip.induct)
  case (1 env n t)
  note ok = "1.prems"(1) and rel = "1.prems"(2)
  show ?case
  proof (cases "n = 0")
    case True
    with ok have "ok (norm_term env t) t'" by (subst (asm) norm_term_skip.simps) simp
    from norm_term_clash_rel[OF this rel] True show ?thesis
      by (subst norm_term_skip.simps) auto
  next
    case False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      obtain a T b where x: "x = (a, T, b)" by (cases x)
      from ok False Some x obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (subst (asm) norm_term_skip.simps) auto
      from clash_rel_dest_all[OF rel Some[unfolded x]] obtain sb where sb: "dest_all s = Some (a, T, sb)"
        "clash_rel env b sb" by blast
      have Tl: "okT (liftMT (norm_type (tyenv env) T)) T'" using T' by simp
      from "1.IH"(2)[OF False Some x[symmetric] refl Tl b' sb(2)]
      obtain sb' where sb': "okT (norm_term_skip env n sb) sb'" "clash_rel env b' sb'" by auto
      have "okT (norm_term_skip env n s) (all_const T' $ Abs a T' sb')"
        using False sb(1) T' sb'(1) by (subst norm_term_skip.simps) auto
      moreover have "clash_rel env t' (all_const T' $ Abs a T' sb')"
        unfolding t' by (intro clash_rel.App clash_rel.Abs clash_rel.Refl sb'(2))
      ultimately show ?thesis by blast
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
        from clash_rel_dest_imp[OF rel Some[unfolded y]] obtain sA sB where s: "dest_imp s = Some (sA, sB)"
          "dest_all s = None" "clash_rel env A sA" "clash_rel env B sB" by blast
        from "1.IH"(1)[OF False None Some y[symmetric] B' s(4)]
        obtain sB' where sB': "okT (norm_term_skip env (n - 1) sB) sB'" "clash_rel env B' sB'" by auto
        have "okT (norm_term_skip env n s) (mk_implies sA sB')"
          using False s(1,2) sB'(1) by (subst norm_term_skip.simps) auto
        moreover have "clash_rel env t' (mk_implies sA sB')"
          unfolding t' mk_implies_def by (intro clash_rel.App clash_rel.Refl s(3) sB'(2))
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

lemma mapW_norm_term_skip_clash_rel:
  assumes "clash_rels env ts ss" "okT (mapW (norm_term_skip env n) ts) ts'"
  shows "\<exists>ss'. okT (mapW (norm_term_skip env n) ss) ss' \<and> clash_rels env ts' ss'"
  using assms unfolding okT_mapW
proof (induction ts ss arbitrary: ts' rule: list_all2_induct)
  case (Cons t ts s ss)
  from Cons.prems obtain u us where ts': "ts' = u # us" "okT (norm_term_skip env n t) u"
    "list_all2 (\<lambda>x. okT (norm_term_skip env n x)) ts us"
    by (cases ts') auto
  from norm_term_skip_clash_rel[OF ts'(2) Cons.hyps(1)] Cons.IH[OF ts'(3)] ts'(1)
  show ?case by (auto simp: list_all2_Cons1)
qed simp

theorem addth_clash_rel:
  assumes r: "okT (addth ctx A na (env, tps)) r"
    and Bs: "clash_rels env (bc_Bs ctx) (bc_Bs ctx')" and C: "clash_rel env (bc_C ctx) (bc_C ctx')"
    and As: "clash_rels env (na_As na) (na_As na')" and tps: "clash_relp env tps tps'"
    and same: "bc_match ctx' = bc_match ctx" "bc_lifted ctx' = bc_lifted ctx" "bc_smax ctx' = bc_smax ctx"
      "bc_nlift ctx' = bc_nlift ctx"
  shows "\<exists>r'. okT (addth ctx' A na' (env, tps')) r' \<and> br_env r' = br_env r \<and> br_tpairs r' = br_tpairs r \<and>
    clash_rel env (br_prop r) (br_prop r')"
proof (cases "env_is_empty env")
  case True
  with r clash_rels_empty[OF True Bs] clash_rel_empty[OF True C] clash_rels_empty[OF True As]
    clash_relp_empty[OF True tps]
  show ?thesis by (auto simp: addth_def)
next
  case False
  from r False obtain ntps where n: "ok (mapM (norm_tpair env) tps) ntps" by (auto simp: addth_def)
  note n' = mapM_norm_tpair_clash_rel[OF tps n]
  show ?thesis
  proof (cases "above env (bc_smax ctx)")
    case ab: True
    show ?thesis
    proof (cases "bc_lifted ctx")
      case True
      with r False ab n obtain As' where a: "okT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na)) As'"
        and r': "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: addth_def dest: okT_det)
      from mapW_norm_term_skip_clash_rel[OF As a] obtain Ss where s: "okT (mapW (norm_term_skip env (bc_nlift ctx)) (na_As na')) Ss"
        "clash_rels env As' Ss" by blast
      have "okT (addth ctx' A na' (env, tps')) (BRes env ntps (list_implies (bc_Bs ctx' @ Ss) (bc_C ctx')) A na')"
        using False ab True n' s(1) same by (auto simp: addth_def)
      moreover have "clash_rel env (list_implies (bc_Bs ctx @ As') (bc_C ctx)) (list_implies (bc_Bs ctx' @ Ss) (bc_C ctx'))"
        by (intro clash_rel_list_implies list_all2_appendI Bs s(2) C)
      ultimately show ?thesis using r' by auto
    next
      case nl: False
      with r False ab n obtain As' where a: "ok (mapM (norm_term env) (na_As na)) As'"
        and r': "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: addth_def dest: okT_det)
      have "okT (addth ctx' A na' (env, tps')) (BRes env ntps (list_implies (bc_Bs ctx' @ As') (bc_C ctx')) A na')"
        using False ab nl n' mapM_norm_term_clash_rel[OF As a] same by (auto simp: addth_def)
      moreover have "clash_rel env (list_implies (bc_Bs ctx @ As') (bc_C ctx)) (list_implies (bc_Bs ctx' @ As') (bc_C ctx'))"
        by (intro clash_rel_list_implies list_all2_appendI Bs C) (simp add: list_all2_refl)
      ultimately show ?thesis using r' by auto
    qed
  next
    case na: False
    with r False n obtain Hs C' where h: "\<not> bc_match ctx" "ok (mapM (norm_term env) (bc_Bs ctx @ na_As na)) Hs"
      "ok (norm_term env (bc_C ctx)) C'" and r': "r = BRes env ntps (list_implies Hs C') A na"
      by (auto simp: addth_def dest: okT_det split: if_splits)
    have "okT (addth ctx' A na' (env, tps')) (BRes env ntps (list_implies Hs C') A na')"
      using False na h(1) n' mapM_norm_term_clash_rel[OF list_all2_appendI[OF Bs As] h(2)]
        norm_term_clash_rel[OF h(3) C] same
      by (auto simp: addth_def)
    then show ?thesis using r' by auto
  qed
qed


subsection \<open>The results of \<open>assumption\<close> and \<open>flexflex_rule\<close>\<close>

text \<open>
  Every result of \<^const>\<open>assumption\<close> is the new theorem of a unifier for the other premises and the
  conclusion of the proof state; every result of \<^const>\<open>flexflex_rule\<close> is the new theorem of its
  environment. So the statements above hold of the results of the rules.
\<close>

lemma newth_env: "okT (newth ctx n (env, tps)) r \<Longrightarrow> ar_env r = env"
  by (auto simp: newth_def split: if_splits)

lemma apull_newth:
  "apull ops s = Some r0 \<Longrightarrow> snd r0 = Ok (Some (r, s')) \<Longrightarrow>
    aseq_ctx s' = aseq_ctx s \<and> (\<exists>n tps. okT (newth (aseq_ctx s) n (ar_env r, tps)) r)"
proof (induction ops s r0 arbitrary: r s' rule: apull.raw_induct[rotated, consumes 1])
  case (1 P ops s r0)
  have IH: "aseq_ctx s1' = aseq_ctx s1 \<and> (\<exists>n tps. okT (newth (aseq_ctx s1) n (ar_env r1, tps)) r1)"
    if "okT (P ops s1) (Some (r1, s1'))" for s1 r1 s1'
  proof -
    from that obtain evs where "P ops s1 = Some (evs, Ok (Some (r1, s1')))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  note hyps = okT_of[OF "1.hyps" "1.prems"(1)]
  show ?case
  proof (cases s)
    case (AQ_Try ctx asms n)
    show ?thesis
    proof (cases asms)
      case Nil
      with hyps AQ_Try show ?thesis by simp
    next
      case (Cons asm rest)
      show ?thesis
      proof (cases "could_unify asm (ac_concl ctx)")
        case False
        with hyps AQ_Try Cons have "okT (P ops (AQ_Try ctx rest (n + 1))) (Some (r, s'))" by simp
        from IH[OF this] AQ_Try show ?thesis by simp
      next
        case True
        with hyps AQ_Try Cons obtain us where "okT (P ops (AQ_Map ctx n us rest (n + 1))) (Some (r, s'))"
          by auto
        from IH[OF this] AQ_Try show ?thesis by simp
      qed
    qed
  next
    case (AQ_Map ctx n us rest m)
    from hyps AQ_Map obtain rr where rr: "okT (bo_pull ops us) rr"
      and cont: "okT (case rr of None \<Rightarrow> P ops (AQ_Try ctx rest m)
        | Some (et, us') \<Rightarrow> do {th \<leftarrow> newth ctx n et; returnW (Some (th, AQ_Map ctx n us' rest m))})
        (Some (r, s'))"
      by auto
    show ?thesis
    proof (cases rr)
      case None
      with cont have "okT (P ops (AQ_Try ctx rest m)) (Some (r, s'))" by simp
      from IH[OF this] AQ_Map show ?thesis by simp
    next
      case (Some c)
      then obtain env tps us' where c: "rr = Some ((env, tps), us')" by (cases c) auto
      from cont c have th: "okT (newth ctx n (env, tps)) r" and s': "s' = AQ_Map ctx n us' rest m" by auto
      from th newth_env[OF th] s' AQ_Map show ?thesis by auto
    qed
  qed
qed

lemma aresult_newth: "aresult ops s r \<Longrightarrow> \<exists>n tps. okT (newth (aseq_ctx s) n (ar_env r, tps)) r"
proof (induction rule: aresult.induct)
  case (First s r s')
  then obtain r0 where "apull ops s = Some r0" "snd r0 = Ok (Some (r, s'))" by (cases "apull ops s") auto
  from apull_newth[OF this] show ?case by blast
next
  case (Next s r' s' r)
  then obtain r0 where "apull ops s = Some r0" "snd r0 = Ok (Some (r', s'))" by (cases "apull ops s") auto
  from apull_newth[OF this] Next.IH show ?case by simp
qed

text \<open>
  A result of \<open>assumption\<close> on a proof state with the other premises \<open>Bs\<close> and the conclusion \<open>C\<close>
  is, for some flex-flex pairs, the new theorem of its environment for \<open>Bs\<close> and \<open>C\<close>, and also
  for all premises, conclusions and flex-flex pairs in which clashing variables are replaced.
\<close>

theorem assumption_result_clash_rel:
  assumes a: "okT (assumption i state) s0" and res: "aresult ops s0 r"
  obtains tpairs Bs Bi C n tps where "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    "ac_Bs (aseq_ctx s0) = Bs" "ac_C (aseq_ctx s0) = C"
    "\<And>ctx' tps'. clash_rels (ar_env r) Bs (ac_Bs ctx') \<Longrightarrow> clash_rel (ar_env r) C (ac_C ctx') \<Longrightarrow>
      clash_relp (ar_env r) tps tps' \<Longrightarrow> okT (newth ctx' n (ar_env r, tps')) r"
proof -
  from a obtain tpairs Bs Bi C where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and s0: "okT (case assum_problems (-1) Bi of (params, asms, concl) \<Rightarrow>
      returnW (AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1)) s0"
    by (auto simp: assumption_def)
  obtain params asms concl where "assum_problems (-1) Bi = (params, asms, concl)"
    by (cases "assum_problems (-1) Bi")
  with s0 have c: "ac_Bs (aseq_ctx s0) = Bs" "ac_C (aseq_ctx s0) = C" by auto
  from aresult_newth[OF res] obtain n tps where n: "okT (newth (aseq_ctx s0) n (ar_env r, tps)) r" by blast
  show thesis
    by (rule that[OF d c]) (rule newth_clash_rel[OF n], simp_all add: c)
qed

lemma fresult_fnewth: "fresult ops sm th s x \<Longrightarrow> ok (fnewth th (fst x)) (snd x)"
proof (induction rule: fresult.induct)
  case (First s x s')
  then show ?case by (cases s) (auto simp: fpull_def split: option.splits)
qed

text \<open>
  A result \<open>(env, th')\<close> of \<open>flexflex_rule\<close> on a theorem is the new theorem of \<open>env\<close> for its
  proposition and flex-flex pairs, also with clashing variables replaced.
\<close>

theorem flexflex_result_clash_rel:
  assumes "fresult ops sm th s (env, th')"
    and "clash_rel env (th_prop th) P'" "clash_relp env (th_tpairs th) tps'"
  shows "ok (fnewth (th\<lparr>th_tpairs := tps', th_prop := P'\<rparr>) env) th'"
  using fnewth_clash_rel[OF _ assms(2,3)] fresult_fnewth[OF assms(1)] by simp

end
