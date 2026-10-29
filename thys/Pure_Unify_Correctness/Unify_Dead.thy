section \<open>Variables That Simplification Does Not Assign\<close>

theory Unify_Dead
  imports Unify_Fin
begin

text \<open>
  The copies of \<open>matchcopy\<close> introduce new variables \<open>?G\<close>, applied to the arguments \<open>targs\<close> of
  the flexible side of the pair. We show that the simplifications of the projections never
  assign them in a way that changes the terms still to be copied:
  \<^item> if one of the arguments is not a bound variable, every occurrence of a new variable is
    applied to a term that is not a bound variable (it is \<^emph>\<open>dead\<close>): it never becomes an
    \<open>\<eta>\<close>-variable, and is never assigned;
  \<^item> otherwise, the new variables occur only at the heads of sides of pairs, applied to terms
    without new variables: an assignment never puts them into the value of a variable.

  Both are invariants of \<^const>\<open>SIMPL\<close>, for the sets \<open>Fd\<close> and \<open>Ft\<close> of the new variables of the
  first and of the second kind.
\<close>


subsection \<open>Dead occurrences\<close>

text \<open>
  \<open>dd F b t\<close>: every occurrence of a variable of \<open>F\<close> in \<open>t\<close> is applied to an argument that is not
  a bound variable, where \<open>b\<close> tells whether the arguments that \<open>t\<close> itself is applied to
  contain one.
\<close>

fun dd :: "indexname set \<Rightarrow> bool \<Rightarrow> pterm \<Rightarrow> bool" where
  "dd F b (f $ a) \<longleftrightarrow> dd F (b \<or> \<not> is_Bound a) f \<and> dd F False a"
| "dd F b (Var y T) \<longleftrightarrow> (y \<in> F \<longrightarrow> b)"
| "dd F b (Abs n T t) \<longleftrightarrow> dd F False t"
| "dd F b _ \<longleftrightarrow> True"

abbreviation dead :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "dead F t \<equiv> dd F False t"

lemma dd_mono: "dd F b t \<Longrightarrow> b \<le> b' \<Longrightarrow> dd F b' t"
  by (induction F b t arbitrary: b' rule: dd.induct) (auto simp: le_bool_def)

lemma dd_True: "dead F t \<Longrightarrow> dd F b t"
  using dd_mono[of F False t b] by simp

lemma dd_list_comb:
  "dd F b (list_comb h ts) \<longleftrightarrow> dd F (b \<or> (\<exists>t\<in>set ts. \<not> is_Bound t)) h \<and> (\<forall>t\<in>set ts. dead F t)"
  by (induction ts arbitrary: h b) (auto simp: list_comb_def intro: dd_mono)

lemma is_Bound_incr_bv[simp]: "is_Bound (incr_bv i k t) \<longleftrightarrow> is_Bound t"
  by (cases "(i, k, t)" rule: incr_bv.cases) auto

lemma dd_incr_bv[simp]: "dd F b (incr_bv i k t) \<longleftrightarrow> dd F b t"
  by (induction i k t arbitrary: b rule: incr_bv.induct) auto

lemma dd_incr_boundvars[simp]: "dd F b (incr_boundvars i t) \<longleftrightarrow> dd F b t"
  by (simp add: incr_boundvars_def)

lemma is_Bound_subst_bound_aux: "\<not> is_Bound t \<Longrightarrow> \<not> is_Bound (subst_bound_aux u k t)"
  by (cases "(u, k, t)" rule: subst_bound_aux.cases) auto

lemma dd_subst_bound_aux: "dead F u \<Longrightarrow> dd F b t \<Longrightarrow> dd F b (subst_bound_aux u k t)"
proof (induction u k t arbitrary: b rule: subst_bound_aux.induct)
  case (3 u k t1 t2)
  have "dd F (b \<or> \<not> is_Bound t2) (subst_bound_aux u k t1)" using 3 by simp
  then have "dd F (b \<or> \<not> is_Bound (subst_bound_aux u k t2)) (subst_bound_aux u k t1)"
    by (rule dd_mono) (auto simp: le_bool_def dest: is_Bound_subst_bound_aux)
  with 3 show ?case by simp
qed (auto intro: dd_True)

lemma dd_subst_bound: "dead F u \<Longrightarrow> dd F b t \<Longrightarrow> dd F b (subst_bound u t)"
  by (simp add: subst_bound_def dd_subst_bound_aux)


subsection \<open>Variables at the head only\<close>

text \<open>\<open>hok F t\<close>: the variables of \<open>F\<close> occur in \<open>t\<close> at most as its head, applied to terms without them.\<close>

fun hok :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "hok F (f $ a) \<longleftrightarrow> hok F f \<and> vars a \<inter> F = {}"
| "hok F (Var y T) \<longleftrightarrow> True"
| "hok F t \<longleftrightarrow> vars t \<inter> F = {}"

fun gs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "gs F (Abs n T t) \<longleftrightarrow> gs F t"
| "gs F t \<longleftrightarrow> hok F t"

lemma hok_free: "vars t \<inter> F = {} \<Longrightarrow> hok F t"
  by (induction F t rule: hok.induct) auto

lemma gs_free: "vars t \<inter> F = {} \<Longrightarrow> gs F t"
  by (induction F t rule: gs.induct) (auto intro: hok_free)

lemma hok_list_comb: "hok F (list_comb h ts) \<longleftrightarrow> hok F h \<and> (\<forall>t\<in>set ts. vars t \<inter> F = {})"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

text \<open>A term with a rigid head and the variables at the head only has none of them.\<close>

lemma hok_nonVar: "hok F t \<Longrightarrow> \<not> is_Var (head_of t) \<Longrightarrow> vars t \<inter> F = {}"
  by (induction F t rule: hok.induct) auto

lemma hok_incr_bv: "hok F (incr_bv i k t) \<longleftrightarrow> hok F t"
  by (induction i k t rule: incr_bv.induct) (auto simp: vars_incr_bv)

lemma gs_incr_bv: "gs F (incr_bv i k t) \<longleftrightarrow> gs F t"
  by (induction i k t rule: incr_bv.induct) (auto simp: vars_incr_bv hok_incr_bv)


subsection \<open>Environments\<close>

text \<open>
  The values of the environment have only dead occurrences of \<open>Fd\<close> and none of \<open>Ft\<close>, and the
  variables of \<open>Fd\<close> are unbound.
\<close>

definition vgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> env \<Rightarrow> bool" where
  "vgood Fd Ft env \<longleftrightarrow>
    (\<forall>x U w. vt_lookup (tenv env) x = Some (U, w) \<longrightarrow> x \<notin> Fd \<and> dead Fd w \<and> vars w \<inter> Ft = {})"

lemma vgoodD:
  "vgood Fd Ft env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, w) \<Longrightarrow> x \<notin> Fd \<and> dead Fd w \<and> vars w \<inter> Ft = {}"
  unfolding vgood_def by blast

lemma ok_lookup_Some: "ok (lookup env xi T) (Some u) \<Longrightarrow> \<exists>U. vt_lookup (tenv env) xi = Some (U, u)"
  by (auto simp: lookup_def bind_def return_def var_clash_def raise_def split: option.splits if_splits
      sum.splits)

subsection \<open>Head normalization\<close>

lemma head_norm_good_aux:
  assumes "head_norm e t = Some r"
  shows "e = env \<Longrightarrow> r = Ok t' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow>
    (dd Fd b t \<longrightarrow> dd Fd b t') \<and> (vars t \<inter> Ft = {} \<longrightarrow> vars t' \<inter> Ft = {}) \<and> (hok Ft t \<longrightarrow> hok Ft t')"
  using assms
proof (induction e t r arbitrary: t' b rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn e t r)
  have t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using "1.hyps" "1.prems"(2) unfolding "1.prems"(1) by simp
  note vg = "1.prems"(3)
  have IH: "(dd Fd b' s \<longrightarrow> dd Fd b' s') \<and> (vars s \<inter> Ft = {} \<longrightarrow> vars s' \<inter> Ft = {}) \<and>
      (hok Ft s \<longrightarrow> hok Ft s')" if "hn env s = Some (Ok s')" for s s' b'
    using "1.IH"[OF that refl refl vg] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis by simp
    next
      case (Some w)
      from ok_lookup_Some[OF lk[unfolded Some]] obtain U where "vt_lookup (tenv env) xi = Some (U, w)" ..
      from vgoodD[OF vg this] have w: "dead Fd w" "vars w \<inter> Ft = {}" by simp_all
      from Some rest have "hn env w = Some (Ok t')" by simp
      from IH[OF this, of b] w show ?thesis by (auto intro: dd_True hok_free)
    qed
  next
    case (Abs a T body)
    with t' obtain b' where h: "hn env body = Some (Ok b')" and e: "t' = pterm.Abs a T b'" by auto
    from IH[OF h, of False] e Abs show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
      have v: "vars (subst_bound u body) \<subseteq> vars u \<union> vars body" by (rule vars_subst_bound)
      note ih = IH[OF h, of b]
      have "dd Fd b t'" if "dd Fd b t" using that ih App f by (auto intro: dd_subst_bound dd_True)
      moreover have "vars t' \<inter> Ft = {}" if "hok Ft t \<or> vars t \<inter> Ft = {}"
        using that ih v App f by auto
      ultimately show ?thesis by (auto intro: hok_free)
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      note IHf = IH[OF nf, of "b \<or> \<not> is_Bound u"]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have h: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have v: "vars (subst_bound u body) \<subseteq> vars u \<union> vars body" by (rule vars_subst_bound)
        note ih = IH[OF h, of b]
        have "dd Fd b t'" if "dd Fd b t" using that ih IHf App nfa by (auto intro: dd_subst_bound dd_True)
        moreover have "vars t' \<inter> Ft = {}" if "hok Ft t \<or> vars t \<inter> Ft = {}"
          using that ih IHf v App nfa by (auto intro: hok_free)
        ultimately show ?thesis by (auto intro: hok_free)
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) auto
        with IHf App show ?thesis by auto
      qed
    qed
  qed (use t' in auto)
qed

lemma head_norm_good:
  assumes "ok (head_norm env t) t'" "vgood Fd Ft env"
  shows "dd Fd b t \<Longrightarrow> dd Fd b t'" "vars t \<inter> Ft = {} \<Longrightarrow> vars t' \<inter> Ft = {}" "hok Ft t \<Longrightarrow> hok Ft t'"
  using head_norm_good_aux[of env t _ env t' Fd Ft b] assms by auto

subsection \<open>Rigid sides\<close>

text \<open>\<open>rrs F t\<close>: \<open>t\<close> is a rigid atom applied to arguments that have \<open>F\<close> at their heads only.\<close>

fun rrs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "rrs F (f $ a) \<longleftrightarrow> rrs F f \<and> gs F a"
| "rrs F (Const c T) \<longleftrightarrow> True"
| "rrs F (Free c T) \<longleftrightarrow> True"
| "rrs F (Bound i) \<longleftrightarrow> True"
| "rrs F _ \<longleftrightarrow> False"

lemma rrs_incr_bv: "rrs F (incr_bv i k t) \<longleftrightarrow> rrs F t"
  by (induction F t arbitrary: k rule: rrs.induct) (auto simp: gs_incr_bv)

lemma rrs_nonAbs: "rrs F t \<Longrightarrow> \<not> is_Abs t"
  by (cases t) auto

lemma rrs_head_norm: "rrs F t \<Longrightarrow> head_norm env t = return t"
proof (induction F t rule: rrs.induct)
  case (1 F f a)
  then have hf: "head_norm env f = return f" by simp
  have "\<not> is_Abs f" using "1.prems" by (cases f) auto
  with hf show ?case by (subst head_norm.simps) (cases f; simp add: return_def)
qed (simp_all add: head_norm.simps return_def)

lemma gs_nonAbs: "\<not> is_Abs t \<Longrightarrow> gs F t \<longleftrightarrow> hok F t"
  by (cases t) auto

lemma hok_gs: "hok F t \<Longrightarrow> gs F t"
  by (cases t) (auto intro: gs_free)

lemma dead_strip_abs_body: "dead F t \<Longrightarrow> dead F (strip_abs_body t)"
  by (induction t) auto

lemma gs_strip_abs_body: "gs F (strip_abs_body t) \<longleftrightarrow> gs F t"
  by (induction t) auto

lemma is_Abs_strip_abs_body: "\<not> is_Abs (strip_abs_body t)"
  by (induction t) auto


subsection \<open>\<open>\<eta>\<close>-expansion\<close>

lemma etif_good_aux:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t \<Longrightarrow>
    (dead Fd t \<longrightarrow> dead Fd t') \<and> (gs Ft t \<longrightarrow> gs Ft t') \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t'))"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  have nA: "\<not> is_Abs t"
    and body: "ok (case T of
      Type a Ts \<Rightarrow>
        (case Ts of
          [T1, U] \<Rightarrow>
            if a = STR ''fun'' then do {
              u \<leftarrow> et tye U (incr_boundvars 1 t $ Bound 0);
              return (Abs STR '''' T1 u)}
            else return t
        | _ \<Rightarrow> return t)
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup tye v S;
        case r of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t}
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  have same: "(dead Fd t \<longrightarrow> dead Fd t) \<and> (gs Ft t \<longrightarrow> gs Ft t) \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t))"
    using nA by (cases t) auto
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with body obtain u where u: "et tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl] have
      "dead Fd (incr_boundvars 1 t $ Bound 0) \<longrightarrow> dead Fd u"
      "gs Ft (incr_boundvars 1 t $ Bound 0) \<longrightarrow> gs Ft u"
      "rrs Ft (incr_boundvars 1 t $ Bound 0) \<longrightarrow> rrs Ft (strip_abs_body u)"
      by simp_all
    moreover have "gs Ft (incr_boundvars 1 t $ Bound 0) \<longleftrightarrow> gs Ft t"
      using nA by (simp add: gs_nonAbs incr_boundvars_def hok_incr_bv)
    ultimately show ?thesis using t' by (simp add: incr_boundvars_def rrs_incr_bv)
  next
    case False
    show ?thesis
    proof (cases T)
      case (Type a Ts)
      with False body have "t' = t" by (auto split: list.splits if_splits)
      with same show ?thesis by simp
    next
      case (TVar v S)
      with body obtain r' where r': "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with r' same show ?thesis by simp
      next
        case (Some T')
        with r' have "et tye T' t = Some (Ok t')" by simp
        from "1.IH"[OF this refl nA] show ?thesis .
      qed
    qed (use body same in auto)
  qed
qed

lemma eta_norm_good:
  "ok (eta_norm env rb t) t' \<Longrightarrow>
    (dead Fd t \<longrightarrow> dead Fd t') \<and> (gs Ft t \<longrightarrow> gs Ft t') \<and> (rrs Ft t \<longrightarrow> rrs Ft (strip_abs_body t'))"
proof (induction env rb t arbitrary: t' rule: eta_norm.induct)
  case (1 env rb a A body)
  then show ?case by (auto dest: rrs_nonAbs)
qed (auto dest!: etif_good_aux[OF _ refl] simp: fastype_def)


subsection \<open>Pairs\<close>

text \<open>
  A pair is good if its sides have only dead occurrences of \<open>Fd\<close>, and both have \<open>Ft\<close> at
  their heads only, or both are rigid with such arguments.
\<close>

definition pgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> dpair \<Rightarrow> bool" where
  "pgood Fd Ft dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    dead Fd t \<and> dead Fd u \<and> (gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u))"

lemma new_dpair_strip:
  "okW (new_dpair alg rb t u env) ((rb', t', u'), env') \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and> tenv env' = tenv env"
proof (induction alg rb t u env rule: new_dpair.induct)
  case (1 alg rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg T U env) env1"
    and rec: "okW (new_dpair alg ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  from "1.IH"[OF cu c_def rec] cunify_types_tenv[OF cu] show ?case by simp
qed auto

lemma head_norm_Abs_ok:
  "ok (head_norm env (Abs a T b)) t' \<Longrightarrow> \<exists>b'. t' = Abs a T b' \<and> ok (head_norm env b) b'"
  by (subst (asm) head_norm.simps) auto

lemma head_norm_gs: "ok (head_norm env t) t' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> gs Ft t \<Longrightarrow> gs Ft t'"
proof (induction t arbitrary: t')
  case (Abs a T b)
  from head_norm_Abs_ok[OF Abs.prems(1)] obtain b' where "t' = Abs a T b'" "ok (head_norm env b) b'" by blast
  with Abs show ?case by simp
qed (auto simp: gs_nonAbs intro: hok_gs dest: head_norm_good(3))

lemma head_norm_dpair_good:
  assumes "okW (head_norm_dpair alg env dp) (dp', env')" "vgood Fd Ft env" "pgood Fd Ft dp"
  shows "pgood Fd Ft dp' \<and> tenv env' = tenv env"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  obtain rb' t' u' where dp': "dp' = (rb', t', u')" by (cases dp')
  from assms(1) obtain t1 t2 u1 u2 where h1: "ok (head_norm env t) t1" and e1: "ok (eta_norm env rb t1) t2"
    and h2: "ok (head_norm env u) u1" and e2: "ok (eta_norm env rb u1) u2"
    and nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp dp')
  note s = new_dpair_strip[OF nd]
  note et = eta_norm_good[OF e1, of Fd Ft] eta_norm_good[OF e2, of Fd Ft]
  have g: "dead Fd t" "dead Fd u" "gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u"
    using assms(3) by (auto simp: pgood_def dp)
  have d: "dead Fd t'" "dead Fd u'"
    using head_norm_good(1)[OF h1 assms(2) g(1)] head_norm_good(1)[OF h2 assms(2) g(2)] et s
    by (auto intro: dead_strip_abs_body)
  from g(3) have "gs Ft t' \<and> gs Ft u' \<or> rrs Ft t' \<and> rrs Ft u'"
  proof
    assume "gs Ft t \<and> gs Ft u"
    with head_norm_gs[OF h1 assms(2)] head_norm_gs[OF h2 assms(2)] et s
    show ?thesis by (simp add: gs_strip_abs_body)
  next
    assume r: "rrs Ft t \<and> rrs Ft u"
    then have "t1 = t" "u1 = u" using h1 h2 by (auto simp: rrs_head_norm return_def)
    with r et s show ?thesis by simp
  qed
  with d s dp' show ?thesis by (simp add: pgood_def)
qed

subsection \<open>Simplification\<close>

definition sgood :: "indexname set \<Rightarrow> indexname set \<Rightarrow> sstate \<Rightarrow> bool" where
  "sgood Fd Ft st \<longleftrightarrow> (case st of (env, ffs, frs) \<Rightarrow>
    vgood Fd Ft env \<and> (\<forall>dp\<in>set (ffs @ frs). pgood Fd Ft dp))"

lemma vgood_tenv: "tenv env' = tenv env \<Longrightarrow> vgood Fd Ft env' \<longleftrightarrow> vgood Fd Ft env"
  by (simp add: vgood_def)

lemma get_eta_var_dead: "okW (get_eta_var rb n t) (v, T) \<Longrightarrow> dead F t \<Longrightarrow> v \<notin> F"
proof (induction rb arbitrary: n t)
  case Nil
  then show ?case by (cases t) auto
next
  case (Cons aT rb)
  from Cons.prems(1) obtain f where t: "t = f $ Bound n"
    and rec: "okW (get_eta_var rb (n + 1) f) (v, T)"
    by (cases "(aT # rb, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  with Cons.IH[OF rec] Cons.prems(2) show ?case by simp
qed

lemma dd_rlist_abs: "dead F t \<Longrightarrow> dead F (rlist_abs rb t)"
proof (induction rb arbitrary: t)
  case (Cons aT rb)
  then show ?case by (cases aT) simp
qed simp

lemma vars_rlist_abs: "vars (rlist_abs rb t) = vars t"
proof (induction rb arbitrary: t)
  case (Cons aT rb)
  then show ?case by (cases aT) simp
qed simp

lemma assignment_good:
  assumes "okW (assignment alg rb t u env) env'" "vgood Fd Ft env" "dead Fd t" "dead Fd u"
    "vars u \<inter> Ft = {}"
  shows "vgood Fd Ft env'"
proof -
  from assms(1) obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types alg T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have "tenv env' = vt_update (v, (T, rlist_abs rb u)) (tenv env)"
    using ok_update(2)[OF upd] cunify_types_tenv[OF cu] by simp
  moreover have "v \<notin> Fd" by (rule get_eta_var_dead[OF gev assms(3)])
  ultimately show ?thesis
    using assms(2,4,5) dd_rlist_abs[OF assms(4), of rb] vars_rlist_abs[of rb u]
    by (auto simp: vgood_def)
qed

text \<open>The arguments of rigid sides, for \<^const>\<open>simrands\<close>:\<close>

fun hargs :: "indexname set \<Rightarrow> pterm \<Rightarrow> bool" where
  "hargs F (f $ a) \<longleftrightarrow> hargs F f \<and> gs F a"
| "hargs F _ \<longleftrightarrow> True"

lemma hargs_free: "vars t \<inter> F = {} \<Longrightarrow> hargs F t"
  by (induction t) (auto intro: gs_free)

lemma rrs_hargs: "rrs F t \<Longrightarrow> hargs F t"
  by (induction F t rule: rrs.induct) auto

lemma simrands_good:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow>
    dd Fd True t \<Longrightarrow> dd Fd True u \<Longrightarrow> hargs Ft t \<Longrightarrow> hargs Ft u \<Longrightarrow> sgood Fd Ft st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  from "1.IH"[OF F r "1.prems"(3)] "1.prems"(4-7) have "sgood Fd Ft st1" by simp
  moreover have "pgood Fd Ft (rb, t, u)" using "1.prems"(4-7) by (simp add: pgood_def)
  ultimately show ?case by (rule F[OF s])
qed auto

lemma SIMPL0_step_good:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
    and sg: "sgood Fd Ft (env, ffs, frs)" and pg: "pgood Fd Ft (rb, t, u)"
    and nA: "\<not> is_Abs t" "\<not> is_Abs u"
  shows "sgood Fd Ft st'"
proof -
  have vg: "vgood Fd Ft env" using sg by (simp add: sgood_def)
  have d: "dead Fd t" "dead Fd u" and g: "gs Ft t \<and> gs Ft u \<or> rrs Ft t \<and> rrs Ft u"
    using pg by (auto simp: pgood_def)
  have rr_V: "\<not> rrs Ft s" if "is_Var (head_of s)" for s
    using that by (induction Ft s rule: rrs.induct) auto
  have free: "vars s \<inter> Ft = {}" if "gs Ft s" "\<not> is_Abs s" "\<not> is_Var (head_of s)" for s
    using hok_nonVar[of Ft s] that by (simp add: gs_nonAbs)
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok obtain T' U' env' where cu: "okW (cunify_types alg T' U' env) env'"
      and st': "st' = (env', (rb, t, u) # ffs, frs)"
      by (auto simp: SIMPL0_step_def)
    with sg pg show ?thesis by (simp add: sgood_def vgood_tenv[OF cunify_types_tenv[OF cu]])
  next
    case VR
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    have fu: "vars u \<inter> Ft = {}" using g rr_V[of t] VR free[of u] nA by auto
    from h consider env' where "okW (assignment alg rb t u env) env'" "st' = (env', ffs, frs)"
      | "st' = (env, ffs, (rb, t, u) # frs)"
      unfolding okW_handleW by (auto dest!: okW_ASSIGN_handler)
    then show ?thesis
    proof cases
      case 1
      from assignment_good[OF 1(1) vg d fu] 1(2) sg show ?thesis by (simp add: sgood_def)
    qed (use sg pg in \<open>simp add: sgood_def\<close>)
  next
    case RV
    with ok have h: "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    have ft: "vars t \<inter> Ft = {}" using g rr_V[of u] RV free[of t] nA by auto
    have pg': "pgood Fd Ft (rb, u, t)" using pg by (auto simp: pgood_def)
    from h consider env' where "okW (assignment alg rb u t env) env'" "st' = (env', ffs, frs)"
      | "st' = (env, ffs, (rb, u, t) # frs)"
      unfolding okW_handleW by (auto dest!: okW_ASSIGN_handler)
    then show ?thesis
    proof cases
      case 1
      from assignment_good[OF 1(1) vg d(2,1) ft] 1(2) sg show ?thesis by (simp add: sgood_def)
    qed (use sg pg' in \<open>simp add: sgood_def\<close>)
  next
    case RR
    have hs: "hargs Ft t" "hargs Ft u"
      using g free[of t] free[of u] RR nA by (auto intro: hargs_free rrs_hargs)
    have ct: "tenv env' = tenv env" if "cunify_types alg T U env = Some (evs, UOk env')" for T U evs env'
      using that by (intro cunify_types_tenv) blast
    from ok RR obtain env1 where e1: "tenv env1 = tenv env"
      and sr: "okW (simrands F rb u t u (env1, ffs, frs)) st'"
      by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_step_def split: if_splits dest: ct)
    have "sgood Fd Ft (env1, ffs, frs)" using sg by (simp add: sgood_def vgood_tenv[OF e1])
    from simrands_good[OF F sr this dd_True[OF d(1)] dd_True[OF d(2)] hs] show ?thesis .
  qed
qed

theorem SIMPL0_good:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp0 \<Longrightarrow> sgood Fd Ft st'"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "sgood Fd Ft st2" if "okW (S alg dp st1) st2" "sgood Fd Ft st1" "pgood Fd Ft dp" for dp st1 st2
  proof -
    from that(1) obtain evs where "S alg dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this _ that(2,3)] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  have "(case st of (env, ffs, frs) \<Rightarrow> do {
      (dp, env) \<leftarrow> head_norm_dpair alg env dp0; SIMPL0_step alg (S alg) dp env ffs frs}) = Some r"
    using "1.hyps" by (simp only: SIMPL0_step_def)
  with "1.prems"(1) st
  have "okW (head_norm_dpair alg env dp0 \<bind>
      (\<lambda>(dp, env). SIMPL0_step alg (S alg) dp env ffs frs)) st'"
    by (cases r) auto
  then obtain dp env1 where hnd: "okW (head_norm_dpair alg env dp0) (dp, env1)"
    and step: "okW (SIMPL0_step alg (S alg) dp env1 ffs frs) st'"
    by (auto split: prod.splits)
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have vg: "vgood Fd Ft env" using "1.prems"(2) st by (simp add: sgood_def)
  note hg = head_norm_dpair_good[OF hnd vg "1.prems"(3)]
  have nA: "\<not> is_Abs t" "\<not> is_Abs u"
  proof -
    obtain rb0 t0 u0 where dp0: "dp0 = (rb0, t0, u0)" by (cases dp0)
    from hnd obtain t2 u2 where "okW (new_dpair alg rb0 t2 u2 env) ((rb, t, u), env1)"
      by (auto simp: head_norm_dpair_def dp0 dp)
    from new_dpair_strip[OF this] show "\<not> is_Abs t" "\<not> is_Abs u"
      by (simp_all add: is_Abs_strip_abs_body)
  qed
  have "sgood Fd Ft (env1, ffs, frs)"
    using "1.prems"(2) st hg by (simp add: sgood_def vgood_tenv[OF hg[THEN conjunct2]])
  from SIMPL0_step_good[OF IH step[unfolded dp] this hg[THEN conjunct1, unfolded dp] nA]
  show ?case .
qed

corollary SIMPL0_good':
  "okW (SIMPL0 alg dp st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using SIMPL0_good by fastforce

lemma foldrW_SIMPL0_good:
  "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> sgood Fd Ft st \<Longrightarrow> \<forall>dp\<in>set dps. pgood Fd Ft dp \<Longrightarrow>
    sgood Fd Ft st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3) have "sgood Fd Ft st1" by simp
  from SIMPL0_good'[OF s this] Cons.prems(3) show ?case by simp
qed simp

theorem SIMPL_good:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> \<forall>dp\<in>set dpairs. pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have "sgood Fd Ft (env, [], [])" using "1.prems"(2) by (simp add: sgood_def)
  from foldrW_SIMPL0_good[OF f this "1.prems"(3)] have g1: "sgood Fd Ft (env1, ffs, frs)" .
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    from "1.IH"[OF this snd_conv] g1 show ?thesis by (auto simp: sgood_def)
  next
    case False
    with r g1 show ?thesis by simp
  qed
qed

corollary SIMPL_good':
  "okW (SIMPL alg env dps) st' \<Longrightarrow> vgood Fd Ft env \<Longrightarrow> \<forall>dp\<in>set dps. pgood Fd Ft dp \<Longrightarrow> sgood Fd Ft st'"
  using SIMPL_good by fastforce

end
