section \<open>Invariants and Measure of \<open>SIMPL\<close>\<close>

theory Unify_Simpl_Inv
  imports Unify_Inv_Base "Pattern_Correctness.Pattern_Termination_Inv" "Pattern_Correctness.Pattern_Most_General" "Pattern_Correctness.Match_Base"
begin

text \<open>
  The invariants, the measure and the auxiliary facts of the termination proof of
  \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> (theory \<open>Unify_Simpl_Termination\<close>):
  problems satisfy the invariants of the termination proof of pattern unification (theory
  \<^theory>\<open>Pattern_Correctness.Pattern_Termination_Inv\<close>), and the results of \<^const>\<open>SIMPL\<close> satisfy
  them again and have the shapes that \<open>MATCH\<close> expects. The measure is lexicographic: the number of unbound type variables
  reachable from a finite set \<open>K\<close>, the number of unbound variables of the problem, and the size of
  the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the instances of the pairs under the most general solution of
  the type environment (the \<open>\<eta>\<close>-expansion of \<open>unify.ML\<close> keeps it, and decomposition reduces it).
\<close>

context pure_sig_gen
begin

subsection \<open>Statements for results that bind no loose name\<close>

text \<open>
  The statements on computations that may bind variables have two readings. Without loose names,
  \<open>lxokE Xe f m P\<close> says that \<open>m\<close> raises an exception in \<open>Xe\<close> or returns a result that
  satisfies \<open>P\<close>: total correctness, as \<^const>\<open>xokW\<close>. With loose names it says that \<open>P\<close>
  holds for every result of \<open>m\<close> whose environment (\<open>f\<close> of the result) binds no loose name.
  The rules below hold for both readings, so that one proof gives termination in \<open>pure_sig\<close> and
  the invariants of the results in \<open>pure_sig_gen\<close>. (Handlers catch exceptions, and a
  computation that has bound a loose name may raise any of them.)
\<close>

definition lxokE :: "(uexn \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> env) \<Rightarrow> 'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "lxokE Xe f m P \<longleftrightarrow> (if loose = {}
    then (\<exists>evs e. m = Some (evs, Err e) \<and> Xe e) \<or> (\<exists>x. okW m x \<and> P x)
    else (\<forall>x. okW m x \<longrightarrow> nfree (f x) \<longrightarrow> P x))"

abbreviation lxok :: "uexn \<Rightarrow> ('a \<Rightarrow> env) \<Rightarrow> 'a W \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "lxok E \<equiv> lxokE (\<lambda>e. e = E)"

lemma lxokE_D: "lxokE Xe f m P \<Longrightarrow> okW m x \<Longrightarrow> nfree (f x) \<Longrightarrow> P x"
  unfolding lxokE_def by (auto split: if_splits)

lemma lxokE_strict: "loose = {} \<Longrightarrow>
    lxokE Xe f m P \<longleftrightarrow> (\<exists>evs e. m = Some (evs, Err e) \<and> Xe e) \<or> (\<exists>x. okW m x \<and> P x)"
  unfolding lxokE_def by simp

lemma lxokE_errI: "m = Some (evs, Err e) \<Longrightarrow> Xe e \<Longrightarrow> lxokE Xe f m P"
  unfolding lxokE_def by auto

lemma lxokE_raiseW [simp]: "Xe e \<Longrightarrow> lxokE Xe f (raiseW e) P"
  by (rule lxokE_errI[of _ "[]"]) (simp_all add: raiseW_def)

lemma lxok_raiseW [simp]: "lxok E f (raiseW E) P"
  by simp

lemma lxokE_returnW [simp]: "lxokE Xe f (returnW x) P \<longleftrightarrow> (nfree (f x) \<longrightarrow> P x)"
  unfolding lxokE_def using nfree_strict by (auto simp: returnW_def)

lemma lxokE_mono: "lxokE Xe f m P \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> lxokE Xe f m Q"
  unfolding lxokE_def by (auto split: if_splits)

lemma lxokE_mono_ok:
  "lxokE Xe f m P \<Longrightarrow> (\<And>x. okW m x \<Longrightarrow> nfree (f x) \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> lxokE Xe f m Q"
  unfolding lxokE_def using nfree_strict by (auto split: if_splits)

text \<open>
  Sequential composition. If the first computation may bind variables, the environments of the
  results of the second one have to extend that of the first:
\<close>

lemma lxokE_bindW:
  assumes m: "lxokE Xe f m P"
    and k: "\<And>x. okW m x \<Longrightarrow> P x \<Longrightarrow> nfree (f x) \<Longrightarrow> lxokE Xe g (k x) Q"
    and anti: "\<And>x y. okW m x \<Longrightarrow> okW (k x) y \<Longrightarrow> nfree (g y) \<Longrightarrow> nfree (f x)"
  shows "lxokE Xe g (bindW m k) Q"
proof (cases "loose = {}")
  case True
  note S = lxokE_strict[OF True]
  from m[unfolded S] consider (err) evs e where "m = Some (evs, Err e)" "Xe e"
    | (ok) x where "okW m x" "P x" by blast
  then show ?thesis
  proof cases
    case err
    then show ?thesis unfolding S by (auto simp: bindW_def)
  next
    case ok
    from k[OF ok nfree_strict[OF True], unfolded S] ok(1) show ?thesis unfolding S
      by (auto simp: bindW_def)
  qed
next
  case False
  have "Q y" if yy: "okW (bindW m k) y" and nf: "nfree (g y)" for y
  proof -
    from yy obtain x where x: "okW m x" and y: "okW (k x) y" by auto
    have nfx: "nfree (f x)" by (rule anti[OF x y nf])
    from lxokE_D[OF k[OF x lxokE_D[OF m x nfx] nfx] y nf] show "Q y" .
  qed
  then show ?thesis unfolding lxokE_def using False by simp
qed

lemma lxokE_notokI: "loose \<noteq> {} \<Longrightarrow> (\<And>x. \<not> okW m x) \<Longrightarrow> lxokE Xe f m P"
  unfolding lxokE_def by simp

subsection \<open>The occurs check\<close>

abbreviation bset :: "env \<Rightarrow> indexname set" where
  "bset env \<equiv> {x. vt_lookup (tenv env) x \<noteq> None}"

lemma card_bset_less:
  "w \<notin> set seen \<Longrightarrow> vt_lookup (tenv env) w \<noteq> None \<Longrightarrow>
    card (bset env - set (w # seen)) < card (bset env - set seen)"
  by (rule psubset_card_mono) (use finite_vt_lookup[of "tenv env"] in auto)

lemma card_bset_mono: "set seen \<subseteq> set s \<Longrightarrow> card (bset env - set s) \<le> card (bset env - set seen)"
  by (rule card_mono) (use finite_vt_lookup[of "tenv env"] in auto)


subsection \<open>Operations on types\<close>

text \<open>The known type variables: those of the type environment and of \<open>A\<close>.\<close>

lemma hnf_tenv: "tenv env' = tenv env \<Longrightarrow> hnf env' t = hnf env t"
  by (induction t) (simp_all add: ahd_def)

lemma head_norm_hnf:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> hnf env t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "hnf env u'" if "ok (hn env u) u'" for u u'
    using "1.IH"[OF that(1) refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with rest Var have "t' = Var x T" by simp
      with ok_lookup_None[of env x T] lr None show ?thesis by (simp add: ahd_def)
    next
      case (Some u)
      with rest IH show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h IH show ?thesis by auto
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with h App IH show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest IH show ?thesis by simp
      next
        case nA: False
        with rest have "t' = nf $ u" by (cases nf) simp_all
        with IH[OF nf] nA show ?thesis by (simp add: hnf_nonAbs ahd_def)
      qed
    qed
  qed (use h in \<open>auto simp: ahd_def\<close>)
qed

subsection \<open>The size of \<open>\<eta>\<close>-long forms\<close>

text \<open>
  The size of the \<open>\<eta>\<close>-long form of a \<open>\<beta>\<close>-normal term, given the types of its loose bound
  variables. As in \<^const>\<open>msz\<close>, a flexible term counts as the \<open>\<eta>\<close>-expansion of its head
  without the arguments; a rigid term counts with the \<open>\<eta>\<close>-expansion to the arity of its type
  (\<open>tsz\<close> is the size of the \<open>\<eta>\<close>-long form of a bound variable of the type).
\<close>

fun tsz :: "ptyp \<Rightarrow> nat" where
  "tsz (Type a [T, U]) = (if a = STR ''fun'' then tsz T + tsz U + 2 else 1)"
| "tsz _ = 1"

lemma tsz_pos: "0 < tsz T"
  by (induction T rule: tsz.induct) auto

function lsz :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" and asz :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> nat" where
  "lsz e (Abs a A t) = lsz (e\<langle>0:A\<rangle>) t + 2"
| "lsz e (Var x T) = 2 * arity T + 1"
| "lsz e (s $ t) = (case dhd s of
      Var x T \<Rightarrow> 2 * (arity T - Suc (dnargs s)) + 1
    | _ \<Rightarrow> tsz (spine_type e (s $ t)) + asz e (s $ t))"
| "lsz e (Bound i) = tsz (e i)"
| "lsz e (Const c T) = tsz T"
| "lsz e (Free x T) = tsz T"
| "asz e (s $ t) = asz e s + lsz e t"
| "asz e (Abs a A t) = 0"
| "asz e (Var x T) = 0"
| "asz e (Bound i) = 0"
| "asz e (Const c T) = 0"
| "asz e (Free x T) = 0"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>x. case x of Inl (e, t) \<Rightarrow> 2 * size t + 1 | Inr (e, t) \<Rightarrow> 2 * size t)") auto

lemma spine_type_lift: "0 \<le> k \<Longrightarrow> spine_type (e\<langle>k:A\<rangle>) (lift t k) = spine_type e t"
  by (induction t) (auto simp: integer_arith)

lemma lsz_lift: "0 \<le> k \<Longrightarrow> lsz (e\<langle>k:A\<rangle>) (lift t k) = lsz e t \<and> asz (e\<langle>k:A\<rangle>) (lift t k) = asz e t"
proof (induction t arbitrary: e k)
  case (Abs a B t)
  from Abs.IH[of "k + 1" "e\<langle>0:B\<rangle>"] Abs.prems show ?case by simp
next
  case (App s t)
  have IH: "asz (e\<langle>k:A\<rangle>) (lift s k) = asz e s" "lsz (e\<langle>k:A\<rangle>) (lift t k) = lsz e t"
    using App.IH App.prems by blast+
  have st: "spine_type (e\<langle>k:A\<rangle>) (lift (s $ t) k) = spine_type e (s $ t)"
    by (rule spine_type_lift[OF App.prems])
  show ?case
  proof (cases "dhd s")
    case (Bound i)
    then show ?thesis using IH st by (simp add: dhd_lift)
  qed (use IH st in \<open>simp_all add: dhd_lift\<close>)
qed (auto simp: integer_arith)

lemma not_App_apps_Abs: "\<not> is_Abs h \<Longrightarrow> \<not> is_Abs (h \<degree>\<degree> ts)"
  by (cases ts rule: rev_exhaust) (simp_all add: app_last[symmetric])

lemma asz_apps: "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> asz e (h \<degree>\<degree> ts) = sum_list (map (lsz e) ts)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) simp_all
next
  case (snoc t ts)
  then show ?case by (simp add: app_last[symmetric])
qed

lemma lsz_rigid_apps: "rigid h \<Longrightarrow> lsz e (h \<degree>\<degree> ts) = tsz (spine_type e (h \<degree>\<degree> ts)) + sum_list (map (lsz e) ts)"
proof -
  assume r: "rigid h"
  then have nA: "\<not> (\<exists>f u. h = f $ u)" by (cases h) simp_all
  have "lsz e (h \<degree>\<degree> ts) = tsz (spine_type e (h \<degree>\<degree> ts)) + asz e (h \<degree>\<degree> ts)"
  proof (cases ts rule: rev_exhaust)
    case Nil
    with r show ?thesis by (cases h) simp_all
  next
    case (snoc ts' t)
    have "dhd (h \<degree>\<degree> ts') = h" using r by (cases h) simp_all
    with r snoc show ?thesis by (cases h) (simp_all add: app_last[symmetric])
  qed
  with asz_apps[OF nA] show ?thesis by simp
qed

lemma lsz_flex_apps: "lsz e (Var x T \<degree>\<degree> ts) = 2 * (arity T - length ts) + 1"
  by (cases ts rule: rev_exhaust) (simp_all add: app_last[symmetric])

lemma lsz_eta:
  assumes h: "rigid h \<or> (\<exists>x T. h = Var x T)" and ty: "e \<turnstile> h \<degree>\<degree> ts : A \<rightarrow>\<^sub>T B" and nr: "no_redex (h \<degree>\<degree> ts)"
  shows "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) + 2 = lsz e (h \<degree>\<degree> ts)"
proof -
  have l: "lift (h \<degree>\<degree> ts) 0 $ Bound 0 = lift h 0 \<degree>\<degree> (map (\<lambda>t. lift t 0) ts @ [Bound 0])"
    by (simp only: incr_bv_apps app_last)
  have ll: "sum_list (map (lsz (e\<langle>0:A\<rangle>)) (map (\<lambda>t. lift t 0) ts)) = sum_list (map (lsz e) ts)"
    using lsz_lift[of 0 e A] by (simp add: comp_def)
  from h show ?thesis
  proof
    assume r: "rigid h"
    have nA: "\<not> is_Abs (h \<degree>\<degree> ts)" by (rule not_App_apps_Abs) (use r in \<open>cases h, simp_all\<close>)
    have "e\<langle>0:A\<rangle> \<turnstile> lift (h \<degree>\<degree> ts) 0 : A \<rightarrow>\<^sub>T B" by (rule lift_type[OF ty]) simp
    then have ty': "e\<langle>0:A\<rangle> \<turnstile> lift (h \<degree>\<degree> ts) 0 $ Bound 0 : B" by (rule typing.App) auto
    have nAl: "\<not> is_Abs (lift (h \<degree>\<degree> ts) 0)" using nA by (cases "h \<degree>\<degree> ts") simp_all
    have "no_redex (lift (h \<degree>\<degree> ts) 0)" using nr no_redex_incr_bv by blast
    then have nr': "no_redex (lift (h \<degree>\<degree> ts) 0 $ Bound 0)" using nAl by simp
    have st': "spine_type (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = B"
      by (rule spine_type_typing[OF ty' nr']) simp
    have st: "spine_type e (h \<degree>\<degree> ts) = A \<rightarrow>\<^sub>T B" by (rule spine_type_typing[OF ty nr nA])
    have "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = tsz B + sum_list (map (lsz e) ts) + tsz A"
      using lsz_rigid_apps[where e = "e\<langle>0:A\<rangle>" and ts = "map (\<lambda>t. lift t 0) ts @ [Bound 0]",
        OF lift_rigid[OF r, of 0]] st' ll
      by (simp add: l[symmetric])
    moreover have "lsz e (h \<degree>\<degree> ts) = tsz A + tsz B + 2 + sum_list (map (lsz e) ts)"
      using lsz_rigid_apps[OF r, of e ts] st by simp
    ultimately show ?thesis by simp
  next
    assume "\<exists>x T. h = Var x T"
    then obtain x T where hx: "h = Var x T" by blast
    from ty hx obtain Us where "e \<turnstile> Var x T : Us \<Rrightarrow> (A \<rightarrow>\<^sub>T B)" "e \<tturnstile> ts : Us" by (blast dest: list_app_typeD)
    then have "T = Us \<Rrightarrow> (A \<rightarrow>\<^sub>T B)" "length ts = length Us" using typings_nth by auto
    then have ar: "arity T = length ts + Suc (arity B)" by (simp add: arity_funs)
    have "lsz (e\<langle>0:A\<rangle>) (lift (h \<degree>\<degree> ts) 0 $ Bound 0) = 2 * (arity T - Suc (length ts)) + 1"
      using lsz_flex_apps[of "e\<langle>0:A\<rangle>" x T "map (\<lambda>t. lift t 0) ts @ [Bound 0]"] by (simp add: l hx)
    moreover have "lsz e (h \<degree>\<degree> ts) = 2 * (arity T - length ts) + 1" by (simp add: hx lsz_flex_apps)
    ultimately show ?thesis using ar by simp
  qed
qed


text \<open>The types of the bound variables of a list of binders:\<close>

fun benv :: "tinst \<Rightarrow> binders \<Rightarrow> integer \<Rightarrow> ptyp" where
  "benv \<rho> [] = (\<lambda>_. TFree STR '''' [])"
| "benv \<rho> (b # bs) = (benv \<rho> bs)\<langle>0:tsubst \<rho> (snd b)\<rangle>"

lemma bs_env_benv: "\<forall>(x, T)\<in>set bs. cert_typ alg ar (tsubst \<rho> T) \<Longrightarrow> bs_env \<rho> (benv \<rho> bs) bs"
proof (induction bs)
  case Nil
  show ?case by (simp add: bs_env_def)
next
  case (Cons b bs)
  obtain a T where b: "b = (a, T)" by force
  with Cons have "bs_env \<rho> (benv \<rho> bs) bs" "cert_typ alg ar (tsubst \<rho> T)" by auto
  from bs_env_Cons[OF this, of a] b show ?case by simp
qed

lemma typing_benv:
  assumes "bs_env \<rho> e bs" "e \<turnstile> s : T" "\<not> loose_bvar s (ilength bs)"
  shows "benv \<rho> bs \<turnstile> s : T"
proof (rule typing_env_cong[OF assms(2)])
  have b: "bs_env \<rho> (benv \<rho> bs) bs" by (rule bs_env_benv) (use assms(1) in \<open>simp add: bs_env_def\<close>)
  fix i assume i: "0 \<le> i" "loose_bvar1 s i"
  with loose_bvar1_less[OF assms(3)] have "i < ilength bs" by blast
  with b assms(1) i(1) show "benv \<rho> bs i = e i" by (simp add: bs_env_def)
qed

subsection \<open>The measure of a pair\<close>

lemma bnorm_ahd:
  assumes at: "atom h" and ty: "e \<turnstile> h \<degree>\<degree> xs : T"
  shows "bnorm (h \<degree>\<degree> xs) = h \<degree>\<degree> map bnorm xs" "e \<turnstile> h \<degree>\<degree> map bnorm xs : T" "no_redex (h \<degree>\<degree> map bnorm xs)"
proof -
  show b: "bnorm (h \<degree>\<degree> xs) = h \<degree>\<degree> map bnorm xs" by (rule bnorm_atom_apps[OF at ty])
  from bnorm_typed[OF ty] b show "e \<turnstile> h \<degree>\<degree> map bnorm xs : T" "no_redex (h \<degree>\<degree> map bnorm xs)"
    using subject_reduction_beta'[OF _ ty] by auto
qed

lemma incr_boundvars_1: "incr_boundvars 1 t = lift t 0"
  by (simp add: incr_boundvars_def)

lemma ahd_head: "ahd env t \<Longrightarrow> rigid (head_of t) \<or> (\<exists>F U. head_of t = Var F U \<and> vt_lookup (tenv env) F = None)"
  by (simp add: ahd_def)

lemma ahd_nonAbs: "ahd env t \<Longrightarrow> \<not> is_Abs t"
  by (cases t) (simp_all add: ahd_def)


subsection \<open>Steps of simplification\<close>

text \<open>
  A step of \<open>SIMPL0\<close> extends the environment, with only type variables that are known (in \<open>A\<close> or
  the type environment) or new (\<^const>\<open>tnew\<close>); it either keeps the type environment, and then it
  reduces the number of unbound variables of the problem or keeps the term environment, or it
  reduces the number of unbound type variables reachable from \<open>K\<close>.
\<close>

definition sstep :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "sstep A K X env env' \<longleftrightarrow> extends env env' \<and> tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env') \<and>
    tnew A env A env' \<and>
    (tyenv env' = tyenv env \<longrightarrow> card (ubv env' X) < card (ubv env X) \<or> tenv env' = tenv env) \<and>
    (tyenv env' \<noteq> tyenv env \<longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K))"

lemma sstep_refl: "sstep A K X env env"
  by (simp add: sstep_def)

lemma sstepD:
  assumes "sstep A K X env env'"
  shows "extends env env'" "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env')"
    "tyenv env' = tyenv env \<Longrightarrow> card (ubv env' X) < card (ubv env X) \<or> tenv env' = tenv env"
    "tyenv env' \<noteq> tyenv env \<Longrightarrow> card (uvarsA (tyenv env') K) < card (uvarsA (tyenv env) K)"
    "tnew A env A env'"
  using assms by (simp_all add: sstep_def)

lemma vt_lookup_antisym:
  assumes "\<And>x b. vt_lookup t x = Some b \<Longrightarrow> vt_lookup t' x = Some b"
    "\<And>x b. vt_lookup t' x = Some b \<Longrightarrow> vt_lookup t x = Some b"
  shows "t' = t"
  by (rule vt_eqI) (metis assms not_None_eq)

lemma extends_mid:
  assumes "extends env env1" "extends env1 env2"
  shows "tyenv env2 = tyenv env \<Longrightarrow> tyenv env1 = tyenv env"
    and "tenv env2 = tenv env \<Longrightarrow> tenv env1 = tenv env"
proof -
  have te: "textends (tyenv env) (tyenv env1)" "textends (tyenv env1) (tyenv env2)"
    using assms by (simp_all add: extends_def)
  show "tyenv env2 = tyenv env \<Longrightarrow> tyenv env1 = tyenv env" using te textends_antisym by metis
  assume e: "tenv env2 = tenv env"
  show "tenv env1 = tenv env"
  proof (rule vt_lookup_antisym)
    fix x b
    show "vt_lookup (tenv env) x = Some b \<Longrightarrow> vt_lookup (tenv env1) x = Some b"
      by (rule extends_lookup[OF assms(1)])
    show "vt_lookup (tenv env1) x = Some b \<Longrightarrow> vt_lookup (tenv env) x = Some b"
      using extends_lookup[OF assms(2)] e by metis
  qed
qed

lemma sstep_trans:
  assumes 1: "sstep A K X env env1" and 2: "sstep A K X env1 env2"
  shows "sstep A K X env env2"
proof -
  note a = sstepD[OF 1] and b = sstepD[OF 2]
  have c: "card (ubv env2 X) < card (ubv env X) \<or> tenv env2 = tenv env" if e2: "tyenv env2 = tyenv env"
  proof -
    have e1: "tyenv env1 = tyenv env" by (rule extends_mid(1)[OF a(1) b(1) e2])
    with e2 have "tyenv env2 = tyenv env1" by simp
    from a(3)[OF e1] b(3)[OF this] show ?thesis using ubv_tenv[of env1 env X] ubv_tenv[of env2 env1 X] by auto
  qed
  have d: "card (uvarsA (tyenv env2) K) < card (uvarsA (tyenv env) K)" if "tyenv env2 \<noteq> tyenv env"
  proof (cases "tyenv env1 = tyenv env")
    case True
    with that b(4) show ?thesis by simp
  next
    case False
    with a(4) b(4) show ?thesis by (cases "tyenv env2 = tyenv env1") auto
  qed
  have "tnew A env A env2" by (rule tnew_trans[OF a(5) b(5) extends_maxidx[OF a(1)]])
  then show ?thesis using extends_trans[OF a(1) b(1)] a(2) b(2) c d by (auto simp: sstep_def)
qed

lemma sstep_tyext:
  assumes "tenv env1 = tenv env" "textends (tyenv env) (tyenv env1)" "maxidx env \<le> maxidx env1"
    "tvars_env (tyenv env) \<subseteq> tvars_env (tyenv env1)" "tnew A env A env1"
    "tyenv env1 = tyenv env \<or> card (uvarsA (tyenv env1) K) < card (uvarsA (tyenv env) K)"
  shows "sstep A K X env env1"
  using assms by (auto simp: sstep_def extends_def)

lemma ulex_sstep:
  assumes "sstep A K X env0 env" "tyenv env = tyenv env0 \<Longrightarrow> tenv env = tenv env0 \<Longrightarrow> d < d0"
  shows "((card (uvarsA (tyenv env) K), card (ubv env X), d), (card (uvarsA (tyenv env0) K), card (ubv env0 X), d0)) \<in> ulex"
proof (cases "tyenv env = tyenv env0")
  case True
  from sstepD(3)[OF assms(1) True] show ?thesis
  proof
    assume "tenv env = tenv env0"
    with assms(2) True ubv_tenv[of env env0 X] show ?thesis by simp
  qed (use True in simp)
next
  case False
  with sstepD(4)[OF assms(1)] show ?thesis by simp
qed

text \<open>Typing of a well-formed pair at the types of its binders:\<close>

lemma upok_benv:
  assumes "upok A env rb X t u" "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  shows "\<exists>T. bs_env \<rho> (benv \<rho> rb) rb \<and> benv \<rho> rb \<turnstile> inst \<rho> t : T \<and> benv \<rho> rb \<turnstile> inst \<rho> u : T"
proof -
  note pd = upokD[OF assms(1)]
  from pd(9)[OF assms(2,3)] obtain e T where e: "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by blast
  have "bs_env \<rho> (benv \<rho> rb) rb" by (rule bs_env_benv) (use e(1) in \<open>simp add: bs_env_def\<close>)
  moreover have "benv \<rho> rb \<turnstile> inst \<rho> t : T" by (rule typing_benv[OF e(1,2)]) (simp add: pd(7))
  moreover have "benv \<rho> rb \<turnstile> inst \<rho> u : T" by (rule typing_benv[OF e(1,3)]) (simp add: pd(8))
  ultimately show ?thesis by blast
qed

subsection \<open>Normalization of pairs\<close>

text \<open>The result of the normalization of a pair:\<close>

lemma upok_Abs:
  assumes p: "upok A env bs X (Abs ns Ts ts) (Abs nt Tt tt)"
    and sol: "\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> tsubst \<rho> Ts = tsubst \<rho> Tt"
  shows "upok A env ((nm, Ts) # bs) X ts tt"
  unfolding upok_def
proof (intro conjI allI impI)
  note pd = upokD[OF p]
  show "vars ts \<union> vars tt \<subseteq> X \<union> evars env" using pd(1,2) by simp
  show "ttvars ts \<union> ttvars tt \<union> btvars ((nm, Ts) # bs) \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A"
    using pd(3-6) by (auto simp: ttvars_def btvars_def)
  show "\<not> loose_bvar ts (ilength ((nm, Ts) # bs))" using pd(7) by (simp add: algebra_simps)
  show "\<not> loose_bvar tt (ilength ((nm, Ts) # bs))" using pd(8) by (simp add: algebra_simps)
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  obtain e T where ty: "bs_env \<rho> e bs" "e \<turnstile> inst \<rho> (Abs ns Ts ts) : T" "e \<turnstile> inst \<rho> (Abs nt Tt tt) : T"
    using pd(9)[OF \<rho>] by blast
  have eq: "tsubst \<rho> Ts = tsubst \<rho> Tt" using sol \<rho>(1) by blast
  from ty(2) obtain U where T: "T = tsubst \<rho> Ts \<rightarrow>\<^sub>T U" and c: "cert_typ alg ar (tsubst \<rho> Ts)"
    and t1: "e\<langle>0:tsubst \<rho> Ts\<rangle> \<turnstile> inst \<rho> ts : U" by auto
  from ty(3) obtain U' where T': "T = tsubst \<rho> Tt \<rightarrow>\<^sub>T U'"
    and t2: "e\<langle>0:tsubst \<rho> Tt\<rangle> \<turnstile> inst \<rho> tt : U'" by auto
  from T T' eq have "U' = U" by simp
  with t1 t2 eq bs_env_Cons[OF ty(1) c]
  show "\<exists>e T. bs_env \<rho> e ((nm, Ts) # bs) \<and> e \<turnstile> inst \<rho> ts : T \<and> e \<turnstile> inst \<rho> tt : T" by metis
qed

lemma upok_eta_norm:
  assumes p: "upok A env rb X t u" and et: "ok (eta_norm env rb t) t'" and tv: "ttvars t' \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "upok A env rb X t' u"
  unfolding upok_def
proof (intro conjI allI impI)
  note pd = upokD[OF p] and E = eta_norm_sound[OF et]
  show "vars t' \<union> vars u \<subseteq> X \<union> evars env" using pd(1,2) E by simp
  show "ttvars t' \<union> ttvars u \<union> btvars rb \<union> vtvars X \<subseteq> tvars_env (tyenv env) \<union> A" using pd(4-6) tv by blast
  show "\<not> loose_bvar t' (ilength rb)" using E pd(7) ilength_nonneg[of rb] by blast
  show "\<not> loose_bvar u (ilength rb)" by (rule pd(8))
  fix \<rho> assume \<rho>: "tsol (tyenv env) \<rho>" "cert_inst \<rho>"
  from pd(9)[OF \<rho>] obtain e T where ty: "bs_env \<rho> e rb" "e \<turnstile> inst \<rho> t : T" "e \<turnstile> inst \<rho> u : T" by blast
  with E \<rho>(1) pd(7) show "\<exists>e T. bs_env \<rho> e rb \<and> e \<turnstile> inst \<rho> t' : T \<and> e \<turnstile> inst \<rho> u : T" by blast
qed

subsection \<open>Assignments\<close>

lemma get_eta_var_cases: "get_eta_var rb n t = raiseW ASSIGN \<or> (\<exists>v T. get_eta_var rb n t = returnW (v, T))"
  by (induction rb n t rule: get_eta_var.induct) auto

text \<open>
  An assignment raises \<open>ASSIGN\<close> or \<open>CANTUNIFY\<close>, or binds the head variable; the result keeps the
  invariants and reduces the number of unbound variables (or of unbound type variables).
\<close>

definition apost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> env \<Rightarrow> bool" where
  "apost A K X env env' \<longleftrightarrow> einv A K env' \<and> winv env' X \<and> sstep A K X env env' \<and> tenv env' \<noteq> tenv env"

subsection \<open>Results of simplification\<close>

lemma sinv_mono: "sinv A K X env dps \<Longrightarrow> set dps' \<subseteq> set dps \<Longrightarrow> sinv A K X env dps'"
  unfolding sinv_def by blast

lemma sinv_ext:
  assumes "sinv A K X env dps" "einv A K env'" "winv env' X" "sstep A K X env env'"
  shows "sinv A K X env' dps"
  using assms upok_mono[OF _ sstepD(1,2)[OF assms(4)]] unfolding sinv_def by blast

text \<open>
  The shapes of the results: the flex-flex pairs have variables as heads on both sides, the
  flex-rigid pairs a variable on the left and a rigid head on the right; no side is an
  abstraction. The head variables are unbound unless the term environment changed.
\<close>

definition ffs0 :: "dpair \<Rightarrow> bool" where
  "ffs0 dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    \<not> is_Abs t \<and> \<not> is_Abs u \<and> is_Var (head_of t) \<and> is_Var (head_of u))"

lemma hunb_tenv: "tenv env' = tenv env \<Longrightarrow> hunb env' dp = hunb env dp"
  by (simp add: hunb_def)

definition spost :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> dpair list \<Rightarrow> dpair list \<Rightarrow> sstate \<Rightarrow> bool" where
  "spost A K X env ffs frs st' \<longleftrightarrow> (case st' of (env', ffs', frs') \<Rightarrow>
    \<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> sinv A K X env' (a @ b) \<and>
      (\<forall>dp\<in>set a. ffs0 dp) \<and> (\<forall>dp\<in>set b. frs0 dp) \<and>
      (tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (a @ b). hunb env' dp)) \<and> sstep A K X env env')"

lemma spost_refl: "sinv A K X env [] \<Longrightarrow> spost A K X env ffs frs (env, ffs, frs)"
  by (simp add: spost_def sstep_refl)

lemma sinv_union: "sinv A K X env xs \<Longrightarrow> sinv A K X env ys \<Longrightarrow> set zs \<subseteq> set xs \<union> set ys \<Longrightarrow> sinv A K X env zs"
  unfolding sinv_def by blast

lemma spost_new:
  assumes "sinv A K X env' (a @ b)" "\<forall>dp\<in>set a. ffs0 dp" "\<forall>dp\<in>set b. frs0 dp"
    "tenv env' = tenv env \<longrightarrow> (\<forall>dp\<in>set (a @ b). hunb env' dp)" "sstep A K X env env'"
  shows "spost A K X env ffs frs (env', a @ ffs, b @ frs)"
  using assms unfolding spost_def by blast

lemma spost_trans:
  assumes 1: "spost A K X env ffs frs (env1, ffs1, frs1)" and 2: "spost A K X env1 ffs1 frs1 st2"
  shows "spost A K X env ffs frs st2"
proof -
  obtain env2 ffs2 frs2 where st2: "st2 = (env2, ffs2, frs2)" by (cases st2)
  from 1 obtain a1 b1 where p1: "ffs1 = a1 @ ffs" "frs1 = b1 @ frs" "sinv A K X env1 (a1 @ b1)"
    "\<forall>dp\<in>set a1. ffs0 dp" "\<forall>dp\<in>set b1. frs0 dp" "tenv env1 = tenv env \<longrightarrow> (\<forall>dp\<in>set (a1 @ b1). hunb env1 dp)"
    "sstep A K X env env1"
    unfolding spost_def by blast
  from 2 st2 obtain a2 b2 where p2: "ffs2 = a2 @ ffs1" "frs2 = b2 @ frs1" "sinv A K X env2 (a2 @ b2)"
    "\<forall>dp\<in>set a2. ffs0 dp" "\<forall>dp\<in>set b2. frs0 dp" "tenv env2 = tenv env1 \<longrightarrow> (\<forall>dp\<in>set (a2 @ b2). hunb env2 dp)"
    "sstep A K X env1 env2"
    unfolding spost_def by blast
  have si: "sinv A K X env2 ((a2 @ a1) @ (b2 @ b1))"
  proof -
    have s1: "sinv A K X env2 (a1 @ b1)"
      by (rule sinv_ext[OF p1(3)]) (use p2(3,7) in \<open>simp_all add: sinv_def\<close>)
    show ?thesis by (rule sinv_union[OF p2(3) s1]) auto
  qed
  have hu: "\<forall>dp\<in>set ((a2 @ a1) @ (b2 @ b1)). hunb env2 dp" if e: "tenv env2 = tenv env"
  proof -
    have e1: "tenv env1 = tenv env" by (rule extends_mid(2)[OF sstepD(1)[OF p1(7)] sstepD(1)[OF p2(7)] e])
    with e have "tenv env2 = tenv env1" by simp
    with p1(6) p2(6) e1 hunb_tenv[OF this] show ?thesis by auto
  qed
  show ?thesis unfolding st2 spost_def prod.case
    by (rule exI[of _ "a2 @ a1"], rule exI[of _ "b2 @ b1"])
      (use p1 p2 si hu sstep_trans[OF p1(7) p2(7)] in auto)
qed

lemma head_typing: "e \<turnstile> inst \<rho> t : T \<Longrightarrow> \<exists>V. e \<turnstile> inst \<rho> (head_of t) : V"
  by (induction t arbitrary: T) auto

lemma head_Var_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Var v T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma head_Const_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Const c T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma head_Free_cert: "e \<turnstile> inst \<rho> t : T0 \<Longrightarrow> head_of t = Free c T \<Longrightarrow> cert_typ alg ar (tsubst \<rho> T)"
  using head_typing[of e \<rho> t T0] by auto

lemma body_type_ok:
  assumes ei: "einv A K env" and tv: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
    and c: "cert_typ alg ar (tsubst (rho0 env) T)"
  shows "\<exists>B. body_type env T = return B \<and> tvars B \<subseteq> tvars_env (tyenv env) \<union> A \<and> wft ar B \<and> sorts_ok alg B"
proof -
  note e = einvD[OF ei] and r0 = einv_rho0[OF ei]
  from body_type_term[OF e(2) refl tv] obtain B where bt: "body_type env T = return B"
    "tvars B \<subseteq> tvars_env (tyenv env) \<union> A" by blast
  from binder_types_term[OF e(2) refl tv] obtain Ts where bts: "binder_types env T = return Ts" by blast
  have "tsubst (rho0 env) T = map (tsubst (rho0 env)) Ts \<Rrightarrow> tsubst (rho0 env) B"
    by (rule binder_body_type_sound[OF bts[unfolded return_def] refl bt(1)[unfolded return_def] r0(1)])
  with c have "cert_typ alg ar (tsubst (rho0 env) B)" by (simp add: cert_typ_funs)
  with cert_typ_rev[OF ei this bt(2)] bt show ?thesis by blast
qed

lemma simrands_atoms:
  "\<not> (\<exists>f u. h = f $ u) \<Longrightarrow> \<not> (\<exists>f u. h' = f $ u) \<Longrightarrow> simrands F rb u0 h h' st = returnW st"
  by (cases h; cases h') simp_all

lemma simrands_snoc:
  "simrands F rb u0 (h \<degree>\<degree> (ss @ [s])) (h' \<degree>\<degree> (ts @ [t])) st =
    bindW (simrands F rb u0 (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) st) (F (rb, s, t))"
  by (simp add: app_last[symmetric])

lemma SIMPL0_unfold:
  "SIMPL0 al dp0 (env, ffs, frs) =
    bindW (head_norm_dpair al env dp0) (\<lambda>(dp, env'). case dp of (rb, t, u) \<Rightarrow> SIMPL0_rest SIMPL0 al rb t u env' ffs frs)"
  by (subst SIMPL0.simps, simp only: prod.case, rule arg_cong[where f = "bindW (head_norm_dpair al env dp0)"],
    rule ext, simp add: SIMPL0_rest_def split: prod.splits)


lemma head_of_not_App: "\<not> (\<exists>f u. head_of t = f $ u)"
  by (induction t) auto

lemma sinv_dzip:
  assumes "einv A K env" "winv env X" "\<forall>(a, b)\<in>set (zip ss ts). upok A env rb X a b"
  shows "sinv A K X env (dzip rb ss ts)"
  unfolding sinv_def
proof (intro conjI ballI)
  fix dp assume "dp \<in> set (dzip rb ss ts)"
  then obtain a b where dp: "dp = (rb, a, b)" "(a, b) \<in> set (zip ss ts)" by auto
  with assms(3) show "case dp of (rb, t, u) \<Rightarrow> upok A env rb X t u" by auto
qed (use assms in auto)

text \<open>The results extend the environment, so they bind what it binds:\<close>

lemma SIMPL0_anti: "okW (SIMPL0 alg' dp st) st' \<Longrightarrow> nfree (fst st') \<Longrightarrow> nfree (fst st)"
proof -
  assume a: "okW (SIMPL0 alg' dp st) st'" "nfree (fst st')"
  obtain env ffs frs env' ffs' frs' where st: "st = (env, ffs, frs)" "st' = (env', ffs', frs')"
    by (cases st; cases st') auto
  from SIMPL0_sound[OF a(1)[unfolded st]] obtain a' b' where "dstep env [dp] env' (a' @ b')" by blast
  from nfree_extends[OF dstepD(1)[OF this]] a(2) st show ?thesis by simp
qed

lemma foldrW_SIMPL0_anti:
  "okW (foldrW (SIMPL0 alg') dps st) st' \<Longrightarrow> nfree (fst st') \<Longrightarrow> nfree (fst st)"
proof -
  assume a: "okW (foldrW (SIMPL0 alg') dps st) st'" "nfree (fst st')"
  obtain env ffs frs env' ffs' frs' where st: "st = (env, ffs, frs)" "st' = (env', ffs', frs')"
    by (cases st; cases st') auto
  from foldrW_SIMPL0_sound[OF a(1)[unfolded st]] obtain a' b' where "dstep env dps env' (a' @ b')" by blast
  from nfree_extends[OF dstepD(1)[OF this]] a(2) st show ?thesis by simp
qed

lemma simrands_anti:
  "okW (simrands (SIMPL0 alg') rb u0 s t st) st' \<Longrightarrow> nfree (fst st') \<Longrightarrow> nfree (fst st)"
proof -
  assume a: "okW (simrands (SIMPL0 alg') rb u0 s t st) st'" "nfree (fst st')"
  have "\<exists>a b. ffs' = a @ ffs \<and> frs' = b @ frs \<and> dstep env [dp] env' (a @ b)"
    if "okW (SIMPL0 alg' dp (env, ffs, frs)) (env', ffs', frs')" for dp env ffs frs env' ffs' frs'
    using SIMPL0_sound[OF that] .
  from simrands_sound[of "SIMPL0 alg'", OF this a(1)] obtain a' b' ss ts where
    "dstep (fst st) (dzip rb ss ts) (fst st') (a' @ b')" by blast
  from nfree_extends[OF dstepD(1)[OF this] a(2)] show ?thesis .
qed

lemma SIMPL_anti: "okW (SIMPL alg' env dps) st' \<Longrightarrow> nfree (fst st') \<Longrightarrow> nfree env"
proof -
  assume a: "okW (SIMPL alg' env dps) st'" "nfree (fst st')"
  obtain env' ffs' frs' where st: "st' = (env', ffs', frs')" by (cases st') auto
  from nfree_extends[OF dstepD(1)[OF SIMPL_sound[OF a(1)[unfolded st]]]] a(2) st show ?thesis by simp
qed


subsection \<open>The results of \<open>SIMPL\<close>\<close>

definition chd :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "chd env t \<longleftrightarrow> (case head_of t of Var F T \<Rightarrow> vt_lookup (tenv env) F \<noteq> None | _ \<Rightarrow> False)"

lemma not_chd_iff: "\<not> chd env t \<longleftrightarrow> (\<forall>F T. head_of t = Var F T \<longrightarrow> vt_lookup (tenv env) F = None)"
proof (cases "head_of t")
  case (Var F T)
  then show ?thesis by (cases "vt_lookup (tenv env) F") (auto simp: chd_def)
qed (auto simp: chd_def)

lemma hunb_chd: "hunb env (rb, t, u) \<longleftrightarrow> \<not> chd env t \<and> \<not> chd env u"
  by (simp only: hunb_def not_chd_iff prod.case)

definition ff_shape :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "ff_shape env dp \<longleftrightarrow> ffs0 dp \<and> hunb env dp"

definition simpl_post :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow>
    env \<Rightarrow> sstate \<Rightarrow> bool" where
  "simpl_post A K X env st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    sinv A K X env' (frs @ ffs) \<and> (\<forall>dp\<in>set ffs. ff_shape env' dp) \<and> (\<forall>dp\<in>set frs. fr_shape env' dp) \<and>
    sstep A K X env env')"

lemma simpl_post_trans: "sstep A K X env env1 \<Longrightarrow> simpl_post A K X env1 st \<Longrightarrow> simpl_post A K X env st"
  by (auto simp: simpl_post_def intro: sstep_trans split: prod.splits)

subsection \<open>Unification of types that are equal in the most general solution\<close>

lemma tnorm_nonType: "tacyc \<theta> \<Longrightarrow> \<not> tbound \<theta> T \<Longrightarrow> \<not> (\<exists>a Ts. T = Type a Ts) \<Longrightarrow> tnorm \<theta> T = T"
  by (cases T) (auto simp: tnorm_TVar split: option.splits)

lemma unify_aux_same:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
  shows "tcons \<theta> T \<Longrightarrow> tcons \<theta> U \<Longrightarrow> tnorm \<theta> T = tnorm \<theta> U \<Longrightarrow> unify_aux alg' T U (\<theta>, n) = return (\<theta>, n)"
proof (induction "size (tnorm \<theta> T)" arbitrary: T U rule: less_induct)
  case less
  obtain T' where T': "devar \<theta> T = return T'" "tnorm \<theta> T' = tnorm \<theta> T" "tcons \<theta> T'" "\<not> tbound \<theta> T'"
    using devar_ok[OF ac tc less.prems(1)] by blast
  obtain U' where U': "devar \<theta> U = return U'" "tnorm \<theta> U' = tnorm \<theta> U" "tcons \<theta> U'" "\<not> tbound \<theta> U'"
    using devar_ok[OF ac tc less.prems(2)] by blast
  have eq: "tnorm \<theta> T' = tnorm \<theta> U'" using T'(2) U'(2) less.prems(3) by simp
  have unf: "unify_aux alg' T U (\<theta>, n) = (case (T', U') of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return (\<theta>, n) else tvar_clash v S1 S2)
          else if sort_le alg' S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T')) \<theta>; return (tye', n)}
          else if sort_le alg' S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U')) \<theta>; return (tye', n)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg' S1 S2) n;
            tye' \<leftarrow> update_new (w, (S2, S)) \<theta>;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> U';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U')) \<theta>; meet alg' U' S (tye', n)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> T';
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T')) \<theta>; meet alg' T' S (tye', n)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. unify_aux alg' T U st) (zip Ts Us) (\<theta>, n)
      | _ \<Rightarrow> if T' = U' then return (\<theta>, n) else raise TUnify)"
    by (subst unify_aux.simps) (simp add: T'(1) U'(1))
  show ?case
  proof (cases "\<exists>a Ts. T' = Type a Ts")
    case False
    have tT: "tnorm \<theta> T' = T'" by (rule tnorm_nonType[OF ac T'(4) False])
    have "\<not> (\<exists>a Us. U' = Type a Us)"
    proof
      assume "\<exists>a Us. U' = Type a Us"
      then obtain a Us where "U' = Type a Us" by blast
      with eq tT False show False by auto
    qed
    then have "tnorm \<theta> U' = U'" by (rule tnorm_nonType[OF ac U'(4)])
    with tT eq have "U' = T'" by simp
    with unf False show ?thesis by (cases T') auto
  next
    case True
    then obtain a Ts where Ta: "T' = Type a Ts" by blast
    have "\<exists>Us. U' = Type a Us"
    proof (cases "\<exists>b Us. U' = Type b Us")
      case True
      then obtain b Us where "U' = Type b Us" by blast
      with eq Ta show ?thesis by auto
    next
      case False
      then have "tnorm \<theta> U' = U'" by (rule tnorm_nonType[OF ac U'(4)])
      with eq Ta False show ?thesis by auto
    qed
    then obtain Us where Ua: "U' = Type a Us" by blast
    from eq Ta Ua have mm: "map (tnorm \<theta>) Ts = map (tnorm \<theta>) Us" by simp
    then have len: "length Ts = length Us" by (metis length_map)
    have sz: "size (tnorm \<theta> V) < size (tnorm \<theta> T)" if "V \<in> set Ts" for V
    proof -
      have "size (tnorm \<theta> V) < size (Type a (map (tnorm \<theta>) Ts))"
        using that by (induction Ts) auto
      moreover have "tnorm \<theta> T = Type a (map (tnorm \<theta>) Ts)" using T'(2) Ta by simp
      ultimately show ?thesis by simp
    qed
    have "foldM (\<lambda>(T, U) st. unify_aux alg' T U st) (zip Ts' Us') (\<theta>, n) = return (\<theta>, n)"
      if "set Ts' \<subseteq> set Ts" "set Us' \<subseteq> set Us" "map (tnorm \<theta>) Ts' = map (tnorm \<theta>) Us'" for Ts' Us'
      using that
    proof (induction Ts' arbitrary: Us')
      case (Cons V Vs)
      then obtain W Ws where Us': "Us' = W # Ws" by (cases Us') auto
      have tV: "tcons \<theta> V" using T'(3) Ta Cons.prems(1) by auto
      have tW: "tcons \<theta> W" using U'(3) Ua Cons.prems(2) Us' by auto
      have "unify_aux alg' V W (\<theta>, n) = return (\<theta>, n)"
        using less.hyps[OF sz tV tW] Cons.prems Us' by auto
      with Cons.IH[of Ws] Cons.prems Us' show ?case by simp
    qed simp
    from this[OF order_refl order_refl mm] unf Ta Ua show ?thesis by simp
  qed
qed

lemma cunify_types_same:
  assumes "tacyc (tyenv env)" "tcons_env (tyenv env)" "tcons (tyenv env) T" "tcons (tyenv env) U"
    "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "cunify_types alg' T U env = returnW env"
proof -
  have "unify_types alg' T U env = return env"
  proof (cases "T = U")
    case False
    have "type_unify alg' U T (tyenv env, maxidx env) = return (tyenv env, maxidx env)"
      unfolding type_unify_def by (rule unify_aux_same[OF assms(1,2,4,3)]) (use assms(5) in simp)
    then show ?thesis using False by (cases env) (simp add: unify_types_def)
  qed (simp add: unify_types_def)
  then show ?thesis by (simp add: cunify_types_def return_def)
qed

end

subsection \<open>Without loose names\<close>

context pure_sig
begin

lemma lxokE_iff:
  "lxokE Xe f m P \<longleftrightarrow> (\<exists>evs e. m = Some (evs, Err e) \<and> Xe e) \<or> (\<exists>x. okW m x \<and> P x)"
  by (rule lxokE_strict) simp

lemma lxok_iff [simp]: "lxok E f m P \<longleftrightarrow> xokW E m P"
  by (auto simp: lxokE_iff xokW_def)

end

end
