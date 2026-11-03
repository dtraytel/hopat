section \<open>The Shape of Normalized Terms\<close>

theory Unify_Shape_Sound
  imports Unify_Match_Sound
begin

context pure_sig
begin

text \<open>
  The normalization of an argument in \<^const>\<open>copycons\<close> (\<^const>\<open>head_norm\<close>, then
  \<^const>\<open>eta_norm\<close>) yields a saturated term (\<^const>\<open>satd\<close>): \<^const>\<open>head_norm\<close> returns a head
  normal form, and \<^const>\<open>eta_norm\<close> \<open>\<eta>\<close>-expands it until its type, modulo the type environment, is not
  a function type, which is then the body type of the type of its head.
\<close>

subsection \<open>Head normal forms\<close>

fun head_nf :: "pterm \<Rightarrow> bool" where
  "head_nf (Abs _ _ b) = head_nf b"
| "head_nf t = (\<not> is_Abs (head_of t))"

lemma head_nf_nonAbs: "\<not> is_Abs t \<Longrightarrow> head_nf t \<longleftrightarrow> \<not> is_Abs (head_of t)"
  by (cases t) auto

lemma head_norm_head_nf:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> head_nf t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note ok = "1.prems"
  show ?case
  proof (cases t)
    case (Var x T)
    with "1.hyps" ok obtain r' where
      rest: "(case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) = Some (Ok t')"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest Var show ?thesis by auto
    next
      case (Some u)
      with rest have "hn env u = Some (Ok t')" by simp
      from "1.IH"[OF this refl] show ?thesis .
    qed
  next
    case (Abs a T body)
    with "1.hyps" ok obtain b' where "hn env body = Some (Ok b')" "t' = Abs a T b'"
      by auto
    with "1.IH"[of env body] show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where "f = Abs a T body" by (cases f) auto
      with "1.hyps" ok App have "hn env (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl] show ?thesis .
    next
      case False
      with "1.hyps" ok App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "(case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) = Some (Ok t')"
        by (cases f) auto
      have head_nf_nf: "head_nf nf" by (rule "1.IH"[OF nf refl])
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl] show ?thesis .
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with head_nf_nf False show ?thesis by (simp add: head_nf_nonAbs)
      qed
    qed
  qed (use "1.hyps" ok in auto)
qed

lemma fst_strip_comb_acc: "fst (strip_comb_acc t ts) = head_of t"
  by (induction t ts rule: strip_comb_acc.induct) auto

lemma fst_strip_comb: "fst (strip_comb t) = head_of t"
  by (simp add: strip_comb_def fst_strip_comb_acc)

lemma is_Abs_head_of_incr_bv: "is_Abs (head_of (incr_bv i l t)) = is_Abs (head_of t)"
  by (induction i l t rule: incr_bv.induct) auto


subsection \<open>Types modulo the type environment\<close>

lemma devar_TVar_Some:
  "ok (type_lookup \<theta> ixn S) (Some U) \<Longrightarrow> devar \<theta> (TVar ixn S) = devar \<theta> U"
  by (subst devar.simps) (simp add: bindM_def)

lemma body_type_devar_aux:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok D \<Longrightarrow> \<theta> = tyenv env \<Longrightarrow> body_type env T = body_type env D"
  using assms
proof (induction \<theta> T r arbitrary: D rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) D"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis by simp
    next
      case (Some U)
      with rest have "dv \<theta> U = Some (Ok D)" by simp
      from "1.IH"[OF this refl "1.prems"(2)] lk Some TVar "1.prems"(2) show ?thesis
        by (subst body_type.simps) (simp add: bindM_def)
    qed
  qed (use "1.hyps" "1.prems" in simp_all)
qed

lemma body_type_devar: "ok (devar (tyenv env) T) D \<Longrightarrow> body_type env T = body_type env D"
  using body_type_devar_aux by blast

text \<open>The body type of the type of the head of an application is the body type of its type:\<close>

lemma env_fastype_apps_body_type:
  "ok (env_fastype env Ts (h \<degree>\<degree> args)) R \<Longrightarrow> ok (env_fastype env Ts h) T0 \<Longrightarrow>
    body_type env T0 = body_type env R"
proof (induction args arbitrary: h T0)
  case Nil
  then show ?case by simp
next
  case (Cons a args)
  from Cons.prems(1) have r: "ok (env_fastype env Ts ((h $ a) \<degree>\<degree> args)) R" by simp
  have "\<exists>R'. ok (env_fastype env Ts (h $ a)) R'"
  proof -
    have "\<exists>R'. ok (env_fastype env Ts s) R'" if "ok (env_fastype env Ts (s \<degree>\<degree> bs)) R" for s bs
      using that
    proof (induction bs arbitrary: s)
      case (Cons b bs)
      from Cons.IH[of "s $ b"] Cons.prems show ?case by auto
    qed auto
    from this[OF r] show ?thesis .
  qed
  then obtain R' where ha: "ok (env_fastype env Ts (h $ a)) R'" by blast
  from ha Cons.prems(2) obtain D where dv: "ok (devar (tyenv env) T0) D"
    and D: "ok (case D of
      Type b Vs \<Rightarrow> (case Vs of [_, U] \<Rightarrow> if b = STR ''fun'' then return U
        else raise (Term_Error funerr [h $ a]) | _ \<Rightarrow> raise (Term_Error funerr [h $ a]))
      | _ \<Rightarrow> raise (Term_Error funerr [h $ a])) R'"
    by auto
  from D obtain A where DA: "D = A \<rightarrow>\<^sub>T R'"
    by (auto split: ptyp.splits list.splits if_splits)
  have "body_type env T0 = body_type env D" by (rule body_type_devar[OF dv])
  also have "\<dots> = body_type env R'" by (subst body_type.simps) (simp add: DA)
  also have "\<dots> = body_type env R" by (rule Cons.IH[OF r ha])
  finally show ?case .
qed

text \<open>A term whose type, modulo the type environment, is not a function type is saturated:\<close>

lemma satd_intro:
  assumes fw: "ok (fastype env rb w) W'" and dv: "ok (devar (tyenv env) W') W"
    and bW: "ok (body_type env W) W" and nab: "\<not> is_Abs (head_of w)"
  shows "satd env rb w"
proof -
  define h where "h = fst (strip_comb w)"
  define args where "args = snd (strip_comb w)"
  have w: "w = h \<degree>\<degree> args" by (rule strip_comb_apps) (simp add: h_def args_def)
  have nh: "\<not> is_Abs h" using nab by (simp add: h_def fst_strip_comb)
  have "U = tsubst \<rho> B"
    if T0: "ok (fastype env rb h) T0" and B: "ok (body_type env T0) B" and tsol: "tsol (tyenv env) \<rho>"
      and bs: "bs_env \<rho> e rb" and ty: "e \<turnstile> inst \<rho> w : U" for T0 B \<rho> e U
  proof -
    have "body_type env T0 = body_type env W'"
      by (rule env_fastype_apps_body_type[OF fw[unfolded fastype_def w] T0[unfolded fastype_def]])
    also have "\<dots> = body_type env W" by (rule body_type_devar[OF dv])
    finally have "B = W" using B bW by simp
    moreover have "tsubst \<rho> W' = U" by (rule fastype_sound[OF fw tsol bs ty])
    moreover have "tsubst \<rho> W = tsubst \<rho> W'" by (rule devar_sound[OF dv refl tsol])
    ultimately show ?thesis by simp
  qed
  with nh show ?thesis
    by (subst satd.simps) (auto simp: h_def split: pterm.splits)
qed

lemma integer_of_nat_nat_of_integer: "0 \<le> i \<Longrightarrow> integer_of_nat (nat_of_integer i) = i"
  by (simp add: integer_eq_iff integer_reps)

lemma ok_nth_nat: "ok (nth xs (integer_of_nat n)) x \<longleftrightarrow> n < length xs \<and> x = xs ! n"
  by (simp add: ok_nth ilength_eq integer_of_nat_less integer_of_nat_nonneg)

lemma env_fastype_incr_bv:
  "ok (env_fastype env Ts t) T \<Longrightarrow> 0 \<le> lev \<Longrightarrow> nat_of_integer lev \<le> length Ts \<Longrightarrow>
    ok (env_fastype env (take (nat_of_integer lev) Ts @ U # drop (nat_of_integer lev) Ts)
      (incr_bv 1 lev t)) T"
proof (induction t arbitrary: Ts lev T)
  case (Bound i)
  have nh: False if "ok (case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound i])
      | _ \<Rightarrow> raise e) y" for e and y :: ptyp
    using that by (cases e) auto
  from Bound.prems(1) have "ok (nth Ts i) T" by (auto simp: ok_handle dest: nh)
  then have i: "0 \<le> i" "i < ilength Ts" "T = Ts ! nat_of_integer i" by (simp_all add: ok_nth)
  define n where "n = nat_of_integer i"
  define l where "l = nat_of_integer lev"
  have n: "i = integer_of_nat n" using i(1) by (simp add: n_def integer_of_nat_nat_of_integer)
  have l: "lev = integer_of_nat l" using Bound.prems(2) by (simp add: l_def integer_of_nat_nat_of_integer)
  have nl: "n < length Ts" "l \<le> length Ts" using i(2) Bound.prems(3)
    by (simp_all add: n ilength_eq integer_of_nat_less l_def)
  let ?Ts = "take l Ts @ U # drop l Ts"
  show ?case
  proof (cases "lev \<le> i")
    case True
    then have ln: "l \<le> n" using integer_of_nat_less[of n l] by (auto simp: n l)
    have "ok (nth ?Ts (integer_of_nat (Suc n))) T"
      using nl ln i(3) by (simp add: ok_nth_nat nth_append n_def[symmetric] Suc_diff_le)
    moreover have "i + 1 = integer_of_nat (Suc n)" by (simp add: n integer_eq_iff integer_reps)
    ultimately show ?thesis using True by (simp add: ok_handle l_def[symmetric])
  next
    case False
    then have ln: "n < l" using integer_of_nat_less[of n l] by (auto simp: n l)
    have "ok (nth ?Ts (integer_of_nat n)) T"
      using nl ln i(3) by (simp add: ok_nth_nat nth_append n_def[symmetric])
    then show ?thesis using False by (simp add: ok_handle l_def[symmetric] n)
  qed
next
  case (Abs a T' b)
  from Abs.prems(1) obtain U' where b: "ok (env_fastype env (T' # Ts) b) U'" and T: "T = T' \<rightarrow>\<^sub>T U'"
    by auto
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using Abs.prems(2) by (simp add: integer_reps)
  with Abs.IH[OF b, of "lev + 1"] Abs.prems(2,3) T show ?case by simp
next
  case (App f u)
  let ?Ts = "take (nat_of_integer lev) Ts @ U # drop (nat_of_integer lev) Ts"
  from App.prems(1) obtain T0 T' where f: "ok (env_fastype env Ts f) T0"
    and d: "ok (devar (tyenv env) T0) T'"
    and r: "ok (case T' of
        Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
          else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by auto
  from r obtain A where T': "T' = A \<rightarrow>\<^sub>T T"
    by (auto split: ptyp.splits list.splits if_splits)
  from App.IH(1)[OF f] App.prems(2,3) have "ok (env_fastype env ?Ts (incr_bv 1 lev f)) T0" by simp
  with d T' show ?case by simp
qed simp_all

lemma fastype_incr_boundvars:
  "ok (fastype env rb t) T \<Longrightarrow> ok (fastype env (b # rb) (incr_boundvars 1 t)) T"
  using env_fastype_incr_bv[of env "map snd rb" t T 0 "snd b"] by (simp add: fastype_def incr_boundvars_def)


subsection \<open>\<open>\<eta>\<close>-normalization saturates\<close>

lemma satd_Abs_intro: "satd env ((a, T) # rb) b \<Longrightarrow> satd env rb (Abs a T b)"
  by (subst satd.simps) (simp add: strip_comb_def)

lemma etif_satd:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> tye = tyenv env \<Longrightarrow> ok (fastype env rb t) T0 \<Longrightarrow> devar tye T0 = devar tye T \<Longrightarrow>
    \<not> is_Abs t \<Longrightarrow> head_nf t \<Longrightarrow> satd env rb t'"
  using assms
proof (induction tye T t r arbitrary: t' rb T0 rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  have na: "\<not> is_Abs (head_of t)" using "1.prems"(5,6) by (simp add: head_nf_nonAbs)
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by auto
    have "devar tye T0 = return T" using "1.prems"(4) T by (simp add: devar_nonTVar)
    with fastype_incr_boundvars[OF "1.prems"(3), of "(STR '''', T1)"] T "1.prems"(2)
    have f: "ok (fastype env ((STR '''', T1) # rb) (incr_boundvars 1 t $ Bound 0)) U"
      by (simp add: fastype_def)
    have h: "head_nf (incr_boundvars 1 t $ Bound 0)"
      using na by (simp add: incr_boundvars_def is_Abs_head_of_incr_bv)
    from "1.IH"[OF u refl "1.prems"(2) f refl _ h] t' show ?thesis by (simp add: satd_Abs_intro)
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup tye v S) r'"
        and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with rest have t': "t' = t" by simp
        from lk None have dv: "devar tye T = return T" using TVar by (subst devar.simps) (simp add: bindM_def)
        from lk None have bT: "ok (body_type env T) T" using TVar "1.prems"(2)
          by (subst body_type.simps) (simp add: bindM_def)
        have "satd env rb t" by (rule satd_intro[OF "1.prems"(3) _ bT na]) (use dv "1.prems"(2,4) in simp)
        with t' show ?thesis by simp
      next
        case (Some T')
        with rest have e: "ef tye T' t = Some (Ok t')" by simp
        have "devar tye T0 = devar tye T'" using "1.prems"(4) devar_TVar_Some[OF lk[unfolded Some]] TVar
          by simp
        from "1.IH"[OF e refl "1.prems"(2,3) this "1.prems"(5,6)] show ?thesis .
      qed
    next
      case (Type a Us)
      with nf "1.hyps" "1.prems"(1) have t': "t' = t" by (auto split: list.splits if_splits)
      have dv: "devar tye T = return T" by (simp add: devar_nonTVar Type)
      have bT: "ok (body_type env T) T" using nf Type
        by (subst body_type.simps) (auto split: list.splits)
      have "satd env rb t" by (rule satd_intro[OF "1.prems"(3) _ bT na]) (use dv "1.prems"(2,4) in simp)
      with t' show ?thesis by simp
    next
      case (TFree a S)
      with "1.hyps" "1.prems"(1) have t': "t' = t" by simp
      have dv: "devar tye T = return T" by (simp add: devar_nonTVar TFree)
      have bT: "ok (body_type env T) T" using TFree by (subst body_type.simps) simp
      have "satd env rb t" by (rule satd_intro[OF "1.prems"(3) _ bT na]) (use dv "1.prems"(2,4) in simp)
      with t' show ?thesis by simp
    qed
  qed
qed

lemma eta_norm_satd: "ok (eta_norm env rb t) t' \<Longrightarrow> head_nf t \<Longrightarrow> satd env rb t'"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  from Abs.prems obtain b' where "ok (eta_norm env ((a, T) # rb) body) b'" "t' = Abs a T b'" by auto
  with Abs.IH[of "(a, T) # rb" b'] Abs.prems(2) show ?case by (simp add: satd_Abs_intro)
qed (auto simp: eta_norm_nonAbs intro: etif_satd[OF _ refl refl])

text \<open>The hypothesis \<open>eta_hyp\<close> of the soundness of the search:\<close>

theorem head_norm_eta_norm_satd:
  "ok (head_norm env t) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
  using eta_norm_satd head_norm_head_nf[OF _ refl] by blast


subsection \<open>The shape of the flex-rigid pairs of \<open>SIMPL\<close>\<close>

lemma etif_head_nf:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> head_nf t \<Longrightarrow> head_nf t'"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by auto
    have "head_nf (incr_boundvars 1 t $ Bound 0)"
      using "1.prems"(2,3) by (simp add: head_nf_nonAbs incr_boundvars_def is_Abs_head_of_incr_bv)
    from "1.IH"[OF u refl _ this] t' show ?thesis by simp
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where
        rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by auto
      show ?thesis
      proof (cases r')
        case None
        with rest "1.prems" show ?thesis by simp
      next
        case (Some T')
        with rest "1.IH"[of tye T' t "Ok t'" t'] "1.prems" show ?thesis by simp
      qed
    next
      case (Type a Ts)
      with nf "1.hyps" "1.prems" show ?thesis by (auto split: list.splits if_splits)
    qed (use "1.hyps" "1.prems" in simp_all)
  qed
qed

lemma eta_norm_head_nf: "ok (eta_norm env rb t) t' \<Longrightarrow> head_nf t \<Longrightarrow> head_nf t'"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  then show ?case by auto
qed (auto simp: eta_norm_nonAbs intro: etif_head_nf[OF _ refl])

lemma head_nf_strip_abs_body: "head_nf t \<Longrightarrow> head_nf (strip_abs_body t)"
  by (induction t rule: strip_abs_body.induct) auto

lemma new_dpair_shape:
  "okW (new_dpair alg' rb t u env) ((rb', t', u'), env') \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and> \<not> is_Abs t' \<and> \<not> is_Abs u'"
proof (induction alg' rb t u env rule: new_dpair.induct)
  case (1 alg' rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg' T U env) env1"
    and rec: "okW (new_dpair alg' ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  from "1.IH"[OF cu c_def rec] show ?case by auto
qed auto

lemma head_norm_dpair_shape:
  assumes "okW (head_norm_dpair alg' env dp) ((rb', t', u'), env')"
  shows "head_nf t' \<and> head_nf u' \<and> \<not> is_Abs t' \<and> \<not> is_Abs u'"
proof -
  obtain bs t u where dp: "dp = (bs, t, u)" by (cases dp)
  from assms obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env bs t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env bs u1) u2" and
    nd: "okW (new_dpair alg' bs t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def dp)
  have "head_nf t2" by (rule eta_norm_head_nf[OF et head_norm_head_nf[OF ht refl]])
  moreover have "head_nf u2" by (rule eta_norm_head_nf[OF eu head_norm_head_nf[OF hu refl]])
  moreover have sh: "t' = strip_abs_body t2" "u' = strip_abs_body u2" "\<not> is_Abs t'" "\<not> is_Abs u'"
    using new_dpair_shape[OF nd] by blast+
  ultimately show ?thesis using head_nf_strip_abs_body by metis
qed

text \<open>
  The flexible side of a flex-rigid pair is not an abstraction and has a variable head; the rigid
  side is a head normal form and not an abstraction. These are syntactic properties, kept by all
  later changes of the environment.
\<close>

definition frs_shape :: "dpair \<Rightarrow> bool" where
  "frs_shape dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> is_Var (head_of t) \<and> \<not> is_Abs t \<and> \<not> is_Abs u \<and> head_nf u)"

lemma simrands_frs:
  "(\<And>dp env ffs frs env' ffs' frs'. okW (f dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)) \<Longrightarrow>
    okW (simrands f bs u0 s t st) st' \<Longrightarrow>
    \<exists>b. snd (snd st') = b @ snd (snd st) \<and> (\<forall>x\<in>set b. frs_shape x)"
proof (induction f bs u0 s t st arbitrary: st' rule: simrands.induct)
  case (1 f bs u0 f1 s1 g1 t1 st)
  from "1.prems"(2) obtain st1 where r1: "okW (simrands f bs u0 f1 g1 st) st1"
    and r2: "okW (f (bs, s1, t1) st1) st'"
    by auto
  have "\<exists>b. snd (snd st1) = b @ snd (snd st) \<and> (\<forall>x\<in>set b. frs_shape x)"
    by (rule "1.IH"[OF _ r1]) (erule "1.prems"(1))
  then obtain b1 where b1: "snd (snd st1) = b1 @ snd (snd st)"
    "\<forall>x\<in>set b1. frs_shape x" by blast
  obtain env1 ffs1 frs1 where st1e: "st1 = (env1, ffs1, frs1)" by (cases st1)
  obtain env' ffs' frs' where st'e: "st' = (env', ffs', frs')" by (cases st')
  from "1.prems"(1)[OF r2[unfolded st1e st'e]] obtain b2 where
    "frs' = b2 @ frs1" "\<forall>x\<in>set b2. frs_shape x" by blast
  with b1 st1e st'e have "snd (snd st') = (b2 @ b1) @ snd (snd st) \<and> (\<forall>x\<in>set (b2 @ b1). frs_shape x)"
    by auto
  then show ?case by blast
qed auto

lemma SIMPL0_rest_frs:
  assumes IH: "\<And>dp env ffs frs env' ffs' frs'. okW (simpl alg' dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
      \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
    and r: "okW (SIMPL0_rest simpl alg' bs t u env ffs frs) (env', ffs', frs')"
    and sh: "head_nf t" "head_nf u" "\<not> is_Abs t" "\<not> is_Abs u"
  shows "\<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
proof (cases "is_Var (head_of t) \<or> is_Var (head_of u)")
  case True
  then consider (FF) "is_Var (head_of t)" "is_Var (head_of u)"
    | (FR) "is_Var (head_of t)" "\<not> is_Var (head_of u)"
    | (RF) "\<not> is_Var (head_of t)" "is_Var (head_of u)"
    by blast
  then show ?thesis
  proof cases
    case FF
    then obtain x T y U where "head_of t = Var x T" "head_of u = Var y U"
      by (cases "head_of t"; cases "head_of u") auto
    with r have "frs' = frs" by (auto simp: SIMPL0_rest_def)
    then show ?thesis by simp
  next
    case FR
    then obtain x T where ht: "head_of t = Var x T" by (cases "head_of t") auto
    have "okW (handleW (do {env' \<leftarrow> assignment alg' bs t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, t, u) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r ht FR(2) by (cases "head_of u") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] have "frs' = [] @ frs \<or> frs' = [(bs, t, u)] @ frs" by auto
    moreover have "frs_shape (bs, t, u)" using FR sh by (simp add: frs_shape_def)
    ultimately show ?thesis by (metis empty_iff empty_set set_ConsD)
  next
    case RF
    then obtain y U where hu: "head_of u = Var y U" by (cases "head_of u") auto
    have "okW (handleW (do {env' \<leftarrow> assignment alg' bs u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (bs, u, t) # frs) | _ \<Rightarrow> raiseW e)) (env', ffs', frs')"
      using r hu RF(1) by (cases "head_of t") (simp_all add: SIMPL0_rest_def)
    from assign_handle_sound[OF this] have "frs' = [] @ frs \<or> frs' = [(bs, u, t)] @ frs" by auto
    moreover have "frs_shape (bs, u, t)" using RF sh by (simp add: frs_shape_def)
    ultimately show ?thesis by (metis empty_iff empty_set set_ConsD)
  qed
next
  case False
  then have "\<exists>env1. okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')"
    using r by (cases "head_of t"; cases "head_of u") (auto simp: SIMPL0_rest_def split: if_splits)
  then obtain env1 where "okW (simrands (simpl alg') bs u t u (env1, ffs, frs)) (env', ffs', frs')" by blast
  from simrands_frs[OF IH this] show ?thesis by simp
qed

lemma SIMPL0_frs_aux:
  assumes "SIMPL0 alg' dp st = Some r"
  shows "snd r = UOk (env', ffs', frs') \<Longrightarrow> st = (env, ffs, frs) \<Longrightarrow>
    \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
  using assms
proof (induction alg' dp st r arbitrary: env ffs frs env' ffs' frs' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 simpl alg' dp0 st r)
  have IH: "\<exists>b. frs2 = b @ frs1 \<and> (\<forall>x\<in>set b. frs_shape x)"
    if "okW (simpl alg' dp (env1, ffs1, frs1)) (env2, ffs2, frs2)" for dp env1 ffs1 frs1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' dp (env1, ffs1, frs1) = Some (evs, UOk (env2, ffs2, frs2))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  have "\<exists>bs t u env1. okW (head_norm_dpair alg' env dp0) ((bs, t, u), env1) \<and>
      okW (SIMPL0_rest simpl alg' bs t u env1 ffs frs) (env', ffs', frs')"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] "1.prems"(2) by (auto simp: SIMPL0_rest_def split: prod.splits)
  then obtain bs t u env1 where hn: "okW (head_norm_dpair alg' env dp0) ((bs, t, u), env1)"
    and rest: "okW (SIMPL0_rest simpl alg' bs t u env1 ffs frs) (env', ffs', frs')"
    by blast
  from head_norm_dpair_shape[OF hn] have "head_nf t" "head_nf u" "\<not> is_Abs t" "\<not> is_Abs u" by simp_all
  from SIMPL0_rest_frs[OF IH rest this] show ?case .
qed

lemma SIMPL0_frs:
  "okW (SIMPL0 alg' dp (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
  using SIMPL0_frs_aux by fastforce

lemma foldrW_SIMPL0_frs:
  "okW (foldrW (SIMPL0 alg') dps (env, ffs, frs)) (env', ffs', frs') \<Longrightarrow>
    \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
proof (induction dps arbitrary: env' ffs' frs')
  case (Cons dp dps)
  from Cons.prems obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg') dps (env, ffs, frs)) (env1, ffs1, frs1)"
    and s: "okW (SIMPL0 alg' dp (env1, ffs1, frs1)) (env', ffs', frs')"
    by auto
  from Cons.IH[OF f] obtain b1 where b1: "frs1 = b1 @ frs" "\<forall>x\<in>set b1. frs_shape x" by blast
  from SIMPL0_frs[OF s] obtain b2 where b2: "frs' = b2 @ frs1" "\<forall>x\<in>set b2. frs_shape x" by blast
  from b1 b2 have "frs' = (b2 @ b1) @ frs \<and> (\<forall>x\<in>set (b2 @ b1). frs_shape x)" by auto
  then show ?case by blast
qed simp

lemma SIMPL_frs_aux:
  assumes "SIMPL alg' env dps = Some r"
  shows "snd r = UOk (env', ffs, frs) \<Longrightarrow> \<forall>x\<in>set frs. frs_shape x"
  using assms
proof (induction alg' env dps r arbitrary: env' ffs frs rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl alg' env dps r)
  have IH: "\<forall>x\<in>set frs2. frs_shape x"
    if "okW (simpl alg' env1 dps1) (env2, ffs2, frs2)" for env1 dps1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' env1 dps1 = Some (evs, UOk (env2, ffs2, frs2))" by blast
    from "1.IH"[OF this] show ?thesis by simp
  qed
  have "\<exists>env1 ffs1 frs1. okW (foldrW (SIMPL0 alg') dps (env, [], [])) (env1, ffs1, frs1) \<and>
      (okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1))"
    using okW_of_Some[OF "1.hyps" "1.prems"(1)] by (auto simp: Let_def split: prod.splits if_splits)
  then obtain env1 ffs1 frs1 where f: "okW (foldrW (SIMPL0 alg') dps (env, [], [])) (env1, ffs1, frs1)"
    and rest: "okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs) \<or> (env', ffs, frs) = (env1, ffs1, frs1)"
    by blast
  from foldrW_SIMPL0_frs[OF f] have "\<forall>x\<in>set frs1. frs_shape x" by auto
  from rest show ?case
  proof
    assume "okW (simpl alg' env1 (frs1 @ ffs1)) (env', ffs, frs)"
    from IH[OF this] show ?thesis .
  qed (use \<open>\<forall>x\<in>set frs1. frs_shape x\<close> in simp)
qed

theorem SIMPL_frs_shape:
  "okW (SIMPL alg' env dps) (env', ffs, dp # frs) \<Longrightarrow> frs_shape dp"
  using SIMPL_frs_aux by fastforce


subsection \<open>Type unification equates the numbers of binder types\<close>

text \<open>
  For well-formed types, \<^const>\<open>type_unify\<close> makes the two types equal modulo the resulting type
  environment, not only under its solutions: in particular, they have as many binder types, in
  every extension of the type environment (\<open>tspine\<close>).
\<close>

lemma textends_lookup: "textends \<theta> \<theta>' \<Longrightarrow> vt_lookup \<theta> v = Some x \<Longrightarrow> vt_lookup \<theta>' v = Some x"
  unfolding textends_def by blast

lemma devar_textends_eq:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok D \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> devar \<theta>' T = devar \<theta>' D"
  using assms
proof (induction \<theta> T r arbitrary: D rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) D"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis by simp
    next
      case (Some U)
      with rest have "dv \<theta> U = Some (Ok D)" by simp
      from "1.IH"[OF this refl "1.prems"(2)] have IH: "devar \<theta>' U = devar \<theta>' D" .
      from lk Some have "vt_lookup \<theta> ixn = Some (S, U)" by (auto simp: ok_type_lookup split: option.splits)
      with "1.prems"(2) have "vt_lookup \<theta>' ixn = Some (S, U)" by (rule textends_lookup)
      then have "ok (type_lookup \<theta>' ixn S) (Some U)" by (simp add: ok_type_lookup)
      from devar_TVar_Some[OF this] IH TVar show ?thesis by simp
    qed
  qed (use "1.hyps" "1.prems"(1) in simp_all)
qed

lemma devar_bound: "vt_lookup \<theta> w = Some (S, X) \<Longrightarrow> devar \<theta> (TVar w S) = devar \<theta> X"
  by (rule devar_TVar_Some) (simp add: ok_type_lookup)

lemma binder_types_devar_aux:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok D \<Longrightarrow> \<theta> = tyenv env \<Longrightarrow> binder_types env T = binder_types env D"
  using assms
proof (induction \<theta> T r arbitrary: D rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) D"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest show ?thesis by simp
    next
      case (Some U)
      with rest have "dv \<theta> U = Some (Ok D)" by simp
      from "1.IH"[OF this refl "1.prems"(2)] lk Some TVar "1.prems"(2) show ?thesis
        by (subst binder_types.simps) (simp add: bindM_def)
    qed
  qed (use "1.hyps" "1.prems" in simp_all)
qed

lemma binder_types_devar: "ok (devar (tyenv env) T) D \<Longrightarrow> binder_types env T = binder_types env D"
  using binder_types_devar_aux by blast

lemma binder_types_ok_devar:
  assumes "binder_types env T = Some r"
  shows "r = Ok Ts \<Longrightarrow> \<exists>D. ok (devar (tyenv env) T) D"
  using assms
proof (induction env T r arbitrary: Ts rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) ixn S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Ts"
      by auto
    show ?thesis
    proof (cases r')
      case None
      have "devar (tyenv env) T = return T" using lk None TVar by (subst devar.simps) (simp add: bindM_def)
      then show ?thesis by (simp add: return_def)
    next
      case (Some T')
      with rest have "bt env T' = Some (Ok Ts)" by simp
      from "1.IH"[OF this refl] devar_TVar_Some[OF lk[unfolded Some]] TVar show ?thesis by simp
    qed
  qed (simp_all add: devar_nonTVar return_def)
qed

definition tspine :: "tyenv \<Rightarrow> ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tspine \<theta> T U \<longleftrightarrow> (\<forall>env Ts Us. textends \<theta> (tyenv env) \<longrightarrow> ok (binder_types env T) Ts \<longrightarrow>
    ok (binder_types env U) Us \<longrightarrow> length Ts = length Us)"

lemma tspine_sym: "tspine \<theta> T U \<Longrightarrow> tspine \<theta> U T"
  unfolding tspine_def by metis

lemma tspine_devar:
  assumes "\<And>\<theta>'. textends \<theta> \<theta>' \<Longrightarrow> devar \<theta>' T = devar \<theta>' U"
  shows "tspine \<theta> T U"
  unfolding tspine_def
proof (intro allI impI)
  fix env Ts Us assume ext: "textends \<theta> (tyenv env)" and bT: "ok (binder_types env T) Ts"
    and bU: "ok (binder_types env U) Us"
  from binder_types_ok_devar[OF bT refl] obtain D where dT: "ok (devar (tyenv env) T) D" by blast
  have dU: "ok (devar (tyenv env) U) D" using assms[OF ext] dT by simp
  from bT bU binder_types_devar[OF dT] binder_types_devar[OF dU] show "length Ts = length Us" by simp
qed

lemma tspine_devar_trans:
  assumes dT: "ok (devar \<theta> ty1) T" and dU: "ok (devar \<theta> ty2) U" and ext: "textends \<theta> \<theta>'"
    and sp: "tspine \<theta>' T U"
  shows "tspine \<theta>' ty1 ty2"
  unfolding tspine_def
proof (intro allI impI)
  fix env Ts Us assume ext': "textends \<theta>' (tyenv env)" and bT: "ok (binder_types env ty1) Ts"
    and bU: "ok (binder_types env ty2) Us"
  have ext'': "textends \<theta> (tyenv env)" by (rule textends_trans[OF ext ext'])
  have "ok (binder_types env T) Ts"
  proof -
    from binder_types_ok_devar[OF bT refl] obtain D where d: "ok (devar (tyenv env) ty1) D" by blast
    have d': "ok (devar (tyenv env) T) D" using d devar_textends_eq[OF dT refl ext''] by simp
    from bT show ?thesis using binder_types_devar[OF d] binder_types_devar[OF d'] by simp
  qed
  moreover have "ok (binder_types env U) Us"
  proof -
    from binder_types_ok_devar[OF bU refl] obtain D where d: "ok (devar (tyenv env) ty2) D" by blast
    have d': "ok (devar (tyenv env) U) D" using d devar_textends_eq[OF dU refl ext''] by simp
    from bU show ?thesis using binder_types_devar[OF d] binder_types_devar[OF d'] by simp
  qed
  ultimately show "length Ts = length Us" using sp ext' unfolding tspine_def by blast
qed

lemma binder_types_Type_devar:
  "ok (devar \<theta> T) (Type a Ts0) \<Longrightarrow> textends \<theta> (tyenv env) \<Longrightarrow>
    binder_types env T = binder_types env (Type a Ts0)"
  using devar_textends_eq[of \<theta> T "Ok (Type a Ts0)" "Type a Ts0" "tyenv env"]
  by (intro binder_types_devar) (simp add: devar_nonTVar return_def)

lemma tspine_fun:
  assumes dT: "ok (devar \<theta> T) (A1 \<rightarrow>\<^sub>T R1)" and dU: "ok (devar \<theta> U) (A2 \<rightarrow>\<^sub>T R2)"
    and sp: "tspine \<theta> R1 R2"
  shows "tspine \<theta> T U"
  unfolding tspine_def
proof (intro allI impI)
  fix env Ts Us assume ext: "textends \<theta> (tyenv env)" and bT: "ok (binder_types env T) Ts"
    and bU: "ok (binder_types env U) Us"
  from bT[unfolded binder_types_Type_devar[OF dT ext]] obtain Ts' where
    Ts: "Ts = A1 # Ts'" and bT': "ok (binder_types env R1) Ts'"
    by (subst (asm) binder_types.simps) auto
  from bU[unfolded binder_types_Type_devar[OF dU ext]] obtain Us' where
    Us: "Us = A2 # Us'" and bU': "ok (binder_types env R2) Us'"
    by (subst (asm) binder_types.simps) auto
  from sp ext bT' bU' have "length Ts' = length Us'" unfolding tspine_def by blast
  with Ts Us show "length Ts = length Us" by simp
qed

lemma tspine_Type:
  assumes dT: "ok (devar \<theta> T) (Type a Ts0)" and dU: "ok (devar \<theta> U) (Type a Us0)"
    and a: "a \<noteq> STR ''fun''"
  shows "tspine \<theta> T U"
  unfolding tspine_def
proof (intro allI impI)
  fix env Ts Us assume ext: "textends \<theta> (tyenv env)" and bT: "ok (binder_types env T) Ts"
    and bU: "ok (binder_types env U) Us"
  from bT[unfolded binder_types_Type_devar[OF dT ext]] a have "Ts = []"
    by (subst (asm) binder_types.simps) (auto split: list.splits)
  moreover from bU[unfolded binder_types_Type_devar[OF dU ext]] a have "Us = []"
    by (subst (asm) binder_types.simps) (auto split: list.splits)
  ultimately show "length Ts = length Us" by simp
qed

lemma update_new_devar:
  "ok (update_new (v, (S, U)) \<theta>) \<theta>1 \<Longrightarrow> textends \<theta>1 \<theta>' \<Longrightarrow> devar \<theta>' (TVar v S) = devar \<theta>' U"
  by (rule devar_bound, rule textends_lookup) (auto simp: ok_update_new)

lemma unify_aux_tspine:
  assumes "unify_aux alg' T U st = Some r"
  shows "r = Ok st' \<Longrightarrow> textends (fst st) (fst st') \<and>
    (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow> tspine (fst st') T U)"
  using assms
proof (induction alg' T U st r arbitrary: st' rule: unify_aux.raw_induct[rotated, consumes 1])
  case (1 ua alg' ty1 ty2 st r)
  obtain \<theta> n where st: "st = (\<theta>, n)" by (cases st)
  from "1.hyps"[unfolded "1.prems"(1) st] obtain T U where
    T: "ok (devar \<theta> ty1) T" and U: "ok (devar \<theta> ty2) U" and
    rest: "ok (case (T, U) of
        (TVar v S1, TVar w S2) \<Rightarrow>
          if v = w then (if S1 = S2 then return (\<theta>, n) else tvar_clash v S1 S2)
          else if sort_le alg' S1 S2 then do {tye' \<leftarrow> update_new (w, (S2, T)) \<theta>; return (tye', n)}
          else if sort_le alg' S2 S1 then do {tye' \<leftarrow> update_new (v, (S1, U)) \<theta>; return (tye', n)}
          else do {
            let (S, cnt') = gen_tyvar (inter_sort alg' S1 S2) n;
            tye' \<leftarrow> update_new (w, (S2, S)) \<theta>;
            tye'' \<leftarrow> update_new (v, (S1, S)) tye';
            return (tye'', cnt')}
      | (TVar v S, _) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> U;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, U)) \<theta>; meet alg' U S (tye', n)}}
      | (_, TVar v S) \<Rightarrow> do {
          b \<leftarrow> type_occurs v \<theta> T;
          if b then raise TUnify else do {tye' \<leftarrow> update_new (v, (S, T)) \<theta>; meet alg' T S (tye', n)}}
      | (Type a Ts, Type b Us) \<Rightarrow>
          if a \<noteq> b then raise TUnify
          else foldM (\<lambda>(T, U) st. ua alg' T U st) (zip Ts Us) (\<theta>, n)
      | _ \<Rightarrow> if T = U then return (\<theta>, n) else raise TUnify) st'"
    by (auto simp: Let_def)
  have same: "tspine \<theta>' T U" if "T = U" for \<theta>' by (rule tspine_devar) (simp add: that)
  text \<open>It suffices to show the claim for the results of \<open>devar\<close>.\<close>
  have "textends \<theta> (fst st') \<and>
    (\<forall>\<rho>. tsol (fst st') \<rho> \<longrightarrow> wft ar (tsubst \<rho> T) \<longrightarrow> wft ar (tsubst \<rho> U) \<longrightarrow> tspine (fst st') T U)"
  proof (cases T)
    case T_TVar: (TVar v S1)
    show ?thesis
    proof (cases U)
      case (TVar w S2)
      show ?thesis
      proof (cases "v = w")
        case True
        with T_TVar TVar rest have "S1 = S2" "st' = (\<theta>, n)" by (auto simp: tvar_clash_def split: if_splits)
        with True T_TVar TVar show ?thesis using same by simp
      next
        case False
        consider (le) "sort_le alg' S1 S2" | (ge) "\<not> sort_le alg' S1 S2" "sort_le alg' S2 S1"
          | (new) "\<not> sort_le alg' S1 S2" "\<not> sort_le alg' S2 S1"
          by blast
        then show ?thesis
        proof cases
          case le
          with False T_TVar TVar rest obtain \<theta>1 where
            u: "ok (update_new (w, (S2, T)) \<theta>) \<theta>1" and st': "st' = (\<theta>1, n)"
            by auto
          have "tspine \<theta>1 T U"
            by (rule tspine_devar) (use update_new_devar[OF u] TVar in simp)
          with textends_update_new[OF u] st' show ?thesis by simp
        next
          case ge
          with False T_TVar TVar rest obtain \<theta>1 where
            u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and st': "st' = (\<theta>1, n)"
            by auto
          have "tspine \<theta>1 T U"
            by (rule tspine_devar) (use update_new_devar[OF u] T_TVar in simp)
          with textends_update_new[OF u] st' show ?thesis by simp
        next
          case new
          let ?V = "TVar (aT, n + 1) (inter_sort alg' S1 S2)"
          from new False T_TVar TVar rest obtain \<theta>1 \<theta>2 where
            u1: "ok (update_new (w, (S2, ?V)) \<theta>) \<theta>1" and u2: "ok (update_new (v, (S1, ?V)) \<theta>1) \<theta>2"
            and st': "st' = (\<theta>2, n + 1)"
            by (auto simp: gen_tyvar_def)
          have e12: "textends \<theta>1 \<theta>2" by (rule textends_update_new[OF u2])
          have "tspine \<theta>2 T U"
          proof (rule tspine_devar)
            fix \<theta>' assume "textends \<theta>2 \<theta>'"
            with update_new_devar[OF u2] update_new_devar[OF u1 textends_trans[OF e12]] T_TVar TVar
            show "devar \<theta>' T = devar \<theta>' U" by simp
          qed
          with textends_trans[OF textends_update_new[OF u1] e12] st' show ?thesis by simp
        qed
      qed
    next
      case (Type b Us)
      with T_TVar rest obtain \<theta>1 where
        u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and m: "ok (meet alg' U S1 (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have e1: "textends \<theta>1 (fst st')" by simp
      have "tspine (fst st') T U"
      proof (rule tspine_devar)
        fix \<theta>' assume "textends (fst st') \<theta>'"
        with update_new_devar[OF u textends_trans[OF e1]] T_TVar show "devar \<theta>' T = devar \<theta>' U" by simp
      qed
      with textends_trans[OF textends_update_new[OF u] e1] show ?thesis by simp
    next
      case (TFree b S2)
      with T_TVar rest obtain \<theta>1 where
        u: "ok (update_new (v, (S1, U)) \<theta>) \<theta>1" and m: "ok (meet alg' U S1 (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have e1: "textends \<theta>1 (fst st')" by simp
      have "tspine (fst st') T U"
      proof (rule tspine_devar)
        fix \<theta>' assume "textends (fst st') \<theta>'"
        with update_new_devar[OF u textends_trans[OF e1]] T_TVar show "devar \<theta>' T = devar \<theta>' U" by simp
      qed
      with textends_trans[OF textends_update_new[OF u] e1] show ?thesis by simp
    qed
  next
    case T_Type: (Type a Ts)
    show ?thesis
    proof (cases U)
      case (TVar v S)
      with T_Type rest obtain \<theta>1 where
        u: "ok (update_new (v, (S, T)) \<theta>) \<theta>1" and m: "ok (meet alg' T S (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have e1: "textends \<theta>1 (fst st')" by simp
      have "tspine (fst st') T U"
      proof (rule tspine_devar)
        fix \<theta>' assume "textends (fst st') \<theta>'"
        with update_new_devar[OF u textends_trans[OF e1]] TVar show "devar \<theta>' T = devar \<theta>' U" by simp
      qed
      with textends_trans[OF textends_update_new[OF u] e1] show ?thesis by simp
    next
      case (Type b Us)
      with T_Type rest have "a = b"
        and f: "ok (foldM (\<lambda>(T, U) st. ua alg' T U st) (zip Ts Us) (\<theta>, n)) st'"
        by (auto split: if_splits)
      have "textends (fst st0) (fst st')"
        if "ok (foldM (\<lambda>(T, U) st. ua alg' T U st) ps st0) st'" for ps st0
        using that
      proof (induction rule: ok_foldM_induct)
        case (Cons p ps b b1 b')
        obtain T0 U0 where p: "p = (T0, U0)" by (cases p)
        with Cons.hyps(1) "1.IH" have "textends (fst b) (fst b1)" by simp
        with Cons.IH show ?case using textends_trans by blast
      qed simp
      from this[OF f] have ext: "textends \<theta> (fst st')" by simp
      have "tspine (fst st') T U"
        if \<rho>: "tsol (fst st') \<rho>" and wf: "wft ar (tsubst \<rho> T)" "wft ar (tsubst \<rho> U)" for \<rho>
      proof (cases "a = STR ''fun''")
        case True
        from wf T_Type Type True \<open>a = b\<close> obtain A1 R1 A2 R2 where Ts: "Ts = [A1, R1]" and Us: "Us = [A2, R2]"
          by (auto simp: tarity_def length_Suc_conv numeral_2_eq_2)
        from f Ts Us obtain st1 where "ok (ua alg' R1 R2 st1) st'" by auto
        from "1.IH"[OF this refl] \<rho> wf Ts Us T_Type Type have "tspine (fst st') R1 R2" by simp
        then show ?thesis
          by (rule tspine_fun[rotated 2]) (simp_all add: T_Type Type Ts Us True \<open>a = b\<close>[symmetric] devar_nonTVar return_def)
      next
        case False
        show ?thesis
          by (rule tspine_Type[OF _ _ False]) (simp_all add: T_Type Type \<open>a = b\<close>[symmetric] devar_nonTVar return_def)
      qed
      with ext show ?thesis by blast
    next
      case (TFree b S)
      with T_Type rest show ?thesis by (auto split: if_splits)
    qed
  next
    case T_TFree: (TFree a S)
    show ?thesis
    proof (cases U)
      case (TVar v S')
      with T_TFree rest obtain \<theta>1 where
        u: "ok (update_new (v, (S', T)) \<theta>) \<theta>1" and m: "ok (meet alg' T S' (\<theta>1, n)) st'"
        by (auto split: if_splits)
      from meet_textends[OF m] have e1: "textends \<theta>1 (fst st')" by simp
      have "tspine (fst st') T U"
      proof (rule tspine_devar)
        fix \<theta>' assume "textends (fst st') \<theta>'"
        with update_new_devar[OF u textends_trans[OF e1]] TVar show "devar \<theta>' T = devar \<theta>' U" by simp
      qed
      with textends_trans[OF textends_update_new[OF u] e1] show ?thesis by simp
    next
      case (TFree b S')
      with T_TFree rest have "T = U" "st' = (\<theta>, n)" by (auto split: if_splits)
      with same show ?thesis by simp
    qed (use T_TFree rest in \<open>auto split: if_splits\<close>)
  qed
  then have ext: "textends \<theta> (fst st')"
    and sp: "\<And>\<rho>. tsol (fst st') \<rho> \<Longrightarrow> wft ar (tsubst \<rho> T) \<Longrightarrow> wft ar (tsubst \<rho> U) \<Longrightarrow> tspine (fst st') T U"
    by blast+
  have "tspine (fst st') ty1 ty2"
    if \<rho>: "tsol (fst st') \<rho>" and wf: "wft ar (tsubst \<rho> ty1)" "wft ar (tsubst \<rho> ty2)" for \<rho>
  proof -
    have "tsubst \<rho> T = tsubst \<rho> ty1" "tsubst \<rho> U = tsubst \<rho> ty2"
      using devar_sound[OF T refl] devar_sound[OF U refl] tsol_textends[OF ext \<rho>] by blast+
    with sp[OF \<rho>] wf have "tspine (fst st') T U" by simp
    from tspine_devar_trans[OF T U ext this] show ?thesis .
  qed
  with ext show ?case unfolding st fst_conv by blast
qed

lemma cunify_types_tspine:
  assumes cu: "okW (cunify_types alg' T U env) env'" and \<rho>: "tsol (tyenv env') \<rho>"
    and wf: "wft ar (tsubst \<rho> T)" "wft ar (tsubst \<rho> U)"
  shows "tspine (tyenv env') T U"
proof -
  have u: "ok (unify_types alg' T U env) env'" using cu cunify_types_ok by blast
  show ?thesis
  proof (cases "T = U")
    case True
    then show ?thesis by (intro tspine_devar) simp
  next
    case False
    have nh: False if "ok (case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U)) | _ \<Rightarrow> raise e) y"
      for e and y :: env
      using that by (cases e) auto
    from u False obtain tye' n' where tu: "ok (type_unify alg' U T (tyenv env, maxidx env)) (tye', n')"
      and env': "env' = Envir n' (tenv env) tye'"
      by (auto simp: unify_types_def ok_handle split: prod.splits dest: nh)
    from unify_aux_tspine[OF tu[unfolded type_unify_def] refl] \<rho> wf env'
    show ?thesis by (auto intro: tspine_sym)
  qed
qed


subsection \<open>The hypothesis of \<open>MATCH\<close>\<close>

lemma env_fastype_apps_head: "ok (env_fastype env Ts (s \<degree>\<degree> bs)) R \<Longrightarrow> \<exists>R'. ok (env_fastype env Ts s) R'"
proof (induction bs arbitrary: s R)
  case (Cons b bs)
  from Cons.IH[of "s $ b"] Cons.prems show ?case by auto
qed auto

text \<open>The binder types of the type of the head of an application, in an extension of the type
  environment, consist of one type for each argument, followed by the binder types of its type:\<close>

lemma env_fastype_apps_binder_types:
  "ok (env_fastype env Ts (h \<degree>\<degree> args)) R \<Longrightarrow> ok (env_fastype env Ts h) H \<Longrightarrow>
    textends (tyenv env) (tyenv env') \<Longrightarrow> ok (binder_types env' H) Hs \<Longrightarrow>
    length args \<le> length Hs \<and> ok (binder_types env' R) (drop (length args) Hs)"
proof (induction args arbitrary: h H Hs)
  case Nil
  then show ?case by simp
next
  case (Cons a args)
  from Cons.prems(1) have r: "ok (env_fastype env Ts ((h $ a) \<degree>\<degree> args)) R" by simp
  from env_fastype_apps_head[OF r] obtain R' where ha: "ok (env_fastype env Ts (h $ a)) R'" by blast
  from ha Cons.prems(2) obtain D where dv: "ok (devar (tyenv env) H) D"
    and D: "ok (case D of
      Type b Vs \<Rightarrow> (case Vs of [_, U] \<Rightarrow> if b = STR ''fun'' then return U
        else raise (Term_Error funerr [h $ a]) | _ \<Rightarrow> raise (Term_Error funerr [h $ a]))
      | _ \<Rightarrow> raise (Term_Error funerr [h $ a])) R'"
    by auto
  from D obtain A where DA: "D = A \<rightarrow>\<^sub>T R'"
    by (auto split: ptyp.splits list.splits if_splits)
  from Cons.prems(4)[unfolded binder_types_Type_devar[OF dv[unfolded DA] Cons.prems(3)]]
  obtain Hs' where Hs: "Hs = A # Hs'" and bt': "ok (binder_types env' R') Hs'"
    by (subst (asm) binder_types.simps) auto
  from Cons.IH[OF r ha Cons.prems(3) bt'] Hs show ?case by simp
qed

text \<open>The type of an application is well-formed if the type of its head is:\<close>

lemma env_fastype_apps_wft:
  "ok (env_fastype env Ts (h \<degree>\<degree> args)) R \<Longrightarrow> ok (env_fastype env Ts h) H \<Longrightarrow>
    tsol (tyenv env) \<rho> \<Longrightarrow> wft ar (tsubst \<rho> H) \<Longrightarrow> wft ar (tsubst \<rho> R)"
proof (induction args arbitrary: h H)
  case Nil
  then show ?case by simp
next
  case (Cons a args)
  from Cons.prems(1) have r: "ok (env_fastype env Ts ((h $ a) \<degree>\<degree> args)) R" by simp
  from env_fastype_apps_head[OF r] obtain R' where ha: "ok (env_fastype env Ts (h $ a)) R'" by blast
  from ha Cons.prems(2) obtain D where dv: "ok (devar (tyenv env) H) D"
    and D: "ok (case D of
      Type b Vs \<Rightarrow> (case Vs of [_, U] \<Rightarrow> if b = STR ''fun'' then return U
        else raise (Term_Error funerr [h $ a]) | _ \<Rightarrow> raise (Term_Error funerr [h $ a]))
      | _ \<Rightarrow> raise (Term_Error funerr [h $ a])) R'"
    by auto
  from D obtain A where DA: "D = A \<rightarrow>\<^sub>T R'"
    by (auto split: ptyp.splits list.splits if_splits)
  have "tsubst \<rho> D = tsubst \<rho> H" by (rule devar_sound[OF dv refl Cons.prems(3)])
  with Cons.prems(4) have "wft ar (tsubst \<rho> D)" by simp
  with DA have "wft ar (tsubst \<rho> R')" by simp
  from Cons.IH[OF r ha Cons.prems(3) this] show ?case .
qed

lemma integer_of_nat_add: "integer_of_nat (m + n) = integer_of_nat m + integer_of_nat n"
  by (simp add: integer_eq_iff integer_reps)

text \<open>The type of an atom does not change when bound variables are inserted:\<close>

lemma env_fastype_incr_atom:
  assumes "\<not> is_Abs h" "\<not> (\<exists>f a. h = f $ a)" "ok (env_fastype env Ts h) H"
  shows "ok (env_fastype env' (Xs @ Ts) (incr_bv (ilength Xs) 0 h)) H"
proof (cases h)
  case (Bound i)
  have nh: False if "ok (case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound i])
      | _ \<Rightarrow> raise e) y" for e and y :: ptyp
    using that by (cases e) auto
  from assms(3) Bound have "ok (nth Ts i) H" by (auto simp: ok_handle dest: nh)
  then have i: "0 \<le> i" "i < ilength Ts" "H = Ts ! nat_of_integer i" by (simp_all add: ok_nth)
  define m where "m = nat_of_integer i"
  have m: "i = integer_of_nat m" using i(1) by (simp add: m_def integer_of_nat_nat_of_integer)
  have ml: "m < length Ts" using i(2) by (simp add: m ilength_eq integer_of_nat_less)
  have "ok (nth (Xs @ Ts) (integer_of_nat (length Xs + m))) H"
    using ml i(3) by (simp add: ok_nth_nat nth_append m_def[symmetric])
  moreover have "incr_bv (ilength Xs) 0 h = Bound (integer_of_nat (length Xs + m))"
    using i(1) by (simp add: Bound m ilength_eq integer_of_nat_add add.commute)
  ultimately show ?thesis by (simp add: ok_handle)
qed (use assms in simp_all)

lemma body_type_binder_types:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> \<exists>Ts. ok (binder_types env T) Ts"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (TVar ixn S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) ixn S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with lk TVar show ?thesis by (subst binder_types.simps) (simp add: bindM_def)
    next
      case (Some T')
      with rest have "bt env T' = Some (Ok B)" by simp
      from "1.IH"[OF this refl] lk Some TVar show ?thesis
        by (subst binder_types.simps) (simp add: bindM_def)
    qed
  next
    case (Type a Us)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Us = [T1, U])")
      case True
      then obtain T1 U where Us: "Us = [T1, U]" and a: "a = STR ''fun''" by auto
      from "1.hyps" "1.prems"(1) Type Us a have "bt env U = Some (Ok B)" by simp
      from "1.IH"[OF this refl] Type Us a show ?thesis by (subst binder_types.simps) auto
    next
      case False
      with Type show ?thesis by (subst binder_types.simps) (auto split: list.splits)
    qed
  next
    case (TFree a S)
    then show ?thesis by (subst binder_types.simps) simp
  qed
qed

text \<open>
  The hypothesis \<^const>\<open>MATCH_ok\<close> of \<open>MATCH\<close> holds for the flex-rigid pairs of \<open>SIMPL\<close>. Its
  saturation condition \<^const>\<open>rsat\<close> assumes that both sides are well-typed with the same type: for
  ill-typed pairs, it may fail. (An example: \<open>SIMPL\<close> on \<open>[([], k (x::?'c), k (x::\<alpha>\<Rightarrow>\<beta>)),
  ([], ?v a, f::?'c)]\<close> with \<open>?v :: P \<Rightarrow> Type ''fun'' [\<alpha>]\<close> keeps the second pair and binds
  \<open>?'c := \<alpha> \<Rightarrow> \<beta>\<close>; the unification of \<open>Type ''fun'' [\<alpha>]\<close> with \<open>?'c\<close> succeeds without a change,
  as \<^const>\<open>zip\<close> truncates the argument lists, and \<open>f\<close> has type \<open>\<alpha> \<Rightarrow> \<beta>\<close>, not the body type
  \<open>\<beta>\<close> of its type.)
\<close>

lemma satd_rsat: "\<not> is_Abs (fst (strip_comb u)) \<Longrightarrow> satd env rb u \<Longrightarrow> rsat env rb t u"
  unfolding rsat_def using satd_base by blast

theorem frs_shape_MATCH_ok:
  assumes sh: "frs_shape dp"
  shows "MATCH_ok env0 dp"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from sh have nAu: "\<not> is_Abs u" and hu: "head_nf u" by (simp_all add: frs_shape_def dp)
  have "msat_ok env2 (rb, t, u)"
    if T1: "ok (fastype env0 rb t) T1" and U1: "ok (fastype env0 rb u) U1"
      and cu: "okW (cunify_types alg' T1 U1 env0) env1" and ext: "extends env1 env2" for alg' T1 U1 env1 env2
    unfolding msat_ok_def prod.case
  proof (intro allI impI)
    fix v T targs Ts assume st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env2 T) Ts"
    have ext1: "extends env0 env1" by (rule cunify_types_sound(2)[OF cu])
    have ext02: "extends env0 env2" by (rule extends_trans[OF ext1 ext])
    have te02: "textends (tyenv env0) (tyenv env2)" and te12: "textends (tyenv env1) (tyenv env2)"
      using ext02 ext by (simp_all add: extends_def)
    have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
    have fv: "ok (env_fastype env0 (map snd rb) (Var v T)) T" by simp
    define Es where "Es = drop (length targs) Ts"
    from env_fastype_apps_binder_types[OF T1[unfolded fastype_def t] fv te02 bt]
    have len: "length targs \<le> length Ts" and bT1: "ok (binder_types env2 T1) Es"
      by (simp_all add: Es_def)
    define hu where "hu = fst (strip_comb u)"
    define uargs where "uargs = snd (strip_comb u)"
    have u: "u = hu \<degree>\<degree> uargs" by (rule strip_comb_apps) (simp add: hu_def uargs_def)
    have nAhu: "\<not> is_Abs hu" using nAu hu by (simp add: head_nf_nonAbs hu_def fst_strip_comb)
    have nApp: "\<not> (\<exists>f a. hu = f $ a)" using strip_comb_head[of u hu uargs] by (simp add: hu_def uargs_def)
    from env_fastype_apps_head[OF U1[unfolded fastype_def u]] obtain H
      where fH: "ok (env_fastype env0 (map snd rb) hu) H" by blast
    define k where "k = ilength Es"
    define rb' where "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb"
    define t' where "t' = incr_bv k 0 t \<degree>\<degree> bvs (length Es)"
    define u' where "u' = incr_bv k 0 u \<degree>\<degree> bvs (length Es)"
    define h' where "h' = incr_bv k 0 hu"
    define args' where "args' = map (incr_bv k 0) uargs @ bvs (length Es)"
    have ed: "eta_expand_dpair Es (rb, t, u) = (rb', t', u')"
      by (simp add: eta_expand_dpair_eq rb'_def t'_def u'_def k_def)
    have u': "u' = h' \<degree>\<degree> args'" by (simp add: u'_def h'_def args'_def u incr_bv_apps)
    have nApp': "\<not> (\<exists>f a. h' = f $ a)" and nAh': "\<not> is_Abs h'"
      using nApp nAhu by (cases hu; simp add: h'_def)+
    have sh': "fst (strip_comb u') = h'" by (simp add: u' strip_comb_atom_apps[OF nApp'])
    have mrb': "map snd rb' = rev Es @ map snd rb" by (simp add: rb'_def rev_map comp_def)
    have fh': "ok (fastype env2 rb' h') H"
      using env_fastype_incr_atom[OF nAhu nApp fH, of env2 "rev Es"]
      by (simp add: fastype_def mrb' h'_def k_def ilength_eq)
    have "rsat env2 rb' t' u'"
      unfolding rsat_def sh'
    proof (intro allI impI)
      fix T0 B \<rho> e U assume f0: "ok (fastype env2 rb' h') T0" and bB: "ok (body_type env2 T0) B"
        and tsol: "tsol (tyenv env2) \<rho>" and bs: "bs_env \<rho> e rb'"
        and tyt: "e \<turnstile> inst \<rho> t' : U" and tyu: "e \<turnstile> inst \<rho> u' : U"
      have T0: "T0 = H" using f0 fh' by simp
      have tsol0: "tsol (tyenv env0) \<rho>" by (rule extends_tsol[OF tsol ext02])
      have tsol1: "tsol (tyenv env1) \<rho>" by (rule extends_tsol[OF tsol ext])
      text \<open>The type of the head of the rigid side:\<close>
      from tyu[unfolded u' inst_apps] obtain Ws where tyh: "e \<turnstile> inst \<rho> h' : Ws \<Rrightarrow> U"
        and tyas: "e \<tturnstile> map (inst \<rho>) args' : Ws"
        by (rule list_app_typeE)
      have lWs: "length Ws = length uargs + length Es" using typings_nth[OF tyas] by (simp add: args'_def)
      have H: "tsubst \<rho> H = Ws \<Rrightarrow> U" by (rule fastype_sound[OF fh' tsol bs tyh])
      have "\<not> loose_bvar h' (ilength rb')"
      proof (cases h')
        case (Bound j)
        have nh: False if "ok (case e of Subscript \<Rightarrow> raise (Term_Error (STR ''fastype: Bound'') [Bound j])
            | _ \<Rightarrow> raise e) y" for e and y :: ptyp
          using that by (cases e) auto
        from fh' Bound have "ok (nth (map snd rb') j) H" by (auto simp: fastype_def ok_handle dest: nh)
        then show ?thesis by (simp add: Bound ok_nth ilength_eq)
      qed (use nAh' nApp' in simp_all)
      from bs_env_cert[OF bs tyh this] H have wH: "wft ar (tsubst \<rho> H)" by (simp add: cert_wft)
      have wU1: "wft ar (tsubst \<rho> U1)"
        by (rule env_fastype_apps_wft[OF U1[unfolded fastype_def u] fH tsol0 wH])
      text \<open>The type of the variable of the flexible side:\<close>
      have st': "strip_comb t' = (Var v T, map (incr_bv k 0) targs @ bvs (length Es))"
        by (simp add: t'_def strip_comb_expand[OF st])
      from tyt[unfolded strip_comb_apps[OF st'] inst_apps] obtain Ws' where
        "e \<turnstile> inst \<rho> (Var v T) : Ws' \<Rrightarrow> U"
        by (rule list_app_typeE)
      then have "cert_typ alg ar (tsubst \<rho> T)" by auto
      then have wT: "wft ar (tsubst \<rho> T)" by (rule cert_wft)
      have wT1: "wft ar (tsubst \<rho> T1)"
        by (rule env_fastype_apps_wft[OF T1[unfolded fastype_def t] fv tsol0 wT])
      text \<open>The arities agree:\<close>
      have sp: "tspine (tyenv env1) T1 U1" by (rule cunify_types_tspine[OF cu tsol1 wT1 wU1])
      from body_type_binder_types[OF bB refl] obtain Hs where bH: "ok (binder_types env2 T0) Hs" by blast
      from env_fastype_apps_binder_types[OF U1[unfolded fastype_def u] fH te02 bH[unfolded T0]]
      have lH: "length uargs \<le> length Hs" and bU1: "ok (binder_types env2 U1) (drop (length uargs) Hs)"
        by simp_all
      from sp te12 bT1 bU1 have "length Es = length (drop (length uargs) Hs)" unfolding tspine_def by blast
      with lH lWs have lHs: "length (map (tsubst \<rho>) Hs) = length Ws" by simp
      from binder_body_type_sound[OF bH refl bB tsol] H T0
      have "Ws \<Rrightarrow> U = map (tsubst \<rho>) Hs \<Rrightarrow> tsubst \<rho> B" by simp
      with funs_eq[OF lHs[symmetric]] show "U = tsubst \<rho> B" by simp
    qed
    with ed len nAh' sh' show "length targs \<le> length Ts \<and>
      (case eta_expand_dpair (drop (length targs) Ts) (rb, t, u) of (rb', t', u') \<Rightarrow>
        rsat env2 rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u')))"
      by (simp add: Es_def)
  qed
  then show ?thesis unfolding MATCH_ok_def dp prod.case by blast
qed

text \<open>The flex-rigid pairs that \<open>SIMPL\<close> returns satisfy the hypothesis of \<open>MATCH\<close>:\<close>

theorem SIMPL_MATCH_ok:
  "okW (SIMPL alg' env dps) (env', ffs, dp # frs) \<Longrightarrow> MATCH_ok env' dp"
  by (rule frs_shape_MATCH_ok[OF SIMPL_frs_shape])

end

end
