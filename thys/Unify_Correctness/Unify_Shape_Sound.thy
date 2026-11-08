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
  "ok (head_norm env0 t) u1 \<Longrightarrow> ok (eta_norm env rb u1) u2 \<Longrightarrow> satd env rb u2"
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
  shows "snd r = Ok (env', ffs', frs') \<Longrightarrow> st = (env, ffs, frs) \<Longrightarrow>
    \<exists>b. frs' = b @ frs \<and> (\<forall>x\<in>set b. frs_shape x)"
  using assms
proof (induction alg' dp st r arbitrary: env ffs frs env' ffs' frs' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 simpl alg' dp0 st r)
  have IH: "\<exists>b. frs2 = b @ frs1 \<and> (\<forall>x\<in>set b. frs_shape x)"
    if "okW (simpl alg' dp (env1, ffs1, frs1)) (env2, ffs2, frs2)" for dp env1 ffs1 frs1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' dp (env1, ffs1, frs1) = Some (evs, Ok (env2, ffs2, frs2))" by blast
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
  shows "snd r = Ok (env', ffs, frs) \<Longrightarrow> \<forall>x\<in>set frs. frs_shape x"
  using assms
proof (induction alg' env dps r arbitrary: env' ffs frs rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 simpl alg' env dps r)
  have IH: "\<forall>x\<in>set frs2. frs_shape x"
    if "okW (simpl alg' env1 dps1) (env2, ffs2, frs2)" for env1 dps1 env2 ffs2 frs2
  proof -
    from that obtain evs where "simpl alg' env1 dps1 = Some (evs, Ok (env2, ffs2, frs2))" by blast
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


subsection \<open>Equal types have equal numbers of binder types\<close>

text \<open>
  Types that are equal modulo the type environment, not only under its solutions, have as many
  binder types, in every extension of the type environment (\<open>tspine\<close>).
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
  assumes dT: "ok (devar \<theta> T) (Type a Ts0)" and dU: "ok (devar \<theta> U) (Type b Us0)"
    and nT: "\<forall>A R. Type a Ts0 \<noteq> A \<rightarrow>\<^sub>T R" and nU: "\<forall>A R. Type b Us0 \<noteq> A \<rightarrow>\<^sub>T R"
  shows "tspine \<theta> T U"
  unfolding tspine_def
proof (intro allI impI)
  fix env Ts Us assume ext: "textends \<theta> (tyenv env)" and bT: "ok (binder_types env T) Ts"
    and bU: "ok (binder_types env U) Us"
  from bT[unfolded binder_types_Type_devar[OF dT ext]] nT have "Ts = []"
    by (subst (asm) binder_types.simps) (auto split: list.splits if_splits)
  moreover from bU[unfolded binder_types_Type_devar[OF dU ext]] nU have "Us = []"
    by (subst (asm) binder_types.simps) (auto split: list.splits if_splits)
  ultimately show "length Ts = length Us" by simp
qed

text \<open>Types that are equal modulo an acyclic type environment have as many binder types:\<close>

lemma tspine_tnorm:
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>"
    and T: "tcons \<theta> T" and U: "tcons \<theta> U" and eq: "tnorm \<theta> T = tnorm \<theta> U"
  shows "tspine \<theta> T U"
proof -
  have "\<forall>T U. tnorm \<theta> T = N \<longrightarrow> tnorm \<theta> U = N \<longrightarrow> tcons \<theta> T \<longrightarrow> tcons \<theta> U \<longrightarrow> tspine \<theta> T U" for N
  proof (induction N)
    case (Type a Ns)
    show ?case
    proof (intro allI impI)
      fix T U assume nT: "tnorm \<theta> T = Type a Ns" and nU: "tnorm \<theta> U = Type a Ns"
        and cT: "tcons \<theta> T" and cU: "tcons \<theta> U"
      from devar_ok[OF ac tc cT] obtain D1 where d1: "devar \<theta> T = return D1" "tnorm \<theta> D1 = tnorm \<theta> T"
        "tcons \<theta> D1" "\<not> tbound \<theta> D1" by blast
      from devar_ok[OF ac tc cU] obtain D2 where d2: "devar \<theta> U = return D2" "tnorm \<theta> D2 = tnorm \<theta> U"
        "tcons \<theta> D2" "\<not> tbound \<theta> D2" by blast
      have Ty: "\<exists>Ts. D = Type a Ts \<and> map (tnorm \<theta>) Ts = Ns" if "tnorm \<theta> D = Type a Ns" "\<not> tbound \<theta> D" for D
        using that by (cases D) (auto simp: tnorm_TVar[OF ac] split: option.splits)
      from Ty[OF d1(2)[unfolded nT] d1(4)] obtain Ts1 where D1: "D1 = Type a Ts1" "map (tnorm \<theta>) Ts1 = Ns"
        by blast
      from Ty[OF d2(2)[unfolded nU] d2(4)] obtain Ts2 where D2: "D2 = Type a Ts2" "map (tnorm \<theta>) Ts2 = Ns"
        by blast
      have dT: "ok (devar \<theta> T) D1" and dU: "ok (devar \<theta> U) D2" using d1(1) d2(1) by (simp_all add: return_def)
      show "tspine \<theta> T U"
      proof (cases "\<exists>A R. D1 = A \<rightarrow>\<^sub>T R")
        case True
        then obtain A1 R1 where f1: "D1 = A1 \<rightarrow>\<^sub>T R1" by blast
        with D1 have a: "a = STR ''fun''" and Ts1: "Ts1 = [A1, R1]" by simp_all
        from D1(2) D2(2) Ts1 obtain A2 R2 where Ts2: "Ts2 = [A2, R2]" and R: "tnorm \<theta> R2 = tnorm \<theta> R1"
          by (cases Ts2 rule: list.exhaust[case_product list.exhaust[case_product list.exhaust]]) auto
        have Ns: "tnorm \<theta> R1 \<in> set Ns" using D1(2) Ts1 by auto
        have "tspine \<theta> R1 R2"
          using Type.IH[OF Ns] R d1(3) d2(3) by (simp add: f1 D2 Ts2)
        then show ?thesis by (rule tspine_fun[OF dT[unfolded f1] dU[unfolded D2 Ts2 a]])
      next
        case False
        have "\<forall>A R. D2 \<noteq> A \<rightarrow>\<^sub>T R"
        proof (intro allI notI)
          fix A R assume "D2 = A \<rightarrow>\<^sub>T R"
          with D2 have a: "a = STR ''fun''" and l2: "length Ts2 = 2" by auto
          have "length Ts1 = length Ts2" using D1(2) D2(2) by (metis length_map)
          with l2 obtain A1 R1 where "Ts1 = [A1, R1]" by (auto simp: numeral_2_eq_2 length_Suc_conv)
          with False D1(1) a show False by simp
        qed
        with False show ?thesis by (intro tspine_Type[OF dT[unfolded D1(1)] dU[unfolded D2(1)]]) (simp_all add: D1 D2)
      qed
    qed
  next
    case (TVar v S)
    show ?case
    proof (intro allI impI)
      fix T U assume nT: "tnorm \<theta> T = TVar v S" and nU: "tnorm \<theta> U = TVar v S"
        and cT: "tcons \<theta> T" and cU: "tcons \<theta> U"
      from devar_ok[OF ac tc cT] obtain D1 where d1: "devar \<theta> T = return D1" "tnorm \<theta> D1 = tnorm \<theta> T"
        "\<not> tbound \<theta> D1" by blast
      from devar_ok[OF ac tc cU] obtain D2 where d2: "devar \<theta> U = return D2" "tnorm \<theta> D2 = tnorm \<theta> U"
        "\<not> tbound \<theta> D2" by blast
      have V: "D = TVar v S" if "tnorm \<theta> D = TVar v S" "\<not> tbound \<theta> D" for D
        using that by (cases D) (auto simp: tnorm_TVar[OF ac] split: option.splits)
      have "D1 = D2" using V[OF d1(2)[unfolded nT] d1(3)] V[OF d2(2)[unfolded nU] d2(3)] by simp
      then have "tspine \<theta> D1 D2" by (intro tspine_devar) simp
      from tspine_devar_trans[OF _ _ textends_refl this] d1(1) d2(1) show "tspine \<theta> T U"
        by (simp add: return_def)
    qed
  next
    case (TFree a S)
    show ?case
    proof (intro allI impI)
      fix T U assume nT: "tnorm \<theta> T = TFree a S" and nU: "tnorm \<theta> U = TFree a S"
        and cT: "tcons \<theta> T" and cU: "tcons \<theta> U"
      from devar_ok[OF ac tc cT] obtain D1 where d1: "devar \<theta> T = return D1" "tnorm \<theta> D1 = tnorm \<theta> T"
        "\<not> tbound \<theta> D1" by blast
      from devar_ok[OF ac tc cU] obtain D2 where d2: "devar \<theta> U = return D2" "tnorm \<theta> D2 = tnorm \<theta> U"
        "\<not> tbound \<theta> D2" by blast
      have V: "D = TFree a S" if "tnorm \<theta> D = TFree a S" "\<not> tbound \<theta> D" for D
        using that by (cases D) (auto simp: tnorm_TVar[OF ac] split: option.splits)
      have "D1 = D2" using V[OF d1(2)[unfolded nT] d1(3)] V[OF d2(2)[unfolded nU] d2(3)] by simp
      then have "tspine \<theta> D1 D2" by (intro tspine_devar) simp
      from tspine_devar_trans[OF _ _ textends_refl this] d1(1) d2(1) show "tspine \<theta> T U"
        by (simp add: return_def)
    qed
  qed
  with T U eq show ?thesis by blast
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
  The hypothesis \<^const>\<open>MATCH_ok\<close> of \<open>MATCH\<close> holds for the flex-rigid pairs of \<open>SIMPL\<close> whose sides
  have types with as many binder types in every extension of the type environment
  (\<^const>\<open>tspine\<close>), as the types of the sides of a well-typed pair do (theorem
  @{thm [source] tspine_tnorm}). For ill-typed pairs, the saturation of the rigid side may fail:
  for \<open>?v c =?= f\<close> with \<open>?v :: d' \<Rightarrow> ?'b\<close> and \<open>f :: ?'c\<close>, where a later pair binds
  \<open>?'c := d \<Rightarrow> e\<close>, the imitation \<open>?v := \<lambda>x. f (?G x)\<close> has type \<open>d' \<Rightarrow> e\<close>, not \<open>d' \<Rightarrow> d \<Rightarrow> e\<close>.
\<close>

lemma satd_rsat: "\<not> is_Abs (fst (strip_comb u)) \<Longrightarrow> satd env rb u \<Longrightarrow> rsat env rb t u"
  unfolding rsat_def using satd_base by blast

text \<open>
  The rigid side of the \<open>\<eta>\<close>-expanded pair is saturated in every extension of the type environment
  (for every typing, as in the proof of completeness):
\<close>

lemma frs_shape_satd:
  assumes sh: "frs_shape (rb, t, u)" and T1: "ok (fastype env0 rb t) T1" and U1: "ok (fastype env0 rb u) U1"
    and sp: "tspine (tyenv env0) T1 U1" and ext02: "extends env0 env2"
    and st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env2 T) Ts"
    and ed: "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
  shows "length targs \<le> length Ts" "satd env2 rb' u'" "\<not> is_Abs (fst (strip_comb u'))"
proof -
  from sh have nAu: "\<not> is_Abs u" and hu: "head_nf u" by (simp_all add: frs_shape_def)
  have te02: "textends (tyenv env0) (tyenv env2)" using ext02 by (simp add: extends_def)
  have t: "t = Var v T \<degree>\<degree> targs" by (rule strip_comb_apps[OF st])
  have fv: "ok (env_fastype env0 (map snd rb) (Var v T)) T" by simp
  define Es where "Es = drop (length targs) Ts"
  from env_fastype_apps_binder_types[OF T1[unfolded fastype_def t] fv te02 bt]
  have len: "length targs \<le> length Ts" and bT1: "ok (binder_types env2 T1) Es"
    by (simp_all add: Es_def)
  then show "length targs \<le> length Ts" by simp
  define hu where "hu = fst (strip_comb u)"
  define uargs where "uargs = snd (strip_comb u)"
  have u: "u = hu \<degree>\<degree> uargs" by (rule strip_comb_apps) (simp add: hu_def uargs_def)
  have nAhu: "\<not> is_Abs hu" using nAu hu by (simp add: head_nf_nonAbs hu_def fst_strip_comb)
  have nApp: "\<not> (\<exists>f a. hu = f $ a)" using strip_comb_head[of u hu uargs] by (simp add: hu_def uargs_def)
  from env_fastype_apps_head[OF U1[unfolded fastype_def u]] obtain H
    where fH: "ok (env_fastype env0 (map snd rb) hu) H" by blast
  define k where "k = ilength Es"
  define h' where "h' = incr_bv k 0 hu"
  define args' where "args' = map (incr_bv k 0) uargs @ bvs (length Es)"
  have rb': "rb' = rev (map (\<lambda>T. (STR '''', T)) Es) @ rb" and u'0: "u' = incr_bv k 0 u \<degree>\<degree> bvs (length Es)"
    using ed by (simp_all add: eta_expand_dpair_eq Es_def k_def)
  have u': "u' = h' \<degree>\<degree> args'" by (simp add: u'0 h'_def args'_def u incr_bv_apps)
  have nApp': "\<not> (\<exists>f a. h' = f $ a)" and nAh': "\<not> is_Abs h'"
    using nApp nAhu by (cases hu; simp add: h'_def)+
  have sh': "fst (strip_comb u') = h'" by (simp add: u' strip_comb_atom_apps[OF nApp'])
  then show "\<not> is_Abs (fst (strip_comb u'))" using nAh' by simp
  have mrb': "map snd rb' = rev Es @ map snd rb" by (simp add: rb' rev_map comp_def)
  have fh': "ok (fastype env2 rb' h') H"
    using env_fastype_incr_atom[OF nAhu nApp fH, of env2 "rev Es"]
    by (simp add: fastype_def mrb' h'_def k_def ilength_eq)
  have "U = tsubst \<rho> B"
    if f0: "ok (fastype env2 rb' h') T0" and bB: "ok (body_type env2 T0) B" and tsol: "tsol (tyenv env2) \<rho>"
      and bs: "bs_env \<rho> e rb'" and tyu: "e \<turnstile> inst \<rho> u' : U" for T0 B \<rho> e U
  proof -
    have T0: "T0 = H" using f0 fh' by simp
    from tyu[unfolded u' inst_apps] obtain Ws where tyh: "e \<turnstile> inst \<rho> h' : Ws \<Rrightarrow> U"
      and tyas: "e \<tturnstile> map (inst \<rho>) args' : Ws" by (rule list_app_typeE)
    have lWs: "length Ws = length uargs + length Es" using typings_nth[OF tyas] by (simp add: args'_def)
    have H: "tsubst \<rho> H = Ws \<Rrightarrow> U" by (rule fastype_sound[OF fh' tsol bs tyh])
    from body_type_binder_types[OF bB refl] obtain Hs where bH: "ok (binder_types env2 T0) Hs" by blast
    from env_fastype_apps_binder_types[OF U1[unfolded fastype_def u] fH te02 bH[unfolded T0]]
    have lH: "length uargs \<le> length Hs" and bU1: "ok (binder_types env2 U1) (drop (length uargs) Hs)"
      by simp_all
    from sp te02 bT1 bU1 have "length Es = length (drop (length uargs) Hs)" unfolding tspine_def by blast
    with lH lWs have lHs: "length (map (tsubst \<rho>) Hs) = length Ws" by simp
    from binder_body_type_sound[OF bH refl bB tsol] H T0
    have "Ws \<Rrightarrow> U = map (tsubst \<rho>) Hs \<Rrightarrow> tsubst \<rho> B" by simp
    with funs_eq[OF lHs[symmetric]] show "U = tsubst \<rho> B" by simp
  qed
  then show "satd env2 rb' u'" using nAh' unfolding sh'[symmetric]
    by (subst satd.simps) (auto split: pterm.splits)
qed

theorem frs_shape_MATCH_ok:
  assumes sh: "frs_shape (rb, t, u)" and T1: "ok (fastype env0 rb t) T1" and U1: "ok (fastype env0 rb u) U1"
    and sp: "tspine (tyenv env0) T1 U1"
  shows "MATCH_ok env0 (rb, t, u)"
  unfolding MATCH_ok_def msat_ok_def prod.case
proof (intro allI impI)
  fix env2 v T targs Ts assume ext: "extends env0 env2" and "tenv env2 = tenv env0"
    and st: "strip_comb t = (Var v T, targs)" and bt: "ok (binder_types env2 T) Ts"
  obtain rb' t' u' where ed: "eta_expand_dpair (drop (length targs) Ts) (rb, t, u) = (rb', t', u')"
    by (cases "eta_expand_dpair (drop (length targs) Ts) (rb, t, u)") auto
  note s = frs_shape_satd[OF sh T1 U1 sp ext st bt ed]
  from s(1) satd_rsat[OF s(3) s(2)] s(3) ed show "length targs \<le> length Ts \<and>
    (case eta_expand_dpair (drop (length targs) Ts) (rb, t, u) of (rb', t', u') \<Rightarrow>
      rsat env2 rb' t' u' \<and> \<not> is_Abs (fst (strip_comb u')))"
    by simp
qed

end

end
