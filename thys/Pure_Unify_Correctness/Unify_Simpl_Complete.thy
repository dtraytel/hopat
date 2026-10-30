section \<open>Completeness of the Simplification Phase\<close>

theory Unify_Simpl_Complete
  imports Unify_Occurs_Complete "Pure_Pattern_Correctness.Pattern_Termination"
begin

text \<open>
  Completeness of \<^const>\<open>SIMPL0\<close> and \<^const>\<open>SIMPL\<close> relative to a given well-typed solution
  \<open>\<sigma>\<close> (\<^const>\<open>solution\<close>): on well-typed disagreement pairs solved by \<open>\<sigma>\<close>, the simplification
  terminates without an exception, \<open>\<sigma>\<close> remains a solution of the resulting environment and
  solves the resulting pairs, and no unbound variable becomes reachable. Termination is shown
  by induction on the size of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the instance under \<open>\<sigma>\<close>
  (\<^const>\<open>lsize\<close>), which does not depend on the environment since \<open>\<sigma>\<close> satisfies it.
\<close>

subsection \<open>Invariants\<close>

context csig
begin

definition dp_typed :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "dp_typed V dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> \<exists>T. has_type V (map snd rb) t T \<and> has_type V (map snd rb) u T)"

definition dp_below :: "integer \<Rightarrow> dpair \<Rightarrow> bool" where
  "dp_below m dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> below m t \<and> below m u)"

definition vps_dp :: "dpair \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps_dp dp = (case dp of (rb, t, u) \<Rightarrow> vps t \<union> vps u)"

abbreviation vps_dps :: "dpair list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps_dps dps \<equiv> \<Union> (vps_dp ` set dps)"

lemma dp_simps[simp]:
  "dp_typed V (rb, t, u) \<longleftrightarrow> (\<exists>T. has_type V (map snd rb) t T \<and> has_type V (map snd rb) u T)"
  "dp_below m (rb, t, u) \<longleftrightarrow> below m t \<and> below m u"
  "vps_dp (rb, t, u) = vps t \<union> vps u"
  by (simp_all add: dp_typed_def dp_below_def vps_dp_def)

text \<open>
  The invariant of a state of the search with respect to a solution \<open>\<sigma>\<close>: the environment is
  acyclic, well-formed, typed by \<open>V\<close> and fresh, \<open>\<sigma>\<close> is a solution of it, and the pairs are
  well-formed, typed, not newer than the environment and solved by \<open>\<sigma>\<close>.
\<close>

definition cinv :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> bool" where
  "cinv ar V \<tau>' \<sigma> env dps \<longleftrightarrow> env_inv ar V env \<and> solution V \<tau>' \<sigma> env \<and>
    (\<forall>dp\<in>set dps. wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp \<and> dsolved \<sigma> dp)"

lemma cinvD:
  assumes "cinv ar V \<tau>' \<sigma> env dps"
  shows "env_inv ar V env" "solution V \<tau>' \<sigma> env"
    "dp \<in> set dps \<Longrightarrow> wf_dp ar dp \<and> dp_typed V dp \<and> dp_below (maxidx env) dp \<and> dsolved \<sigma> dp"
  using assms by (simp_all add: cinv_def)

lemma cinv_append: "cinv ar V \<tau>' \<sigma> env (dps @ dps') \<longleftrightarrow> cinv ar V \<tau>' \<sigma> env dps \<and> cinv ar V \<tau>' \<sigma> env dps'"
  by (auto simp: cinv_def)

lemma cinv_Cons: "cinv ar V \<tau>' \<sigma> env (dp # dps) \<longleftrightarrow> cinv ar V \<tau>' \<sigma> env [dp] \<and> cinv ar V \<tau>' \<sigma> env dps"
  by (auto simp: cinv_def)

text \<open>Shapes of the pairs collected by \<^const>\<open>SIMPL0\<close>: both sides have a base type and no outer abstraction.\<close>

definition ff_shape :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "ff_shape V dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<exists>B. \<not> is_funT B \<and> has_type V (map snd rb) t B \<and> has_type V (map snd rb) u B) \<and>
    is_Var (head_of t) \<and> is_Var (head_of u))"

definition fr_shape :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> dpair \<Rightarrow> bool" where
  "fr_shape V dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<exists>B. \<not> is_funT B \<and> has_type V (map snd rb) t B \<and> has_type V (map snd rb) u B) \<and>
    is_Var (head_of t) \<and> is_rigid (head_of u))"

text \<open>
  The result of simplifying the pairs \<open>dps\<close> in state \<open>(env, ffs, frs)\<close>: new pairs are added in
  front, the invariant holds, and the bindings only make variables reachable that were reachable
  from \<open>dps\<close>.
\<close>

definition heads_unb :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "heads_unb env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow>
    (\<forall>x T. head_of t = Var x T \<longrightarrow> vt_lookup (tenv env) x = None) \<and>
    (\<forall>x T. head_of u = Var x T \<longrightarrow> vt_lookup (tenv env) x = None))"

lemma extends_unbound: "extends env' env \<Longrightarrow> vt_lookup (tenv env') x = None \<Longrightarrow> vt_lookup (tenv env) x = None"
  unfolding extends_def by (cases x; cases "vt_lookup (tenv env) x") force+

lemma heads_unb_extends: "heads_unb env' dp \<Longrightarrow> extends env' env \<Longrightarrow> heads_unb env dp"
  by (auto simp: heads_unb_def split: prod.splits intro: extends_unbound)

definition sres :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow>
    dpair list \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "sres ar V \<tau>' \<sigma> dps st st' \<longleftrightarrow> (case (st, st') of ((env, ffs, frs), (env', ffs', frs')) \<Rightarrow>
    \<exists>ffn frn. ffs' = ffn @ ffs \<and> frs' = frn @ frs \<and> cinv ar V \<tau>' \<sigma> env' (ffn @ frn) \<and>
      env_inv ar V env' \<and> extends env' env \<and> maxidx env' = maxidx env \<and>
      (\<forall>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps)) \<and>
      vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps) \<and>
      (\<forall>dp\<in>set ffn. ff_shape V dp) \<and> (\<forall>dp\<in>set frn. fr_shape V dp) \<and>
      (\<forall>dp\<in>set (ffn @ frn). heads_unb env dp))"

subsection \<open>Termination and shape of \<open>\<eta>\<close>-normalization\<close>

lemma vars_vps_eq: "vars t = fst ` vps t"
  by (induction t) auto

lemma below_vps_iff: "below m t \<longleftrightarrow> (\<forall>y\<in>vps t. snd (fst y) \<le> m)"
  by (auto simp: below_def vars_vps_eq)

lemma etif_term: "vt_is_empty tye \<Longrightarrow> \<exists>t'. etif tye T t = Some (Ok t')"
proof (induction T arbitrary: t)
  case (Type a Ts)
  show ?case
  proof (cases "\<exists>T1 U. Ts = [T1, U] \<and> a = STR ''fun''")
    case True
    then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by blast
    from Type.IH[of U "incr_boundvars 1 t $ Bound 0"] Type.prems Ts obtain u
      where "etif tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)" by auto
    then show ?thesis using Ts a by (subst etif.simps) (simp add: bindM_def return_def)
  next
    case False
    then show ?thesis by (subst etif.simps) (auto simp: return_def split: list.splits)
  qed
next
  case (TVar v S)
  then show ?case by (subst etif.simps) (simp add: type_lookup_empty return_def)
qed (subst etif.simps; simp add: return_def)+

lemma eta_norm_term:
  "vt_is_empty (tyenv env) \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow> \<exists>t'. eta_norm env rb t = Some (Ok t')"
proof (induction env rb t arbitrary: T rule: eta_norm.induct)
  case (1 env rb a A body)
  from "1.prems"(2) obtain U where "has_type V (A # map snd rb) body U" by (auto elim: has_type_elims)
  with "1.IH"[OF "1.prems"(1)] obtain b' where "eta_norm env ((a, A) # rb) body = Some (Ok b')" by auto
  then show ?case by (simp add: return_def)
qed (auto simp: fastype_typed etif_term)

text \<open>Heads related by \<open>\<eta>\<close>-expansion: the same variable, and rigid stays rigid.\<close>

definition head_rel :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "head_rel h h' \<longleftrightarrow> (\<forall>x U. h' = Var x U \<longleftrightarrow> h = Var x U) \<and> (is_rigid h \<longrightarrow> is_rigid h')"

lemma head_rel_refl[simp]: "head_rel h h"
  by (simp add: head_rel_def)

lemma head_rel_trans: "head_rel h h' \<Longrightarrow> head_rel h' h'' \<Longrightarrow> head_rel h h''"
  by (simp add: head_rel_def)

lemma head_of_incr_bv: "head_of (incr_bv inc lev t) = incr_bv inc lev (head_of t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma head_rel_incr: "head_rel h (incr_boundvars 1 h)"
  by (cases h) (auto simp: head_rel_def incr_boundvars_def is_rigid_def)

lemma etif_shape:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vt_is_empty tye \<Longrightarrow> \<not> is_Abs t \<Longrightarrow>
    vps t' = vps t \<and> head_rel (head_of t) (head_of (strip_abs_body t'))"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  have e: "vt_is_empty tye" and nA: "\<not> is_Abs t"
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
  show ?case
  proof (cases "\<exists>T1 U. T = T1 \<rightarrow>\<^sub>T U")
    case True
    then obtain T1 U where T: "T = T1 \<rightarrow>\<^sub>T U" by blast
    with body obtain u where u: "et tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u" by auto
    from "1.IH"[OF u refl e] have "vps u = vps (incr_boundvars 1 t $ Bound 0)"
      "head_rel (head_of (incr_boundvars 1 t $ Bound 0)) (head_of (strip_abs_body u))"
      by simp_all
    moreover have "head_of (incr_boundvars 1 t $ Bound 0) = incr_boundvars 1 (head_of t)"
      by (simp add: incr_boundvars_def head_of_incr_bv)
    ultimately show ?thesis using t' head_rel_trans[OF head_rel_incr]
      by (simp add: incr_boundvars_def vps_incr_bv)
  next
    case False
    have "t' = t"
    proof (cases T)
      case (Type a Ts)
      with False body show ?thesis by (auto split: list.splits if_splits)
    next
      case (TVar v S)
      with body e show ?thesis by (auto simp: type_lookup_empty)
    qed (use body in auto)
    with nA show ?thesis by (cases t) auto
  qed
qed

lemma eta_norm_shape:
  "ok (eta_norm env rb t) t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow>
    vps t' = vps t \<and> head_rel (head_of (strip_abs_body t)) (head_of (strip_abs_body t'))"
proof (induction env rb t arbitrary: t' rule: eta_norm.induct)
  case (1 env rb a A body)
  then show ?case by auto
next
  case ("2_1" env rb c T)
  then show ?case using etif_shape[of "tyenv env" _ "Const c T" _ t'] by auto
next
  case ("2_2" env rb c T)
  then show ?case using etif_shape[of "tyenv env" _ "Free c T" _ t'] by auto
next
  case ("2_3" env rb x T)
  then show ?case using etif_shape[of "tyenv env" _ "Var x T" _ t'] by auto
next
  case ("2_4" env rb i)
  then show ?case using etif_shape[of "tyenv env" _ "Bound i" _ t'] by auto
next
  case ("2_5" env rb f u)
  then show ?case using etif_shape[of "tyenv env" _ "f $ u" _ t'] by auto
qed

subsection \<open>Head normalization of disagreement pairs\<close>

text \<open>The head of the body of a head normal form is an unbound variable or rigid.\<close>

lemma head_norm_body_head_unbound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> head_of (strip_abs_body t') = Var F U \<Longrightarrow>
    vt_lookup (tenv env) F = None"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  from "1.hyps" "1.prems"(1) have h: "(case t of
      Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) = Some (Ok t')"
    by simp
  note IH = "1.IH"[OF _ refl "1.prems"(2)]
  have hd: "head_of (strip_abs_body t') = Var F U" by (rule "1.prems"(3))
  show ?case
  proof (cases t)
    case (Var xi T)
    from h Var obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "(case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) = Some (Ok t')"
      by (auto elim!: bindM_SomeE)
    from ok_lookup[OF "1.prems"(2) lk]
    consider "r' = None" "vt_lookup (tenv env) xi = None" | u where "r' = Some u"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest Var have "t' = Var xi T" by (simp add: return_def)
      with 1 hd show ?thesis by simp
    next
      case 2
      with rest IH hd show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with h obtain b' where "hn env body = Some (Ok b')" "t' = Abs a T b'"
      by (auto elim!: bindM_SomeE simp: return_def)
    with IH hd show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a W body where f: "f = Abs a W body" by (cases f) auto
      with h App IH hd show ?thesis by simp
    next
      case False
      with h App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "(case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) =
          Some (Ok t')"
        by (cases f) (auto elim!: bindM_SomeE)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a W body where nfa: "nf = Abs a W body" by (cases nf) auto
        with rest IH hd show ?thesis by simp
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) (simp_all add: return_def)
        moreover have "strip_abs_body nf = nf" using False by (cases nf) simp_all
        ultimately show ?thesis using hd IH[OF nf] by simp
      qed
    qed
  qed (use h hd in \<open>auto simp: return_def\<close>)
qed

lemma head_of_in_nonVar:
  "\<not> is_Var (head_of t) \<Longrightarrow> head_of_in env t = return (head_of t)"
proof (induction t)
  case (App f u)
  then show ?case by (simp add: head_of_in_App)
qed (subst head_of_in.simps; simp)+

lemma hrig_rigid: "is_rigid (head_of t) \<Longrightarrow> hrig env t"
  by (auto simp: hrig_def head_of_in_nonVar is_rigid_def return_def)

lemma vps_strip_abs_body[simp]: "vps (strip_abs_body t) = vps t"
  by (induction t rule: strip_abs_body.induct) auto

lemma liftM_Ok[simp]: "liftM (Some (Ok x)) = returnW x"
  by (simp add: liftM_def returnW_def)

text \<open>
  On a pair in the invariant, \<^const>\<open>head_norm_dpair\<close> terminates without an exception and
  yields a pair in the invariant whose sides have a base type, no outer abstraction, and an
  unbound variable or a rigid head.
\<close>

lemma head_norm_dpair_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env [(rb, t, u)]"
  obtains rb' t' u' T where
    "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    "cinv ar V \<tau>' \<sigma> env [(rb', t', u')]"
    "has_type V (map snd rb) t T" "map snd rb' = rev (arg_types T) @ map snd rb"
    "has_type V (map snd rb') t' (res_type T)" "has_type V (map snd rb') u' (res_type T)"
    "\<not> is_Abs t'" "\<not> is_Abs u'" "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    "vps t' \<subseteq> reach env (vps t)" "vps u' \<subseteq> reach env (vps u)"
    "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    "mk_subst \<sigma> (tr (rlist_abs rb' t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  from cinvD(3)[OF inv, of "(rb, t, u)"] obtain T where wfd: "wf_dp ar (rb, t, u)"
    and tyt: "has_type V (map snd rb) t T" and tyu: "has_type V (map snd rb) u T"
    and bl: "below (maxidx env) t" "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    by auto
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from head_norm_term[OF ei(1,2,3) tyt] obtain t1 where ht: "head_norm env t = Some (Ok t1)" by blast
  from head_norm_term[OF ei(1,2,3) tyu] obtain u1 where hu: "head_norm env u = Some (Ok u1)" by blast
  have tyt1: "has_type V (map snd rb) t1 T" by (rule head_norm_typed[OF ht refl ei(2,3) tyt])
  have tyu1: "has_type V (map snd rb) u1 T" by (rule head_norm_typed[OF hu refl ei(2,3) tyu])
  from eta_norm_term[OF e tyt1] obtain t2 where et: "eta_norm env rb t1 = Some (Ok t2)" by blast
  from eta_norm_term[OF e tyu1] obtain u2 where eu: "eta_norm env rb u1 = Some (Ok u2)" by blast
  have hlt: "hlong V (map snd rb) t2 T" by (rule eta_norm_hlong[OF e tyt1]) (simp add: et)
  have hlu: "hlong V (map snd rb) u2 T" by (rule eta_norm_hlong[OF e tyu1]) (simp add: eu)
  from new_dpair_hlong[OF hlt hlu, of alg env] obtain rb' where
    nd: "new_dpair alg rb t2 u2 env = returnW ((rb', strip_abs_body t2, strip_abs_body u2), env)"
    and rb': "map snd rb' = rev (arg_types T) @ map snd rb"
    and ty': "has_type V (map snd rb') (strip_abs_body t2) (res_type T)"
      "has_type V (map snd rb') (strip_abs_body u2) (res_type T)"
    and nA: "\<not> is_Abs (strip_abs_body t2)" "\<not> is_Abs (strip_abs_body u2)"
    by blast
  define t' where "t' = strip_abs_body t2"
  define u' where "u' = strip_abs_body u2"
  have hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    by (simp add: head_norm_dpair_def ht hu et eu nd t'_def u'_def)
  note snd = head_norm_dpair_sound[OF hd ei(2) wfd]
  note shp = head_norm_dpair_shape[OF hd ei(2) wfd]
  have eqt: "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb' t'))"
    by (rule env_equivD[OF snd(3) \<sigma>(1,4)])
  have equ: "mk_subst \<sigma> (tr (rlist_abs rb u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb' u'))"
    by (rule env_equivD[OF snd(4) \<sigma>(1,4)])
  have ds': "dsolved \<sigma> (rb', t', u')"
    using equiv_trans[OF equiv_trans[OF equiv_sym[OF eqt] dsolvedD[OF ds]] equ] by (rule dsolvedI)
  note est = eta_norm_shape[OF _ e, of rb t1 t2] eta_norm_shape[OF _ e, of rb u1 u2]
  have vt: "vps t' = vps t1" "vps u' = vps u1" using est et eu by (simp_all add: t'_def u'_def)
  have rt: "vps t1 \<subseteq> reach env (vps t)" "vps u1 \<subseteq> reach env (vps u)"
    using hn_vps[OF head_norm_hn[OF ht e refl]] hn_vps[OF head_norm_hn[OF hu e refl]] by simp_all
  have bt: "below (maxidx env) t'" "below (maxidx env) u'"
    using below_head_norm[OF ht refl ei(2,4) bl(1)] below_head_norm[OF hu refl ei(2,4) bl(2)] vt
    by (simp_all add: below_vps_iff)
  have "cinv ar V \<tau>' \<sigma> env [(rb', t', u')]"
    using cinvD(1,2)[OF inv] snd(2) ty' ds' bt by (auto simp: cinv_def t'_def u'_def)
  moreover have "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    using shp(3,4) nA by (simp_all add: hnf_nonAbs t'_def u'_def)
  moreover have "vt_lookup (tenv env) F = None" if "head_of t' = Var F U" for F U
  proof -
    have "head_rel (head_of (strip_abs_body t1)) (head_of t')"
      using est(1) et by (simp add: t'_def)
    with that have "head_of (strip_abs_body t1) = Var F U" unfolding head_rel_def by blast
    from head_norm_body_head_unbound[OF ht refl e this] show ?thesis .
  qed
  moreover have "vt_lookup (tenv env) F = None" if "head_of u' = Var F U" for F U
  proof -
    have "head_rel (head_of (strip_abs_body u1)) (head_of u')"
      using est(2) eu by (simp add: u'_def)
    with that have "head_of (strip_abs_body u1) = Var F U" unfolding head_rel_def by blast
    from head_norm_body_head_unbound[OF hu refl e this] show ?thesis .
  qed
  ultimately show ?thesis
    using that[OF hd _ tyt rb' ty'[folded t'_def u'_def] nA[folded t'_def u'_def]] vt rt equiv_sym[OF eqt]
    by blast
qed

subsection \<open>The termination measure\<close>

lemma has_type_rlist_abs:
  "has_type V (map snd rb @ Ts) t T \<Longrightarrow> has_type V Ts (rlist_abs rb t) (foldr fun_type (rev (map snd rb)) T)"
proof (induction rb arbitrary: t T)
  case (Cons aA rb)
  obtain a A where aA: "aA = (a, A)" by (cases aA)
  with Cons.prems have "has_type V (map snd rb @ Ts) (Abs a A t) (A \<rightarrow>\<^sub>T T)" by (auto intro: has_type.Abs)
  from Cons.IH[OF this] aA show ?case by simp
qed simp

text \<open>
  The size of the \<open>\<eta>\<close>-long \<open>\<beta>\<close>-normal form of the closed instance of a side of a disagreement
  pair. It only depends on the instance modulo \<open>\<beta>\<eta>\<close>.
\<close>

definition dsz :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> nat" where
  "dsz \<tau>' \<sigma> rb t T = lsize (\<lambda>_. Atom 0) \<tau>' (SOME w. \<beta>\<eta>cl (mk_subst \<sigma> (tr (rlist_abs rb t))) w \<and> normal w)
    (trty (foldr fun_type (rev (map snd rb)) T))"

lemma dsz_lsize:
  assumes ty: "has_type V (map snd rb) t T" and \<sigma>: "closed_on UNIV \<sigma>" "typed_on (range code) (tau V) \<tau>' \<sigma>"
    and w: "w \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))" "no_redex w"
      "(\<lambda>_. Atom 0, \<tau>') \<turnstile> w : trty (foldr fun_type (rev (map snd rb)) T)"
  shows "dsz \<tau>' \<sigma> rb t T = lsize (\<lambda>_. Atom 0) \<tau>' w (trty (foldr fun_type (rev (map snd rb)) T))"
proof -
  let ?x = "mk_subst \<sigma> (tr (rlist_abs rb t))" and ?T = "trty (foldr fun_type (rev (map snd rb)) T)"
  have tyc: "has_type V [] (rlist_abs rb t) (foldr fun_type (rev (map snd rb)) T)"
    using has_type_rlist_abs[of V rb "[]" t T] ty by simp
  have "(bnd_env [], \<tau>') \<turnstile> ?x : ?T" by (rule has_type_subst[OF tyc \<sigma>(2)])
  moreover have "no_loose_bound ?x 0"
    using has_type_closed[OF tyc] by (intro mk_subst_no_loose_bound closed_on_mono[OF \<sigma>(1)]) simp_all
  ultimately have tyx: "(\<lambda>_. Atom 0, \<tau>') \<turnstile> ?x : ?T" by (rule typing_closed)
  from normal_form_ex[OF tyx] have "\<exists>w. \<beta>\<eta>cl ?x w \<and> normal w" .
  from someI_ex[OF this]
  have n: "\<beta>\<eta>cl ?x (SOME w. \<beta>\<eta>cl ?x w \<and> normal w)" "normal (SOME w. \<beta>\<eta>cl ?x w \<and> normal w)"
    by blast+
  show ?thesis unfolding dsz_def
  proof (rule lsize_equiv)
    show "(SOME w. \<beta>\<eta>cl ?x w \<and> normal w) \<equiv>\<^sub>\<beta>\<^sub>\<eta> w"
      using equiv_trans[OF equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF n(1)]] equiv_sym[OF w(1)]] .
    show "(\<lambda>_. Atom 0, \<tau>') \<turnstile> (SOME w. \<beta>\<eta>cl ?x w \<and> normal w) : ?T"
      by (rule subject_reduction_\<beta>\<eta>[OF n(1) tyx])
  qed (use n w normal_no_redex in auto)
qed

lemma dsz_equiv:
  assumes ty: "has_type V (map snd rb) t T" "has_type V (map snd rb') t' T'"
    and TT: "foldr fun_type (rev (map snd rb')) T' = foldr fun_type (rev (map snd rb)) T"
    and eq: "mk_subst \<sigma> (tr (rlist_abs rb' t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))"
    and \<sigma>: "closed_on UNIV \<sigma>" "typed_on (range code) (tau V) \<tau>' \<sigma>"
  shows "dsz \<tau>' \<sigma> rb' t' T' = dsz \<tau>' \<sigma> rb t T"
proof -
  let ?x = "mk_subst \<sigma> (tr (rlist_abs rb t))" and ?T = "trty (foldr fun_type (rev (map snd rb)) T)"
  have tyc: "has_type V [] (rlist_abs rb t) (foldr fun_type (rev (map snd rb)) T)"
    using has_type_rlist_abs[of V rb "[]" t T] ty(1) by simp
  have "(bnd_env [], \<tau>') \<turnstile> ?x : ?T" by (rule has_type_subst[OF tyc \<sigma>(2)])
  moreover have "no_loose_bound ?x 0"
    using has_type_closed[OF tyc] by (intro mk_subst_no_loose_bound closed_on_mono[OF \<sigma>(1)]) simp_all
  ultimately have tyx: "(\<lambda>_. Atom 0, \<tau>') \<turnstile> ?x : ?T" by (rule typing_closed)
  from nf_typed[OF tyx] obtain w where w: "\<beta>\<eta>cl ?x w" "normal w" "(\<lambda>_. Atom 0, \<tau>') \<turnstile> w : ?T" .
  have "dsz \<tau>' \<sigma> rb t T = lsize (\<lambda>_. Atom 0) \<tau>' w ?T"
    using w by (intro dsz_lsize[OF ty(1) \<sigma>]) (auto intro: equiv_sym \<beta>\<eta>cl_into_equiv normal_no_redex)
  moreover have "dsz \<tau>' \<sigma> rb' t' T' = lsize (\<lambda>_. Atom 0) \<tau>' w ?T"
    using dsz_lsize[OF ty(2) \<sigma> equiv_trans[OF equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF w(1)]] equiv_sym[OF eq]]
      normal_no_redex[OF w(2)]] w(3) TT by simp
  ultimately show ?thesis by simp
qed

text \<open>The arguments of a rigid head are smaller than the application.\<close>

lemma dsz_args:
  assumes tyh: "has_type V (map snd rb) h (foldr fun_type Us B)"
    and tyas: "list_all2 (has_type V (map snd rb)) as Us"
    and rig: "is_rigid h" and \<sigma>: "closed_on UNIV \<sigma>" "typed_on (range code) (tau V) \<tau>' \<sigma>" "rigid_subst \<sigma>"
    and i: "i < length as"
  shows "dsz \<tau>' \<sigma> rb (as ! i) (Us ! i) < dsz \<tau>' \<sigma> rb (list_comb h as) B"
proof -
  define Ts where "Ts = map snd rb"
  define n where "n = length rb"
  define Rs where "Rs = map trty (rev Ts)"
  define e' where "e' = env_ext (\<lambda>_. Atom 0) Rs"
  have lRs: "length Rs = n" by (simp add: Rs_def Ts_def n_def)
  have al: "bnd_env Ts j = e' j" if "j < n" for j
  proof -
    have "n - Suc j < length Ts" using that by (simp add: Ts_def n_def)
    then show ?thesis using that lRs
      by (simp add: e'_def env_ext_less Rs_def bnd_env_def rev_nth Ts_def n_def)
  qed
  have tr_ty: "(e', \<tau>') \<turnstile> mk_subst \<sigma> (tr x) : trty X" if "has_type V Ts x X" for x X
  proof (rule typing_bound_cong[OF has_type_subst[OF that \<sigma>(2)]])
    show "no_loose_bound (mk_subst \<sigma> (tr x)) n"
      using has_type_closed[OF that] by (intro mk_subst_no_loose_bound closed_on_mono[OF \<sigma>(1)])
        (simp_all add: Ts_def n_def)
  qed (rule al)
  have lUs: "length Us = length as" using list_all2_lengthD[OF tyas] by simp
  note atom = conjunct2[OF rigid_tr[OF rig \<sigma>(3)]]
  have th: "(e', \<tau>') \<turnstile> tr h : map trty Us \<Rrightarrow> trty B"
    using tr_ty[OF tyh[folded Ts_def]] rigid_tr[OF rig \<sigma>(3)] by (simp add: trty_foldr)
  have targs: "(e', \<tau>') \<tturnstile> map (\<lambda>a. mk_subst \<sigma> (tr a)) as : map trty Us"
    by (rule typings_map2) (use lUs list_all2_nthD[OF tyas] tr_ty in \<open>auto simp: Ts_def\<close>)
  obtain ws where
    ws0: "length ws = length (map (\<lambda>a. mk_subst \<sigma> (tr a)) as)"
      "\<And>j. j < length (map (\<lambda>a. mk_subst \<sigma> (tr a)) as) \<Longrightarrow>
        \<beta>\<eta>cl (map (\<lambda>a. mk_subst \<sigma> (tr a)) as ! j) (ws ! j) \<and> normal (ws ! j) \<and>
        (e', \<tau>') \<turnstile> ws ! j : map trty Us ! j"
      "tr h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) as \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" "no_redex (tr h \<degree>\<degree> ws)"
      "(e', \<tau>') \<turnstile> tr h \<degree>\<degree> ws : trty B"
      "\<And>j. j < length (map (\<lambda>a. mk_subst \<sigma> (tr a)) as) \<Longrightarrow>
        Suc (ld e' \<tau>' (ws ! j) (map trty Us ! j)) \<le> ld e' \<tau>' (tr h \<degree>\<degree> ws) (trty B)"
    by (rule atom_apps_nf[OF atom th targs]) fast
  have ws: "length ws = length as"
      "\<And>j. j < length as \<Longrightarrow> \<beta>\<eta>cl (mk_subst \<sigma> (tr (as ! j))) (ws ! j) \<and> normal (ws ! j) \<and>
        (e', \<tau>') \<turnstile> ws ! j : trty (Us ! j)"
      "tr h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) as \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h \<degree>\<degree> ws" "no_redex (tr h \<degree>\<degree> ws)"
      "(e', \<tau>') \<turnstile> tr h \<degree>\<degree> ws : trty B"
    using ws0 lUs by simp_all
  have tws: "(e', \<tau>') \<tturnstile> ws : map trty Us"
    by (rule typings_map2) (use ws(1,2) lUs in auto)
  have nrws: "\<forall>w\<in>set ws. no_redex w"
  proof
    fix w assume "w \<in> set ws"
    then obtain j where "j < length as" "w = ws ! j" using ws(1) by (auto simp: in_set_conv_nth)
    with ws(2)[of j] show "no_redex w" by (simp add: normal_no_redex)
  qed
  have ws6: "Suc (lsize e' \<tau>' (ws ! j) (trty (Us ! j))) \<le> lsize e' \<tau>' (tr h \<degree>\<degree> ws) (trty B)"
    if "j < length as" for j
  proof -
    have "lsize e' \<tau>' (ws ! j) (map trty Us ! j) \<le> (\<Sum>k<length ws. lsize e' \<tau>' (ws ! k) (map trty Us ! k))"
      using that ws(1) by (intro member_le_sum) auto
    with lsize_atom_apps[OF atom th tws nrws] that lUs show ?thesis by simp
  qed
  have rT: "trty (foldr fun_type (rev (map snd rb)) X) = Rs \<Rrightarrow> trty X" for X
    by (simp add: trty_foldr Rs_def Ts_def)
  have tyt: "has_type V (map snd rb) (list_comb h as) B"
    using tyh tyas by (auto simp: has_type_list_comb)
  have "dsz \<tau>' \<sigma> rb (list_comb h as) B = lsize (\<lambda>_. Atom 0) \<tau>' (Abs_m n (tr h \<degree>\<degree> ws)) (Rs \<Rrightarrow> trty B)"
  proof -
    have "mk_subst \<sigma> (tr (rlist_abs rb (list_comb h as))) = Abs_m n (tr h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) as)"
      using rigid_tr[OF rig \<sigma>(3)] by (simp add: tr_rlist_abs mk_subst_Abs_m tr_list_comb n_def comp_def)
    with ws(3) have "Abs_m n (tr h \<degree>\<degree> ws) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb (list_comb h as)))"
      by (simp add: equiv_Abs_m equiv_sym)
    moreover have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m n (tr h \<degree>\<degree> ws) : Rs \<Rrightarrow> trty B"
      using typing_Abs_m[of "\<lambda>_. Atom 0" Rs \<tau>'] ws(5) lRs by (simp add: e'_def)
    ultimately show ?thesis using dsz_lsize[OF tyt \<sigma>(1,2)] ws(4) rT by simp
  qed
  also have "\<dots> = lsize e' \<tau>' (tr h \<degree>\<degree> ws) (trty B)" using lsize_Abs_m[OF lRs] by (simp add: e'_def)
  finally have L: "dsz \<tau>' \<sigma> rb (list_comb h as) B = lsize e' \<tau>' (tr h \<degree>\<degree> ws) (trty B)" .
  have tyi: "has_type V (map snd rb) (as ! i) (Us ! i)" using list_all2_nthD[OF tyas i] .
  have "dsz \<tau>' \<sigma> rb (as ! i) (Us ! i) = lsize (\<lambda>_. Atom 0) \<tau>' (Abs_m n (ws ! i)) (Rs \<Rrightarrow> trty (Us ! i))"
  proof -
    have "Abs_m n (ws ! i) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb (as ! i)))"
      using ws(2)[OF i] by (simp add: tr_rlist_abs mk_subst_Abs_m n_def equiv_Abs_m equiv_sym \<beta>\<eta>cl_into_equiv)
    moreover have "(\<lambda>_. Atom 0, \<tau>') \<turnstile> Abs_m n (ws ! i) : Rs \<Rrightarrow> trty (Us ! i)"
      using typing_Abs_m[of "\<lambda>_. Atom 0" Rs \<tau>'] ws(2)[OF i] lRs by (simp add: e'_def)
    ultimately show ?thesis using dsz_lsize[OF tyi \<sigma>(1,2)] ws(2)[OF i] normal_no_redex rT by simp
  qed
  also have "\<dots> = lsize e' \<tau>' (ws ! i) (trty (Us ! i))" using lsize_Abs_m[OF lRs] by (simp add: e'_def)
  finally show ?thesis using L ws6[OF i] by simp
qed

subsection \<open>Termination of the occurs checks\<close>

text \<open>
  On terms and environments typed by \<open>V\<close>, \<^const>\<open>occur\<close> and \<^const>\<open>rocc\<close> terminate since every
  binding is followed at most once (the list \<open>seen\<close> only grows); \<^const>\<open>head_of_in\<close>
  terminates on acyclic environments.
\<close>

definition bnd :: "env \<Rightarrow> indexname set" where
  "bnd env = {x. vt_lookup (tenv env) x \<noteq> None}"

lemma finite_bnd[simp]: "finite (bnd env)"
  unfolding bnd_def by (rule finite_vt_lookup)

lemma card_bnd_mono: "set seen \<subseteq> set seen' \<Longrightarrow> card (bnd env - set seen') \<le> card (bnd env - set seen)"
  by (rule card_mono) auto

lemma card_bnd_less:
  "w \<notin> set seen \<Longrightarrow> w \<in> bnd env \<Longrightarrow> card (bnd env - set (w # seen)) < card (bnd env - set seen)"
  by (rule psubset_card_mono) auto

definition vtyped :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> bool" where
  "vtyped V t \<longleftrightarrow> (\<forall>y\<in>vps t. V (fst y) = snd y)"

lemma vtyped_simps[simp]:
  "vtyped V (Var x T) \<longleftrightarrow> V x = T" "vtyped V (Abs a T t) \<longleftrightarrow> vtyped V t"
  "vtyped V (f $ u) \<longleftrightarrow> vtyped V f \<and> vtyped V u"
  "vtyped V (Const c T)" "vtyped V (Free c T)" "vtyped V (Bound i)"
  by (auto simp: vtyped_def)

lemma has_type_vtyped: "has_type V Ts t T \<Longrightarrow> vtyped V t"
  by (auto simp: vtyped_def dest: has_type_vps)

lemma vtyped_list_comb: "vtyped V (list_comb h ts) \<longleftrightarrow> vtyped V h \<and> (\<forall>t\<in>set ts. vtyped V t)"
  by (auto simp: vtyped_def vps_list_comb)

lemma lookup_typed:
  assumes "vt_is_empty (tyenv env)" "env_typed V env" "V x = T"
  shows "\<exists>r. lookup env x T = return r \<and> (\<forall>u. r = Some u \<longrightarrow> vt_lookup (tenv env) x = Some (T, u) \<and> vtyped V u)"
proof (cases "vt_lookup (tenv env) x")
  case None
  then show ?thesis using lookup_unbound[OF assms(1)] by auto
next
  case (Some p)
  obtain U u where p: "p = (U, u)" by (cases p)
  with Some env_typedD[OF assms(2)] assms(3) have "U = T" "has_type V [] u T" by auto
  with Some p lookup_bound[OF assms(1)] show ?thesis by (auto intro: has_type_vtyped)
qed

lemma occur_term:
  assumes e: "vt_is_empty (tyenv env)" and ety: "env_typed V env"
  shows "card (bnd env - set seen) \<le> k \<Longrightarrow> vtyped V t \<Longrightarrow>
    \<exists>b s. occur t env v seen = Some (Ok (b, s)) \<and> set seen \<subseteq> set s"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  show ?case using less.prems
  proof (induction t arbitrary: seen)
    case (Var w T)
    show ?case
    proof (cases "w \<in> set seen \<or> v = w")
      case True
      then show ?thesis by (subst occur.simps) (auto simp: return_def)
    next
      case False
      from lookup_typed[OF e ety, of w T] Var.prems obtain r where
        lk: "lookup env w T = return r" and r: "\<And>u. r = Some u \<Longrightarrow> vt_lookup (tenv env) w = Some (T, u) \<and> vtyped V u"
        by auto
      show ?thesis
      proof (cases r)
        case None
        then show ?thesis using False lk by (subst occur.simps) (auto simp: return_def)
      next
        case (Some u)
        with r have b: "vt_lookup (tenv env) w = Some (T, u)" and vu: "vtyped V u" by auto
        have "w \<in> bnd env" using b by (simp add: bnd_def)
        with False Var.prems have lt: "card (bnd env - set (w # seen)) < k"
          using card_bnd_less[of w seen env] by simp
        from less.IH[OF lt order_refl vu] obtain b s
          where "occur u env v (w # seen) = Some (Ok (b, s))" "set (w # seen) \<subseteq> set s" by blast
        then show ?thesis using False lk Some by (subst occur.simps) (auto simp: return_def)
      qed
    qed
  next
    case (Abs a T body)
    then show ?case by (subst occur.simps) simp
  next
    case (App f u)
    from App.IH(2)[of seen] App.prems obtain b1 s1 where
      r1: "occur u env v seen = Some (Ok (b1, s1))" "set seen \<subseteq> set s1" by auto
    from App.IH(1)[of s1] App.prems card_bnd_mono[OF r1(2), of env] obtain b2 s2 where
      r2: "occur f env v s1 = Some (Ok (b2, s2))" "set s1 \<subseteq> set s2" by fastforce
    show ?case using r1 r2 by (subst occur.simps) (auto simp: return_def)
  qed (subst occur.simps; auto simp: return_def)+
qed

lemma nonrigid_term:
  assumes "vt_is_empty (tyenv env)" "env_typed V env" "vtyped V t"
  shows "\<exists>oc s. nonrigid env v seen t = Some (Ok (oc, s)) \<and> set seen \<subseteq> set s"
proof -
  from occur_term[OF assms(1,2) order_refl assms(3), of v seen] obtain b s where
    "occur t env v seen = Some (Ok (b, s))" "set seen \<subseteq> set s" by blast
  then show ?thesis by (auto simp: nonrigid_def return_def)
qed

lemma head_of_in_term:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed V env"
  shows "card (reach env (vps t)) \<le> k \<Longrightarrow> vtyped V t \<Longrightarrow> \<exists>h. head_of_in env t = Some (Ok h)"
proof (induction k arbitrary: t rule: less_induct)
  case (less k)
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  show ?case using less.prems
  proof (induction t)
    case (Var x T)
    from lookup_typed[OF e ety, of x T] Var.prems obtain r where
      lkp: "lookup env x T = return r" and r: "\<And>u. r = Some u \<Longrightarrow> vt_lookup (tenv env) x = Some (T, u) \<and> vtyped V u"
      by auto
    show ?case
    proof (cases r)
      case None
      then show ?thesis using lkp by (subst head_of_in.simps) (simp add: return_def)
    next
      case (Some u)
      with r have b: "vt_lookup (tenv env) x = Some (T, u)" and vu: "vtyped V u" by auto
      then have "lk env x T = Some u" by (simp add: lk_def)
      from reach_card_less[OF ac wf ety this] Var.prems(1)
      have "card (reach env (vps u)) < k" by simp
      from less.IH[OF this order_refl vu] obtain h where "head_of_in env u = Some (Ok h)" by blast
      then show ?thesis using lkp Some by (subst head_of_in.simps) (simp add: return_def)
    qed
  next
    case (App f u)
    have "card (reach env (vps f)) \<le> card (reach env (vps (f $ u)))"
      by (rule card_mono) (auto simp: finite_reach intro: set_mp[OF reach_subset])
    with App show ?case by (simp add: head_of_in_App)
  qed (subst head_of_in.simps; simp add: return_def)+
qed

lemma occomb_term:
  assumes H: "\<And>s seen'. size s < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen' \<Longrightarrow> vtyped V s \<Longrightarrow>
      \<exists>r. oc seen' s = Some (Ok r) \<and> set seen' \<subseteq> set (snd r)"
  shows "size t \<le> size t0 \<Longrightarrow> (\<exists>f u. t = f $ u) \<or> size t < size t0 \<Longrightarrow> set seen0 \<subseteq> set seen \<Longrightarrow>
    vtyped V t \<Longrightarrow> \<exists>r. occomb oc seen t = Some (Ok r) \<and> set seen \<subseteq> set (snd r)"
proof (induction t arbitrary: seen)
  case (App f x)
  from H[of x seen] App.prems obtain r1 where r1: "oc seen x = Some (Ok r1)" "set seen \<subseteq> set (snd r1)"
    by auto
  show ?case
  proof (cases "fst r1 = Rigid")
    case True
    then show ?thesis using r1 by (simp add: return_def)
  next
    case False
    from App.IH(1)[of "snd r1"] App.prems r1(2) obtain r2 where
      r2: "occomb oc (snd r1) f = Some (Ok r2)" "set (snd r1) \<subseteq> set (snd r2)"
      by fastforce
    show ?thesis using r1 r2 False by (simp add: return_def)
  qed
qed (use H in fastforce)+

lemma rocc_term:
  assumes ac: "acyc env" and wf: "wf_env ar env" and ety: "env_typed V env"
  shows "card (bnd env - set seen) \<le> k \<Longrightarrow> vtyped V t \<Longrightarrow>
    \<exists>oc s. rocc t env v seen = Some (Ok (oc, s)) \<and> set seen \<subseteq> set s"
proof (induction k arbitrary: t seen rule: less_induct)
  case (less k)
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF wf])
  show ?case using less.prems
  proof (induction "size t" arbitrary: t seen rule: less_induct)
    case less2: less
    show ?case
    proof (cases t)
      case (Var w T)
      show ?thesis
      proof (cases "w \<in> set seen \<or> v = w")
        case True
        then show ?thesis using Var by (subst rocc.simps) (auto simp: return_def)
      next
        case False
        from lookup_typed[OF e ety, of w T] less2.prems Var obtain r where
          lk: "lookup env w T = return r"
          and r: "\<And>u. r = Some u \<Longrightarrow> vt_lookup (tenv env) w = Some (T, u) \<and> vtyped V u"
          by auto
        show ?thesis
        proof (cases r)
          case None
          then show ?thesis using False lk Var by (subst rocc.simps) (auto simp: return_def)
        next
          case (Some u)
          with r have b: "vt_lookup (tenv env) w = Some (T, u)" and vu: "vtyped V u" by auto
          have "w \<in> bnd env" using b by (simp add: bnd_def)
          with False less2.prems have lt: "card (bnd env - set (w # seen)) < k"
            using card_bnd_less[of w seen env] by simp
          from less.IH[OF lt order_refl vu] obtain oc s
            where "rocc u env v (w # seen) = Some (Ok (oc, s))" "set (w # seen) \<subseteq> set s" by blast
          then show ?thesis using False lk Some Var by (subst rocc.simps) (auto simp: return_def)
        qed
      qed
    next
      case (Abs a T body)
      from less2.hyps[of body seen] less2.prems Abs show ?thesis by (subst rocc.simps) simp
    next
      case (App f u)
      have vf: "vtyped V f" using less2.prems App by simp
      from head_of_in_term[OF ac wf ety order_refl vf] obtain h where hd: "head_of_in env f = Some (Ok h)"
        by blast
      have nr: "\<exists>oc s. nonrigid env v seen t = Some (Ok (oc, s)) \<and> set seen \<subseteq> set s"
        using nonrigid_term[OF e ety] less2.prems by blast
      have oc: "\<exists>r. occomb (\<lambda>seen t. rocc t env v seen) seen t = Some (Ok r) \<and> set seen \<subseteq> set (snd r)"
      proof (rule occomb_term[where t0 = t and seen0 = seen])
        fix s seen' assume s: "size s < size t" "set seen \<subseteq> set seen'" "vtyped V s"
        have "card (bnd env - set seen') \<le> k" using card_bnd_mono[OF s(2), of env] less2.prems by simp
        from less2.hyps[OF s(1) this s(3)] show "\<exists>r. rocc s env v seen' = Some (Ok r) \<and> set seen' \<subseteq> set (snd r)"
          by auto
      qed (use App less2.prems in auto)
      show ?thesis
      proof (cases h)
        case (Var x U)
        then show ?thesis using hd nr App by (subst rocc.simps) (auto simp: return_def)
      next
        case (Abs a T b)
        then show ?thesis using hd nr App by (subst rocc.simps) auto
      qed (use hd oc App in \<open>subst rocc.simps, auto simp del: occomb.simps\<close>)+
    qed (subst rocc.simps; auto simp: return_def)+
  qed
qed

lemma rigid_occurs_term_terminates:
  assumes "acyc env" "wf_env ar env" "env_typed V env" "vtyped V t"
  shows "\<exists>oc. rigid_occurs_term env v t = return oc"
  using rocc_term[OF assms(1-3), of "[]" _ t v, OF order_refl assms(4)]
  by (auto simp: rigid_occurs_term_def return_def)

subsection \<open>Assignments\<close>

lemma get_eta_var_cases:
  "get_eta_var rb n t = raiseW ASSIGN \<or> (\<exists>v T. get_eta_var rb n t = returnW (v, T))"
  by (induction rb n t rule: get_eta_var.induct) auto

lemma get_eta_var_type:
  assumes "okW (get_eta_var rb n t) (v, T)" "0 \<le> n" "has_type V Ts t B"
    "\<And>k. k < length rb \<Longrightarrow> nat_of_integer n + k < length Ts \<and> Ts ! (nat_of_integer n + k) = snd (rb ! k)"
  shows "T = foldr fun_type (rev (map snd rb)) B \<and> V v = T \<and> head_of t = Var v T"
  using assms
proof (induction rb arbitrary: n t B)
  case Nil
  then show ?case by (cases t) (auto elim: has_type_elims)
next
  case (Cons aA rb)
  from Cons.prems(1) obtain f where t: "t = f $ Bound n"
    and rec: "okW (get_eta_var rb (n + 1) f) (v, T)"
    by (cases "(aA # rb, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  from Cons.prems(3) t obtain A where tf: "has_type V Ts f (A \<rightarrow>\<^sub>T B)" and tb: "has_type V Ts (Bound n) A"
    by (auto elim: has_type_elims)
  from Cons.prems(4)[of 0] tb have A: "A = snd aA" by (simp add: has_type_Bound_iff)
  have n1: "0 \<le> n + 1" using Cons.prems(2) by simp
  have shift: "nat_of_integer (n + 1) = Suc (nat_of_integer n)"
    using Cons.prems(2) by (simp add: integer_reps)
  have "nat_of_integer (n + 1) + k < length Ts \<and> Ts ! (nat_of_integer (n + 1) + k) = snd (rb ! k)"
    if "k < length rb" for k
    using Cons.prems(4)[of "Suc k"] that by (simp add: shift)
  from Cons.IH[OF rec n1 tf this] A t show ?case by simp
qed

lemma vps_head_of: "head_of t = Var x T \<Longrightarrow> (x, T) \<in> vps t"
  by (induction t) auto

lemma update_unbound_ok:
  "vt_lookup (tenv env) F = None \<Longrightarrow> \<exists>env'. update (F, T) t env = Some (Ok env')"
  by (cases env) (auto simp: update_def update_new_def vt_defined_lookup return_def)

lemma reach_update:
  assumes "ok (update (F, T) t env) env'"
  shows "reach env' X \<subseteq> reach env (X \<union> vps t)"
proof
  note u = ok_update[OF assms]
  have d: "dep env' = dep env \<union> (\<lambda>y. (y, (F, T))) ` vps t" by (rule dep_update[OF u(2,1)])
  fix y assume "y \<in> reach env' X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env')\<^sup>*" by (auto simp: reach_def)
  from x(2) have "y \<in> reach env ({x} \<union> vps t)"
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case using reach_incl[of "{x} \<union> vps t" env] by blast
  next
    case (step y z)
    from step.hyps(1) d consider "(y, z) \<in> dep env" | "y \<in> vps t" by auto
    then show ?case
    proof cases
      case 1
      with step.IH show ?thesis by (blast intro: reach_pred)
    qed (use reach_incl[of "{x} \<union> vps t" env] in blast)
  qed
  then show "y \<in> reach env (X \<union> vps t)" using x(1) reach_subset[of "{x} \<union> vps t" "X \<union> vps t" env] by blast
qed

text \<open>
  \<^const>\<open>assignment\<close> on a flex-rigid pair solved by \<open>\<sigma>\<close>, whose flexible head is unbound: it
  gives up with \<open>ASSIGN\<close>, or it binds the variable keeping \<open>\<sigma>\<close> a solution.
\<close>

lemma assignment_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env [(rb, t, u)]"
    and ty: "has_type V (map snd rb) t B" "has_type V (map snd rb) u B" "\<not> is_funT B"
    and xu: "\<And>x T. head_of t = Var x T \<Longrightarrow> vt_lookup (tenv env) x = None"
    and hu: "is_rigid (head_of u)"
  shows "(\<exists>evs. assignment alg rb t u env = Some (evs, UErr ASSIGN)) \<or>
    (\<exists>env'. okW (assignment alg rb t u env) env' \<and> env_inv ar V env' \<and> solution V \<tau>' \<sigma> env' \<and>
      extends env' env \<and> maxidx env' = maxidx env \<and> (\<forall>X. reach env' X \<subseteq> reach env (X \<union> vps u)))"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note sol = cinvD(2)[OF inv]
  note \<sigma> = solutionD[OF sol]
  from cinvD(3)[OF inv, of "(rb, t, u)"] have wfd: "wf_dp ar (rb, t, u)"
    and bl: "below (maxidx env) t" "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    by auto
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  consider "get_eta_var rb 0 t = raiseW ASSIGN" | v T where "get_eta_var rb 0 t = returnW (v, T)"
    using get_eta_var_cases by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: assignment_def bindW_def raiseW_def)
  next
    case 2
    then have gev: "okW (get_eta_var rb 0 t) (v, T)" by (simp add: returnW_def)
    from get_eta_var_type[OF gev _ ty(1)] have T: "T = foldr fun_type (rev (map snd rb)) B"
      and Vv: "V v = T" and ht: "head_of t = Var v T"
      by (simp_all add: rev_nth)
    have vu: "vt_lookup (tenv env) v = None" using xu[OF ht] .
    from rigid_occurs_term_terminates[OF ei(1,2,3) has_type_vtyped[OF ty(2)], of v] obtain oc
      where oc: "rigid_occurs_term env v u = return oc" by blast
    show ?thesis
    proof (cases oc)
      case Rigid
      have "ok (rigid_occurs_term env v u) Rigid" using oc Rigid by (simp add: return_def)
      from rigid_occurs_unsolvable[OF gev this ei(2,3) sol vu ty(1,2) hrig_rigid[OF hu] ds] show ?thesis ..
    next
      case Nonrigid
      then show ?thesis using 2 oc by (simp add: assignment_def returnW_def return_def raiseW_def bindW_def)
    next
      case NoOcc
      have bt: "body_type env T = return B" using T body_type_base[OF e ty(3)] by simp
      have ft: "fastype env rb u = return B" by (rule fastype_typed[OF e ty(2)])
      from update_unbound_ok[OF vu, of T "rlist_abs rb u"] obtain env' where
        upd: "update (v, T) (rlist_abs rb u) env = Some (Ok env')" by blast
      have ok: "okW (assignment alg rb t u env) env'"
        using 2 oc NoOcc bt ft upd by (simp add: assignment_def cunify_types_same return_def)
      have eqv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb u))"
      proof -
        have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (dB.Var (code (AVar v)))"
          using mk_subst_equiv[OF conjunct1[OF get_eta_var_equiv[OF gev]] \<sigma>(1)] .
        then have "mk_subst \<sigma> (tr (rlist_abs rb t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma> (code (AVar v))" by simp
        from equiv_trans[OF equiv_sym[OF this] dsolvedD[OF ds]] show ?thesis .
      qed
      have tyr: "has_type V [] (rlist_abs rb u) T"
        using has_type_rlist_abs[of V rb "[]" u B] ty(2) T by simp
      have Fm: "snd v \<le> maxidx env" using below_vps[OF bl(1) vps_head_of[OF ht]] by simp
      have tm: "below (maxidx env) (rlist_abs rb u)" using bl(2) by (simp add: below_vps_iff vps_rlist_abs)
      have upd': "ok (update (v, T) (rlist_abs rb u) env) env'" using upd by simp
      note su = solution_update[OF sol ei(4) ei(3) upd' eqv Vv tyr Fm tm]
      have "acyc env'" by (rule assignment_acyc[OF ok ei(2) wfd ei(1)])
      moreover have "wf_env ar env'" by (rule assignment_wf[OF ok ei(2) wfd])
      ultimately have "env_inv ar V env'" using su by (simp add: env_inv_def)
      moreover have "reach env' X \<subseteq> reach env (X \<union> vps u)" for X
        using reach_update[OF upd'] by (simp add: vps_rlist_abs)
      ultimately show ?thesis using ok su ok_update_extends[OF upd'] by blast
    qed
  qed
qed

subsection \<open>Composing simplification steps\<close>

lemma cinv_transfer:
  "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow> cinv ar V \<tau>' \<sigma> env' [] \<Longrightarrow> maxidx env' = maxidx env \<Longrightarrow>
    cinv ar V \<tau>' \<sigma> env' dps"
  by (simp add: cinv_def)

lemma cinv_Nil: "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow> cinv ar V \<tau>' \<sigma> env []"
  by (simp add: cinv_def)

lemma sresD:
  assumes "sres ar V \<tau>' \<sigma> dps (env, ffs, frs) st'"
  obtains env' ffn frn where "st' = (env', ffn @ ffs, frn @ frs)" "cinv ar V \<tau>' \<sigma> env' (ffn @ frn)"
    "env_inv ar V env'" "extends env' env" "maxidx env' = maxidx env"
    "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps)" "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
  using assms by (cases st') (auto simp: sres_def)

lemma sresI:
  assumes "cinv ar V \<tau>' \<sigma> env' (ffn @ frn)" "env_inv ar V env'" "extends env' env" "maxidx env' = maxidx env"
    "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps)" "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps)"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
  shows "sres ar V \<tau>' \<sigma> dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
  using assms by (auto simp: sres_def)

lemma sres_refl:
  "cinv ar V \<tau>' \<sigma> env [] \<Longrightarrow> sres ar V \<tau>' \<sigma> dps (env, ffs, frs) (env, ffs, frs)"
  using sresI[of ar V \<tau>' \<sigma> env "[]" "[]" env dps ffs frs] reach_subset[of _ _ env]
  by (auto simp: cinv_def)

lemma sres_trans:
  assumes "sres ar V \<tau>' \<sigma> dps1 (env, ffs, frs) st1" "sres ar V \<tau>' \<sigma> dps2 st1 st2"
  shows "sres ar V \<tau>' \<sigma> (dps1 @ dps2) (env, ffs, frs) st2"
proof -
  from sresD[OF assms(1)] obtain env1 ffn1 frn1 where s1: "st1 = (env1, ffn1 @ ffs, frn1 @ frs)"
    "cinv ar V \<tau>' \<sigma> env1 (ffn1 @ frn1)" "env_inv ar V env1" "extends env1 env" "maxidx env1 = maxidx env"
    "\<And>X. reach env1 X \<subseteq> reach env (X \<union> vps_dps dps1)" "vps_dps (ffn1 @ frn1) \<subseteq> reach env (vps_dps dps1)"
    "\<And>dp. dp \<in> set ffn1 \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn1 \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn1 @ frn1) \<Longrightarrow> heads_unb env dp"
    by blast
  from sresD[OF assms(2)[unfolded s1(1)]] obtain env2 ffn2 frn2 where s2: "st2 = (env2, ffn2 @ ffn1 @ ffs, frn2 @ frn1 @ frs)"
    "cinv ar V \<tau>' \<sigma> env2 (ffn2 @ frn2)" "env_inv ar V env2" "extends env2 env1" "maxidx env2 = maxidx env1"
    "\<And>X. reach env2 X \<subseteq> reach env1 (X \<union> vps_dps dps2)" "vps_dps (ffn2 @ frn2) \<subseteq> reach env1 (vps_dps dps2)"
    "\<And>dp. dp \<in> set ffn2 \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn2 \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn2 @ frn2) \<Longrightarrow> heads_unb env1 dp"
    by blast
  have r: "reach env2 X \<subseteq> reach env (X \<union> vps_dps (dps1 @ dps2))" for X
  proof -
    have "reach env2 X \<subseteq> reach env1 (X \<union> vps_dps dps2)" by (rule s2(6))
    also have "\<dots> \<subseteq> reach env (X \<union> vps_dps dps2 \<union> vps_dps dps1)" by (rule s1(6))
    finally show ?thesis by (auto simp: Un_ac)
  qed
  have c1: "cinv ar V \<tau>' \<sigma> env2 (ffn1 @ frn1)" using cinv_transfer[OF s1(2) cinv_Nil[OF s2(2)]] s2(5) by simp
  have c: "cinv ar V \<tau>' \<sigma> env2 ((ffn2 @ ffn1) @ frn2 @ frn1)"
    using c1 s2(2) by (auto simp: cinv_def)
  have vv: "vps_dps ((ffn2 @ ffn1) @ frn2 @ frn1) \<subseteq> reach env (vps_dps (dps1 @ dps2))"
  proof -
    have "vps_dps (ffn2 @ frn2) \<subseteq> reach env (vps_dps dps2 \<union> vps_dps dps1)"
      using s2(7) s1(6)[of "vps_dps dps2"] by blast
    moreover have "vps_dps (ffn1 @ frn1) \<subseteq> reach env (vps_dps dps2 \<union> vps_dps dps1)"
      using s1(7) reach_subset[of "vps_dps dps1" "vps_dps dps2 \<union> vps_dps dps1" env] by blast
    ultimately show ?thesis by (auto simp: Un_ac)
  qed
  have ex: "extends env2 env" using s2(4) s1(4) by (rule extends_trans)
  have mx: "maxidx env2 = maxidx env" using s2(5) s1(5) by simp
  have ffh: "ff_shape V dp" if "dp \<in> set (ffn2 @ ffn1)" for dp using that s1(8) s2(8) by (metis Un_iff set_append)
  have frh: "fr_shape V dp" if "dp \<in> set (frn2 @ frn1)" for dp using that s1(9) s2(9) by (metis Un_iff set_append)
  have hh: "heads_unb env dp" if "dp \<in> set ((ffn2 @ ffn1) @ frn2 @ frn1)" for dp
    using that s1(10) s2(10) heads_unb_extends[OF _ s1(4)] by (metis Un_iff set_append)
  have "sres ar V \<tau>' \<sigma> (dps1 @ dps2) (env, ffs, frs) (env2, (ffn2 @ ffn1) @ ffs, (frn2 @ frn1) @ frs)"
    by (rule sresI[OF c s2(3) ex mx r vv ffh frh hh])
  then show ?thesis using s2(1) by simp
qed

lemma sres_mono_dps:
  assumes "sres ar V \<tau>' \<sigma> dps' (env, ffs, frs) st'" "vps_dps dps' \<subseteq> reach env (vps_dps dps)"
  shows "sres ar V \<tau>' \<sigma> dps (env, ffs, frs) st'"
proof -
  have m: "reach env (X \<union> vps_dps dps') \<subseteq> reach env (X \<union> vps_dps dps)" for X
    using assms(2) by (intro reach_mono) (auto intro: set_mp[OF reach_incl] set_mp[OF reach_subset])
  have m': "reach env (vps_dps dps') \<subseteq> reach env (vps_dps dps)"
    using assms(2) by (rule reach_mono)
  from sresD[OF assms(1)] obtain env' ffn frn where s: "st' = (env', ffn @ ffs, frn @ frs)"
    "cinv ar V \<tau>' \<sigma> env' (ffn @ frn)" "env_inv ar V env'" "extends env' env" "maxidx env' = maxidx env"
    "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps')" "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps')"
    "\<And>dp. dp \<in> set ffn \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frn \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffn @ frn) \<Longrightarrow> heads_unb env dp"
    by blast
  have "sres ar V \<tau>' \<sigma> dps (env, ffs, frs) (env', ffn @ ffs, frn @ frs)"
  proof (rule sresI[OF s(2,3,4,5) _ _ s(8,9,10)])
    show "reach env' X \<subseteq> reach env (X \<union> vps_dps dps)" for X using s(6)[of X] m[of X] by blast
    show "vps_dps (ffn @ frn) \<subseteq> reach env (vps_dps dps)" using s(7) m' by blast
  qed
  with s(1) show ?thesis by simp
qed

text \<open>The arguments of rigid-rigid pairs with equal heads.\<close>

lemma simrands_complete:
  assumes F: "\<And>i st. i < length as \<Longrightarrow> cinv ar V \<tau>' \<sigma> (fst st) [] \<Longrightarrow> maxidx (fst st) = m \<Longrightarrow>
      \<exists>st'. okW (F (rb, as ! i, bs ! i) st) st' \<and> sres ar V \<tau>' \<sigma> [(rb, as ! i, bs ! i)] st st'"
    and h: "\<nexists>f u. h = f $ u"
  shows "length as = length bs \<Longrightarrow> cinv ar V \<tau>' \<sigma> (fst st) [] \<Longrightarrow> maxidx (fst st) = m \<Longrightarrow>
    \<exists>st'. okW (simrands F rb u0 (list_comb h as) (list_comb h bs) st) st' \<and>
      sres ar V \<tau>' \<sigma> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) st st'"
  using F
proof (induction as arbitrary: bs st rule: rev_induct)
  case Nil
  then have "bs = []" by simp
  moreover have "simrands F rb u0 h h st = returnW st" using h by (cases h) simp_all
  ultimately show ?case using sres_refl[OF Nil.prems(2)] by (cases st) simp
next
  case (snoc a as)
  obtain env0 ffs0 frs0 where st: "st = (env0, ffs0, frs0)" by (cases st)
  from snoc.prems(1) obtain b bs' where bs: "bs = bs' @ [b]" "length as = length bs'"
    by (metis length_Suc_conv_rev)
  have F': "\<exists>st'. okW (F (rb, as ! i, bs' ! i) st) st' \<and> sres ar V \<tau>' \<sigma> [(rb, as ! i, bs' ! i)] st st'"
    if "i < length as" "cinv ar V \<tau>' \<sigma> (fst st) []" "maxidx (fst st) = m" for i st
    using snoc.prems(4)[of i st] that bs by (simp add: nth_append)
  from snoc.IH[OF bs(2) snoc.prems(2,3) F'] obtain st1 where
    r1: "okW (simrands F rb u0 (list_comb h as) (list_comb h bs') st) st1"
      "sres ar V \<tau>' \<sigma> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs')) st st1"
    by blast
  from sresD[OF r1(2)[unfolded st]] obtain env1 ffn frn where
    "st1 = (env1, ffn @ ffs0, frn @ frs0)" "cinv ar V \<tau>' \<sigma> env1 (ffn @ frn)" "maxidx env1 = maxidx env0"
    by blast
  then have c1: "cinv ar V \<tau>' \<sigma> (fst st1) []" "maxidx (fst st1) = m"
    using snoc.prems(3) st by (simp_all add: cinv_Nil)
  from snoc.prems(4)[of "length as" st1] c1 bs obtain st2 where
    r2: "okW (F (rb, a, b) st1) st2" "sres ar V \<tau>' \<sigma> [(rb, a, b)] st1 st2"
    by (auto simp: nth_append)
  have "okW (simrands F rb u0 (list_comb h (as @ [a])) (list_comb h bs) st) st2"
    using r1(1) r2(1) bs by (cases st1) (fastforce simp: list_comb_snoc)
  moreover have "sres ar V \<tau>' \<sigma> (map (\<lambda>(a, b). (rb, a, b)) (zip (as @ [a]) bs)) st st2"
    using sres_trans[OF r1(2)[unfolded st] r2(2)] bs st by simp
  ultimately show ?case by blast
qed

subsection \<open>Completeness of \<open>SIMPL0\<close>\<close>

lemma head_of_not_App: "head_of t \<noteq> f $ u"
  by (induction t) auto

lemma has_type_head_of: "has_type V Ts t T \<Longrightarrow> \<exists>U. has_type V Ts (head_of t) U"
  by (induction t arbitrary: T) (auto elim: has_type_elims)

lemma head_cases:
  assumes "has_type V Ts t T" "\<not> is_Abs (head_of t)"
  obtains x U where "head_of t = Var x U" | "is_rigid (head_of t)"
proof -
  from has_type_head_of[OF assms(1)] obtain U where ty: "has_type V Ts (head_of t) U" ..
  show ?thesis
  proof (cases "head_of t")
    case (Bound i)
    with ty have "0 \<le> i" by (simp add: has_type_Bound_iff)
    with Bound that(2) show ?thesis by (simp add: is_rigid_def)
  next
    case (App f u)
    with head_of_not_App show ?thesis by blast
  qed (use that assms(2) in \<open>auto simp: is_rigid_def\<close>)
qed

lemma head_of_list_comb: "t = list_comb (head_of t) (snd (strip_comb t))"
  by (metis prod.collapse fst_strip_comb strip_comb_list_comb)

lemma tr_rigid_inj: "is_rigid h \<Longrightarrow> is_rigid h' \<Longrightarrow> tr h = tr h' \<Longrightarrow> h = h'"
  by (auto simp: is_rigid_def integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq eq_nat_nat_iff)

lemma foldr_fun_type_inj:
  "length Us = length Us' \<Longrightarrow> foldr fun_type Us B = foldr fun_type Us' B' \<Longrightarrow> Us = Us' \<and> B = B'"
  by (induction Us Us' rule: list_induct2) auto

lemma body_type_head:
  assumes "has_type V Ts t B" "\<not> is_funT B" "head_of t = Var x U" "vt_is_empty (tyenv env)"
  shows "body_type env U = return B"
proof -
  from assms(1) head_of_list_comb[of t] assms(3) obtain Us where
    "has_type V Ts (Var x U) (foldr fun_type Us B)"
    by (metis has_type_list_comb)
  then have "U = foldr fun_type Us B" by (auto elim: has_type_elims)
  with body_type_base[OF assms(4,2)] show ?thesis by simp
qed

lemma cinv_swap: "cinv ar V \<tau>' \<sigma> env [(rb, t, u)] \<Longrightarrow> cinv ar V \<tau>' \<sigma> env [(rb, u, t)]"
  by (auto simp: cinv_def intro: dsolved_sym)

text \<open>One step of \<^const>\<open>SIMPL0\<close> on a head-normalized pair.\<close>

lemma SIMPL0_step_complete:
  assumes inv: "cinv ar V \<tau>' \<sigma> env [(rb, t, u)]"
    and ty: "has_type V (map snd rb) t B" "has_type V (map snd rb) u B" "\<not> is_funT B"
    and nA: "\<not> is_Abs (head_of t)" "\<not> is_Abs (head_of u)"
    and ut: "\<And>F U. head_of t = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and IH: "\<And>i st as bs Us. is_rigid (head_of t) \<Longrightarrow> t = list_comb (head_of t) as \<Longrightarrow>
      has_type V (map snd rb) (head_of t) (foldr fun_type Us B) \<Longrightarrow>
      list_all2 (has_type V (map snd rb)) as Us \<Longrightarrow> i < length as \<Longrightarrow>
      cinv ar V \<tau>' \<sigma> (fst st) [(rb, as ! i, bs ! i)] \<Longrightarrow>
      \<exists>st'. okW (F (rb, as ! i, bs ! i) st) st' \<and> sres ar V \<tau>' \<sigma> [(rb, as ! i, bs ! i)] st st'"
  shows "\<exists>st'. okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st' \<and> sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) st'"
proof -
  note ei = env_invD[OF cinvD(1)[OF inv]]
  note sol = cinvD(2)[OF inv]
  note \<sigma> = solutionD[OF sol]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from cinvD(3)[OF inv, of "(rb, t, u)"] have wfd: "wf_dp ar (rb, t, u)"
    and bl: "below (maxidx env) t" "below (maxidx env) u" and ds: "dsolved \<sigma> (rb, t, u)"
    by auto
  have c0: "cinv ar V \<tau>' \<sigma> env []" by (rule cinv_Nil[OF inv])
  have ei': "env_inv ar V env" by (rule cinvD(1)[OF inv])
  have rsub: "reach env X \<subseteq> reach env (X \<union> vps_dps [(rb, t, u)])" for X by (rule reach_subset) auto
  have vsub: "vps_dps [(rb, t, u)] \<subseteq> reach env (vps_dps [(rb, t, u)])" by (rule reach_incl)
  have hb: "heads_unb env (rb, t, u)" "heads_unb env (rb, u, t)"
    using ut uu by (auto simp: heads_unb_def)
  text \<open>Keeping the pair as flex-rigid pair.\<close>
  have keep_fr: "sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) (env, ffs, (rb, t, u) # frs)"
    if "fr_shape V (rb, t, u)"
    using sresI[of ar V \<tau>' \<sigma> env "[]" "[(rb, t, u)]" env "[(rb, t, u)]" ffs frs] inv ei' rsub vsub hb that by simp
  have keep_fr': "sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) (env, ffs, (rb, u, t) # frs)"
    if "fr_shape V (rb, u, t)"
    using sresI[of ar V \<tau>' \<sigma> env "[]" "[(rb, u, t)]" env "[(rb, t, u)]" ffs frs] cinv_swap[OF inv] ei' rsub vsub hb that
    by (simp add: Un_commute)
  text \<open>A successful assignment.\<close>
  have asg: "sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) (env', ffs, frs)"
    if "env_inv ar V env'" "solution V \<tau>' \<sigma> env'" "extends env' env" "maxidx env' = maxidx env"
      "\<And>X. reach env' X \<subseteq> reach env (X \<union> V')" "V' \<subseteq> vps t \<union> vps u" for env' V'
  proof -
    have "reach env' X \<subseteq> reach env (X \<union> vps_dps [(rb, t, u)])" for X
      using that(5)[of X] reach_subset[of "X \<union> V'" "X \<union> vps_dps [(rb, t, u)]" env] that(6) by auto
    then show ?thesis
      using sresI[of ar V \<tau>' \<sigma> env' "[]" "[]" env "[(rb, t, u)]" ffs frs] that(1-4) by (simp add: cinv_def)
  qed
  consider (VV) x X y Y where "head_of t = Var x X" "head_of u = Var y Y"
    | (VR) x X where "head_of t = Var x X" "is_rigid (head_of u)"
    | (RV) y Y where "is_rigid (head_of t)" "head_of u = Var y Y"
    | (RR) "is_rigid (head_of t)" "is_rigid (head_of u)"
    using head_cases[OF ty(1) nA(1)] head_cases[OF ty(2) nA(2)] by metis
  then show ?thesis
  proof cases
    case VV
    have bt: "body_type env X = return B" "body_type env Y = return B"
      using body_type_head[OF ty(1,3) VV(1) e] body_type_head[OF ty(2,3) VV(2) e] by simp_all
    have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, (rb, t, u) # ffs, frs)"
      using VV bt by (simp add: SIMPL0_step_def cunify_types_same return_def)
    moreover have "ff_shape V (rb, t, u)" using ty VV by (auto simp: ff_shape_def)
    ultimately show ?thesis
      using sresI[of ar V \<tau>' \<sigma> env "[(rb, t, u)]" "[]" env "[(rb, t, u)]" ffs frs] inv ei' rsub vsub hb by auto
  next
    case VR
    have fr: "fr_shape V (rb, t, u)" using ty VR by (auto simp: fr_shape_def)
    from assignment_complete[OF inv ty _ VR(2), where alg = alg] ut
    consider evs where "assignment alg rb t u env = Some (evs, UErr ASSIGN)"
      | env' where "okW (assignment alg rb t u env) env'" "env_inv ar V env'" "solution V \<tau>' \<sigma> env'"
          "extends env' env" "maxidx env' = maxidx env" "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps u)"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, ffs, (rb, t, u) # frs)"
        using VR 1 by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr[OF fr] show ?thesis by blast
    next
      case 2
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env', ffs, frs)"
        using VR 2(1) by (cases "head_of u") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF 2(2-6)] show ?thesis by blast
    qed
  next
    case RV
    have fr: "fr_shape V (rb, u, t)" using ty RV by (auto simp: fr_shape_def)
    from assignment_complete[OF cinv_swap[OF inv] ty(2,1,3) _ RV(1), where alg = alg] uu
    consider evs where "assignment alg rb u t env = Some (evs, UErr ASSIGN)"
      | env' where "okW (assignment alg rb u t env) env'" "env_inv ar V env'" "solution V \<tau>' \<sigma> env'"
          "extends env' env" "maxidx env' = maxidx env" "\<And>X. reach env' X \<subseteq> reach env (X \<union> vps t)"
      by blast
    then show ?thesis
    proof cases
      case 1
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env, ffs, (rb, u, t) # frs)"
        using RV 1 by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def bindW_def)
      with keep_fr'[OF fr] show ?thesis by blast
    next
      case 2
      have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) (env', ffs, frs)"
        using RV 2(1) by (cases "head_of t") (auto simp: SIMPL0_step_def okW_handleW is_rigid_def)
      with asg[OF 2(2-6)] show ?thesis by blast
    qed
  next
    case RR
    define h where "h = head_of t"
    define as where "as = snd (strip_comb t)"
    define h' where "h' = head_of u"
    define bs where "bs = snd (strip_comb u)"
    have t: "t = list_comb h as" using head_of_list_comb[of t] by (simp add: h_def as_def)
    have u0: "u = list_comb h' bs" using head_of_list_comb[of u] by (simp add: bs_def h'_def)
    from ty(1) t obtain Us where tyh: "has_type V (map snd rb) h (foldr fun_type Us B)"
      and tyas: "list_all2 (has_type V (map snd rb)) as Us"
      by (auto simp: has_type_list_comb)
    from ty(2) u0 obtain Us' where tyh': "has_type V (map snd rb) h' (foldr fun_type Us' B)"
      and tybs: "list_all2 (has_type V (map snd rb)) bs Us'"
      by (auto simp: has_type_list_comb)
    have rig: "is_rigid h" "is_rigid h'" using RR by (simp_all add: h_def h'_def)
    note at = conjunct2[OF rigid_tr[OF rig(1) \<sigma>(3)]] conjunct2[OF rigid_tr[OF rig(2) \<sigma>(3)]]
    have "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
      using dsolvedD[OF ds] by (simp add: tr_rlist_abs mk_subst_Abs_m Abs_m_equiv_reflect)
    then have "tr h \<degree>\<degree> map (\<lambda>a. mk_subst \<sigma> (tr a)) as \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr h' \<degree>\<degree> map (\<lambda>b. mk_subst \<sigma> (tr b)) bs"
      using rigid_tr[OF rig(1) \<sigma>(3)] rigid_tr[OF rig(2) \<sigma>(3)] t u0
      by (simp add: tr_list_comb comp_def)
    from atom_apps_equiv[OF at this] have trh: "tr h = tr h'"
      and args: "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (\<lambda>a. mk_subst \<sigma> (tr a)) as) (map (\<lambda>b. mk_subst \<sigma> (tr b)) bs)"
      by simp_all
    have hu: "h' = h" using tr_rigid_inj[OF rig(2,1)] trh by simp
    have u: "u = list_comb h bs" using u0 hu by simp
    have len: "length as = length bs" using list_all2_lengthD[OF args] by simp
    have lUs: "length Us = length as" "length Us' = length bs"
      using list_all2_lengthD[OF tyas] list_all2_lengthD[OF tybs] by simp_all
    have "foldr fun_type Us B = foldr fun_type Us' B" using has_type_unique[OF tyh tyh'[unfolded hu]] .
    with lUs len have UU: "Us' = Us" using foldr_fun_type_inj[of Us Us' B B] by simp
    have h0: "\<nexists>f u. h = f $ u" using head_of_not_App h_def by metis
    have step_eq: "SIMPL0_step alg F (rb, t, u) env ffs frs = simrands F rb u t u (env, ffs, frs)"
      using rig(1) hu by (auto simp: SIMPL0_step_def is_rigid_def h_def h'_def cunify_types_same bindW_def
        returnW_def case_prod_beta option.map_ident option.map_id)
    have wfa: "wf_tm ar rb (as ! i)" "wf_tm ar rb (bs ! i)" if "i < length as" for i
      using wfd that len t u by (auto simp: wf_tm_list_comb)
    have bla: "below (maxidx env) (as ! i)" "below (maxidx env) (bs ! i)" if "i < length as" for i
      using bl that len t u by (auto simp: below_list_comb)
    have dsa: "dsolved \<sigma> (rb, as ! i, bs ! i)" if "i < length as" for i
    proof (rule dsolvedI)
      have "mk_subst \<sigma> (tr (as ! i)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (bs ! i))"
        using list_all2_nthD[OF args] that len by simp
      then show "mk_subst \<sigma> (tr (rlist_abs rb (as ! i))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb (bs ! i)))"
        by (simp add: tr_rlist_abs mk_subst_Abs_m equiv_Abs_m)
    qed
    have F: "\<exists>st'. okW (F (rb, as ! i, bs ! i) st) st' \<and> sres ar V \<tau>' \<sigma> [(rb, as ! i, bs ! i)] st st'"
      if i: "i < length as" and st: "cinv ar V \<tau>' \<sigma> (fst st) []" "maxidx (fst st) = maxidx env" for i st
    proof (rule IH[OF RR(1)])
      show "t = list_comb (head_of t) as" using t by (simp add: h_def)
      show "has_type V (map snd rb) (head_of t) (foldr fun_type Us B)" using tyh by (simp add: h_def)
      show "list_all2 (has_type V (map snd rb)) as Us" by (rule tyas)
      show "i < length as" by (rule i)
      have "has_type V (map snd rb) (bs ! i) (Us ! i)" using list_all2_nthD[OF tybs] i len UU by simp
      moreover have "has_type V (map snd rb) (as ! i) (Us ! i)" using list_all2_nthD[OF tyas i] .
      ultimately show "cinv ar V \<tau>' \<sigma> (fst st) [(rb, as ! i, bs ! i)]"
        using st wfa[OF i] bla[OF i] dsa[OF i] wfd by (auto simp: cinv_def)
    qed
    have "\<exists>st'. okW (simrands F rb u (list_comb h as) (list_comb h bs) (env, ffs, frs)) st' \<and>
      sres ar V \<tau>' \<sigma> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) (env, ffs, frs) st'"
      by (rule simrands_complete[where F = F and st = "(env, ffs, frs)", OF F h0 len])
        (use c0 in simp_all)
    then obtain st' where st': "okW (simrands F rb u (list_comb h as) (list_comb h bs) (env, ffs, frs)) st'"
      "sres ar V \<tau>' \<sigma> (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) (env, ffs, frs) st'"
      by blast
    have "vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> reach env (vps_dps [(rb, t, u)])"
    proof -
      have "vps_dps (map (\<lambda>(a, b). (rb, a, b)) (zip as bs)) \<subseteq> vps t \<union> vps u"
        using t u by (fastforce simp: vps_list_comb dest: set_zip_leftD set_zip_rightD)
      then show ?thesis using reach_incl[of "vps t \<union> vps u" env] by auto
    qed
    note sr = sres_mono_dps[OF st'(2) this]
    have "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
      using step_eq st'(1) by (simp add: t[symmetric] u[symmetric])
    with sr show ?thesis by blast
  qed
qed

text \<open>
  \<^const>\<open>SIMPL0\<close> terminates without an exception on a pair in the invariant, by induction on
  the size \<^const>\<open>dsz\<close> of the instance of the pair.
\<close>

lemma SIMPL0_complete_aux:
  "dsz \<tau>' \<sigma> rb t T < n \<Longrightarrow> cinv ar V \<tau>' \<sigma> env [(rb, t, u)] \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow>
    \<exists>st'. okW (SIMPL0 alg (rb, t, u) (env, ffs, frs)) st' \<and> sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) st'"
proof (induction n arbitrary: rb t u T env ffs frs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note inv = Suc.prems(2)
  note \<sigma> = solutionD[OF cinvD(2)[OF inv]]
  obtain rb' t' u' T0 where hd: "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env)"
    and inv': "cinv ar V \<tau>' \<sigma> env [(rb', t', u')]"
    and tyt0: "has_type V (map snd rb) t T0" and rb': "map snd rb' = rev (arg_types T0) @ map snd rb"
    and ty': "has_type V (map snd rb') t' (res_type T0)" "has_type V (map snd rb') u' (res_type T0)"
    and nA: "\<not> is_Abs (head_of t')" "\<not> is_Abs (head_of u')"
    and vt: "vps t' \<subseteq> reach env (vps t)" "vps u' \<subseteq> reach env (vps u)"
    and ut: "\<And>F U. head_of t' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and uu: "\<And>F U. head_of u' = Var F U \<Longrightarrow> vt_lookup (tenv env) F = None"
    and eq: "mk_subst \<sigma> (tr (rlist_abs rb' t')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))"
    by (rule head_norm_dpair_complete[OF inv, where alg = alg]) blast
  have T0: "T0 = T" by (rule has_type_unique[OF tyt0 Suc.prems(3)])
  define B where "B = res_type T"
  have nfB: "\<not> is_funT B" by (simp add: B_def res_type_base)
  have TT: "foldr fun_type (rev (map snd rb')) B = foldr fun_type (rev (map snd rb)) T"
    using rb' T0 arg_res_type[of T] by (simp add: B_def)
  have dszeq: "dsz \<tau>' \<sigma> rb' t' B = dsz \<tau>' \<sigma> rb t T"
    by (rule dsz_equiv[OF Suc.prems(3) ty'(1)[unfolded T0, folded B_def] TT eq \<sigma>(1,2)])
  have "\<exists>st'. okW (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) st' \<and>
    sres ar V \<tau>' \<sigma> [(rb', t', u')] (env, ffs, frs) st'"
  proof (rule SIMPL0_step_complete[OF inv' ty'[unfolded T0, folded B_def] nfB nA ut uu])
    fix i and st :: sstate and as bs Us
    assume rig: "is_rigid (head_of t')" and t': "t' = list_comb (head_of t') as"
      and tyh: "has_type V (map snd rb') (head_of t') (foldr fun_type Us B)"
      and tyas: "list_all2 (has_type V (map snd rb')) as Us" and i: "i < length as"
      and ci: "cinv ar V \<tau>' \<sigma> (fst st) [(rb', as ! i, bs ! i)]"
    have "dsz \<tau>' \<sigma> rb' (as ! i) (Us ! i) < dsz \<tau>' \<sigma> rb' (list_comb (head_of t') as) B"
      by (rule dsz_args[OF tyh tyas rig \<sigma>(1,2,3) i])
    with dszeq t' Suc.prems(1) have lt: "dsz \<tau>' \<sigma> rb' (as ! i) (Us ! i) < n" by simp
    have tyi: "has_type V (map snd rb') (as ! i) (Us ! i)" using list_all2_nthD[OF tyas i] .
    obtain env1 ffs1 frs1 where st: "st = (env1, ffs1, frs1)" by (cases st)
    from Suc.IH[OF lt ci[unfolded st, simplified] tyi, of ffs1 frs1] st
    show "\<exists>st'. okW (SIMPL0 alg (rb', as ! i, bs ! i) st) st' \<and> sres ar V \<tau>' \<sigma> [(rb', as ! i, bs ! i)] st st'"
      by simp
  qed
  then obtain st' where st': "okW (SIMPL0_step alg (SIMPL0 alg) (rb', t', u') env ffs frs) st'"
    "sres ar V \<tau>' \<sigma> [(rb', t', u')] (env, ffs, frs) st'" by blast
  have "okW (SIMPL0 alg (rb, t, u) (env, ffs, frs)) st'"
    using hd st'(1) by (subst SIMPL0_unfold) auto
  moreover have "sres ar V \<tau>' \<sigma> [(rb, t, u)] (env, ffs, frs) st'"
  proof (rule sres_mono_dps[OF st'(2)])
    show "vps_dps [(rb', t', u')] \<subseteq> reach env (vps_dps [(rb, t, u)])"
      using vt reach_subset[of "vps t" "vps t \<union> vps u" env] reach_subset[of "vps u" "vps t \<union> vps u" env]
      by auto
  qed
  ultimately show ?case by blast
qed

theorem SIMPL0_complete:
  assumes "cinv ar V \<tau>' \<sigma> env [dp]"
  shows "\<exists>st'. okW (SIMPL0 alg dp (env, ffs, frs)) st' \<and> sres ar V \<tau>' \<sigma> [dp] (env, ffs, frs) st'"
proof -
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  from cinvD(3)[OF assms, of dp] dp obtain T where "has_type V (map snd rb) t T" by auto
  from SIMPL0_complete_aux[OF lessI assms[unfolded dp] this, of alg ffs frs] dp show ?thesis by blast
qed

subsection \<open>Completeness of \<open>SIMPL\<close>\<close>

lemma sres_set: "set dps = set dps' \<Longrightarrow> sres ar V \<tau>' \<sigma> dps st st' = sres ar V \<tau>' \<sigma> dps' st st'"
  by (simp add: sres_def)

lemma foldrW_SIMPL0_complete:
  "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow>
    \<exists>st'. okW (foldrW (SIMPL0 alg) dps (env, [], [])) st' \<and> sres ar V \<tau>' \<sigma> dps (env, [], []) st'"
proof (induction dps)
  case Nil
  then show ?case using sres_refl[OF cinv_Nil[OF Nil]] by simp
next
  case (Cons dp dps)
  from Cons.prems have c1: "cinv ar V \<tau>' \<sigma> env [dp]" and c2: "cinv ar V \<tau>' \<sigma> env dps"
    by (simp_all add: cinv_def)
  from Cons.IH[OF c2] obtain st1 where r1: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) st1"
    "sres ar V \<tau>' \<sigma> dps (env, [], []) st1" by blast
  from sresD[OF r1(2)] obtain env1 ffn frn where s1: "st1 = (env1, ffn @ [], frn @ [])"
    "cinv ar V \<tau>' \<sigma> env1 (ffn @ frn)" "maxidx env1 = maxidx env"
    by blast
  have "cinv ar V \<tau>' \<sigma> env1 [dp]" using cinv_transfer[OF c1 cinv_Nil[OF s1(2)] s1(3)] .
  from SIMPL0_complete[OF this, of alg ffn frn] obtain st2 where
    r2: "okW (SIMPL0 alg dp (env1, ffn, frn)) st2" "sres ar V \<tau>' \<sigma> [dp] (env1, ffn, frn) st2" by blast
  have "okW (foldrW (SIMPL0 alg) (dp # dps) (env, [], [])) st2" using r1(1) r2(1) s1(1) by auto
  moreover have "sres ar V \<tau>' \<sigma> (dp # dps) (env, [], []) st2"
    using sres_trans[OF r1(2)[unfolded s1(1) append_Nil2] r2(2)] sres_set[of "dps @ [dp]" "dp # dps"]
    by simp
  ultimately show ?case by blast
qed

lemma changed_typed:
  assumes "vt_is_empty (tyenv env)" "env_typed V env"
  shows "vtyped V t \<Longrightarrow> changed env t = return (\<exists>x T. head_of t = Var x T \<and> vt_lookup (tenv env) x \<noteq> None)"
proof (induction t)
  case (Var x T)
  from lookup_typed[OF assms, of x T] Var obtain r where
    "lookup env x T = return r" "\<And>u. r = Some u \<Longrightarrow> vt_lookup (tenv env) x = Some (T, u)"
    by auto
  moreover have "vt_lookup (tenv env) x = None" if "r = None"
    using that lookup_unbound[OF assms(1)] \<open>lookup env x T = return r\<close>
    by (cases "vt_lookup (tenv env) x") (auto simp: lookup_bound[OF assms(1)] return_def lookup_def
      unified_empty var_clash_def raise_def split: if_splits)
  ultimately show ?case by (cases r) (auto simp: return_def)
qed (simp_all add: return_def)

lemma existsM_return: "(\<And>x. x \<in> set xs \<Longrightarrow> P x = return (Q x)) \<Longrightarrow> existsM P xs = return (\<exists>x\<in>set xs. Q x)"
  by (induction xs) (auto simp: return_def)

text \<open>The result of \<^const>\<open>SIMPL\<close>: no head variable of the pairs is bound any more.\<close>

definition simpl_res :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow>
    dpair list \<Rightarrow> env \<Rightarrow> sstate \<Rightarrow> bool" where
  "simpl_res ar V \<tau>' \<sigma> dps env st' \<longleftrightarrow> (case st' of (env', ffs, frs) \<Rightarrow>
    cinv ar V \<tau>' \<sigma> env' (ffs @ frs) \<and> extends env' env \<and> maxidx env' = maxidx env \<and>
    (\<forall>X. reach env' X \<subseteq> reach env (X \<union> vps_dps dps)) \<and> vps_dps (ffs @ frs) \<subseteq> reach env (vps_dps dps) \<and>
    (\<forall>dp\<in>set ffs. ff_shape V dp) \<and> (\<forall>dp\<in>set frs. fr_shape V dp) \<and>
    (\<forall>dp\<in>set (ffs @ frs). heads_unb env' dp))"

lemma reach_absorb: "A \<subseteq> reach env B \<Longrightarrow> reach env (X \<union> A \<union> B) = reach env (X \<union> B)"
  using reach_mono[of A env B] reach_incl[of B env] by (auto simp: reach_Un)

lemma SIMPL_complete_aux:
  "card (unb env (vps_dps dps)) < n \<Longrightarrow> cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow>
    \<exists>st'. okW (SIMPL alg env dps) st' \<and> simpl_res ar V \<tau>' \<sigma> dps env st'"
proof (induction n arbitrary: env dps)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note ei = env_invD[OF cinvD(1)[OF Suc.prems(2)]]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF ei(2)])
  from foldrW_SIMPL0_complete[OF Suc.prems(2), of alg] obtain st1 where
    r1: "okW (foldrW (SIMPL0 alg) dps (env, [], [])) st1" "sres ar V \<tau>' \<sigma> dps (env, [], []) st1" by blast
  from sresD[OF r1(2)] obtain env1 ffs frs where s1: "st1 = (env1, ffs @ [], frs @ [])"
    "cinv ar V \<tau>' \<sigma> env1 (ffs @ frs)" "env_inv ar V env1" "extends env1 env" "maxidx env1 = maxidx env"
    "\<And>X. reach env1 X \<subseteq> reach env (X \<union> vps_dps dps)" "vps_dps (ffs @ frs) \<subseteq> reach env (vps_dps dps)"
    "\<And>dp. dp \<in> set ffs \<Longrightarrow> ff_shape V dp" "\<And>dp. dp \<in> set frs \<Longrightarrow> fr_shape V dp"
    "\<And>dp. dp \<in> set (ffs @ frs) \<Longrightarrow> heads_unb env dp"
    by blast
  note ei1 = env_invD[OF s1(3)]
  have e1: "vt_is_empty (tyenv env1)" by (rule wf_envD(1)[OF ei1(2)])
  define dps' where "dps' = frs @ ffs"
  define ch where "ch = (\<lambda>s. \<exists>x T. head_of s = Var x T \<and> vt_lookup (tenv env1) x \<noteq> None)"
  have vty: "vtyped V t \<and> vtyped V u" if "(rb, t, u) \<in> set dps'" for rb t u
    using cinvD(3)[OF s1(2), of "(rb, t, u)"] that by (auto simp: dps'_def intro: has_type_vtyped)
  have ex: "existsM (\<lambda>(_, t, u). do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) dps' =
    return (\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
  proof (rule existsM_return)
    fix dp assume "dp \<in> set dps'"
    obtain rb t u where dp0: "dp = (rb, t, u)" by (cases dp)
    with \<open>dp \<in> set dps'\<close> vty have dp: "dp = (rb, t, u)" "vtyped V t" "vtyped V u" by auto
    then show "(case dp of (_, t, u) \<Rightarrow> do {b \<leftarrow> changed env1 t; if b then return True else changed env1 u}) =
      return (case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u)"
      by (auto simp: changed_typed[OF e1 ei1(3)] ch_def return_def)
  qed
  have body: "SIMPL alg env dps = do {
      st \<leftarrow> foldrW (SIMPL0 alg) dps (env, [], []);
      case st of (env', ffs, frs) \<Rightarrow> do {
        let dps = frs @ ffs;
        b \<leftarrow> liftM (existsM (\<lambda>(_, t, u).
          do {b \<leftarrow> changed env' t; if b then return True else changed env' u}) dps);
        if b then SIMPL alg env' dps else returnW st}}"
    by (subst SIMPL.simps) (rule refl)
  show ?case
  proof (cases "\<exists>dp\<in>set dps'. case dp of (_, t, u) \<Rightarrow> ch t \<or> ch u")
    case False
    have "okW (SIMPL alg env dps) st1" using r1(1) s1(1) ex False
      by (subst body) (auto simp: dps'_def return_def)
    moreover have "heads_unb env1 dp" if "dp \<in> set (ffs @ frs)" for dp
    proof -
      obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
      with that have "(rb, t, u) \<in> set dps'" by (auto simp: dps'_def)
      with False have "\<not> ch t" "\<not> ch u" by auto
      then show ?thesis unfolding dp heads_unb_def prod.case ch_def by blast
    qed
    ultimately show ?thesis using s1 by (auto simp: simpl_res_def)
  next
    case True
    then obtain rb t u where dp: "(rb, t, u) \<in> set dps'" and cht: "ch t \<or> ch u" by blast
    have c1: "cinv ar V \<tau>' \<sigma> env1 dps'" using s1(2) by (auto simp: cinv_def dps'_def)
    text \<open>The changed head variable was unbound and reachable before the round.\<close>
    obtain s x T where s: "s \<in> {t, u}" "head_of s = Var x T" "vt_lookup (tenv env1) x \<noteq> None"
      using cht unfolding ch_def by blast
    have hb: "heads_unb env (rb, t, u)" using s1(10) dp by (auto simp: dps'_def)
    then have xu: "vt_lookup (tenv env) x = None" using s(1,2) unfolding heads_unb_def prod.case by blast
    have "vps s \<subseteq> vps_dps dps'" using dp s(1) by auto
    moreover have "vps_dps dps' \<subseteq> reach env (vps_dps dps)" using s1(7) by (auto simp: dps'_def)
    ultimately have xr: "(x, T) \<in> reach env (vps_dps dps)" using vps_head_of[OF s(2)] by blast
    have xin: "(x, T) \<in> unb env (vps_dps dps)" using xr xu by (simp add: unb_def lk_def)
    have Vx: "V x = T" using vty[OF dp] s vps_head_of[OF s(2)] by (auto simp: vtyped_def)
    have xout: "(x, T) \<notin> unb env1 (vps_dps dps')"
    proof -
      from s(3) obtain U w where "vt_lookup (tenv env1) x = Some (U, w)" by auto
      moreover from this env_typedD[OF ei1(3)] Vx have "U = T" by blast
      ultimately show ?thesis by (simp add: unb_def lk_def)
    qed
    have sub: "unb env1 (vps_dps dps') \<subseteq> unb env (vps_dps dps)"
    proof
      fix y assume y: "y \<in> unb env1 (vps_dps dps')"
      then have "y \<in> reach env1 (vps_dps dps')" by (simp add: unb_def)
      with s1(6) have "y \<in> reach env (vps_dps dps' \<union> vps_dps dps)" by blast
      moreover have "vps_dps dps' \<subseteq> reach env (vps_dps dps)" using s1(7) by (auto simp: dps'_def)
      ultimately have "y \<in> reach env (vps_dps dps)" using reach_absorb[of "vps_dps dps'" env "vps_dps dps" "{}"]
        by simp
      moreover have "lk env (fst y) (snd y) = None"
        using y extends_lk[OF s1(4)] by (cases "lk env (fst y) (snd y)") (auto simp: unb_def)
      ultimately show "y \<in> unb env (vps_dps dps)" by (simp add: unb_def)
    qed
    have fin: "finite (unb env (vps_dps dps))"
      by (rule finite_subset[OF _ finite_reach[of "vps_dps dps" env]]) (auto simp: unb_def)
    have "card (unb env1 (vps_dps dps')) < card (unb env (vps_dps dps))"
      using sub xin xout by (intro psubset_card_mono[OF fin]) blast
    with Suc.prems(1) have lt: "card (unb env1 (vps_dps dps')) < n" by simp
    from Suc.IH[OF lt c1] obtain st' where r2: "okW (SIMPL alg env1 dps') st'"
      "simpl_res ar V \<tau>' \<sigma> dps' env1 st'" by blast
    have "okW (SIMPL alg env dps) st'" using r1(1) s1(1) ex True r2(1)
      by (subst body) (auto simp: dps'_def return_def)
    moreover have "simpl_res ar V \<tau>' \<sigma> dps env st'"
    proof -
      obtain env2 ffs2 frs2 where st': "st' = (env2, ffs2, frs2)" by (cases st')
      have v1: "vps_dps dps' \<subseteq> reach env (vps_dps dps)" using s1(7) by (auto simp: dps'_def)
      from r2(2) st' have r: "cinv ar V \<tau>' \<sigma> env2 (ffs2 @ frs2)" "extends env2 env1" "maxidx env2 = maxidx env1"
        "\<And>X. reach env2 X \<subseteq> reach env1 (X \<union> vps_dps dps')" "vps_dps (ffs2 @ frs2) \<subseteq> reach env1 (vps_dps dps')"
        "\<forall>dp\<in>set ffs2. ff_shape V dp" "\<forall>dp\<in>set frs2. fr_shape V dp" "\<forall>dp\<in>set (ffs2 @ frs2). heads_unb env2 dp"
        by (auto simp: simpl_res_def)
      have "reach env2 X \<subseteq> reach env (X \<union> vps_dps dps)" for X
        using r(4)[of X] s1(6)[of "X \<union> vps_dps dps'"] reach_absorb[OF v1, of X] by (auto simp: Un_ac)
      moreover have "vps_dps (ffs2 @ frs2) \<subseteq> reach env (vps_dps dps)"
        using r(5) s1(6)[of "vps_dps dps'"] reach_absorb[OF v1, of "{}"] by auto
      ultimately show ?thesis using r s1(4,5) st' extends_trans[OF r(2) s1(4)] by (simp add: simpl_res_def)
    qed
    ultimately show ?thesis by blast
  qed
qed

theorem SIMPL_complete:
  "cinv ar V \<tau>' \<sigma> env dps \<Longrightarrow> \<exists>st'. okW (SIMPL alg env dps) st' \<and> simpl_res ar V \<tau>' \<sigma> dps env st'"
  using SIMPL_complete_aux[OF lessI] by blast

end

end
