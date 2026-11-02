section \<open>Completeness of the Simplification Phase\<close>

theory Unify_Simpl_Complete
  imports Unify_Occurs_Complete "Pure_Pattern_Correctness.Pattern_Termination"
begin

context csig
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

lemma extends_unbound: "extends env env' \<Longrightarrow> vt_lookup (tenv env') x = None \<Longrightarrow> vt_lookup (tenv env) x = None"
  unfolding extends_def by (cases x; cases "vt_lookup (tenv env) x") force+

lemma heads_unb_extends: "heads_unb env' dp \<Longrightarrow> extends env env' \<Longrightarrow> heads_unb env dp"
  by (auto simp: heads_unb_def split: prod.splits intro: extends_unbound)

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

subsection \<open>Completeness of \<open>SIMPL\<close>\<close>

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

lemma reach_absorb: "A \<subseteq> reach env B \<Longrightarrow> reach env (X \<union> A \<union> B) = reach env (X \<union> B)"
  using reach_mono[of A env B] reach_incl[of B env] by (auto simp: reach_Un)

end

end
