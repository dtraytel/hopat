section \<open>The Shape of Head-Normalized Disagreement Pairs\<close>

theory Unify_Shape
  imports Unify_Beta
begin

context csig
begin

text \<open>
  \<open>MATCH\<close> relies on two properties of the flex-rigid pairs \<open>(rb, t, u)\<close> that \<open>SIMPL\<close> returns,
  both established by the head normalization of pairs (\<^const>\<open>head_norm_dpair\<close>):
  \<^item> the flexible side \<open>t = ?F t\<^sub>1 \<dots> t\<^sub>k\<close> is \<open>\<eta>\<close>-expanded, so its type is not a function type and
    \<open>?F\<close> takes exactly \<open>k\<close> arguments: the binder types of the type of \<open>?F\<close> are as many as the
    arguments \<open>t\<^sub>i\<close>, which \<open>MATCH\<close> takes for granted;
  \<^item> the rigid side \<open>u\<close> is in head normal form, so that its abstractions, when \<open>MATCH\<close> copies them,
    have no arguments.
\<close>


subsection \<open>Head normal forms\<close>

fun hnf :: "pterm \<Rightarrow> bool" where
  "hnf (Abs _ _ b) = hnf b"
| "hnf t = (\<not> is_Abs (head_of t))"

lemma hnf_nonAbs: "\<not> is_Abs t \<Longrightarrow> hnf t \<longleftrightarrow> \<not> is_Abs (head_of t)"
  by (cases t) auto

lemma head_norm_hnf:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> hnf t'"
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
      have hnf_nf: "hnf nf" by (rule "1.IH"[OF nf refl])
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where "nf = Abs a T body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl] show ?thesis .
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with hnf_nf False show ?thesis by (simp add: hnf_nonAbs)
      qed
    qed
  qed (use "1.hyps" ok in auto)
qed

lemma is_Abs_head_of_incr_bv: "is_Abs (head_of (incr_bv i l t)) = is_Abs (head_of t)"
  by (induction i l t rule: incr_bv.induct) auto

lemma etif_hnf:
  assumes "vt_is_empty tye"
  shows "ok (etif tye T t) t' \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> hnf t \<Longrightarrow> hnf t'"
proof (induction T arbitrary: t t')
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
    case True
    then obtain T1 U where Ts: "Ts = [T1, U]" by auto
    with True Type.prems(1) obtain u where u: "ok (etif tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u"
      by (subst (asm) etif.simps) (auto split: ptyp.splits list.splits if_splits)
    have "hnf (incr_boundvars 1 t $ Bound 0)"
      using Type.prems(2,3) by (simp add: hnf_nonAbs incr_boundvars_def is_Abs_head_of_incr_bv)
    with Type.IH[of U] Ts u t' show ?thesis by simp
  next
    case False
    with Type.prems have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits if_splits)
    with Type.prems show ?thesis by simp
  qed
next
  case (TFree a S)
  then show ?case by (subst (asm) etif.simps) auto
next
  case (TVar v S)
  from assms have "type_lookup tye v S = return None"
    by (simp add: type_lookup_def vt_is_empty_lookup)
  with TVar.prems show ?case by (subst (asm) etif.simps) simp
qed

lemma eta_norm_hnf:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (eta_norm env rb t) t' \<Longrightarrow> hnf t \<Longrightarrow> hnf t'"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  then show ?case by auto
qed (auto simp: eta_norm_nonAbs intro: etif_hnf[OF assms])

lemma hnf_strip_abs_body: "hnf t \<Longrightarrow> hnf (strip_abs_body t)"
  by (induction t rule: strip_abs_body.induct) auto


subsection \<open>Stripping common abstractions\<close>

text \<open>The types of the outer abstractions of a term, innermost first (as in a binder).\<close>

fun abs_tys :: "pterm \<Rightarrow> ptyp list" where
  "abs_tys (Abs _ T b) = abs_tys b @ [T]"
| "abs_tys _ = []"

lemma new_dpair_shape:
  "okW (new_dpair alg rb t u env) ((rb', t', u'), env') \<Longrightarrow> wf_dp ar (rb, t, u) \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and>
    map snd rb' = abs_tys t @ map snd rb \<and> map snd rb' = abs_tys u @ map snd rb \<and>
    \<not> is_Abs t' \<and> \<not> is_Abs u'"
proof (induction alg rb t u env rule: new_dpair.induct)
  case (1 alg rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg T U env) env1"
    and rec: "okW (new_dpair alg ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  have gT: "ground ar T" "ground ar U" using "1.prems"(2) by (simp_all add: wf_tm_def)
  from cunify_types_ground[OF gT cu] have TU: "T = U" by simp
  have wf1: "wf_dp ar ((c, T) # rb, body1, body2)"
    using "1.prems"(2) TU by (auto simp: wf_tm_def binders_ok_def)
  from "1.IH"[OF cu c_def rec wf1] TU show ?case by auto
qed auto


subsection \<open>Saturated flexible terms\<close>

fun is_funT :: "ptyp \<Rightarrow> bool" where
  "is_funT (Type a [_, _]) = (a = STR ''fun'')"
| "is_funT _ = False"

text \<open>A term is \<^emph>\<open>saturated\<close> if its (fast) type is not a function type.\<close>

definition satT :: "env \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> bool" where
  "satT env Ts t \<longleftrightarrow> (\<exists>R. ok (env_fastype env Ts t) R \<and> \<not> is_funT R)"

lemma env_fastype_empty_tyenv:
  "vt_is_empty (tyenv env1) \<Longrightarrow> vt_is_empty (tyenv env2) \<Longrightarrow>
    env_fastype env1 Ts t = env_fastype env2 Ts t"
  by (induction env1 Ts t rule: env_fastype.induct) (simp_all add: devar_empty)

lemma satT_cong:
  "vt_is_empty (tyenv env1) \<Longrightarrow> vt_is_empty (tyenv env2) \<Longrightarrow> satT env1 Ts t \<longleftrightarrow> satT env2 Ts t"
  using env_fastype_empty_tyenv[of env1 env2 Ts t] by (simp add: satT_def)

lemma env_fastype_incr_bv:
  "ok (env_fastype env Ts t) T \<Longrightarrow> proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> nat_of_integer lev \<le> length Ts \<Longrightarrow>
    ok (env_fastype env (take (nat_of_integer lev) Ts @ U # drop (nat_of_integer lev) Ts)
      (incr_bv 1 lev t)) T"
proof (induction t arbitrary: Ts lev T)
  case (Bound i)
  from Bound.prems(1) have i: "ok (nth Ts i) T" by (auto simp: ok_handle not_ok_reraise)
  then have i': "0 \<le> i" "nat_of_integer i < length Ts" "T = Ts ! nat_of_integer i"
    by (simp_all add: ok_nth)
  let ?l = "nat_of_integer lev"
  show ?case
  proof (cases "lev \<le> i")
    case True
    then have "?l \<le> nat_of_integer i" using Bound.prems(3) i'(1) by (simp add: nat_of_integer_less_iff[symmetric] not_less integer_reps)
    moreover have "nat_of_integer (i + 1) = Suc (nat_of_integer i)" using i'(1) by (simp add: integer_reps)
    ultimately show ?thesis using True i' Bound.prems(4)
      by (simp add: ok_handle ok_nth nth_append min_def integer_reps)
  next
    case False
    then have "nat_of_integer i < ?l" using Bound.prems(3) i'(1) by (simp add: integer_reps)
    with False i' Bound.prems(4) show ?thesis
      by (simp add: ok_handle ok_nth nth_append min_def)
  qed
next
  case (Abs a T' b)
  from Abs.prems(1) obtain U' where b: "ok (env_fastype env (T' # Ts) b) U'" and T: "T = T' \<rightarrow>\<^sub>T U'"
    by auto
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using Abs.prems(3) by (simp add: integer_reps)
  with Abs.IH[OF b, of "lev + 1"] Abs.prems(2-4) T show ?case by simp
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
  from r obtain A where T': "T' = Type STR ''fun'' [A, T]"
    by (auto split: ptyp.splits list.splits if_splits)
  from App.IH(1)[OF f] App.prems(2-4) have "ok (env_fastype env ?Ts (incr_bv 1 lev f)) T0" by simp
  with d T' show ?case by simp
qed simp_all

lemma etif_sat:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (etif (tyenv env) T0 t) t' \<Longrightarrow> ground ar T0 \<Longrightarrow> ok (env_fastype env Ts t) T0 \<Longrightarrow>
    proper t \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> satT env (abs_tys t' @ Ts) (strip_abs_body t')"
proof (induction T0 arbitrary: t t' Ts)
  case (Type a Tys)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Tys = [T1, U])")
    case True
    then obtain T1 U where Tys: "Tys = [T1, U]" and a: "a = STR ''fun''" by auto
    with Type.prems(1) obtain u where u: "ok (etif (tyenv env) U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u"
      by (subst (asm) etif.simps) (auto split: ptyp.splits list.splits if_splits)
    have "ok (env_fastype env (T1 # Ts) (incr_boundvars 1 t)) (Type a Tys)"
      using env_fastype_incr_bv[OF Type.prems(3,4), of 0 T1] by (simp add: incr_boundvars_def)
    then have f: "ok (env_fastype env (T1 # Ts) (incr_boundvars 1 t $ Bound 0)) U"
      using Tys a by (simp add: devar_empty[OF assms])
    have pr: "proper (incr_boundvars 1 t $ Bound 0)"
      using Type.prems(4) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
    have gU: "ground ar U" using Type.prems(2) Tys by simp
    from Tys have "U \<in> set Tys" by simp
    from Type.IH[OF this u gU f pr] t' show ?thesis by simp
  next
    case False
    with Type.prems(1) have t': "t' = t"
      by (subst (asm) etif.simps) (auto split: list.splits if_splits)
    have nf: "\<not> is_funT (Type a Tys)"
      using False by (cases "Type a Tys" rule: is_funT.cases) auto
    have "satT env Ts t" using Type.prems(3) nf by (auto simp: satT_def)
    with t' Type.prems(5) show ?thesis by (cases t) auto
  qed
next
  case (TFree b S)
  then have "t' = t" by (subst (asm) etif.simps) simp
  with TFree.prems show ?case by (cases t) (auto simp: satT_def)
qed simp

lemma eta_norm_nonAbs_sat:
  assumes "vt_is_empty (tyenv env)" "\<not> is_Abs t" "ok (eta_norm env rb t) t'" "binders_ok ar rb"
    "typs_ok ar t" "proper t"
  shows "satT env (abs_tys t' @ map snd rb) (strip_abs_body t')"
proof -
  from assms(3) obtain T where T: "ok (fastype env rb t) T" and e: "ok (etif (tyenv env) T t) t'"
    using assms(2) by (auto simp: eta_norm_nonAbs)
  have "ground ar T" by (rule fastype_ground[OF assms(1,4,5) T])
  from etif_sat[OF assms(1) e this T[unfolded fastype_def] assms(6,2)] show ?thesis .
qed

lemma eta_norm_sat:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (eta_norm env rb t) t' \<Longrightarrow> binders_ok ar rb \<Longrightarrow> typs_ok ar t \<Longrightarrow> proper t \<Longrightarrow>
    satT env (abs_tys t' @ map snd rb) (strip_abs_body t')"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rb) body) b'"
    and t': "t' = Abs a T b'" by auto
  have "binders_ok ar ((a, T) # rb)" using Abs.prems(2,3) by (simp add: binders_ok_def)
  from Abs.IH[OF b' this] Abs.prems(3,4) t' show ?case by simp
qed (erule eta_norm_nonAbs_sat[OF assms, rotated]; simp)+


subsection \<open>Saturated flexible terms take all their arguments\<close>

fun n_arrows :: "ptyp \<Rightarrow> nat" where
  "n_arrows (Type a [A, B]) = (if a = STR ''fun'' then Suc (n_arrows B) else 0)"
| "n_arrows _ = 0"

lemma n_arrows_nonfun: "\<not> is_funT R \<Longrightarrow> n_arrows R = 0"
  by (cases R rule: n_arrows.cases) auto

lemma binder_types_n_arrows:
  assumes "vt_is_empty (tyenv env)"
  shows "ground ar T \<Longrightarrow> ok (binder_types env T) Ts \<Longrightarrow> length Ts = n_arrows T"
proof (induction T arbitrary: Ts)
  case (Type a Tys)
  note gr = Type.prems(1) and bt = Type.prems(2)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U'. Tys = [T1, U'])")
    case True
    then obtain T1 U' where Tys: "Tys = [T1, U']" and a: "a = STR ''fun''" by auto
    from bt Tys a obtain Us' where "ok (binder_types env U') Us'" "Ts = T1 # Us'"
      by (subst (asm) binder_types.simps) auto
    moreover have "ground ar U'" using gr Tys by simp
    ultimately show ?thesis using Type.IH[of U'] Tys a by simp
  next
    case False
    from bt False have "Ts = []"
      by (subst (asm) binder_types.simps) (auto split: list.splits if_splits)
    with False show ?thesis by (cases "Type a Tys" rule: n_arrows.cases) auto
  qed
next
  case (TFree a S)
  then show ?case by (subst (asm) binder_types.simps) simp
qed simp

lemma list_comb_snoc: "list_comb h (args @ [a]) = list_comb h args $ a"
  by (simp add: list_comb_def)

lemma env_fastype_list_comb:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (env_fastype env Ts (list_comb h args)) R \<Longrightarrow>
    \<exists>T0. ok (env_fastype env Ts h) T0 \<and> n_arrows T0 = length args + n_arrows R"
proof (induction args arbitrary: R rule: rev_induct)
  case (snoc a args)
  from snoc.prems obtain T where f: "ok (env_fastype env Ts (list_comb h args)) T"
    and r: "ok (case T of Type b Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if b = STR ''fun'' then return U
        else raise (Term_Error funerr [list_comb h args $ a])
      | _ \<Rightarrow> raise (Term_Error funerr [list_comb h args $ a]))
      | _ \<Rightarrow> raise (Term_Error funerr [list_comb h args $ a])) R"
    by (auto simp: list_comb_snoc devar_empty[OF assms])
  from r have "n_arrows T = Suc (n_arrows R)" by (auto split: ptyp.splits list.splits if_splits)
  with snoc.IH[OF f] show ?case by auto
qed (simp add: list_comb_def)

theorem satT_binder_types:
  assumes "vt_is_empty (tyenv env)" "satT env Ts t" "strip_comb t = (Var v T, targs)"
    "ground ar T" "ok (binder_types env T) Us"
  shows "length Us = length targs"
proof -
  from assms(2) obtain R where R: "ok (env_fastype env Ts t) R" "\<not> is_funT R"
    by (auto simp: satT_def)
  have t: "t = list_comb (Var v T) targs" by (rule strip_comb_list_comb[OF assms(3)])
  from env_fastype_list_comb[OF assms(1) R(1)[unfolded t]] n_arrows_nonfun[OF R(2)]
  have "n_arrows T = length targs" by auto
  with binder_types_n_arrows[OF assms(1,4,5)] show ?thesis by simp
qed



subsection \<open>Head-normalized pairs\<close>

text \<open>Saturation does not depend on the environment, as long as its type environment is empty.\<close>

definition env_empty :: env where
  "env_empty = Envir 0 vt_empty vt_empty"

lemma vt_is_empty_vt_empty[simp]: "vt_is_empty vt_empty"
  by transfer simp

definition satT0 :: "ptyp list \<Rightarrow> pterm \<Rightarrow> bool" where
  "satT0 Ts t \<longleftrightarrow> satT env_empty Ts t"

lemma satT_satT0: "vt_is_empty (tyenv env) \<Longrightarrow> satT env Ts t \<longleftrightarrow> satT0 Ts t"
  unfolding satT0_def by (rule satT_cong) (simp_all add: env_empty_def)

lemma head_norm_dpair_shape:
  assumes "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')"
    "wf_env ar env" "wf_dp ar (rb, t, u)"
  shows "satT0 (map snd rb') t'" "satT0 (map snd rb') u'" "hnf t'" "hnf u'"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  from assms(1) obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env rb t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env rb u1) u2" and
    nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def)
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    using assms(3) by simp_all
  have wt1: "wf_tm ar rb t1" using head_norm_wf_tm[OF ht assms(2) wt] by simp
  have wu1: "wf_tm ar rb u1" using head_norm_wf_tm[OF hu assms(2) wu] by simp
  have wt2: "wf_tm ar rb t2" using eta_norm_wf_tm[OF et assms(2) bok wt1] by simp
  have wu2: "wf_tm ar rb u2" using eta_norm_wf_tm[OF eu assms(2) bok wu1] by simp
  have wd2: "wf_dp ar (rb, t2, u2)" using bok wt2 wu2 by simp
  from new_dpair_shape[OF nd wd2]
  have sh: "t' = strip_abs_body t2" "u' = strip_abs_body u2"
    "map snd rb' = abs_tys t2 @ map snd rb" "map snd rb' = abs_tys u2 @ map snd rb"
    by blast+
  have "satT env (abs_tys t2 @ map snd rb) (strip_abs_body t2)"
    using eta_norm_sat[OF e et bok] wt1 by (simp add: wf_tm_def)
  with sh e show "satT0 (map snd rb') t'" by (simp add: satT_satT0)
  have "satT env (abs_tys u2 @ map snd rb) (strip_abs_body u2)"
    using eta_norm_sat[OF e eu bok] wu1 by (simp add: wf_tm_def)
  with sh e show "satT0 (map snd rb') u'" by (simp add: satT_satT0)
  have "hnf t2" by (rule eta_norm_hnf[OF e et head_norm_hnf[OF ht refl]])
  with sh show "hnf t'" by (simp add: hnf_strip_abs_body)
  have "hnf u2" by (rule eta_norm_hnf[OF e eu head_norm_hnf[OF hu refl]])
  with sh show "hnf u'" by (simp add: hnf_strip_abs_body)
qed


subsection \<open>The flex-rigid pairs returned by \<open>SIMPL\<close>\<close>

definition frs_ok :: "dpair \<Rightarrow> bool" where
  "frs_ok dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> satT0 (map snd rb) t \<and> hnf u)"

lemma frs_ok_simp[simp]: "frs_ok (rb, t, u) \<longleftrightarrow> satT0 (map snd rb) t \<and> hnf u"
  by (simp add: frs_ok_def)

abbreviation frs_st :: "sstate \<Rightarrow> bool" where
  "frs_st st \<equiv> (\<forall>dp\<in>set (snd (snd st)). frs_ok dp)"

lemma simrands_frs:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow>
      wf_st ar st' \<and> simp_rel [dp] st st' \<and> (frs_st st \<longrightarrow> frs_st st')) \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar (rb, t, u) \<Longrightarrow>
    head_of t = head_of u \<Longrightarrow> frs_st st \<Longrightarrow> frs_st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have w1: "wf_dp ar (rb, f1, g1)" and w2: "wf_dp ar (rb, t, u)"
    using "1.prems"(4) by (simp_all add: wf_tm_App)
  have hd: "head_of f1 = head_of g1" using "1.prems"(5) by simp
  have F': "wf_st ar st' \<and> simp_rel [dp] st st'" if "okW (F dp st) st'" "wf_st ar st" "wf_dp ar dp"
    for dp st st'
    using F[OF that] by simp
  have ws1: "wf_st ar st1" using simrands_sound[OF F' r "1.prems"(3) w1 hd] by simp
  from "1.IH"[OF F r "1.prems"(3) w1 hd "1.prems"(6)] have "frs_st st1" .
  with F[OF s ws1 w2] show ?case by simp
qed auto

lemma SIMPL0_step_frs:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow>
      wf_st ar st' \<and> simp_rel [dp] st st' \<and> (frs_st st \<longrightarrow> frs_st st')"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
    and wst: "wf_st ar (env, ffs, frs)" and wdp: "wf_dp ar (rb, t, u)"
    and fr: "frs_st (env, ffs, frs)"
    and sh: "satT0 (map snd rb) t" "satT0 (map snd rb) u" "hnf t" "hnf u"
  shows "frs_st st'"
proof -
  have ht: "typs_ok ar (head_of t)" and hu: "typs_ok ar (head_of u)"
    using wdp by (simp_all add: wf_tm_def typs_ok_head_of)
  have new: "frs_ok (rb, t, u)" "frs_ok (rb, u, t)" using sh by simp_all
  have assign: "frs_st st'"
    if "okW (handleW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs) | _ \<Rightarrow> raiseW e)) st'"
      "frs_ok (rb, t', u')" for t' u'
  proof -
    have "okW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)}) st' \<or>
      (\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs) | _ \<Rightarrow> raiseW e) st')"
      using that(1) unfolding okW_handleW by blast
    then show ?thesis
    proof
      assume "okW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)}) st'"
      with fr show ?thesis by auto
    next
      assume "\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs) | _ \<Rightarrow> raiseW e) st'"
      then obtain e where "okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs)
        | _ \<Rightarrow> raiseW e) st'" by blast
      from okW_ASSIGN_handler[OF this] fr that(2) show ?thesis by simp
    qed
  qed
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok have "okW (do {T' \<leftarrow> liftM (body_type env T); U' \<leftarrow> liftM (body_type env U);
        env' \<leftarrow> cunify_types alg T' U' env; returnW (env', (rb, t, u) # ffs, frs)}) st'"
      by (simp add: SIMPL0_step_def)
    with fr show ?thesis by auto
  next
    case VR
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    from assign[OF this new(1)] show ?thesis .
  next
    case RV
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    from assign[OF this new(2)] show ?thesis .
  next
    case RR
    have "head_of t = head_of u \<and> okW (simrands F rb u t u (env, ffs, frs)) st'"
      using ok RR ht hu
      by (cases "head_of t"; cases "head_of u")
        (auto simp: SIMPL0_step_def split: if_splits dest: cunify_types_ground_eq)
    then show ?thesis using simrands_frs[OF F] wst wdp fr by blast
  qed
qed

theorem SIMPL0_sound_frs:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp0 \<Longrightarrow>
    wf_st ar st' \<and> simp_rel [dp0] st st' \<and> (frs_st st \<longrightarrow> frs_st st')"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "wf_st ar st2 \<and> simp_rel [dp] st1 st2 \<and> (frs_st st1 \<longrightarrow> frs_st st2)"
    if "okW (S alg dp st1) st2" "wf_st ar st1" "wf_dp ar dp" for dp st1 st2
  proof -
    from that(1) obtain evs where "S alg dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this _ that(2,3)] show ?thesis by simp
  qed
  have IH': "wf_st ar st2 \<and> simp_rel [dp] st1 st2"
    if "okW (S alg dp st1) st2" "wf_st ar st1" "wf_dp ar dp" for dp st1 st2
    using IH[OF that] by simp
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  obtain rb0 t0 u0 where dp0: "dp0 = (rb0, t0, u0)" by (cases dp0)
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
  have wenv: "wf_env ar env" using "1.prems"(2) st by simp
  note hs = head_norm_dpair_sound[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  note hsh = head_norm_dpair_shape[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  from SIMPL0_step_sound[OF IH' step[unfolded dp hs(1)]] "1.prems"(2) hs(2) st
  have ss: "wf_st ar st'" "simp_rel [(rb, t, u)] (env, ffs, frs) st'" by auto
  have "simp_rel [dp0] st st'"
  proof (rule simp_relI)
    show "extends (fst st) (fst st')" using simp_relD(1)[OF ss(2)] st by simp
  next
    fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from simp_relD(2)[OF ss(2) \<sigma> s'] have "dsolved \<sigma> (rb, t, u)" "dsolved_all \<sigma> (ffs @ frs)" by auto
    moreover have "sat \<sigma> env" using sat_extends[OF \<sigma>(2) simp_relD(1)[OF ss(2)]] by simp
    ultimately show "dsolved_all \<sigma> ([dp0] @ st_pairs st)"
      using dsolved_env_equiv[OF hs(3,4) \<sigma>(1)] dp0 st by auto
  qed
  moreover have "frs_st st'" if "frs_st st"
  proof -
    have wst0: "wf_st ar (env, ffs, frs)" using "1.prems"(2) st by simp
    from that st have fr0: "frs_st (env, ffs, frs)" by simp
    show ?thesis by (rule SIMPL0_step_frs[OF IH step[unfolded dp hs(1)] wst0 hs(2) fr0 hsh])
  qed
  ultimately show ?case using ss(1) by (simp only: simp_thms) blast
qed

corollary SIMPL0_frs:
  "okW (SIMPL0 alg dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow> frs_st st \<Longrightarrow> frs_st st'"
  using SIMPL0_sound_frs by fastforce

lemma foldrW_SIMPL0_frs:
  "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow>
    frs_st st \<Longrightarrow> frs_st st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  have w1: "wf_st ar st1" using foldrW_SIMPL0_sound[OF f Cons.prems(2)] Cons.prems(3) by simp
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3,4) have "frs_st st1" by simp
  with SIMPL0_frs[OF s w1] Cons.prems(3) show ?case by simp
qed simp

theorem SIMPL_frs:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dpairs. wf_dp ar dp \<Longrightarrow> frs_st st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have w0: "wf_st ar (env, [], [])" using "1.prems"(2) by simp
  note fs = foldrW_SIMPL0_sound[OF f w0 "1.prems"(3)]
  have i1: "wf_st ar (env1, ffs, frs)" using fs by blast
  have fr1: "frs_st (env1, ffs, frs)" using foldrW_SIMPL0_frs[OF f w0 "1.prems"(3)] by simp
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where S_ok: "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    have w1: "wf_env ar env1" "\<forall>dp\<in>set (frs @ ffs). wf_dp ar dp" using i1 by auto
    from "1.IH"[OF S_ok snd_conv w1(1) w1(2)] show ?thesis .
  next
    case False
    with r have "st' = (env1, ffs, frs)" by blast
    with fr1 show ?thesis by simp
  qed
qed

end

end
