section \<open>Problems with Type Variables: the Shape of Flex-Rigid Pairs\<close>

theory Unify_Poly_Shape
  imports Unify_Poly_Simpl
begin

context csig
begin

text \<open>
  With type variables, the type environment grows during \<open>SIMPL\<close>, and a flex-rigid pair that
  was \<open>\<eta>\<close>-expanded earlier may not be saturated any more; \<^const>\<open>MATCH\<close> saturates it. What
  \<^const>\<open>MATCH\<close> needs from \<open>SIMPL\<close> is that the type of the flexible side can be computed
  (\<open>fsat\<close>), so that its variable takes at least as many arguments as it is applied to, and that
  the rigid side is in head normal form. Both are kept when the type environment grows.
\<close>

subsection \<open>Types of terms in larger type environments\<close>

lemma devar_textends:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok D \<Longrightarrow> \<not> is_TVar D \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> devar \<theta>' T = return D"
  using assms
proof (induction \<theta> T r arbitrary: D rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases "is_TVar T")
    case True
    then obtain ixn S where TVar: "T = TVar ixn S" by (cases T) auto
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) D"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest TVar "1.prems"(2) show ?thesis by (auto simp: return_def)
    next
      fix U assume r': "r' = Some U" and l: "vt_lookup \<theta> ixn = Some (S, U)"
      with rest have "dv \<theta> U = Some (Ok D)" by simp
      have l': "vt_lookup \<theta>' ixn = Some (S, U)" using l "1.prems"(3) unfolding textends_def by blast
      from "1.IH"[OF \<open>dv \<theta> U = Some (Ok D)\<close> refl "1.prems"(2,3)] l' TVar show ?thesis
        by (subst devar.simps) (simp add: type_lookup_ok)
    qed
  next
    case False
    with "1.hyps" "1.prems"(1) have "D = T" by (cases T) (simp_all add: return_def)
    with False show ?thesis by (subst devar.simps) (cases T; simp)
  qed
qed

lemma env_fastype_textends:
  "ok (env_fastype env Ts t) R \<Longrightarrow> textends (tyenv env) (tyenv env') \<Longrightarrow> ok (env_fastype env' Ts t) R"
proof (induction env Ts t arbitrary: R rule: env_fastype.induct)
  case (1 env Ts f u)
  from "1.prems"(1) obtain T0 T' where f: "ok (env_fastype env Ts f) T0"
    and dv: "ok (devar (tyenv env) T0) T'"
    and rest: "ok (case T' of
      Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
        else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) R"
    by (auto simp: bind_def split: option.splits res.splits)
  from rest obtain A where T': "T' = Type STR ''fun'' [A, R]"
    by (auto simp: return_def raise_def split: ptyp.splits list.splits if_splits)
  have "devar (tyenv env') T0 = return T'"
    by (rule devar_textends[OF dv refl _ "1.prems"(2)]) (simp add: T')
  with "1.IH"[OF f "1.prems"(2)] T' show ?case by (simp add: return_def)
next
  case (6 env Ts a T b)
  then show ?case by (auto simp: bind_def return_def split: option.splits res.splits)
qed (simp_all add: return_def)

definition fsat :: "env \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> bool" where
  "fsat env Ts t \<longleftrightarrow> (\<exists>R. ok (env_fastype env Ts t) R)"

lemma fsat_textends: "fsat env Ts t \<Longrightarrow> textends (tyenv env) (tyenv env') \<Longrightarrow> fsat env' Ts t"
  unfolding fsat_def by (blast intro: env_fastype_textends)

lemma fsat_pextends: "fsat env Ts t \<Longrightarrow> pextends env env' \<Longrightarrow> fsat env' Ts t"
  by (auto simp: pextends_def intro: fsat_textends)


subsection \<open>A flexible term takes at most as many arguments as its type has argument types\<close>

lemma binder_types_devar_aux:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok D \<Longrightarrow> \<theta> = tyenv env \<Longrightarrow> binder_types env T = binder_types env D"
  using assms
proof (induction \<theta> T r arbitrary: D rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  show ?case
  proof (cases "is_TVar T")
    case True
    then obtain ixn S where TVar: "T = TVar ixn S" by (cases T) auto
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup \<theta> ixn S) r'"
      and rest: "ok (case r' of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return T) D"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest show ?thesis by (simp add: return_def)
    next
      fix U assume r': "r' = Some U" and l: "vt_lookup \<theta> ixn = Some (S, U)"
      with rest have "dv \<theta> U = Some (Ok D)" by simp
      from "1.IH"[OF this refl "1.prems"(2)] l TVar "1.prems"(2) show ?thesis
        by (subst binder_types.simps) (simp add: type_lookup_ok)
    qed
  next
    case False
    with "1.hyps" "1.prems"(1) show ?thesis by (cases T) (simp_all add: return_def)
  qed
qed

lemma binder_types_devar: "ok (devar (tyenv env) T) D \<Longrightarrow> binder_types env T = binder_types env D"
  using binder_types_devar_aux by blast

lemma list_comb_Cons_app: "list_comb h (a # args) = list_comb (h $ a) args"
  by (simp add: list_comb_def)

lemma fastype_list_comb_head: "ok (env_fastype env Ts (list_comb f args)) R \<Longrightarrow> \<exists>R'. ok (env_fastype env Ts f) R'"
proof (induction args arbitrary: f R)
  case (Cons a args)
  from Cons.IH[of "f $ a" R] Cons.prems obtain R' where "ok (env_fastype env Ts (f $ a)) R'"
    by (auto simp: list_comb_Cons_app)
  then show ?case by (auto simp: bind_def split: option.splits res.splits)
qed (auto simp: list_comb_def)

lemma fastype_list_comb_binder_types:
  "ok (env_fastype env Ts (list_comb h args)) R \<Longrightarrow> ok (env_fastype env Ts h) T \<Longrightarrow>
    ok (binder_types env T) Us \<Longrightarrow> length args \<le> length Us"
proof (induction args arbitrary: h T Us)
  case (Cons a args)
  have "ok (env_fastype env Ts (list_comb (h $ a) args)) R" using Cons.prems(1) by (simp add: list_comb_Cons_app)
  then obtain R' where ha: "ok (env_fastype env Ts (h $ a)) R'"
    using fastype_list_comb_head by blast
  from ha Cons.prems(2) obtain D where dv: "ok (devar (tyenv env) T) D"
    and D: "ok (case D of
      Type b Vs \<Rightarrow> (case Vs of [_, U] \<Rightarrow> if b = STR ''fun'' then return U
        else raise (Term_Error funerr [h $ a]) | _ \<Rightarrow> raise (Term_Error funerr [h $ a]))
      | _ \<Rightarrow> raise (Term_Error funerr [h $ a])) R'"
    by (auto simp: bind_def split: option.splits res.splits)
  from D obtain A where DA: "D = Type STR ''fun'' [A, R']"
    by (auto simp: return_def raise_def split: ptyp.splits list.splits if_splits)
  have "binder_types env T = binder_types env D" by (rule binder_types_devar[OF dv])
  with Cons.prems(3) DA obtain Us' where Us: "Us = A # Us'" and bt': "ok (binder_types env R') Us'"
    by (subst (asm) (2) binder_types.simps) (auto simp: bind_def return_def split: option.splits res.splits)
  from Cons.IH[OF \<open>ok (env_fastype env Ts (list_comb (h $ a) args)) R\<close> ha bt'] Us show ?case by simp
qed simp

lemma fsat_binder_types:
  "fsat env Ts t \<Longrightarrow> strip_comb t = (Var v T, targs) \<Longrightarrow> ok (binder_types env T) Us \<Longrightarrow>
    length targs \<le> length Us"
  unfolding fsat_def
  by (auto dest: strip_comb_list_comb intro: fastype_list_comb_binder_types[of env Ts "Var v T" targs _ T Us]
      simp: return_def)

text \<open>The type of a term with a variable head does not depend on the types of the bound variables.\<close>

lemma env_fastype_Var_head: "env_fastype env Ts (list_comb (Var v T) args) = env_fastype env Us (list_comb (Var v T) args)"
  by (induction args rule: rev_induct) (simp_all add: list_comb_snoc list_comb_def)

lemma fsat_Var_head: "is_Var (head_of t) \<Longrightarrow> fsat env Ts t \<longleftrightarrow> fsat env Us t"
proof -
  assume "is_Var (head_of t)"
  then obtain v T where h: "head_of t = Var v T" by (cases "head_of t") auto
  have "t = list_comb (Var v T) (snd (strip_comb t))"
    using strip_comb_list_comb[of t "head_of t" "snd (strip_comb t)"] h
    by (simp add: fst_strip_comb[symmetric] prod_eq_iff)
  then show ?thesis unfolding fsat_def by (metis env_fastype_Var_head)
qed


subsection \<open>\<open>\<eta>\<close>-normalization\<close>

lemma etif_phnf:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> hnf t \<Longrightarrow> hnf t'"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  show ?case
  proof (cases "\<exists>T1 U. T = Type STR ''fun'' [T1, U]")
    case True
    then obtain T1 U where T: "T = Type STR ''fun'' [T1, U]" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have "hnf (incr_boundvars 1 t $ Bound 0)"
      using "1.prems"(2,3) by (simp add: hnf_nonAbs incr_boundvars_def is_Abs_head_of_incr_bv)
    from "1.IH"[OF u refl _ this] t' show ?thesis by simp
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup tye v S) r'"
        and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by (auto simp: bind_def split: option.splits res.splits)
      show ?thesis
      proof (cases r')
        case None
        with rest "1.prems" show ?thesis by (simp add: return_def)
      next
        case (Some T')
        with rest "1.IH"[of tye T' t "Ok t'" t'] "1.prems" show ?thesis by simp
      qed
    next
      case (Type a Ts)
      with nf "1.hyps" "1.prems" show ?thesis
        by (auto simp: return_def split: list.splits if_splits)
    qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
  qed
qed

lemma eta_norm_phnf: "ok (eta_norm env rb t) t' \<Longrightarrow> hnf t \<Longrightarrow> hnf t'"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  then show ?case by auto
qed (auto simp: eta_norm_nonAbs bind_def split: option.splits res.splits intro: etif_phnf)

lemma devar_TVar_Some:
  "ok (type_lookup \<theta> ixn S) (Some U) \<Longrightarrow> devar \<theta> (TVar ixn S) = devar \<theta> U"
  by (subst devar.simps) (simp add: bind_def)

lemma etif_fsat:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> tye = tyenv env \<Longrightarrow> ok (env_fastype env Ts t) T0 \<Longrightarrow> devar tye T0 = devar tye T \<Longrightarrow>
    proper t \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> fsat env (abs_tys t' @ Ts) (strip_abs_body t')"
  using assms
proof (induction tye T t r arbitrary: t' Ts T0 rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  show ?case
  proof (cases "\<exists>T1 U. T = Type STR ''fun'' [T1, U]")
    case True
    then obtain T1 U where T: "T = Type STR ''fun'' [T1, U]" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have "ok (env_fastype env (T1 # Ts) (incr_boundvars 1 t)) T0"
      using env_fastype_incr_bv[OF "1.prems"(3,5), of 0 T1] by (simp add: incr_boundvars_def)
    moreover have "devar (tyenv env) T0 = return T"
      using "1.prems"(2,4) T by (simp add: devar.simps[of _ "T1 \<rightarrow>\<^sub>T U"])
    ultimately have f: "ok (env_fastype env (T1 # Ts) (incr_boundvars 1 t $ Bound 0)) U"
      using T by (simp add: return_def)
    have pr: "proper (incr_boundvars 1 t $ Bound 0)"
      using "1.prems"(5) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
    from "1.IH"[OF u refl "1.prems"(2) f refl pr] t' show ?thesis by simp
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup tye v S) r'"
        and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by (auto simp: bind_def split: option.splits res.splits)
      show ?thesis
      proof (cases r')
        case None
        with rest "1.prems"(3,6) show ?thesis by (cases t) (auto simp: return_def fsat_def)
      next
        case (Some T')
        with rest have e: "ef tye T' t = Some (Ok t')" by simp
        have "devar tye T0 = devar tye T'" using "1.prems"(4) devar_TVar_Some[OF lk[unfolded Some]] TVar
          by simp
        from "1.IH"[OF e refl "1.prems"(2,3) this "1.prems"(5,6)] show ?thesis .
      qed
    next
      case (Type a Us)
      with nf "1.hyps" "1.prems"(1) have "t' = t" by (auto simp: return_def split: list.splits if_splits)
      with "1.prems"(3,6) show ?thesis by (cases t) (auto simp: fsat_def)
    next
      case (TFree a S)
      with "1.hyps" "1.prems"(1) have "t' = t" by (simp add: return_def)
      with "1.prems"(3,6) show ?thesis by (cases t) (auto simp: fsat_def)
    qed
  qed
qed

lemma eta_norm_fsat:
  "ok (eta_norm env rb t) t' \<Longrightarrow> proper t \<Longrightarrow> fsat env (abs_tys t' @ map snd rb) (strip_abs_body t')"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rb) body) b'"
    and t': "t' = Abs a T b'" by auto
  from Abs.IH[OF b'] Abs.prems(2) t' show ?case by simp
qed (auto simp: eta_norm_nonAbs fastype_def bind_def split: option.splits res.splits
    intro!: etif_fsat[OF _ refl refl _ refl])


subsection \<open>Stripping common abstractions\<close>

lemma new_dpair_pshape:
  "okW (new_dpair alg rb t u env) ((rb', t', u'), env') \<Longrightarrow>
    t' = strip_abs_body t \<and> u' = strip_abs_body u \<and> map snd rb' = abs_tys t @ map snd rb \<and>
    \<not> is_Abs t' \<and> \<not> is_Abs u'"
proof (induction alg rb t u env rule: new_dpair.induct)
  case (1 alg rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg T U env) env1"
    and rec: "okW (new_dpair alg ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  from "1.IH"[OF cu c_def rec] show ?case by auto
qed auto


subsection \<open>Head-normalized pairs\<close>

lemma head_norm_dpair_pshape:
  assumes "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')"
    "swf_env ar env" "swf_dp ar (rb, t, u)"
  shows "is_Var (head_of t') \<Longrightarrow> fsat env' [] t'" "is_Var (head_of u') \<Longrightarrow> fsat env' [] u'" "hnf t'" "hnf u'"
    "\<not> is_Abs t'" "\<not> is_Abs u'"
proof -
  from assms(1) obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env rb t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env rb u1) u2" and
    nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def)
  have wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u" using assms(3) by simp_all
  have pt1: "proper t1" using head_norm_swf_tm[OF ht assms(2) wt] by (simp add: swf_tm_def)
  have pu1: "proper u1" using head_norm_swf_tm[OF hu assms(2) wu] by (simp add: swf_tm_def)
  from new_dpair_pshape[OF nd] have sh: "t' = strip_abs_body t2" "u' = strip_abs_body u2" by simp_all
  have ext: "pextends env env'"
    using head_norm_dpair_ssound(1)[OF assms] .
  have "fsat env (abs_tys t2 @ map snd rb) (strip_abs_body t2)" by (rule eta_norm_fsat[OF et pt1])
  then have "fsat env' (abs_tys t2 @ map snd rb) t'" using sh fsat_pextends[OF _ ext] by simp
  then show "is_Var (head_of t') \<Longrightarrow> fsat env' [] t'" using fsat_Var_head by blast
  have "fsat env (abs_tys u2 @ map snd rb) (strip_abs_body u2)" by (rule eta_norm_fsat[OF eu pu1])
  then have "fsat env' (abs_tys u2 @ map snd rb) u'" using sh fsat_pextends[OF _ ext] by simp
  then show "is_Var (head_of u') \<Longrightarrow> fsat env' [] u'" using fsat_Var_head by blast
  have "hnf t2" by (rule eta_norm_phnf[OF et head_norm_hnf[OF ht refl]])
  with sh show "hnf t'" by (simp add: hnf_strip_abs_body)
  have "hnf u2" by (rule eta_norm_phnf[OF eu head_norm_hnf[OF hu refl]])
  with sh show "hnf u'" by (simp add: hnf_strip_abs_body)
  from new_dpair_pshape[OF nd] show "\<not> is_Abs t'" "\<not> is_Abs u'" by blast+
qed


subsection \<open>The flex-rigid pairs returned by \<open>SIMPL\<close>\<close>

definition pfrs_ok :: "env \<Rightarrow> dpair \<Rightarrow> bool" where
  "pfrs_ok env dp \<longleftrightarrow> (case dp of (rb, t, u) \<Rightarrow> fsat env [] t \<and> hnf u \<and> \<not> is_Abs u)"

lemma pfrs_ok_simp[simp]: "pfrs_ok env (rb, t, u) \<longleftrightarrow> fsat env [] t \<and> hnf u \<and> \<not> is_Abs u"
  by (simp add: pfrs_ok_def)

lemma pfrs_ok_pextends: "pfrs_ok env dp \<Longrightarrow> pextends env env' \<Longrightarrow> pfrs_ok env' dp"
  by (cases dp) (auto intro: fsat_pextends)

abbreviation pfrs_st :: "sstate \<Rightarrow> bool" where
  "pfrs_st st \<equiv> (\<forall>dp\<in>set (snd (snd st)). pfrs_ok (fst st) dp)"

lemma pfrs_st_pextends:
  "pfrs_st (env, ffs, frs) \<Longrightarrow> pextends env env' \<Longrightarrow> pfrs_st (env', ffs', frs)"
  by (auto intro: pfrs_ok_pextends)

lemma psimrands_frs:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow>
      swf_st ar st' \<and> psimp_rel [dp] st st' \<and> (pfrs_st st \<longrightarrow> pfrs_st st')) \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar (rb, t, u) \<Longrightarrow>
    heads_eq (fst st) (head_of t) (head_of u) \<Longrightarrow> pfrs_st st \<Longrightarrow> pfrs_st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have w1: "swf_dp ar (rb, f1, g1)" and w2: "swf_dp ar (rb, t, u)"
    using "1.prems"(4) by (simp_all add: swf_tm_App)
  have hd: "heads_eq (fst st) (head_of f1) (head_of g1)" using "1.prems"(5) by simp
  have F': "swf_st ar st' \<and> psimp_rel [dp] st st'" if "okW (F dp st) st'" "swf_st ar st" "swf_dp ar dp"
    for dp st st'
    using F[OF that] by simp
  have ws1: "swf_st ar st1" using psimrands_sound[OF F' r "1.prems"(3) w1 hd] by simp
  from "1.IH"[OF F r "1.prems"(3) w1 hd "1.prems"(6)] have "pfrs_st st1" .
  with F[OF s ws1 w2] show ?case by simp
qed auto

lemma SIMPL0_step_pfrs:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow>
      swf_st ar st' \<and> psimp_rel [dp] st st' \<and> (pfrs_st st \<longrightarrow> pfrs_st st')"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
    and wst: "swf_st ar (env, ffs, frs)" and wdp: "swf_dp ar (rb, t, u)"
    and fr: "pfrs_st (env, ffs, frs)"
    and sh: "is_Var (head_of t) \<Longrightarrow> fsat env [] t" "is_Var (head_of u) \<Longrightarrow> fsat env [] u" "hnf t" "hnf u"
      "\<not> is_Abs t" "\<not> is_Abs u"
  shows "pfrs_st st'"
proof -
  have F': "swf_st ar st' \<and> psimp_rel [dp] st st'" if "okW (F dp st) st'" "swf_st ar st" "swf_dp ar dp"
    for dp st st'
    using F[OF that] by simp
  have step: "swf_st ar st' \<and> psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
    by (rule SIMPL0_step_ssound[OF F' ok wst wdp])
  then have ext: "pextends env (fst st')" by (auto dest: psimp_relD(1))
  have ht: "twft ar (head_of t)" and hu: "twft ar (head_of u)"
    using wdp by (simp_all add: swf_tm_def twft_head_of)
  have tw: "twf ar (tyenv env)" using wst by (auto dest: swf_envD(1))
  have assign: "pfrs_st st'"
    if "okW (handleW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs) | _ \<Rightarrow> raiseW e)) st'"
      "pfrs_ok env (rb, t', u')" for t' u'
  proof -
    have "okW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)}) st' \<or>
      (\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t', u') # frs) | _ \<Rightarrow> raiseW e) st')"
      using that(1) unfolding okW_handleW by blast
    then show ?thesis
    proof
      assume "okW (do {env' \<leftarrow> assignment alg rb t' u' env; returnW (env', ffs, frs)}) st'"
      then obtain env' where st': "st' = (env', ffs, frs)" by auto
      with fr ext show ?thesis by (auto intro: pfrs_ok_pextends)
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
    then obtain env' where "st' = (env', (rb, t, u) # ffs, frs)" by auto
    with fr ext show ?thesis by (auto intro: pfrs_ok_pextends)
  next
    case VR
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    moreover have "pfrs_ok env (rb, t, u)" using sh VR by simp
    ultimately show ?thesis by (rule assign)
  next
    case RV
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    moreover have "pfrs_ok env (rb, u, t)" using sh RV by simp
    ultimately show ?thesis by (rule assign)
  next
    case RR
    have "\<exists>env'. pextends env env' \<and> twf ar (tyenv env') \<and> tenv env' = tenv env \<and>
        heads_eq env' (head_of t) (head_of u) \<and> okW (simrands F rb u t u (env', ffs, frs)) st'"
    proof (cases "head_of t"; cases "head_of u")
      fix a T b U assume h: "head_of t = Const a T" "head_of u = Const b U"
      with ok RR obtain env' where ab: "a = b" and cu: "okW (cunify_types alg T U env) env'"
        and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      have "wft ar T" "wft ar U" using h ht hu by simp_all
      from cunify_types_psound[OF cu tw this] heads_eq_cunify[OF cu tw this] h ab s show ?thesis by auto
    next
      fix a T b U assume h: "head_of t = Free a T" "head_of u = Free b U"
      with ok RR obtain env' where ab: "a = b" and cu: "okW (cunify_types alg T U env) env'"
        and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      have "wft ar T" "wft ar U" using h ht hu by simp_all
      from cunify_types_psound[OF cu tw this] heads_eq_cunify[OF cu tw this] h ab s show ?thesis by auto
    next
      fix i j assume h: "head_of t = Bound i" "head_of u = Bound j"
      with ok RR have "i = j" "okW (simrands F rb u t u (env, ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      with h tw show ?thesis by (intro exI[of _ env]) (simp add: heads_eq_def)
    qed (use ok RR in \<open>auto simp: SIMPL0_step_def\<close>)
    then obtain env' where e': "pextends env env'" "twf ar (tyenv env')" "tenv env' = tenv env"
      "heads_eq env' (head_of t) (head_of u)" and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
      by blast
    have w': "swf_st ar (env', ffs, frs)" using wst e'(2,3) by (auto simp: swf_env_def)
    have fr': "pfrs_st (env', ffs, frs)" using fr e'(1) by (auto intro: pfrs_ok_pextends)
    from psimrands_frs[OF F s w' wdp] e'(4) fr' show ?thesis by simp
  qed
qed

theorem SIMPL0_ssound_frs:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp0 \<Longrightarrow>
    swf_st ar st' \<and> psimp_rel [dp0] st st' \<and> (pfrs_st st \<longrightarrow> pfrs_st st')"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "swf_st ar st2 \<and> psimp_rel [dp] st1 st2 \<and> (pfrs_st st1 \<longrightarrow> pfrs_st st2)"
    if "okW (S alg dp st1) st2" "swf_st ar st1" "swf_dp ar dp" for dp st1 st2
  proof -
    from that(1) obtain evs where "S alg dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this _ that(2,3)] show ?thesis by simp
  qed
  have IH': "swf_st ar st2 \<and> psimp_rel [dp] st1 st2"
    if "okW (S alg dp st1) st2" "swf_st ar st1" "swf_dp ar dp" for dp st1 st2
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
  have wenv: "swf_env ar env" using "1.prems"(2) st by simp
  note hs = head_norm_dpair_ssound[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  note hsh = head_norm_dpair_pshape[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  have w1: "swf_st ar (env1, ffs, frs)" using "1.prems"(2) st hs(3) by simp
  from SIMPL0_step_ssound[OF IH' step[unfolded dp] w1 hs(4)]
  have ss: "swf_st ar st'" "psimp_rel [(rb, t, u)] (env1, ffs, frs) st'" by blast+
  have ext: "pextends env (fst st')" using pextends_trans[OF hs(1) psimp_relD(1)[OF ss(2), simplified]] .
  have "psimp_rel [dp0] st st'"
  proof (rule psimp_relI)
    show "pextends (fst st) (fst st')" using ext st by (simp only: fst_conv)
  next
    fix \<sigma> assume \<sigma>: "psat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from psimp_relD(2)[OF ss(2) \<sigma> s'] have "dsolved \<sigma> (rb, t, u)" "dsolved_all \<sigma> (ffs @ frs)" by auto
    moreover have "psat \<sigma> env" by (rule psat_pextends[OF \<sigma> ext])
    ultimately show "dsolved_all \<sigma> ([dp0] @ st_pairs st)"
      using dsolved_env_equiv[OF hs(5,6)] psatD[of \<sigma> env] dp0 st by auto
  qed
  moreover have "pfrs_st st'" if "pfrs_st st"
  proof -
    from that st hs(1) have fr1: "pfrs_st (env1, ffs, frs)" by (auto intro: pfrs_ok_pextends)
    show ?thesis by (rule SIMPL0_step_pfrs[OF IH step[unfolded dp] w1 hs(4) fr1 hsh])
  qed
  ultimately show ?case using ss(1) by blast
qed

corollary SIMPL0_pfrs:
  "okW (SIMPL0 alg dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow> pfrs_st st \<Longrightarrow> pfrs_st st'"
  using SIMPL0_ssound_frs by fastforce

lemma foldrW_SIMPL0_pfrs:
  "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow>
    pfrs_st st \<Longrightarrow> pfrs_st st'"
proof (induction dps arbitrary: st')
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  have w1: "swf_st ar st1" using foldrW_SIMPL0_ssound[OF f Cons.prems(2)] Cons.prems(3) by simp
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3,4) have "pfrs_st st1" by simp
  with SIMPL0_pfrs[OF s w1] Cons.prems(3) show ?case by simp
qed simp

theorem SIMPL_pfrs:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dpairs. swf_dp ar dp \<Longrightarrow> pfrs_st st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have w0: "swf_st ar (env, [], [])" using "1.prems"(2) by simp
  note fs = foldrW_SIMPL0_ssound[OF f w0 "1.prems"(3)]
  have i1: "swf_st ar (env1, ffs, frs)" using fs by blast
  have fr1: "pfrs_st (env1, ffs, frs)" using foldrW_SIMPL0_pfrs[OF f w0 "1.prems"(3)] by simp
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where S_ok: "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    have w1: "swf_env ar env1" "\<forall>dp\<in>set (frs @ ffs). swf_dp ar dp" using i1 by auto
    from "1.IH"[OF S_ok snd_conv w1(1) w1(2)] show ?thesis .
  next
    case False
    with r have "st' = (env1, ffs, frs)" by blast
    with fr1 show ?thesis by simp
  qed
qed

end

end
