section \<open>Smashing the Remaining Flex-Flex Pairs, with Type Variables\<close>

theory Unify_Poly_Smash
  imports Unify_Poly_Unifiers Unify_Smash
begin

hide_const (open) Unify_Flexflex_Complete.inst

text \<open>
  The analogue of \<open>Unify_Smash\<close> for problems with type variables: on the unifiers that the
  search returns, \<^const>\<open>smash_flexflex\<close> terminates normally and solves the remaining pairs.
  The type of a remaining pair may have become a function type after the pair was classified;
  smashing binds the heads to constant functions over all their argument types, which still
  solves the pair.
\<close>

subsection \<open>The innermost head of a normal form\<close>

abbreviation hnfv :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "hnfv env t \<equiv> head_of (strip_abs_body t) = fhd t \<and>
    (\<forall>x U. fhd t = Var x U \<longrightarrow> vt_lookup (tenv env) x = None \<and> tnorm (tyenv env) U = U)"

lemma ok_lookup_None: "ok (lookup env xi T) None \<Longrightarrow> vt_lookup (tenv env) xi = None"
  by (auto simp: lookup_def bind_def return_def var_clash_def raise_def split: option.splits if_splits res.splits)

lemma ok_lookup1_None: "ok (lookup1 te xi T) None \<Longrightarrow> vt_lookup te xi = None"
  by (auto simp: lookup1_def return_def var_clash_def raise_def split: option.splits if_splits)

lemma fhd_no_redex: "\<not> could_beta_contract t \<Longrightarrow> head_of (strip_abs_body t) = fhd t"
proof (induction t)
  case (App f u)
  then show ?case by (cases f) auto
qed auto

lemma norm_term2_fhd:
  assumes "norm_term2 e t = Some r"
  shows "e = env \<Longrightarrow> r = Ok t' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow>
    \<forall>U\<in>tys t \<union> etys env. tcons (tyenv env) U \<Longrightarrow> hnfv env t' \<and> (\<forall>U\<in>tys t'. tcons (tyenv env) U)"
  using assms
proof (induction e t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt e t r)
  let ?\<theta> = "tyenv env"
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" and tc: "\<forall>U\<in>tys t \<union> etys env. tcons ?\<theta> U" using "1.prems" by simp_all
  have t': "ok (case t of
      Const a T \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Const a T'))
    | Free a T \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Free a T'))
    | Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Var xi T')))
    | Abs a T body \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. nt env body \<bind> (\<lambda>body'. return (Abs a T' body')))
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
        | _ \<Rightarrow> nt env f \<bind> (\<lambda>nf. case nf of
            Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using "1.hyps" "1.prems"(2) unfolding "1.prems"(1) by simp
  have IH: "hnfv env s' \<and> (\<forall>U\<in>tys s'. tcons ?\<theta> U)"
    if "nt env s = Some (Ok s')" "\<forall>U\<in>tys s. tcons ?\<theta> U" for s s'
    using "1.IH"[OF that(1) refl refl ac] that(2) tc by blast
  have nta: "ok (norm_type_aux ?\<theta> T) T' \<Longrightarrow> tcons ?\<theta> T \<Longrightarrow> T' = tnorm ?\<theta> T \<and> tcons ?\<theta> T'" for T T'
    using norm_type_aux_ok[OF ac, of T] tcons_tnorm[OF ac(1), of T] by (auto simp: return_def)
  show ?case
  proof (cases t)
    case (Const a T)
    with t' tc nta show ?thesis by (auto simp: bind_def return_def split: option.splits res.splits)
  next
    case (Free a T)
    with t' tc nta show ?thesis by (auto simp: bind_def return_def split: option.splits res.splits)
  next
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u | None \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Var xi T'))) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest obtain T' where "ok (norm_type_aux ?\<theta> T) T'" "t' = Var xi T'"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      moreover have "tcons ?\<theta> T" using tc Var by simp
      ultimately show ?thesis using ok_lookup_None[OF lk[unfolded None]] nta[of T T'] tnorm_idem[OF ac(1)] by auto
    next
      case (Some u)
      from ok_lookup_some[OF lk] Some obtain U where b: "vt_lookup (tenv env) xi = Some (U, u)" by auto
      have "\<forall>X\<in>tys u. tcons ?\<theta> X" using tc etysI[OF b] by auto
      with IH rest Some show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with t' obtain T' b' where "ok (norm_type_aux ?\<theta> T) T'" "nt env body = Some (Ok b')" "t' = Abs a T' b'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    moreover have "tcons ?\<theta> T" "\<forall>X\<in>tys body. tcons ?\<theta> X" using tc Abs by auto
    ultimately show ?thesis using IH nta by fastforce
  next
    case (App f u)
    have tcs: "\<forall>X\<in>tys (subst_bound u body). tcons ?\<theta> X" if "\<forall>X\<in>tys body. tcons ?\<theta> X" for body
      using tys_subst_bound[of u body] that tc App by auto
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      with t' App have h: "nt env (subst_bound u body) = Some (Ok t')" by simp
      have "\<forall>X\<in>tys body. tcons ?\<theta> X" using tc App f by auto
      from IH[OF h tcs[OF this]] show ?thesis .
    next
      case False
      with t' App obtain nf where nf: "nt env f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> nt env u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      have IHf: "hnfv env nf \<and> (\<forall>U\<in>tys nf. tcons ?\<theta> U)" using IH[OF nf] tc App by auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = Abs a T body" by (cases nf) auto
        with rest have h: "nt env (subst_bound u body) = Some (Ok t')" by simp
        have "\<forall>X\<in>tys body. tcons ?\<theta> X" using IHf nfa by auto
        from IH[OF h tcs[OF this]] show ?thesis .
      next
        case nA: False
        with rest obtain nu where nu: "nt env u = Some (Ok nu)" and e: "t' = nf $ nu"
          by (cases nf) (auto simp: bind_def return_def split: option.splits res.splits)
        have "\<forall>U\<in>tys nu. tcons ?\<theta> U" using IH[OF nu] tc App by auto
        moreover have "strip_abs_body nf = nf" using nA by (cases nf) auto
        ultimately show ?thesis using IHf e by auto
      qed
    qed
  qed (use t' in \<open>auto simp: return_def\<close>)
qed

lemma norm_term1_fhd:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> head_of (strip_abs_body t') = fhd t' \<and> (\<forall>x U. fhd t' = Var x U \<longrightarrow> vt_lookup te x = None)"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  have t': "ok (case t of
      Var xi T \<Rightarrow> lookup1 te xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t)
    | Abs a T body \<Rightarrow> nt te body \<bind> (\<lambda>body'. return (Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
        | _ \<Rightarrow> nt te f \<bind> (\<lambda>nf. case nf of
            Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))))
    | _ \<Rightarrow> return t) t'"
    using "1.hyps" "1.prems"(1) by simp
  have IH: "head_of (strip_abs_body s') = fhd s' \<and> (\<forall>x U. fhd s' = Var x U \<longrightarrow> vt_lookup te x = None)"
    if "nt te s = Some (Ok s')" for s s'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases r')
      case None
      with rest Var ok_lookup1_None[OF lk[unfolded None]] show ?thesis by (auto simp: return_def)
    next
      case (Some u)
      with IH rest show ?thesis by simp
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "nt te body = Some (Ok b')" "t' = Abs a T b'"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    with IH show ?thesis by fastforce
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = Abs a T body" by (cases f) auto
      with t' App have "nt te (subst_bound u body) = Some (Ok t')" by simp
      with IH show ?thesis by blast
    next
      case False
      with t' App obtain nf where nf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> nt te u \<bind> (\<lambda>nu. return (nf $ nu))) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = Abs a T body" by (cases nf) auto
        with rest have "nt te (subst_bound u body) = Some (Ok t')" by simp
        with IH show ?thesis by blast
      next
        case nA: False
        with rest obtain nu where e: "t' = nf $ nu"
          by (cases nf) (auto simp: bind_def return_def split: option.splits res.splits)
        have "strip_abs_body nf = nf" using nA by (cases nf) auto
        with IH[OF nf] e show ?thesis by auto
      qed
    qed
  qed (use t' in \<open>auto simp: return_def\<close>)
qed

lemma norm_term_fhd:
  assumes "ok (norm_term env t) t'" "tacyc (tyenv env)" "tcons_env (tyenv env)"
    "\<forall>U\<in>tys t \<union> etys env. tcons (tyenv env) U"
  shows "hnfv env t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "t' = t" using assms(1) by (simp add: norm_term_def return_def)
    with id show ?thesis
      by (auto simp: fhd_no_redex env_is_empty_def vt_is_empty_lookup tnorm_empty)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_fhd[OF this refl] n1(2) show ?thesis by (simp add: tnorm_empty)
  next
    case n2
    with assms(1) have "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_fhd[OF this refl refl assms(2-4)] show ?thesis by blast
  qed
qed


subsection \<open>Types of normal heads\<close>

lemma body_type_unb:
  "\<forall>(w, S)\<in>tvars T. vt_lookup (tyenv env) w = None \<Longrightarrow> body_type env T = return (res_type T)"
proof (induction T)
  case (Type a Ts)
  then show ?case by (subst body_type.simps) (auto split: list.splits)
next
  case (TVar v S)
  then show ?case by (subst body_type.simps) (simp add: type_lookup_def bindM_def return_def)
qed (subst body_type.simps; simp)

lemma binder_types_unb:
  "\<forall>(w, S)\<in>tvars T. vt_lookup (tyenv env) w = None \<Longrightarrow> binder_types env T = return (arg_types T)"
proof (induction T)
  case (Type a Ts)
  then show ?case by (subst binder_types.simps) (auto simp: bindM_def return_def split: list.splits)
next
  case (TVar v S)
  then show ?case by (subst binder_types.simps) (simp add: type_lookup_def bindM_def return_def)
qed (subst binder_types.simps; simp)

subsection \<open>The constant instance of a flexible term\<close>

lemma flex_pconst:
  assumes cl: "closed_on UNIV \<sigma>" and ty: "has_type V Bs (tnormt \<theta> a) X"
    and h: "head_of (strip_abs_body a) = Var v T"
    and sv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types (tnorm \<theta> T))) c" and nl: "no_loose_bound c 0"
  shows "mk_subst \<sigma> (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types X)) c"
  using ty h
proof (induction a arbitrary: Bs X)
  case (Abs n A b)
  from Abs.prems(1) obtain Y where X: "X = fun_type (tnorm \<theta> A) Y" and tb: "has_type V (tnorm \<theta> A # Bs) (tnormt \<theta> b) Y"
    by (auto elim: has_type_elims)
  have "head_of (strip_abs_body b) = Var v T" using Abs.prems(2) by simp
  from equiv_Abs[OF Abs.IH[OF tb this]]
  have "dB.Abs (mk_subst \<sigma> (tr b)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (Abs_m (length (arg_types Y)) c)" .
  moreover have "mk_subst \<sigma> (tr (Abs n A b)) = dB.Abs (mk_subst \<sigma> (tr b))" by simp
  moreover have "Abs_m (length (arg_types X)) c = dB.Abs (Abs_m (length (arg_types Y)) c)" using X by simp
  ultimately show ?case by (simp only:)
next
  case (App f u)
  let ?a = "f $ u"
  let ?args = "snd (strip_comb ?a)"
  let ?H = "Abs_m (length (arg_types X)) c"
  let ?ts = "map (mk_subst \<sigma> \<circ> tr) ?args"
  have a: "?a = list_comb (Var v T) ?args" using head_of_list_comb[of ?a] App.prems(2) by simp
  from App.prems(1) a obtain As where hv: "has_type V Bs (Var v (tnorm \<theta> T)) (foldr fun_type As X)"
    and As: "list_all2 (has_type V Bs) (map (tnormt \<theta>) ?args) As"
    by (metis has_type_list_comb tnormt_list_comb tnormt.simps(3))
  from hv have T: "tnorm \<theta> T = foldr fun_type As X" by (auto elim: has_type.cases)
  have m: "length (arg_types (tnorm \<theta> T)) = length ?ts + length (arg_types X)"
    using T list_all2_lengthD[OF As] by (simp add: arg_types_foldr_fun)
  have e1: "mk_subst \<sigma> (tr ?a) = \<sigma> (code (AVar v)) \<degree>\<degree> ?ts"
    by (subst a) (simp add: tr_list_comb)
  have mH: "Abs_m (length (arg_types (tnorm \<theta> T))) c = Abs_m (length ?ts) ?H" using m by (simp add: Abs_m_add)
  have e2: "\<sigma> (code (AVar v)) \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length ?ts) ?H \<degree>\<degree> ?ts"
    by (rule equiv_list_app[OF sv[unfolded mH]]) (simp add: list_all2_conv_all_nth)
  have nH: "no_loose_bound ?H 0" using no_loose_bound_mono[OF nl] by (simp add: loose_bound_Abs_m)
  have e3: "Abs_m (length ?ts) ?H \<degree>\<degree> ?ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?H"
    using Abs_m_apps_closed_head[OF nH, of ?ts "length ?ts" "[]", OF refl] by (simp only: foldl_Nil list.map)
  from equiv_trans[OF e2 e3] show ?case unfolding e1 .
next
  case (Var x U)
  then have "x = v" "U = T" by simp_all
  moreover from Var.prems(1) have "X = tnorm \<theta> U" by (auto elim: has_type.cases)
  moreover have "mk_subst \<sigma> (tr (Var x U)) = \<sigma> (code (AVar x))" by simp
  ultimately show ?case using sv by (simp only:)
qed simp_all

lemma has_type_head_res:
  assumes "has_type V Bs a X" "head_of (strip_abs_body a) = Var v T"
  shows "V v = T \<and> res_type T = res_type X"
  using assms
proof (induction a arbitrary: Bs X)
  case (Abs n A b)
  from Abs.prems(1) obtain Y where "X = fun_type A Y" "has_type V (A # Bs) b Y"
    by (auto elim: has_type_elims)
  with Abs.IH Abs.prems(2) show ?case by simp
next
  case (App f u)
  let ?a = "f $ u"
  have a: "?a = list_comb (Var v T) (snd (strip_comb ?a))" using head_of_list_comb[of ?a] App.prems(2) by simp
  from App.prems(1) a obtain As where "has_type V Bs (Var v T) (foldr fun_type As X)"
    by (metis has_type_list_comb)
  then show ?case by (auto simp: arg_res_types_foldr elim: has_type.cases)
qed (auto elim: has_type.cases)

subsection \<open>The head variables of a remaining pair\<close>

lemma var_head_of_pflex:
  assumes pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>" and fb: "flexb e0 env"
    and ty: "typed env W [] t X" and tw: "\<forall>U\<in>tys t. tyw ar (tyenv env) A U"
    and bt: "below (maxidx env) t" and ws: "swf_tm ar [] t" and fht: "fh e0 t"
  obtains t' v T where "var_head_of env t = returnW (v, T)" "ok (norm_term env t) t'"
    "typed env W [] t' X" "head_of (strip_abs_body t') = Var v T"
    "vt_lookup (tenv env) v = None" "vt_lookup (tenv e0) v = None" "tnorm (tyenv env) T = T"
    "env \<Turnstile>\<^sub>p t \<approx> t'" "\<forall>U\<in>tys t'. tyw ar (tyenv env) A U" "below (maxidx env) t'"
proof -
  note p = pinvD[OF pi]
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] by simp_all
  from norm_term_pterm[OF pi g ty _ bt] tw fb fht obtain t' where nt: "norm_term env t = return t'"
    and ty': "typed env W [] t' X" and tw': "\<forall>U\<in>tys t'. tyw ar (tyenv env) A U"
    and bt': "below (maxidx env) t'" and fh': "fh e0 t'"
    by auto
  have ok: "ok (norm_term env t) t'" using nt by (simp add: return_def)
  have "\<forall>U\<in>tys t \<union> etys env. tcons (tyenv env) U" using tw p(3) tyw_tcons[OF p(2)] by blast
  note hn = norm_term_fhd[OF ok ac this]
  from fh' obtain v T where v: "fhd t' = Var v T" "vt_lookup (tenv e0) v = None" by (auto simp: fh_def)
  have h: "head_of (strip_abs_body t') = Var v T" using hn v by simp
  have hv: "var_head_of env t = returnW (v, T)" using nt h by (simp add: var_head_of_def)
  have eq: "env \<Turnstile>\<^sub>p t \<approx> t'" using norm_term_swf_tm[OF ok penv_inv_swf_env[OF p(1)] ws] by blast
  show ?thesis by (rule that[OF hv ok ty' h _ v(2) _ eq tw' bt']) (use hn v in simp_all)
qed

subsection \<open>Auxiliary lemmas\<close>

lemma head_strip_tnormt: "head_of (strip_abs_body t) = Var v T \<Longrightarrow>
    head_of (strip_abs_body (tnormt \<theta> t)) = Var v (tnorm \<theta> T)"
  by (induction t) auto

lemma vps_head_strip: "head_of (strip_abs_body t) = Var x T \<Longrightarrow> (x, T) \<in> vps t"
  by (induction t) (auto simp: vps_head_of)

lemma vreach_unbound: "\<forall>x\<in>X. vt_lookup (tenv env) x = None \<Longrightarrow> vreach env X = X"
proof
  assume X: "\<forall>x\<in>X. vt_lookup (tenv env) x = None"
  show "vreach env X \<subseteq> X"
  proof
    fix y assume "y \<in> vreach env X"
    then obtain x where x: "x \<in> X" "(y, x) \<in> (ndep env)\<^sup>*" by (auto simp: vreach_def)
    from x(2) show "y \<in> X" by (cases rule: rtranclE) (use x(1) X in \<open>auto simp: ndep_def\<close>)
  qed
qed (rule vreach_incl)

lemma typed_rlist_abs:
  "typed env W (map snd rb) t B \<Longrightarrow> typed env W [] (rlist_abs rb t) (foldr fun_type (rev (map snd rb)) B)"
proof -
  assume "typed env W (map snd rb) t B"
  then have "has_type (tctx env W) (map snd (tnormb (tyenv env) rb) @ []) (tnormt (tyenv env) t) (tnorm (tyenv env) B)"
    by (simp add: typed_def)
  from has_type_rlist_abs[OF this] show ?thesis
    by (simp add: typed_def tnormt_rlist_abs tnorm_foldr_fun rev_map)
qed

text \<open>
  The unifiers that the search returns: an environment in the invariant, and remaining flex-flex
  pairs as in @{const ptpok}, relative to an environment \<open>e0\<close> that it extends by flexible
  bindings only.
\<close>

definition prres :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> bool" where
  "prres alg ar A env tps \<longleftrightarrow> (\<exists>W e0. pinv alg ar A W env [] \<and> flexb e0 env \<and> extends env e0 \<and>
    (\<forall>ab\<in>set tps. ptpok ar A W env e0 ab))"

subsection \<open>One pair\<close>

context wf_algebra
begin

lemma psmash_flexflex1_ok:
  assumes pi: "pinv alg ar A W env []" and fb: "flexb e0 env" and ext: "extends env e0"
    and tp: "ptpok ar A W env e0 tu"
  shows "\<exists>env1 W1. okW (smash_flexflex1 tu env) env1 \<and> pinv alg ar A W1 env1 [] \<and> agreeV (maxidx env) W W1 \<and>
    maxidx env \<le> maxidx env1 \<and> pextends env1 env \<and> flexb e0 env1 \<and> env1 \<Turnstile>\<^sub>p fst tu \<approx> snd tu"
proof -
  let ?\<theta> = "tyenv env"
  note p = pinvD[OF pi]
  note pe = penv_invD[OF p(1)]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF p(2)] tinv_tcons_env[OF p(2)] by simp_all
  obtain \<rho> where g: "gsol alg ar ?\<theta> \<rho>" by (rule pinv_gsol_exists[OF pi])
  from tp obtain rb a b B where tu: "tu = (rlist_abs rb a, rlist_abs rb b)" and bok: "sbinders ar rb"
    and wa: "swf_tm ar rb a" and wb: "swf_tm ar rb b" and tw: "\<forall>U\<in>snd ` set rb \<union> tys a \<union> tys b. tyw ar ?\<theta> A U"
    and tya: "typed env W (map snd rb) a B" and tyb: "typed env W (map snd rb) b B"
    and ba: "below (maxidx env) a" and bb: "below (maxidx env) b" and fha: "fh e0 a" and fhb: "fh e0 b"
    unfolding ptpok_def by blast
  define X where "X = foldr fun_type (rev (map snd rb)) B"
  let ?t = "rlist_abs rb a" and ?u = "rlist_abs rb b"
  have tyt: "typed env W [] ?t X" and tyu: "typed env W [] ?u X"
    using typed_rlist_abs[OF tya] typed_rlist_abs[OF tyb] by (simp_all add: X_def)
  have twt: "\<forall>U\<in>tys ?t. tyw ar ?\<theta> A U" and twu: "\<forall>U\<in>tys ?u. tyw ar ?\<theta> A U"
    using tw by (auto simp: tys_rlist_abs)
  have wst: "swf_tm ar [] ?t" and wsu: "swf_tm ar [] ?u"
    using swf_tm_binding[OF bok wa] swf_tm_binding[OF bok wb] by (simp_all add: swf_tm_def)
  have bt: "below (maxidx env) ?t" and bu: "below (maxidx env) ?u" using ba bb by (simp_all add: below_rlist_abs)
  have fht: "fh e0 ?t" and fhu: "fh e0 ?u" using fha fhb by (simp_all add: fh_def)
  obtain t' v T where va: "var_head_of env ?t = returnW (v, T)" and okt: "ok (norm_term env ?t) t'"
    and tyt': "typed env W [] t' X" and ht: "head_of (strip_abs_body t') = Var v T"
    and vn: "vt_lookup (tenv env) v = None" and vn0: "vt_lookup (tenv e0) v = None"
    and Tn: "tnorm ?\<theta> T = T" and eqt: "env \<Turnstile>\<^sub>p ?t \<approx> t'"
    and twt': "\<forall>U\<in>tys t'. tyw ar ?\<theta> A U" and bt': "below (maxidx env) t'"
    by (rule var_head_of_pflex[OF pi g fb tyt twt bt wst fht])
  obtain u' w U where vb: "var_head_of env ?u = returnW (w, U)" and oku: "ok (norm_term env ?u) u'"
    and tyu': "typed env W [] u' X" and hu: "head_of (strip_abs_body u') = Var w U"
    and wn: "vt_lookup (tenv env) w = None" and wn0: "vt_lookup (tenv e0) w = None"
    and Un: "tnorm ?\<theta> U = U" and equ: "env \<Turnstile>\<^sub>p ?u \<approx> u'"
    and twu': "\<forall>U\<in>tys u'. tyw ar ?\<theta> A U" and bu': "below (maxidx env) u'"
    by (rule var_head_of_pflex[OF pi g fb tyu twu bu wsu fhu])
  text \<open>The types of the heads.\<close>
  have htt: "has_type (tctx env W) [] (tnormt ?\<theta> t') (tnorm ?\<theta> X)" using tyt' by (simp add: typed_def)
  have htu: "has_type (tctx env W) [] (tnormt ?\<theta> u') (tnorm ?\<theta> X)" using tyu' by (simp add: typed_def)
  define R where "R = res_type (tnorm ?\<theta> X)"
  have hT: "tctx env W v = T" "res_type T = R"
    using has_type_head_res[OF htt head_strip_tnormt[OF ht]] Tn by (simp_all add: R_def)
  have hU: "tctx env W w = U" "res_type U = R"
    using has_type_head_res[OF htu head_strip_tnormt[OF hu]] Un by (simp_all add: R_def)
  define Ts where "Ts = arg_types T"
  define Us where "Us = arg_types U"
  have T_eq: "T = foldr fun_type Ts R" using arg_res_type[of T] hT(2) by (simp add: Ts_def)
  have U_eq: "U = foldr fun_type Us R" using arg_res_type[of U] hU(2) by (simp add: Us_def)
  have Rn: "tnorm ?\<theta> R = R" using tnorm_res_type[OF Tn] hT(2) by simp
  have WT: "tnorm ?\<theta> (W v) = T" and WU: "tnorm ?\<theta> (W w) = U" using hT(1) hU(1) vn wn by (simp_all add: vtyp_def)
  have twT: "tyw ar ?\<theta> A T" and twU: "tyw ar ?\<theta> A U"
    using tyw_tnorm[OF p(2) p(5)[of v]] tyw_tnorm[OF p(2) p(5)[of w]] WT WU by simp_all
  have twR: "tyw ar ?\<theta> A R" and twTs: "\<forall>Z\<in>set Ts. tyw ar ?\<theta> A Z" and twUs: "\<forall>Z\<in>set Us. tyw ar ?\<theta> A Z"
    using twT twU T_eq U_eq tyw_foldr_fun by metis+
  have vm: "snd v \<le> maxidx env" using below_vps[OF bt' vps_head_strip[OF ht]] by simp
  have wm: "snd w \<le> maxidx env" using below_vps[OF bu' vps_head_strip[OF hu]] by simp
  have unbT: "\<forall>(y, S)\<in>tvars T. vt_lookup ?\<theta> y = None" and unbU: "\<forall>(y, S)\<in>tvars U. vt_lookup ?\<theta> y = None"
    using tnorm_unbound[OF ac(1), of _ _ T] tnorm_unbound[OF ac(1), of _ _ U] Tn Un by auto
  have bT: "body_type env T = return R" using body_type_unb[OF unbT] hT(2) by simp
  text \<open>The new variable.\<close>
  obtain env' var where G: "genvar (fst v) env R = (env', var)" by (cases "genvar (fst v) env R")
  define x0 where "x0 = (fst v, maxidx env + 1)"
  define W1 where "W1 = W(x0 := R)"
  note ge = genvar_pinv[OF pi G twR, folded x0_def W1_def]
  have te': "tyenv env' = ?\<theta>" by (rule ge(7))
  have x0n: "vt_lookup (tenv env') x0 = None"
  proof (rule ccontr)
    assume "vt_lookup (tenv env') x0 \<noteq> None"
    then obtain U' u where "vt_lookup (tenv env) x0 = Some (U', u)" using ge(6) by auto
    from fresh_envD[OF pe(6) this] show False by (simp add: x0_def)
  qed
  have x0n0: "vt_lookup (tenv e0) x0 = None" using extends_None[OF ext] x0n ge(6) by simp
  have vx0: "v \<noteq> x0" "w \<noteq> x0"
    using vm wm by (cases v; cases w; auto simp: x0_def less_eq_integer.rep_eq)+
  have vn': "vt_lookup (tenv env') v = None" and wn': "vt_lookup (tenv env') w = None" using vn wn ge(6) by simp_all
  have bTs: "binder_types env' T = return Ts" and bUs: "binder_types env' U = return Us"
    using binder_types_unb[of T env'] binder_types_unb[of U env'] unbT unbU te' by (simp_all add: Ts_def Us_def)
  text \<open>The solution that maps the unbound variables to constant functions.\<close>
  have g': "gsol alg ar (tyenv env') \<rho>" using g te' by simp
  define V where "V = ityp \<rho> env' W1"
  define \<sigma> where "\<sigma> = smash_sol (instE \<rho> env') V"
  have pc: "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env' []" unfolding V_def \<sigma>_def by (rule pinv_smash[OF ge(1) g']) simp
  note ei = env_invD[OF penv_inv_inst[OF pinvD(1)[OF ge(1)] g']]
  have \<sigma>u: "\<sigma> (code (AVar y)) = Abs_m (length (arg_types (V y))) (dB.Var (code (AFree STR '''' (res_type (V y)))))"
    if "vt_lookup (tenv env') y = None" for y
    using env_map_unbound[OF ei(1) ei(3), of y] that by (simp add: \<sigma>_def V_def smash_sol_def smash_atom_def)
  have Vu: "V y = tsubst \<rho> (tnorm ?\<theta> (W1 y))" if "vt_lookup (tenv env') y = None" for y
    using that te' by (simp add: V_def vtyp_def)
  define c where "c = dB.Var (code (AFree STR '''' (res_type (tsubst \<rho> R))))"
  have \<sigma>x0: "\<sigma> (code (AVar x0)) = Abs_m (length (arg_types (tsubst \<rho> R))) c"
    using \<sigma>u[OF x0n] Vu[OF x0n] Rn by (simp add: W1_def c_def)
  have \<sigma>v: "\<sigma> (code (AVar v)) = Abs_m (length Ts) (\<sigma> (code (AVar x0)))"
    using \<sigma>u[OF vn'] Vu[OF vn'] WT vx0 \<sigma>x0 T_eq
    by (simp add: W1_def c_def tsubst_foldr_fun arg_res_types_foldr Abs_m_add)
  have \<sigma>w: "\<sigma> (code (AVar w)) = Abs_m (length Us) (\<sigma> (code (AVar x0)))"
    using \<sigma>u[OF wn'] Vu[OF wn'] WU vx0 \<sigma>x0 U_eq
    by (simp add: W1_def c_def tsubst_foldr_fun arg_res_types_foldr Abs_m_add)
  text \<open>The new bodies.\<close>
  have trv: "mk_subst \<sigma>' (tr (types_abs Zs var)) = Abs_m (length Zs) (\<sigma>' (code (AVar x0)))" for \<sigma>' Zs
    by (simp add: ge(4) tr_types_abs mk_subst_Abs_m)
  have trvi: "mk_subst \<sigma>' (tr (inst \<rho> (types_abs Zs var))) = Abs_m (length Zs) (\<sigma>' (code (AVar x0)))" for \<sigma>' Zs
    by (simp add: ge(4) inst_types_abs tr_types_abs mk_subst_Abs_m)
  have tyvar: "typed env' W1 Bs var R" for Bs
    using x0n Rn te' by (simp add: ge(4) typed_def vtyp_def W1_def has_type.Var)
  have tyabs: "typed env' W1 [] (types_abs Zs var) (foldr fun_type Zs R)" for Zs
    using typed_types_abs[of env' W1 Zs "[]" var R] tyvar by simp
  have twabs: "\<forall>X'\<in>tys (types_abs Zs var). tyw ar (tyenv env') A X'" if "\<forall>Z\<in>set Zs. tyw ar ?\<theta> A Z" for Zs
    using that twR te' by (auto simp: tys_types_abs ge(4))
  have wsabs: "swf_tm ar [] (types_abs Zs var)" if "\<forall>Z\<in>set Zs. tyw ar ?\<theta> A Z" for Zs
  proof -
    have h: "has_type (tctx env' W1) [] (tnormt ?\<theta> (types_abs Zs var)) (tnorm ?\<theta> (foldr fun_type Zs R))"
      using tyabs[of Zs] te' by (simp add: typed_def)
    have "proper (types_abs Zs var)" using has_type_proper[OF h] by simp
    moreover have "no_loose_bound (tr (types_abs Zs var)) 0" using has_type_closed[OF h] by simp
    moreover have "twft ar (types_abs Zs var)" using twabs[OF that] by (simp add: twft_tys tyw_def)
    ultimately show ?thesis by (simp add: swf_tm_def)
  qed
  have babs: "below (maxidx env') (types_abs Zs var)" for Zs using ge(3,4) by (simp add: below_vps_iff x0_def)
  have vpsabs: "vps (inst \<rho> (types_abs Zs var)) = {(x0, tsubst \<rho> R)}" for Zs by (simp add: ge(4) inst_types_abs)
  have r0: "reach (instE \<rho> env') {(x0, Z)} = {(x0, Z)}" "reach (instE \<rho> env') {(w, Z)} = {(w, Z)}" for Z
    using reach_unbound[of "instE \<rho> env'" x0 Z] reach_unbound[of "instE \<rho> env'" w Z] x0n wn'
    by (simp_all add: lk_def)
  have xm: "snd x0 \<le> maxidx env'" using ge(3) by (simp add: x0_def)
  have vm': "snd v \<le> maxidx env'" and wm': "snd w \<le> maxidx env'"
    using vm wm ge(3) by (simp_all add: less_eq_integer.rep_eq)
  have twR': "tyw ar (tyenv env') A R" using twR te' by simp
  have wsw: "swf_tm ar [] (Var y R)" for y using twR by (simp add: swf_tm_def twft_tys tyw_def)
  text \<open>The first update binds \<open>w\<close>, or \<open>x0\<close> to \<open>w\<close>.\<close>
  obtain F1 T1 t1 env'' where up1: "vupdate (w, U) (types_abs Us var) env' = return env''"
    and u1: "ok (update (F1, T1) t1 env') env''"
    and F1: "F1 = w \<and> T1 = U \<and> t1 = types_abs Us var \<or> Us = [] \<and> U = R \<and> F1 = x0 \<and> T1 = R \<and> t1 = Var w R"
    and pc'': "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env'' []" and ext'': "pextends env'' env'"
    and te'': "tyenv env'' = tyenv env'" and mx'': "maxidx env'' = maxidx env'"
    and tl'': "tenv env'' = vt_update (F1, (T1, t1)) (tenv env')"
  proof (cases "Us = [] \<and> indexname_less w x0")
    case True
    then have UR: "U = R" using U_eq by simp
    have "(x0, tsubst \<rho> R) \<notin> reach (instE \<rho> env') (vps (inst \<rho> (Var w R)))" using r0(2) vx0(2) by simp
    moreover have "\<sigma> (code (AVar x0)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (Var w R)))"
      using \<sigma>w True by simp
    moreover have "typed env' W1 [] (Var w R) R"
      using wn' WU UR Rn te' vx0(2) by (simp add: typed_def vtyp_def W1_def has_type.Var)
    moreover have "below (maxidx env') (Var w R)" using wm' by (simp add: below_def)
    ultimately obtain e2 where u: "update (x0, R) (Var w R) env' = return e2"
      "pcinv alg ar A W1 \<rho> (tau V) \<sigma> e2 []" "pextends e2 env'" "tyenv e2 = tyenv env'" "maxidx e2 = maxidx env'"
      "tenv e2 = vt_update (x0, (R, Var w R)) (tenv env')"
      using pupdate_complete[OF pc x0n _ twR' _ _ wsw _ xm] twR' by (fastforce simp: W1_def)
    have "lookup env' x0 R = return None" using x0n by (simp add: lookup_def)
    then have "vupdate (w, U) (types_abs Us var) env' = return e2"
      using True vx0(2) u(1) by (subst vupdate.simps) (simp add: ge(4) bindM_def return_def)
    then show ?thesis using that[of e2 x0 R "Var w R"] u True UR by (auto simp: return_def)
  next
    case False
    have up: "vupdate (w, U) (types_abs Us var) env' = update (w, U) (types_abs Us var) env'"
    proof (cases Us)
      case Nil
      then show ?thesis using False vx0(2) by (subst vupdate.simps) (simp add: ge(4))
    next
      case (Cons Z Zs)
      then show ?thesis by (subst vupdate.simps) (simp add: ge(4))
    qed
    have "(w, tsubst \<rho> U) \<notin> reach (instE \<rho> env') (vps (inst \<rho> (types_abs Us var)))"
      unfolding vpsabs r0(1) using vx0(2) by simp
    moreover have "\<sigma> (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (types_abs Us var)))"
      using \<sigma>w by (simp add: trvi)
    moreover have "tnorm (tyenv env') (W1 w) = tnorm (tyenv env') U" using WU Un vx0(2) te' by (simp add: W1_def)
    moreover have "typed env' W1 [] (types_abs Us var) U" using tyabs[of Us] U_eq by simp
    ultimately obtain e2 where u: "update (w, U) (types_abs Us var) env' = return e2"
      "pcinv alg ar A W1 \<rho> (tau V) \<sigma> e2 []" "pextends e2 env'" "tyenv e2 = tyenv env'" "maxidx e2 = maxidx env'"
      "tenv e2 = vt_update (w, (U, types_abs Us var)) (tenv env')"
      using pupdate_complete[OF pc wn' _ _ _ twabs[OF twUs] wsabs[OF twUs] babs wm'] twU te' by fastforce
    show ?thesis using that[of e2 w U "types_abs Us var"] u up by (auto simp: return_def)
  qed
  have VR: "vreach env'' {x0} \<subseteq> {x0, w}"
  proof -
    have "vreach env'' {x0} \<subseteq> vreach env' ({x0} \<union> vars t1)" by (rule vreach_update[OF tl''])
    also have "\<dots> \<subseteq> vreach env' {x0, w}"
      by (rule vreach_subset) (use F1 in \<open>auto simp: ge(4) vars_vps_eq\<close>)
    also have "\<dots> = {x0, w}" using vreach_unbound[of "{x0, w}" env'] x0n wn' by simp
    finally show ?thesis .
  qed
  have RR: "\<forall>Y. (y, Y) \<notin> reach (instE \<rho> env'') {(x0, Z)}" if "y \<noteq> x0" "y \<noteq> w" for y Z
  proof (intro allI notI)
    fix Y assume "(y, Y) \<in> reach (instE \<rho> env'') {(x0, Z)}"
    from reach_inst_vreach[OF this] VR that show False by auto
  qed
  have pc0'': "pinv alg ar A W1 env'' []" by (rule pcinvD(1)[OF pc''])
  have te2: "tyenv env'' = ?\<theta>" using te'' te' by simp
  have vm'': "snd v \<le> maxidx env''" using vm' mx'' by simp
  have vn'': "vt_lookup (tenv env'') v = None" if "v \<noteq> w" using tl'' F1 that vx0(1) vn' by auto
  have wm'': "snd w \<le> maxidx env''" using wm' mx'' by simp
  have tcR: "tcons ?\<theta> R" by (rule tyw_tcons[OF p(2) twR])
  text \<open>The second update binds \<open>v\<close>, or \<open>w\<close> or \<open>x0\<close> to \<open>v\<close>.\<close>
  have step2: "\<exists>env1. vupdate (v, T) (types_abs Ts var) env'' = return env1 \<and>
      pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 [] \<and> pextends env1 env'' \<and> maxidx env1 = maxidx env'' \<and>
      (\<forall>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
        (\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}))"
    if vw: "v \<noteq> w"
  proof -
    note vn2 = vn''[OF vw]
    have WT'': "tnorm (tyenv env'') (W1 v) = tnorm (tyenv env'') T" using WT Tn vx0(1) te2 by (simp add: W1_def)
    have twT'': "tyw ar (tyenv env'') A T" using twT te2 by simp
    have cx0: "tctx env'' W1 x0 = R" using tl'' F1 x0n Rn te2 vx0(2) by (auto simp: vtyp_def W1_def)
    have cw: "tctx env'' W1 w = U" if "vt_lookup (tenv env'') w = None"
      using that WU vx0(2) te2 by (simp add: vtyp_def W1_def)
    have tyvar'': "typed env'' W1 Bs (Var x0 R) R" for Bs using cx0 Rn te2 by (simp add: typed_def has_type.Var)
    have tyT: "typed env'' W1 [] (types_abs Ts var) T"
      using typed_types_abs[of env'' W1 Ts "[]" var R] tyvar'' T_eq by (simp add: ge(4))
    have twTs'': "\<forall>X'\<in>tys (types_abs Ts var). tyw ar (tyenv env'') A X'" using twabs[OF twTs] te'' by simp
    have bTs'': "below (maxidx env'') (types_abs Ts var)" using babs mx'' by simp
    have acT: "\<forall>U'. (v, U') \<notin> reach (instE \<rho> env'') (vps (inst \<rho> (types_abs Ts var)))"
      unfolding vpsabs using RR[OF vx0(1) vw] by blast
    have eqT: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (types_abs Ts var)))"
      using \<sigma>v by (simp add: trvi)
    consider (S1) "vt_lookup (tenv env'') x0 = None \<or> Ts \<noteq> []"
      | (S2) "vt_lookup (tenv env'') x0 \<noteq> None" "Ts = []"
      by blast
    then show ?thesis
    proof cases
      case S1
      have hs: "\<forall>y Y. types_abs Ts var = Var y Y \<longrightarrow> vt_lookup (tenv env'') y = None"
        using S1 by (cases Ts) (auto simp: ge(4))
      from pvupdate_complete[OF pc'' vn2 WT'' twT'' tyT twTs'' wsabs[OF twTs] bTs'' vm'' acT eqT hs]
      obtain env1 where c: "vupdate (v, T) (types_abs Ts var) env'' = return env1"
        "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 []" "pextends env1 env''" "maxidx env1 = maxidx env''"
        "\<forall>x U' u. vt_lookup (tenv env1) x = Some (U', u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
          (x = v \<and> u = types_abs Ts var) \<or> (\<exists>U. types_abs Ts var = Var x U \<and> u = Var v U)"
        by blast
      have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
        if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
        using c(5) that by (fastforce simp: ge(4))
      with c(1-4) show ?thesis by blast
    next
      case S2
      have TR: "T = R" using S2(2) T_eq by simp
      have F1x: "F1 = x0" using S2(1) tl'' x0n by (cases "F1 = x0") auto
      with F1 vx0(2) have UR: "Us = []" "U = R" "T1 = R" "t1 = Var w R" by auto
      have lx0: "vt_lookup (tenv env'') x0 = Some (R, Var w R)" using tl'' F1x UR by simp
      have wn'': "vt_lookup (tenv env'') w = None" using tl'' F1x vx0(2) wn' by simp
      have tx: "types_abs Ts var = Var x0 R" using S2(2) by (simp add: ge(4))
      show ?thesis
      proof (cases "indexname_less v x0")
        case True
        have "lookup env'' x0 R = return (Some (Var w R))"
          using lx0 unified_ok[OF ac tcR tcR] te2 by (simp add: lookup_def bindM_def return_def)
        then have vu: "vupdate (v, T) (types_abs Ts var) env'' = vupdate (v, T) (Var w R) env''"
          using True vx0(1) by (subst vupdate.simps) (simp add: tx bindM_def return_def)
        have "\<forall>U'. (v, U') \<notin> reach (instE \<rho> env'') (vps (inst \<rho> (Var w R)))"
          using reach_unbound[of "instE \<rho> env''" w "tsubst \<rho> R"] wn'' vw by (simp add: lk_def)
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (Var w R)))"
          using \<sigma>v \<sigma>w S2(2) UR by simp
        moreover have "typed env'' W1 [] (Var w R) T" using cw[OF wn''] UR TR Rn te2 by (simp add: typed_def has_type.Var)
        moreover have "below (maxidx env'') (Var w R)" using wm'' by (simp add: below_def)
        ultimately obtain env1 where c: "vupdate (v, T) (Var w R) env'' = return env1"
          "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 []" "pextends env1 env''" "maxidx env1 = maxidx env''"
          "\<forall>x U' u. vt_lookup (tenv env1) x = Some (U', u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
            (x = v \<and> u = Var w R) \<or> (\<exists>U. Var w R = Var x U \<and> u = Var v U)"
          using pvupdate_complete[OF pc'' vn2 WT'' twT'' _ _ wsw _ vm''] twR te2 wn'' by fastforce
        have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
          if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
          using c(5) that by fastforce
        with c(1-4) vu show ?thesis by auto
      next
        case False
        have vu: "vupdate (v, T) (types_abs Ts var) env'' = update (v, T) (Var x0 R) env''"
          using False vx0(1) by (subst vupdate.simps) (simp add: tx)
        have "(v, tsubst \<rho> T) \<notin> reach (instE \<rho> env'') (vps (inst \<rho> (Var x0 R)))" using RR[OF vx0(1) vw] by simp
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (inst \<rho> (Var x0 R)))"
          using \<sigma>v S2(2) by simp
        moreover have "typed env'' W1 [] (Var x0 R) T" using tyvar'' TR by simp
        moreover have "below (maxidx env'') (Var x0 R)" using xm mx'' by (simp add: below_def)
        ultimately obtain env1 where c: "update (v, T) (Var x0 R) env'' = return env1"
          "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 []" "pextends env1 env''" "maxidx env1 = maxidx env''"
          "tenv env1 = vt_update (v, (T, Var x0 R)) (tenv env'')"
          using pupdate_complete[OF pc'' vn2 WT'' twT'' _ _ wsw _ vm''] twR te2 by fastforce
        have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
          if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
          using c(5) that by (cases x0) (auto split: if_splits)
        with c(1-4) vu show ?thesis by auto
      qed
    qed
  qed
  have taT: "type_abs env' T var = return (types_abs Ts var)" using bTs by (simp add: type_abs_def bindM_def return_def)
  have taU: "type_abs env' U var = return (types_abs Us var)" using bUs by (simp add: type_abs_def bindM_def return_def)
  have sm: "smash_flexflex1 tu env = (if v = w \<and> T = U then returnW env''
      else liftM (vupdate (v, T) (types_abs Ts var) env''))"
    by (simp add: smash_flexflex1_def tu va vb bT G taT taU up1)
  have swe': "swf_env ar env'" by (rule penv_inv_swf_env[OF pinvD(1)[OF ge(1)]])
  have swe'': "swf_env ar env''" by (rule penv_inv_swf_env[OF pinvD(1)[OF pc0'']])
  have wftT: "wft ar T" and wftU: "wft ar U" using twT twU by (simp_all add: tyw_def)
  have okw: "ok (vupdate (w, U) (types_abs Us var) env') env''" using up1 by (simp add: return_def)
  obtain env1 where r1: "okW (smash_flexflex1 tu env) env1" and pc1: "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 []"
    and ext1: "pextends env1 env''" and mx1: "maxidx env1 = maxidx env''"
    and nb: "\<And>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<Longrightarrow> vt_lookup (tenv env'') x = None \<Longrightarrow>
      \<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
    and vsat: "\<And>\<sigma>'. psat \<sigma>' env1 \<Longrightarrow> \<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (types_abs Ts var))"
  proof (cases "v = w")
    case True
    then have TU: "T = U" using WT WU by simp
    then have "Ts = Us" by (simp add: Ts_def Us_def)
    note vupdate_pwf(3)[OF okw swe' wsabs[OF twUs] wftU]
    with \<open>Ts = Us\<close> show ?thesis using that[of env''] sm True TU pc'' by auto
  next
    case False
    from step2[OF False] obtain env1 where c: "vupdate (v, T) (types_abs Ts var) env'' = return env1"
      "pcinv alg ar A W1 \<rho> (tau V) \<sigma> env1 []" "pextends env1 env''" "maxidx env1 = maxidx env''"
      "\<forall>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
        (\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0})"
      by blast
    have "ok (vupdate (v, T) (types_abs Ts var) env'') env1" using c(1) by (simp add: return_def)
    note vupdate_pwf(3)[OF this swe'' wsabs[OF twTs] wftT]
    with c sm False show ?thesis using that[of env1] by auto
  qed
  have ext1': "pextends env1 env" by (rule pextends_trans[OF ext1 pextends_trans[OF ext'' ge(5)]])
  text \<open>The new bindings are flexible.\<close>
  have fh3: "fh e0 u" if "fhd u = Var y Y'" "y \<in> {v, w, x0}" for u y Y'
    using that vn0 wn0 x0n0 by (auto simp: fh_def)
  have "flexb e0 env1"
  proof (rule flexb_step[OF fb pextendsD(1)[OF ext1']])
    fix x Y u assume x: "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env) x = None"
    show "fh e0 u"
    proof (cases "vt_lookup (tenv env'') x")
      case None
      from nb[OF x(1) None] fh3 show ?thesis by blast
    next
      case (Some b)
      with extendsD[OF pextendsD(1)[OF ext1] Some] x(1) have "vt_lookup (tenv env'') x = Some (Y, u)" by simp
      with tl'' x(2) ge(6) have "x = F1" "u = t1" by (auto split: if_splits)
      with F1 show ?thesis using fh3[of u x0 R] fh3[of u w R] by (auto simp: ge(4))
    qed
  qed
  text \<open>The pair is solved.\<close>
  moreover have "env1 \<Turnstile>\<^sub>p fst tu \<approx> snd tu"
  proof (rule penv_equivI)
    fix \<sigma>' assume ps: "psat \<sigma>' env1"
    have cl: "closed_on UNIV \<sigma>'" by (rule psatD(1)[OF ps])
    have ps'': "psat \<sigma>' env''" by (rule psat_pextends[OF ps ext1])
    have nl: "no_loose_bound (\<sigma>' (code (AVar x0))) 0" using closed_onD[OF cl] by simp
    have sw: "\<sigma>' (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types (tnorm ?\<theta> U))) (\<sigma>' (code (AVar x0)))"
      using vupdate_pwf(3)[OF okw swe' wsabs[OF twUs] wftU ps''] Un by (simp add: trv Us_def)
    have sv: "\<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types (tnorm ?\<theta> T))) (\<sigma>' (code (AVar x0)))"
      using vsat[OF ps] Tn by (simp add: trv Ts_def)
    have ca: "mk_subst \<sigma>' (tr t') \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types (tnorm ?\<theta> X))) (\<sigma>' (code (AVar x0)))"
      by (rule flex_pconst[OF cl htt ht sv nl])
    have cb: "mk_subst \<sigma>' (tr u') \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types (tnorm ?\<theta> X))) (\<sigma>' (code (AVar x0)))"
      by (rule flex_pconst[OF cl htu hu sw nl])
    have ps0: "psat \<sigma>' env" by (rule psat_pextends[OF ps ext1'])
    have ea: "mk_subst \<sigma>' (tr ?t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr t')" by (rule penv_equivD[OF eqt ps0])
    have eb: "mk_subst \<sigma>' (tr ?u) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr u')" by (rule penv_equivD[OF equ ps0])
    show "mk_subst \<sigma>' (tr (fst tu)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (snd tu))"
      using equiv_trans[OF equiv_trans[OF ea ca] equiv_sym[OF equiv_trans[OF eb cb]]] by (simp add: tu)
  qed
  ultimately show ?thesis using r1 pcinvD(1)[OF pc1] ge(2,3) mx1 mx'' ext1'
    by (intro exI[of _ env1] exI[of _ W1]) simp
qed


subsection \<open>All pairs\<close>


lemma foldrW_psmash:
  assumes "pinv alg ar A W env []" "flexb e0 env" "extends env e0" "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
  shows "\<exists>env' W'. okW (foldrW smash_flexflex1 tps env) env' \<and> pinv alg ar A W' env' [] \<and> pextends env' env \<and>
    flexb e0 env' \<and> maxidx env \<le> maxidx env' \<and> agreeV (maxidx env) W W' \<and>
    (\<forall>ab\<in>set tps. env' \<Turnstile>\<^sub>p fst ab \<approx> snd ab)"
  using assms(4)
proof (induction tps)
  case Nil
  then show ?case using assms(1,2) by (intro exI[of _ env] exI[of _ W]) (simp add: agreeV_def)
next
  case (Cons ab tps)
  from Cons obtain env1 W1 where f: "okW (foldrW smash_flexflex1 tps env) env1" and i1: "pinv alg ar A W1 env1 []"
    and x1: "pextends env1 env" and fb1: "flexb e0 env1" and m1: "maxidx env \<le> maxidx env1"
    and a1: "agreeV (maxidx env) W W1" and s1: "\<forall>ab\<in>set tps. env1 \<Turnstile>\<^sub>p fst ab \<approx> snd ab"
    by auto
  have tp: "ptpok ar A W1 env1 e0 ab" using Cons.prems ptpok_mono[OF _ assms(1) i1 x1 a1 m1] by simp
  from psmash_flexflex1_ok[OF i1 fb1 extends_trans[OF pextendsD(1)[OF x1] assms(3)] tp]
  obtain env2 W2 where s: "okW (smash_flexflex1 ab env1) env2" "pinv alg ar A W2 env2 []"
    "agreeV (maxidx env1) W1 W2" "maxidx env1 \<le> maxidx env2" "pextends env2 env1" "flexb e0 env2"
    "env2 \<Turnstile>\<^sub>p fst ab \<approx> snd ab"
    by blast
  have "okW (foldrW smash_flexflex1 (ab # tps) env) env2" using f s(1) by auto
  moreover have "\<forall>ab\<in>set tps. env2 \<Turnstile>\<^sub>p fst ab \<approx> snd ab" using s1 penv_equiv_pextends[OF _ s(5)] by blast
  ultimately show ?case using s(2-7) pextends_trans[OF s(5) x1] agreeV_trans[OF a1 s(3) m1] m1
    by (intro exI[of _ env2] exI[of _ W2]) auto
qed

text \<open>On the unifiers of the search (\<^const>\<open>prres\<close>), unifiers, \<^const>\<open>smash_flexflex\<close> terminates normally and solves the pairs.\<close>

theorem psmash_flexflex_prres:
  assumes "prres alg ar A env tps"
  obtains env' W' where "okW (smash_flexflex (env, tps)) env'" "pextends env' env" "pinv alg ar A W' env' []"
    "\<And>\<sigma>. psat \<sigma> env' \<Longrightarrow> tsolved \<sigma> tps"
proof -
  from assms obtain W e0 where "pinv alg ar A W env []" "flexb e0 env" "extends env e0"
    "\<forall>ab\<in>set tps. ptpok ar A W env e0 ab"
    unfolding prres_def by blast
  from foldrW_psmash[OF this] obtain env' W' where f: "okW (foldrW smash_flexflex1 tps env) env'"
    "pinv alg ar A W' env' []" "pextends env' env" "\<forall>ab\<in>set tps. env' \<Turnstile>\<^sub>p fst ab \<approx> snd ab"
    by blast
  have "tsolved \<sigma> tps" if "psat \<sigma> env'" for \<sigma>
    using f(4) that by (fastforce simp: tsolved_def penv_equiv_def)
  with f(1-3) show ?thesis using that by (simp add: smash_flexflex_def)
qed

lemma foldrW_padd_ffpair_prres:
  assumes "pinv alg ar A W env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs" and r: "okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  shows "prres alg ar A (fst r) (snd r)"
proof -
  obtain \<rho> where g: "gsol alg ar (tyenv env) \<rho>" by (rule pinv_gsol_exists[OF assms(1)])
  from foldrW_padd_ffpair_complete[OF pinv_smash[OF assms(1) g assms(2)] assms(2,3)] obtain env' tps' W' \<sigma>'
    where o: "okW (foldrW (add_ffpair alg) ffs (env, [])) (env', tps')"
      and c: "pcinv alg ar A W' \<rho> (tau (ityp \<rho> env W)) \<sigma>' env' []" "pextends env' env" "flexb env env'"
        "\<forall>ab\<in>set tps'. ptpok ar A W' env' env ab"
    by blast
  from o r have "r = (env', tps')" by auto
  then show ?thesis using pcinvD(1)[OF c(1)] c(2-4) pextendsD(1)[OF c(2)] unfolding prres_def by auto
qed

subsection \<open>The enumerated unifiers\<close>

theorem hounifiers_prres:
  assumes "cfg_alg cfg = alg" "finite A" "pinv alg ar A W env (map (\<lambda>(t, u). (rb, t, u)) tus)"
  shows "fin cfg (hounifiers rb env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)"
  unfolding hounifiers_def
proof (rule fin_AddUnify_paux[OF assms(1) pmatch_fin_holds[OF assms(1,2)] assms(2) _ assms(3) fin_Empty])
  fix W env ffs \<theta>0 r
  assume "pinv alg ar A W env ffs" "\<forall>dp\<in>set ffs. pff_shape env W dp \<and> heads_unb env dp"
    "fch W (tyenv env) \<theta>0 ffs" "okW (foldrW (add_ffpair alg) ffs (env, [])) r"
  from foldrW_padd_ffpair_prres[OF this]
  show "\<exists>env' tps. El_R (fst r) (snd r) = El_R env' tps \<and> prres alg ar A env' tps" by simp
qed

theorem unifiers_prres:
  assumes cfg: "cfg_alg cfg = alg" and finA: "finite A" and pi: "pinv alg ar A W env (dps_of tus)"
  obtains s where "unifiers alg env tus = Some (Ok s)"
    "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)"
proof -
  from foldM_unify_pinv[OF finA pi] obtain r where
    r: "foldM (\<lambda>(t, u) env. unify alg t u env) tus env = Some r" "fails_ok (Some r)"
      "\<forall>env'. r = Ok env' \<longrightarrow> (\<exists>W'. pinv alg ar A W' env' [])"
    by blast
  show thesis
  proof (cases r)
    case (Ok env')
    with r have "unifiers alg env tus = Some (Ok (S_Single (El_R env' [])))"
      by (simp add: unifiers_def handle_def bindM_def return_def)
    moreover have "prres alg ar A env' []"
      using r(3) Ok unfolding prres_def by (auto simp: flexb_def intro!: exI[of _ env'] extends_refl)
    then have "fin cfg (S_Single (El_R env' [])) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)"
      by (auto intro: fin_Single)
    ultimately show thesis by (rule that)
  next
    case (Err e)
    with r(2) have "e = Pattern \<or> (\<exists>u. e = Unif u)" by (simp add: fails_ok_def exn_ok_def)
    then show thesis
    proof
      assume "e = Pattern"
      with r(1) Err have "unifiers alg env tus = Some (Ok (hounifiers [] env tus))"
        by (simp add: unifiers_def handle_def bindM_def return_def)
      moreover have "fin cfg (hounifiers [] env tus) (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)"
        by (rule hounifiers_prres[OF cfg finA]) (use pi in simp)
      ultimately show thesis by (rule that)
    next
      assume "\<exists>u. e = Unif u"
      with r(1) Err have "unifiers alg env tus = Some (Ok S_Empty)"
        by (auto simp: unifiers_def handle_def bindM_def return_def)
      then show thesis by (rule that) simp
    qed
  qed
qed

text \<open>
  Hence every unifier that the enumeration of \<^const>\<open>unifiers\<close> yields, which is finite, can be
  smashed to an extension without remaining flex-flex pairs.
\<close>

theorem unifiers_psmash:
  assumes "cfg_alg cfg = alg" "finite A" "pinv alg ar A W env (dps_of tus)"
  obtains s xs where "unifiers alg env tus = Some (Ok s)" "evals cfg s xs"
    "\<forall>x\<in>set xs. \<exists>env' tps env'' W'. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and>
      pextends env'' env' \<and> pinv alg ar A W' env'' [] \<and> (\<forall>\<sigma>. psat \<sigma> env'' \<longrightarrow> tsolved \<sigma> tps)"
proof -
  from unifiers_prres[OF assms] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps)"
    by blast
  from f obtain xs where xs: "evals cfg s xs" "\<forall>x\<in>set xs. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps"
    by (auto simp: fin_def)
  have "\<exists>env' tps env'' W'. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and>
      pextends env'' env' \<and> pinv alg ar A W' env'' [] \<and> (\<forall>\<sigma>. psat \<sigma> env'' \<longrightarrow> tsolved \<sigma> tps)"
    if x: "x \<in> set xs" for x
  proof -
    from xs(2) x obtain env' tps where xe: "x = El_R env' tps" and r: "prres alg ar A env' tps" by blast
    from psmash_flexflex_prres[OF r] obtain env'' W' where "okW (smash_flexflex (env', tps)) env''"
      "pextends env'' env'" "pinv alg ar A W' env'' []" "\<And>\<sigma>. psat \<sigma> env'' \<Longrightarrow> tsolved \<sigma> tps"
      by blast
    with xe show ?thesis by blast
  qed
  with u xs(1) that show ?thesis by blast
qed

lemma evals_psinv:
  "evals cfg s xs \<Longrightarrow> psinv ar (GR e0 ds0) s \<Longrightarrow> x \<in> set xs \<Longrightarrow>
    \<exists>env tps. x = El_R env tps \<and> punifier e0 ds0 env tps"
proof (induction rule: evals.induct)
  case (Cons s evs y s' xs)
  from pull_punifier[OF Cons.prems(1) Cons.hyps(1)] obtain env tps where
    "y = El_R env tps" "punifier e0 ds0 env tps" "psinv ar (GR e0 ds0) s'" by auto
  with Cons.IH Cons.prems(2) show ?case by auto
qed simp

text \<open>
  For \<^const>\<open>hounifiers\<close>, the smashed unifiers are sound: they extend the input environment, and
  their solutions solve the input pairs.
\<close>

theorem hounifiers_psmash:
  assumes "cfg_alg cfg = alg" "finite A" "pinv alg ar A W env (map (\<lambda>(t, u). (rb, t, u)) tus)"
    and rb: "sbinders ar rb"
  obtains xs where "evals cfg (hounifiers rb env tus) xs"
    "\<forall>x\<in>set xs. \<exists>env' tps env''. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and>
      punifier env (map (\<lambda>(t, u). (rb, t, u)) tus) env'' []"
proof -
  let ?dps = "map (\<lambda>(t, u). (rb, t, u)) tus"
  note p = pinvD[OF assms(3)]
  have "\<forall>(t, u)\<in>set tus. swf_tm ar rb t \<and> swf_tm ar rb u"
    using p(4) by (fastforce simp: swf_dp_def)
  note ps = hounifiers_psinv[OF penv_inv_swf_env[OF p(1)] rb this]
  from hounifiers_prres[OF assms(1-3)] obtain xs where xs: "evals cfg (hounifiers rb env tus) xs"
    "\<forall>x\<in>set xs. \<exists>env' tps. x = El_R env' tps \<and> prres alg ar A env' tps"
    by (auto simp: fin_def)
  have "\<exists>env' tps env''. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and> punifier env ?dps env'' []"
    if x: "x \<in> set xs" for x
  proof -
    from xs(2) x obtain env' tps where xe: "x = El_R env' tps" and r: "prres alg ar A env' tps" by blast
    from evals_psinv[OF xs(1) ps x] xe have un: "punifier env ?dps env' tps" by simp
    from psmash_flexflex_prres[OF r] obtain env'' where sm: "okW (smash_flexflex (env', tps)) env''"
      "pextends env'' env'" "\<And>\<sigma>. psat \<sigma> env'' \<Longrightarrow> tsolved \<sigma> tps"
      by blast
    have "punifier env ?dps env'' []"
      using un sm(2,3) unfolding punifier_def tsolved_def by (blast intro: pextends_trans psat_pextends)
    with xe sm(1) show ?thesis by blast
  qed
  with xs(1) that show ?thesis by blast
qed
end
end
