section \<open>Smashing the Remaining Flex-Flex Pairs\<close>

theory Unify_Smash
  imports Unify_Match_Fin
begin

context csig
begin

text \<open>
  \<^const>\<open>smash_flexflex\<close> solves the flex-flex pairs that remain with a unifier by binding both
  head variables of each pair to constant functions with the same new body variable. On the
  unifiers that the search returns (\<^const>\<open>rres\<close>), it terminates without an exception, and its
  result solves the original problem: the heads of the remaining pairs are unbound variables
  after normalization, and the new bindings keep the environment acyclic.
\<close>

subsection \<open>Normalizing under a binder\<close>

lemma could_beta_contract_rlist_abs[simp]: "could_beta_contract (rlist_abs rb t) = could_beta_contract t"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma strip_abs_body_rlist_abs[simp]: "strip_abs_body (rlist_abs rb t) = strip_abs_body t"
  by (induction rb t rule: rlist_abs.induct) simp_all

lemma norm_term1_rlist_abs:
  "norm_term1 te t = Some (Ok t') \<Longrightarrow> norm_term1 te (rlist_abs rb t) = Some (Ok (rlist_abs rb t'))"
proof (induction rb arbitrary: t t')
  case (Cons aT rb)
  obtain a T where aT: "aT = (a, T)" by (cases aT)
  have "norm_term1 te (Abs a T t) = Some (Ok (Abs a T t'))"
    using Cons.prems by (subst norm_term1.simps) (simp add: bindM_def return_def)
  from Cons.IH[OF this] show ?case by (simp add: aT)
qed simp

lemma norm_term_rlist_abs:
  "vt_is_empty (tyenv env) \<Longrightarrow> norm_term env t = return t' \<Longrightarrow> norm_term env (rlist_abs rb t) = return (rlist_abs rb t')"
  by (cases "env_is_empty env \<and> \<not> could_beta_contract t")
    (auto simp: norm_term_def return_def intro: norm_term1_rlist_abs)

subsection \<open>Flexible bindings\<close>

lemma flexb_step:
  assumes "flexb env0 env" "extends env env'"
    "\<And>x U u. vt_lookup (tenv env') x = Some (U, u) \<Longrightarrow> vt_lookup (tenv env) x = None \<Longrightarrow> fh env0 u"
  shows "flexb env0 env'"
  unfolding flexb_def
proof (intro allI impI)
  fix x U u assume x: "vt_lookup (tenv env') x = Some (U, u)" "vt_lookup (tenv env0) x = None"
  show "fh env0 u"
  proof (cases "vt_lookup (tenv env) x")
    case None
    with assms(3) x(1) show ?thesis by blast
  next
    case (Some b)
    with extendsD[OF assms(2) Some] x(1) have "vt_lookup (tenv env) x = Some (U, u)" by simp
    with assms(1) x(2) show ?thesis unfolding flexb_def by blast
  qed
qed

subsection \<open>The constant instance of a flexible term\<close>

lemma flex_const:
  assumes cl: "closed_on UNIV \<sigma>" and ty: "has_type W Bs a B" and nf: "\<not> is_funT B"
    and h: "head_of a = Var v T" and sv: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types T)) c"
    and nl: "no_loose_bound c 0"
  shows "mk_subst \<sigma> (tr a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> c"
proof -
  let ?args = "snd (strip_comb a)"
  have a: "a = list_comb (Var v T) ?args" using head_of_list_comb[of a] h by simp
  from ty a obtain As where hv: "has_type W Bs (Var v T) (foldr fun_type As B)"
    and As: "list_all2 (has_type W Bs) ?args As"
    by (metis has_type_list_comb)
  from hv have T: "T = foldr fun_type As B" by (auto elim: has_type.cases)
  have m: "length (arg_types T) = length (map (mk_subst \<sigma> \<circ> tr) ?args)"
    using arg_res_type_fun[OF nf, of As] list_all2_lengthD[OF As] T by simp
  have e1: "mk_subst \<sigma> (tr a) = \<sigma> (code (AVar v)) \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) ?args"
    by (subst a) (simp add: tr_list_comb)
  have e2: "\<sigma> (code (AVar v)) \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) ?args \<equiv>\<^sub>\<beta>\<^sub>\<eta>
      Abs_m (length (arg_types T)) c \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) ?args"
    by (rule equiv_list_app[OF sv]) (simp add: list_all2_conv_all_nth equiv_refl)
  have e3: "Abs_m (length (arg_types T)) c \<degree>\<degree> map (mk_subst \<sigma> \<circ> tr) ?args \<equiv>\<^sub>\<beta>\<^sub>\<eta> c"
    using Abs_m_apps_closed_head[OF nl m[symmetric], of "[]"] by simp
  from equiv_trans[OF e2 e3] e1 show ?thesis by simp
qed

subsection \<open>The head variables of a remaining pair\<close>

lemma var_head_of_flex:
  assumes ei: "env_inv ar V env" and fb: "flexb env0 env" and ext: "extends env0 env"
    and tya: "has_type V (map snd rb) a B" and nf: "\<not> is_funT B" and wa: "wf_tm ar rb a"
    and ba: "below (maxidx env) a" and fha: "fh env0 a"
  obtains a' v T where "var_head_of env (rlist_abs rb a) = returnW (v, T)" "has_type V (map snd rb) a' B"
    "head_of a' = Var v T" "vt_lookup (tenv env) v = None" "vt_lookup (tenv env0) v = None"
    "wf_tm ar rb a'" "below (maxidx env) a'" "env \<Turnstile> rlist_abs rb a \<approx> rlist_abs rb a'"
proof -
  note e0 = env_invD[OF ei]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF e0(2)])
  from norm_term_term[OF e0(1-3) tya] obtain a' where nt: "norm_term env a = return a'"
    and tya': "has_type V (map snd rb) a' B" and hn: "\<forall>x U. head_of a' = Var x U \<longrightarrow> vt_lookup (tenv env) x = None"
    and at: "is_Abs a' \<or> fhd a' = head_of a'" and fl: "fh env0 a'"
    using fb fha by blast
  have nA: "\<not> is_Abs a'" using has_type_Abs_funT tya' nf by blast
  from at nA fl obtain v T where h: "head_of a' = Var v T" "vt_lookup (tenv env0) v = None"
    by (auto simp: fh_def)
  have vn: "vt_lookup (tenv env) v = None" using hn h by blast
  have ntr: "norm_term env (rlist_abs rb a) = return (rlist_abs rb a')" by (rule norm_term_rlist_abs[OF e nt])
  have hv: "var_head_of env (rlist_abs rb a) = returnW (v, T)"
    using ntr h nA by (simp add: var_head_of_def liftM_return strip_abs_body_nonAbs)
  have ok: "ok (norm_term env a) a'" using nt by (simp add: return_def)
  note nw = norm_term_wf_tm[OF ok e0(2) wa]
  have bw: "below (maxidx env) a'" by (rule norm_term_below[OF nt e e0(4) ba])
  have eqv: "env \<Turnstile> rlist_abs rb a \<approx> rlist_abs rb a'" using env_equiv_rlist_abs nw by blast
  show ?thesis by (rule that[OF hv tya' h(1) vn h(2) conjunct1[OF nw] bw eqv])
qed

subsection \<open>One pair\<close>

text \<open>
  The new variable \<open>x0\<close> of \<^const>\<open>smash_flexflex1\<close> and the head variables \<open>v\<close>, \<open>w\<close> of the
  pair are unbound; the bindings bind them to each other or to the constant functions with body
  \<open>x0\<close>. The canonical solution that maps unbound variables to constant functions
  (\<^const>\<open>smash_sol\<close>) satisfies these bindings, so they keep the invariant.
\<close>

lemma smash_flexflex1_ok:
  assumes ei: "env_inv ar V env" and fb: "flexb env0 env" and ext: "extends env0 env"
    and fr0: "fresh_env env0" and mx: "maxidx env0 \<le> maxidx env" and tp: "tpok ar V env0 (maxidx env) tu"
  shows "\<exists>env1 V1. okW (smash_flexflex1 tu env) env1 \<and> env_inv ar V1 env1 \<and> agreeV (maxidx env) V V1 \<and>
    maxidx env \<le> maxidx env1 \<and> extends env env1 \<and> flexb env0 env1 \<and> env1 \<Turnstile> fst tu \<approx> snd tu"
proof -
  note e0 = env_invD[OF ei]
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF e0(2)])
  from tp obtain rb a b B where tu: "tu = (rlist_abs rb a, rlist_abs rb b)" and bok: "binders_ok ar rb"
    and wa: "wf_tm ar rb a" and wb: "wf_tm ar rb b" and tya: "has_type V (map snd rb) a B"
    and tyb: "has_type V (map snd rb) b B" and nf: "\<not> is_funT B" and ba: "below (maxidx env) a"
    and bb: "below (maxidx env) b" and fha: "fh env0 a" and fhb: "fh env0 b"
    unfolding tpok_def by blast
  obtain a' v T where va: "var_head_of env (rlist_abs rb a) = returnW (v, T)"
    and tya': "has_type V (map snd rb) a' B" and ha: "head_of a' = Var v T"
    and vn: "vt_lookup (tenv env) v = None" and vn0: "vt_lookup (tenv env0) v = None"
    and wa': "wf_tm ar rb a'" and ba': "below (maxidx env) a'" and eqa: "env \<Turnstile> rlist_abs rb a \<approx> rlist_abs rb a'"
    by (rule var_head_of_flex[OF ei fb ext tya nf wa ba fha])
  obtain b' w U where vb: "var_head_of env (rlist_abs rb b) = returnW (w, U)"
    and tyb': "has_type V (map snd rb) b' B" and hb: "head_of b' = Var w U"
    and wn: "vt_lookup (tenv env) w = None" and wn0: "vt_lookup (tenv env0) w = None"
    and wb': "wf_tm ar rb b'" and bb': "below (maxidx env) b'" and eqb: "env \<Turnstile> rlist_abs rb b \<approx> rlist_abs rb b'"
    by (rule var_head_of_flex[OF ei fb ext tyb nf wb bb fhb])
  text \<open>The types of the heads.\<close>
  have tyv: "has_type V (map snd rb) (Var v T) T" and Vv: "V v = T"
    using has_type_head_of[OF tya'] ha by (auto elim: has_type_elims intro: has_type.Var)
  have tyw: "has_type V (map snd rb) (Var w U) U" and Vw: "V w = U"
    using has_type_head_of[OF tyb'] hb by (auto elim: has_type_elims intro: has_type.Var)
  have rT: "res_type T = B" using res_type_head(1)[OF tya' nf tyv[folded ha]] .
  have rU: "res_type U = B" using res_type_head(1)[OF tyb' nf tyw[folded hb]] .
  have whv: "wf_tm ar rb (Var v T)" using wa' head_of_list_comb[of a'] ha by (metis wf_tm_list_comb)
  have whw: "wf_tm ar rb (Var w U)" using wb' head_of_list_comb[of b'] hb by (metis wf_tm_list_comb)
  have gT: "ground ar T" by (rule ground_has_type[OF e bok whv tyv])
  have gU: "ground ar U" by (rule ground_has_type[OF e bok whw tyw])
  define Ts where "Ts = arg_types T"
  define Us where "Us = arg_types U"
  have T_eq: "T = foldr fun_type Ts B" using arg_res_type[of T] rT by (simp add: Ts_def)
  have U_eq: "U = foldr fun_type Us B" using arg_res_type[of U] rU by (simp add: Us_def)
  have gTs: "\<forall>A\<in>set Ts. ground ar A" and gB: "ground ar B" using gT T_eq ground_foldr_iff by metis+
  have gUs: "\<forall>A\<in>set Us. ground ar A" using gU U_eq ground_foldr_iff by metis
  have vm: "snd v \<le> maxidx env" using below_vps[OF ba' vps_head_of[OF ha]] by simp
  have wm: "snd w \<le> maxidx env" using below_vps[OF bb' vps_head_of[OF hb]] by simp
  text \<open>The new variable.\<close>
  obtain env' var where G: "genvar (fst v) env B = (env', var)" by (cases "genvar (fst v) env B")
  define x0 where "x0 = (fst v, maxidx env + 1)"
  define V1 where "V1 = V(x0 := B)"
  note g = genvar_term[OF ei G, folded x0_def V1_def]
  note e1 = env_invD[OF g(1)]
  have e': "vt_is_empty (tyenv env')" by (rule wf_envD(1)[OF e1(2)])
  have x0n: "vt_lookup (tenv env') x0 = None"
    using g(6) fresh_envD[OF e0(4), of x0] by (cases "vt_lookup (tenv env) x0") (auto simp: x0_def)
  have x0n0: "vt_lookup (tenv env0) x0 = None" using extends_None[OF ext] x0n g(6) by simp
  have vx0: "v \<noteq> x0" "w \<noteq> x0" using vm wm less_add_one[of "maxidx env"] by (auto simp: x0_def prod_eq_iff)
  have V1v: "V1 v = T" and V1w: "V1 w = U" and V1x0: "V1 x0 = B" using Vv Vw vx0 by (simp_all add: V1_def)
  have vn': "vt_lookup (tenv env') v = None" and wn': "vt_lookup (tenv env') w = None" using vn wn g(6) by simp_all
  have mx': "maxidx env' = maxidx env + 1" by (rule g(3))
  text \<open>The solution that maps the unbound variables to constant functions.\<close>
  define \<sigma> where "\<sigma> = smash_sol env' V1"
  have sol: "solution V1 (tau V1) \<sigma> env'" unfolding \<sigma>_def by (rule smash_solution[OF e1(1,3,2)])
  define cB where "cB = dB.Var (code (AFree STR '''' B))"
  have aB: "arg_types B = []" "res_type B = B" using arg_res_type_fun[OF nf, of "[]"] by simp_all
  have \<sigma>u: "\<sigma> (code (AVar y)) = Abs_m (length (arg_types (V1 y))) (dB.Var (code (AFree STR '''' (res_type (V1 y)))))"
    if "vt_lookup (tenv env') y = None" for y
    using env_map_unbound[OF e1(1) e1(3) that] by (simp add: \<sigma>_def smash_sol_def smash_atom_def)
  have \<sigma>x0: "\<sigma> (code (AVar x0)) = cB" using \<sigma>u[OF x0n] V1x0 aB by (simp add: cB_def)
  have \<sigma>v: "\<sigma> (code (AVar v)) = Abs_m (length Ts) cB" using \<sigma>u[OF vn'] V1v rT by (simp add: cB_def Ts_def)
  have \<sigma>w: "\<sigma> (code (AVar w)) = Abs_m (length Us) cB" using \<sigma>u[OF wn'] V1w rU by (simp add: cB_def Us_def)
  have trv: "mk_subst \<sigma>' (tr (types_abs Zs var)) = Abs_m (length Zs) (\<sigma>' (code (AVar x0)))" for \<sigma>' Zs
    by (simp add: g(4) tr_types_abs)
  have tyabs: "has_type V1 [] (types_abs Zs var) (foldr fun_type Zs B)" for Zs
    using has_type_types_abs[of V1 Zs "[]" var B] V1x0 by (simp add: g(4) has_type.Var)
  have wsabs: "wf_tm ar [] (types_abs Zs var)" if "\<forall>A\<in>set Zs. ground ar A" for Zs
    by (rule wf_tm_types_abs[OF that]) (simp add: g(4) wf_cp_def gB)
  have "below (maxidx env') var" using mx' by (simp add: g(4) below_def x0_def)
  then have babs: "below (maxidx env') (types_abs Zs var)" for Zs by simp
  have vpsabs: "vps (types_abs Zs var) = {(x0, B)}" for Zs by (simp add: g(4))
  have r0: "reach env' {(x0, B)} = {(x0, B)}" "reach env' {(w, B)} = {(w, B)}"
    using reach_unbound[of env' x0 B] reach_unbound[of env' w B] x0n wn' by (simp_all add: lk_def)
  have xm: "snd x0 \<le> maxidx env'" using mx' by (simp add: x0_def)
  have vm': "snd v \<le> maxidx env'" and wm': "snd w \<le> maxidx env'" using vm wm mx' by simp_all
  text \<open>The first update binds \<open>w\<close>, or \<open>x0\<close> to \<open>w\<close>.\<close>
  obtain F1 T1 t1 env'' where up1: "vupdate (w, U) (types_abs Us var) env' = return env''"
    and u1: "update (F1, T1) t1 env' = return env''"
    and F1: "F1 = w \<and> t1 = types_abs Us var \<or> Us = [] \<and> U = B \<and> F1 = x0 \<and> T1 = B \<and> t1 = Var w B"
    and inv'': "env_inv ar V1 env''" and sol'': "solution V1 (tau V1) \<sigma> env''"
    and ext'': "extends env' env''" and mx'': "maxidx env'' = maxidx env'"
    and te'': "tenv env'' = vt_update (F1, (T1, t1)) (tenv env')"
  proof (cases "Us = [] \<and> indexname_less w x0")
    case True
    then have UB: "U = B" using U_eq by simp
    have "(x0, B) \<notin> reach env' (vps (Var w B))" using r0(2) vx0(2) by auto
    moreover have "\<sigma> (code (AVar x0)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (Var w B))"
      using \<sigma>x0 \<sigma>w True by (simp add: equiv_refl)
    moreover have "has_type V1 [] (Var w B) B" using V1w UB by (simp add: has_type.Var)
    moreover have "wf_tm ar [] (Var w B)" using gB by (simp add: wf_tm_def)
    moreover have "below (maxidx env') (Var w B)" using wm' by (simp add: below_def)
    ultimately obtain e2 where u: "update (x0, B) (Var w B) env' = return e2" "env_inv ar V1 e2"
      "solution V1 (tau V1) \<sigma> e2" "extends env' e2" "maxidx e2 = maxidx env'"
      "tenv e2 = vt_update (x0, (B, Var w B)) (tenv env')"
      using update_complete[OF g(1) sol x0n V1x0 _ _ gB _ xm] by blast
    have "vupdate (w, U) (types_abs Us var) env' = return e2"
      using True vx0(2) u(1) lookup_unbound[OF e' x0n, of B]
      by (subst vupdate.simps) (simp add: g(4) UB)
    then show ?thesis using that[of e2 x0 B "Var w B"] u True UB by auto
  next
    case False
    have up: "vupdate (w, U) (types_abs Us var) env' = update (w, U) (types_abs Us var) env'"
    proof (cases Us)
      case Nil
      then show ?thesis using False vx0(2) by (subst vupdate.simps) (simp add: g(4))
    next
      case (Cons A As)
      then show ?thesis by (subst vupdate.simps) (simp add: g(4))
    qed
    have "(w, U) \<notin> reach env' (vps (types_abs Us var))" unfolding vpsabs using r0(1) vx0(2) by simp
    moreover have "\<sigma> (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Us var))"
      using \<sigma>w \<sigma>x0 by (simp add: trv equiv_refl)
    ultimately obtain e2 where u: "update (w, U) (types_abs Us var) env' = return e2" "env_inv ar V1 e2"
      "solution V1 (tau V1) \<sigma> e2" "extends env' e2" "maxidx e2 = maxidx env'"
      "tenv e2 = vt_update (w, (U, types_abs Us var)) (tenv env')"
      using update_complete[OF g(1) sol wn' V1w tyabs[of Us, folded U_eq] wsabs[OF gUs] gU babs wm'] by blast
    show ?thesis using that[of e2 w U "types_abs Us var"] u up by auto
  qed
  note e2 = env_invD[OF inv'']
  have e'': "vt_is_empty (tyenv env'')" by (rule wf_envD(1)[OF e2(2)])
  have ok1: "ok (update (F1, T1) t1 env') env''" using u1 by (simp add: return_def)
  have R: "reach env'' {(x0, B)} \<subseteq> {(x0, B), (w, B)}"
  proof -
    have "reach env'' {(x0, B)} \<subseteq> reach env' ({(x0, B)} \<union> vps t1)"
      by (rule Unify_Simpl_Complete.csig.reach_update[OF ok1])
    also have "\<dots> \<subseteq> reach env' ({(x0, B)} \<union> {(w, B)})" by (rule reach_subset) (use F1 in \<open>auto simp: g(4)\<close>)
    also have "\<dots> = {(x0, B), (w, B)}" unfolding reach_Un r0 by auto
    finally show ?thesis .
  qed
  have vm'': "snd v \<le> maxidx env''" using vm' mx'' by simp
  have babs'': "below (maxidx env'') (types_abs Zs var)" for Zs using babs mx'' by simp
  text \<open>The second update binds \<open>v\<close>, or \<open>x0\<close> or \<open>w\<close> to \<open>v\<close>.\<close>
  have step2: "\<exists>env1. vupdate (v, T) (types_abs Ts var) env'' = return env1 \<and> env_inv ar V1 env1 \<and>
      extends env'' env1 \<and> maxidx env1 = maxidx env'' \<and>
      (\<forall>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
        (\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}))"
    if vw: "v \<noteq> w"
  proof -
    have vn'': "vt_lookup (tenv env'') v = None" using te'' F1 vw vx0(1) vn' by auto
    have tyT: "has_type V1 [] (types_abs Ts var) T" using tyabs[of Ts] T_eq by simp
    have eqT: "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (types_abs Ts var))"
      using \<sigma>v \<sigma>x0 by (simp add: trv equiv_refl)
    have acT: "\<forall>U'. (v, U') \<notin> reach env'' (vps (types_abs Ts var))"
      unfolding vpsabs using R vx0(1) vw by auto
    consider (S1) "vt_lookup (tenv env'') x0 = None \<or> Ts \<noteq> []"
      | (S2) "vt_lookup (tenv env'') x0 \<noteq> None" "Ts = []"
      by blast
    then show ?thesis
    proof cases
      case S1
      have hs: "\<forall>y Y. types_abs Ts var = Var y Y \<longrightarrow> vt_lookup (tenv env'') y = None"
        using S1 by (cases Ts) (auto simp: g(4))
      from vupdate_complete[OF inv'' sol'' vn'' V1v tyT wsabs[OF gTs] gT babs'' vm'' acT eqT hs]
      obtain env1 where c: "vupdate (v, T) (types_abs Ts var) env'' = return env1" "env_inv ar V1 env1"
        "extends env'' env1" "maxidx env1 = maxidx env''"
        "\<forall>x U' u. vt_lookup (tenv env1) x = Some (U', u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
          (x = v \<and> u = types_abs Ts var) \<or> (\<exists>U. types_abs Ts var = Var x U \<and> u = Var v U)"
        by blast
      have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
        if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
        using c(5) that by (fastforce simp: g(4))
      with c(1-4) show ?thesis by blast
    next
      case S2
      have TB: "T = B" using S2(2) T_eq by simp
      have F1x: "F1 = x0" using S2(1) te'' x0n by (cases "F1 = x0") auto
      with F1 vx0(2) have UB: "Us = []" "U = B" "T1 = B" "t1 = Var w B" by auto
      have lx0: "vt_lookup (tenv env'') x0 = Some (B, Var w B)" using te'' F1x UB by simp
      have wn'': "vt_lookup (tenv env'') w = None" using te'' F1x vx0(2) wn' by simp
      have Rw: "reach env'' {(w, B)} = {(w, B)}"
        using reach_unbound[of env'' w B] wn'' by (simp add: lk_def)
      have tx: "types_abs Ts var = Var x0 B" using S2(2) by (simp add: g(4))
      show ?thesis
      proof (cases "indexname_less v x0")
        case True
        from Unify_Simpl_Complete.csig.lookup_typed[OF e'' e2(3) V1x0] obtain r where
          lr: "lookup env'' x0 B = return r" by blast
        then have "ok (lookup env'' x0 B) r" by (simp add: return_def)
        from ok_lookup[OF e'' this] lx0 have r: "r = Some (Var w B)" by auto
        have vu: "vupdate (v, T) (types_abs Ts var) env'' = vupdate (v, T) (Var w B) env''"
          using True vx0(1) lr r by (subst vupdate.simps) (simp add: tx)
        have "\<forall>U'. (v, U') \<notin> reach env'' (vps (Var w B))" using Rw vw by simp
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (Var w B))"
          using \<sigma>v \<sigma>w S2(2) UB by (simp add: equiv_refl)
        moreover have "has_type V1 [] (Var w B) T" using V1w UB TB by (simp add: has_type.Var)
        moreover have "wf_tm ar [] (Var w B)" using gB by (simp add: wf_tm_def)
        moreover have "below (maxidx env'') (Var w B)" using wm' mx'' by (simp add: below_def)
        ultimately obtain env1 where c: "vupdate (v, T) (Var w B) env'' = return env1" "env_inv ar V1 env1"
          "extends env'' env1" "maxidx env1 = maxidx env''"
          "\<forall>x U' u. vt_lookup (tenv env1) x = Some (U', u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
            (x = v \<and> u = Var w B) \<or> (\<exists>U. Var w B = Var x U \<and> u = Var v U)"
          using vupdate_complete[OF inv'' sol'' vn'' V1v _ _ gT _ vm'' _ _] wn'' by blast
        have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
          if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
          using c(5) that by fastforce
        with c(1-4) vu show ?thesis by auto
      next
        case False
        have vu: "vupdate (v, T) (types_abs Ts var) env'' = update (v, T) (Var x0 B) env''"
          using False vx0(1) by (subst vupdate.simps) (simp add: tx)
        have "(v, T) \<notin> reach env'' (vps (Var x0 B))" using R vx0(1) vw by auto
        moreover have "\<sigma> (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (Var x0 B))"
          using \<sigma>v \<sigma>x0 S2(2) by (simp add: equiv_refl)
        moreover have "has_type V1 [] (Var x0 B) T" using V1x0 TB by (simp add: has_type.Var)
        moreover have "wf_tm ar [] (Var x0 B)" using gB by (simp add: wf_tm_def)
        moreover have "below (maxidx env'') (Var x0 B)" using xm mx'' by (simp add: below_def)
        ultimately obtain env1 where c: "update (v, T) (Var x0 B) env'' = return env1" "env_inv ar V1 env1"
          "extends env'' env1" "maxidx env1 = maxidx env''"
          "tenv env1 = vt_update (v, (T, Var x0 B)) (tenv env'')"
          using update_complete[OF inv'' sol'' vn'' V1v _ _ gT _ vm''] by blast
        have "\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
          if "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env'') x = None" for x Y u
          using c(5) that by (cases x0) (auto split: if_splits)
        with c(1-4) vu show ?thesis by auto
      qed
    qed
  qed
  have sm: "smash_flexflex1 tu env = (if v = w \<and> T = U then returnW env''
      else liftM (vupdate (v, T) (types_abs Ts var) env''))"
    by (simp add: smash_flexflex1_def tu va vb liftM_return body_type_res[OF e] rT G type_abs_def
        binder_types_arg[OF e'] Ts_def[symmetric] Us_def[symmetric] up1)
  obtain env1 where r1: "okW (smash_flexflex1 tu env) env1" and inv1: "env_inv ar V1 env1"
    and ext1: "extends env'' env1" and mx1: "maxidx env1 = maxidx env''"
    and nb: "\<And>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<Longrightarrow> vt_lookup (tenv env'') x = None \<Longrightarrow>
      \<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0}"
    and vsat: "\<And>\<sigma>'. closed_on UNIV \<sigma>' \<Longrightarrow> sat \<sigma>' env1 \<Longrightarrow>
      \<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (types_abs Ts var))"
  proof (cases "v = w")
    case True
    then have TU: "T = U" using Vv Vw by simp
    then have "Ts = Us" by (simp add: Ts_def Us_def)
    moreover have "ok (vupdate (w, U) (types_abs Us var) env') env''" using up1 by (simp add: return_def)
    note vupdate_wf(3)[OF this e1(2) wsabs[OF gUs] gU]
    ultimately show ?thesis using that[of env''] sm True TU inv'' by (auto simp: extends_refl)
  next
    case False
    from step2[OF False] obtain env1 where c: "vupdate (v, T) (types_abs Ts var) env'' = return env1"
      "env_inv ar V1 env1" "extends env'' env1" "maxidx env1 = maxidx env''"
      "\<forall>x Y u. vt_lookup (tenv env1) x = Some (Y, u) \<longrightarrow> vt_lookup (tenv env'') x = None \<longrightarrow>
        (\<exists>y Y'. fhd u = Var y Y' \<and> y \<in> {v, w, x0})"
      by blast
    have "ok (vupdate (v, T) (types_abs Ts var) env'') env1" using c(1) by (simp add: return_def)
    note vupdate_wf(3)[OF this e2(2) wsabs[OF gTs] gT]
    with c sm False show ?thesis using that[of env1] by (auto simp: return_def)
  qed
  have ext1': "extends env env1" using extends_trans[OF extends_trans[OF g(5) ext''] ext1] .
  text \<open>The new bindings are flexible.\<close>
  have fh3: "fh env0 u" if "fhd u = Var y Y'" "y \<in> {v, w, x0}" for u y Y'
    using that vn0 wn0 x0n0 by (auto simp: fh_def)
  have "flexb env0 env1"
  proof (rule flexb_step[OF fb ext1'])
    fix x Y u assume x: "vt_lookup (tenv env1) x = Some (Y, u)" "vt_lookup (tenv env) x = None"
    show "fh env0 u"
    proof (cases "vt_lookup (tenv env'') x")
      case None
      from nb[OF x(1) None] fh3 show ?thesis by blast
    next
      case (Some b)
      with extendsD[OF ext1 Some] x(1) have "vt_lookup (tenv env'') x = Some (Y, u)" by simp
      with te'' x(2) g(6) have "x = F1" "u = t1" by (auto split: if_splits)
      with F1 show ?thesis using fh3[of u x0 B] fh3[of u w B] by (auto simp: g(4))
    qed
  qed
  text \<open>The pair is solved.\<close>
  moreover have "env1 \<Turnstile> fst tu \<approx> snd tu"
    unfolding env_equiv_def
  proof (intro allI impI)
    fix \<sigma>' assume cl: "closed_on UNIV \<sigma>'" and st: "sat \<sigma>' env1"
    have st'': "sat \<sigma>' env''" by (rule sat_extends[OF st ext1])
    have nl: "no_loose_bound (\<sigma>' (code (AVar x0))) 0" using closed_onD[OF cl] by simp
    have okw: "ok (vupdate (w, U) (types_abs Us var) env') env''" using up1 by (simp add: return_def)
    have sw: "\<sigma>' (code (AVar w)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types U)) (\<sigma>' (code (AVar x0)))"
      using vupdate_wf(3)[OF okw e1(2) wsabs[OF gUs] gU cl st''] by (simp add: trv Us_def)
    have sv: "\<sigma>' (code (AVar v)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (arg_types T)) (\<sigma>' (code (AVar x0)))"
      using vsat[OF cl st] by (simp add: trv Ts_def)
    have ca: "mk_subst \<sigma>' (tr (rlist_abs rb a')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length rb) (\<sigma>' (code (AVar x0)))"
      using equiv_Abs_m[OF flex_const[OF cl tya' nf ha sv nl]] by (simp add: tr_rlist_abs)
    have cb: "mk_subst \<sigma>' (tr (rlist_abs rb b')) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length rb) (\<sigma>' (code (AVar x0)))"
      using equiv_Abs_m[OF flex_const[OF cl tyb' nf hb sw nl]] by (simp add: tr_rlist_abs)
    have ea: "mk_subst \<sigma>' (tr (rlist_abs rb a)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (rlist_abs rb a'))"
      using env_equiv_extends[OF eqa ext1'] cl st by (simp add: env_equiv_def)
    have eb: "mk_subst \<sigma>' (tr (rlist_abs rb b)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (rlist_abs rb b'))"
      using env_equiv_extends[OF eqb ext1'] cl st by (simp add: env_equiv_def)
    show "mk_subst \<sigma>' (tr (fst tu)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr (snd tu))"
      using equiv_trans[OF equiv_trans[OF ea ca] equiv_sym[OF equiv_trans[OF eb cb]]] by (simp add: tu)
  qed
  ultimately show ?thesis using r1 inv1 g(2) mx1 mx'' mx' ext1'
    by (intro exI[of _ env1] exI[of _ V1]) simp
qed

subsection \<open>All pairs\<close>

lemma foldrW_smash:
  assumes "env_inv ar V env" "flexb env0 env" "extends env0 env" "fresh_env env0" "maxidx env0 \<le> maxidx env"
    "\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab"
  shows "\<exists>env' V'. okW (foldrW smash_flexflex1 tps env) env' \<and> env_inv ar V' env' \<and> extends env env' \<and>
    flexb env0 env' \<and> maxidx env \<le> maxidx env' \<and> agreeV (maxidx env) V V' \<and>
    (\<forall>ab\<in>set tps. env' \<Turnstile> fst ab \<approx> snd ab)"
  using assms(6)
proof (induction tps)
  case Nil
  then show ?case using assms(1,2) by (intro exI[of _ env] exI[of _ V]) (simp add: agreeV_def)
next
  case (Cons ab tps)
  from Cons obtain env1 V1 where f: "okW (foldrW smash_flexflex1 tps env) env1" and i1: "env_inv ar V1 env1"
    and x1: "extends env env1" and fb1: "flexb env0 env1" and m1: "maxidx env \<le> maxidx env1"
    and a1: "agreeV (maxidx env) V V1" and s1: "\<forall>ab\<in>set tps. env1 \<Turnstile> fst ab \<approx> snd ab"
    by auto
  have tp: "tpok ar V1 env0 (maxidx env1) ab" using Cons.prems tpok_mono[OF _ a1 m1] by simp
  from smash_flexflex1_ok[OF i1 fb1 extends_trans[OF assms(3) x1] assms(4) _ tp] assms(5) m1
  obtain env2 V2 where s: "okW (smash_flexflex1 ab env1) env2" "env_inv ar V2 env2"
    "agreeV (maxidx env1) V1 V2" "maxidx env1 \<le> maxidx env2" "extends env1 env2" "flexb env0 env2"
    "env2 \<Turnstile> fst ab \<approx> snd ab"
    by auto
  have "okW (foldrW smash_flexflex1 (ab # tps) env) env2" using f s(1) by auto
  moreover have "\<forall>ab\<in>set tps. env2 \<Turnstile> fst ab \<approx> snd ab" using s1 env_equiv_extends[OF _ s(5)] by blast
  ultimately show ?case using s(2-7) extends_trans[OF x1 s(5)] agreeV_trans[OF a1 s(3) m1] m1
    by (intro exI[of _ env2] exI[of _ V2]) auto
qed

text \<open>On the unifiers of the search, \<^const>\<open>smash_flexflex\<close> terminates normally and solves the pairs.\<close>

theorem smash_flexflex_rres:
  assumes "rres ar env tps"
  obtains env' where "okW (smash_flexflex (env, tps)) env'" "extends env env'"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env' \<Longrightarrow> tsolved \<sigma> tps"
proof -
  from assms obtain V env0 where "env_inv ar V env" "flexb env0 env" "extends env0 env" "fresh_env env0"
    "maxidx env0 \<le> maxidx env" "\<forall>ab\<in>set tps. tpok ar V env0 (maxidx env) ab"
    unfolding rres_def by blast
  from foldrW_smash[OF this] obtain env' where f: "okW (foldrW smash_flexflex1 tps env) env'"
    "extends env env'" "\<forall>ab\<in>set tps. env' \<Turnstile> fst ab \<approx> snd ab"
    by blast
  have "tsolved \<sigma> tps" if "closed_on UNIV \<sigma>" "sat \<sigma> env'" for \<sigma>
    using f(3) that by (fastforce simp: tsolved_def env_equiv_def)
  with f(1,2) show ?thesis using that by (simp add: smash_flexflex_def)
qed

text \<open>
  Hence every unifier that the enumeration of \<^const>\<open>unifiers\<close> yields, which is finite, can be
  smashed to a unifier without remaining flex-flex pairs.
\<close>

theorem unifiers_smash:
  assumes inv: "tyinv ar V env (dps_of tus)"
  obtains s xs where "unifiers alg env tus = Some (Ok s)" "evals cfg s xs"
    "\<forall>x\<in>set xs. \<exists>env' tps env''. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and>
      unifier env (dps_of tus) env'' []"
proof -
  from unifiers_fin[OF inv, of alg cfg] obtain s where u: "unifiers alg env tus = Some (Ok s)"
    and f: "fin cfg s (\<lambda>x. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps)"
    by blast
  from f obtain xs where xs: "evals cfg s xs" "\<forall>x\<in>set xs. \<exists>env' tps. x = El_R env' tps \<and> rres ar env' tps"
    by (auto simp: fin_def)
  have "\<exists>env' tps env''. x = El_R env' tps \<and> okW (smash_flexflex (env', tps)) env'' \<and>
      unifier env (dps_of tus) env'' []" if x: "x \<in> set xs" for x
  proof -
    from xs(2) x obtain env' tps where xe: "x = El_R env' tps" and r: "rres ar env' tps" by blast
    from unifiers_sound[OF inv u xs(1) x] xe have un: "unifier env (dps_of tus) env' tps" by simp
    from smash_flexflex_rres[OF r] obtain env'' where sm: "okW (smash_flexflex (env', tps)) env''"
      "extends env' env''" "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env'' \<Longrightarrow> tsolved \<sigma> tps"
      by blast
    have "unifier env (dps_of tus) env'' []"
      using un sm(2,3) unfolding unifier_def tsolved_def by (blast intro: extends_trans sat_extends)
    with xe sm(1) show ?thesis by blast
  qed
  with u xs(1) that show ?thesis by blast
qed

end

end
