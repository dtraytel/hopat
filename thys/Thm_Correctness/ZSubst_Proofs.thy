section \<open>Validity of the tight proofs of instantiation\<close>

theory ZSubst_Proofs
  imports ZRule_Proofs
begin

text \<open>A tight type is canonical if it is the encoding of its decoding:\<close>

definition zcanon :: "ztyp \<Rightarrow> bool" where
  "zcanon T \<longleftrightarrow> ztyp_of (typ_of T) = T"

lemma zcanon_ztyp_of: "tnoneg T \<Longrightarrow> zcanon (ztyp_of T)"
  by (simp add: zcanon_def typ_of_ztyp_of_tnoneg)

lemma map_eq_selfD: "map f xs = xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = x"
  by (induction xs) auto

lemma zcanon_zsubst_type:
  assumes "zcanon T" and tv: "\<And>v U. tv v = Some U \<Longrightarrow> zcanon U"
  shows "zcanon (zsubst_type tv T)"
  using assms(1)
proof (induction T)
  case (ZTVar v S)
  then show ?case using tv[of "(v, S)"] by (cases "tv (v, S)") (auto simp: zcanon_def)
next
  case (ZFun T U)
  then show ?case by (auto simp: zcanon_def)
next
  case (ZType1 c T)
  then show ?case by (auto simp: zcanon_def)
next
  case (ZType c Ts)
  have IH: "ztyp_of (typ_of (zsubst_type tv T)) = zsubst_type tv T" if "T \<in> set Ts" "ztyp_of (typ_of T) = T" for T
    using ZType.IH[OF that(1)] that(2) by (simp add: zcanon_def)
  from ZType.prems show ?case
  proof (cases Ts rule: remdups_adj.cases)
    case (3 T U Ws)
    show ?thesis
    proof (cases Ws)
      case Nil
      with 3 ZType.prems IH show ?thesis by (auto simp: zcanon_def split: if_splits)
    next
      case (Cons W Ws')
      with 3 ZType.prems IH show ?thesis by (auto simp: zcanon_def intro!: map_idI dest: map_eq_selfD)
    qed
  qed (auto simp: zcanon_def split: if_splits)
qed (simp_all add: zcanon_def)

lemma lookup_zvar_map_of: "lookup_zvar xs v = map_of xs v"
  by (induction xs) (auto simp: prod_eq_iff)

lemma lookup_var_subst_map_of: "Pure_Subst_Rules.lookup_var xs v = map_of xs v"
  by (induction xs) (auto simp: prod_eq_iff)

text \<open>The lookup of a tight variable of canonical type is the lookup of its decoding:\<close>

lemma lookup_zinst:
  assumes zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ta t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    and kt: "\<forall>((v, T), t)\<in>set insts. tnoneg T" and c: "zcanon U"
  shows "(lookup_zvar zinst (x, U) = None \<longleftrightarrow> map_of insts (x, typ_of U) = None) \<and>
    (\<forall>z. lookup_zvar zinst (x, U) = Some z \<longrightarrow> (\<exists>t. map_of insts (x, typ_of U) = Some t \<and> zterm_of ta t = return z))"
  using zi kt
proof (induction rule: list_all2_induct)
  case (Cons a insts e zinst)
  obtain v T t where a: "a = ((v, T), t)" by (cases a) auto
  from Cons.hyps(1) a obtain t' where t': "zterm_of ta t = return t'" and e: "e = ((v, ztyp_of T), t')" by auto
  have tT: "tnoneg T" using Cons.prems a by simp
  have "(v, ztyp_of T) = (x, U) \<longleftrightarrow> (v, T) = (x, typ_of U)"
    using c tT by (auto simp: zcanon_def typ_of_ztyp_of_tnoneg)
  with Cons show ?case by (auto simp: a e lookup_zvar_map_of t')
qed simp

lemma typ_of_zsubst_instT:
  assumes "\<forall>((v, S), T)\<in>set instT. snd v \<noteq> -1 \<and> tnoneg T"
  shows "typ_of (zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT)) Z) =
    tsubst (tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)) (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  have m1: "map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT) = map_option ztyp_of \<circ> map_of instT"
    and m2: "map_of (map (\<lambda>(v, T). (v, (T, -1 :: integer))) instT) = map_option (\<lambda>T. (T, -1)) \<circ> map_of instT"
    by (simp_all add: map_of_map[symmetric] case_prod_beta')
  show ?case
  proof (cases "map_of instT (v, S)")
    case None
    then show ?thesis by (simp add: m1 m2 tab_inst_def)
  next
    case (Some T)
    from map_of_SomeD[OF Some] assms have "snd v \<noteq> -1" "tnoneg T" by auto
    with Some show ?thesis by (simp add: m1 m2 tab_inst_def typ_of_ztyp_of_tnoneg)
  qed
qed (simp_all add: propT_def)

context prf_model
begin

lemma erase_zdec_zinst:
  assumes ty: "\<And>Z. typ_of (ty Z) = tsubst \<rho>0 (typ_of Z)"
    and zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ta t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    and kt: "\<forall>((v, T), t)\<in>set insts. snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    and c: "\<forall>(x, T)\<in>zvars t. zcanon (ty T)"
  shows "erase (zdec (zsubst_term ty (lookup_zvar zinst) t)) =
    erase (vsubst (tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) insts)) (inst \<rho>0 (zdec t)))"
  using c
proof (induction t)
  case (ZVar x T)
  have kt': "\<forall>((v, T), t)\<in>set insts. tnoneg T" using kt by auto
  note lk = lookup_zinst[OF zi kt' ZVar.prems[simplified], of x]
  have m: "map_of (map (\<lambda>(v, t). (v, (remove_types t, -1 :: integer))) insts) =
      map_option (\<lambda>t. (remove_types t, -1)) \<circ> map_of insts"
    by (simp add: map_of_map[symmetric] case_prod_beta')
  show ?case
  proof (cases "snd x = -1")
    case True
    have "lookup_zvar zinst (x, ty T) = None"
    proof (rule ccontr)
      assume "lookup_zvar zinst (x, ty T) \<noteq> None"
      then have "map_of insts (x, typ_of (ty T)) \<noteq> None" using lk by (cases x) auto
      then obtain t where "((x, typ_of (ty T)), t) \<in> set insts" by (auto dest: map_of_SomeD)
      with kt True show False by auto
    qed
    with True show ?thesis by (cases x) (simp add: ty)
  next
    case False
    show ?thesis
    proof (cases "lookup_zvar zinst (x, ty T)")
      case None
      with lk have "map_of insts (x, typ_of (ty T)) = None" by (cases x) auto
      with None False show ?thesis by (simp add: ty tab_subst_def lookup_var_subst_map_of m)
    next
      case (Some z)
      with lk obtain t where t: "map_of insts (x, typ_of (ty T)) = Some t" and z: "zterm_of ta t = return z"
        by (cases x) auto
      have "noneg t" using map_of_SomeD[OF t] kt by auto
      then have "erase (zdec z) = erase t" using zdec_zterm_of[OF z] by (metis erase_remove_types)
      with Some t False show ?thesis by (simp add: ty tab_subst_def lookup_var_subst_map_of m)
    qed
  qed
next
  case (ZAbs a T t)
  then show ?case by simp
next
  case (ZApp t u)
  then show ?case by simp
next
  case (ZOfclass T c)
  then show ?case by (simp add: Proof_Judgment.of_class_def)
qed simp_all

end

context prf_model
begin

theorem zinstantiate_proof_valid:
  fixes instT :: instT and insts :: inst
  defines "\<rho>0 \<equiv> tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)"
    and "\<sigma>0 \<equiv> tab_subst (map (\<lambda>(v, t). (v, (t, -1))) insts)"
  assumes p: "zvalid ax H tps pf \<phi>" and \<rho>0: "cinst \<rho>0" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow>
      (x, U) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> prf_vars (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps)
        (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) (inst \<rho>0 \<phi>) \<Longrightarrow> cert_typ alg ar T"
    and kT: "\<forall>((v, S), T)\<in>set instT. snd v \<noteq> -1 \<and> tnoneg T"
    and kt: "\<forall>((v, T), t)\<in>set insts. snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    and c: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. zcanon T) (\<lambda>_. True) pf"
    and z: "zinstantiate_proof ztargs instT insts pf = return q"
  shows "zvalid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps) q (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
proof -
  let ?ty = "zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) instT))"
  let ?\<sigma>r = "tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) insts)"
  from z obtain zinst where zi0: "mapM (\<lambda>((v, T), t). do {t' \<leftarrow> zterm_of ztargs t; return ((v, ztyp_of T), t')})
      insts = return zinst"
    and m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty (lookup_zvar zinst) t)) pf = return q"
    by (auto simp: zinstantiate_proof_def bindZ_eq_returnZ Let_def)
  have zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ztargs t = return t' \<and> e = ((v, ztyp_of T), t')) insts zinst"
    using zi0[unfolded mapZ_eq_returnZ] by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
  obtain w where w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax H tps w \<phi>" using p by (rule zvalidE)
  have tw: "prf_terms w = prf_terms (zprf_tr pf)" using arg_cong[OF w(1), of prf_terms] by simp
  have pv: "prf_vars X (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) w) Y =
      prf_vars X (map_proof_terms (inst \<rho>0) (tsubst \<rho>0) (zprf_tr pf)) Y" for X Y
    by (simp add: prf_vars_def prf_terms_map_proof_terms tw)
  have v: "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps)
      (instantiate_proof instT insts w) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
    by (rule instantiate_proof_valid[OF w(2) \<rho>0[unfolded \<rho>0_def] \<sigma>0[unfolded \<sigma>0_def], folded \<rho>0_def \<sigma>0_def])
      (use uniq cert in \<open>simp_all only: pv\<close>)
  have ip: "instantiate_proof instT insts w = map_proof_terms (\<lambda>t. vsubst ?\<sigma>r (inst \<rho>0 t)) (tsubst \<rho>0) w"
    by (simp add: instantiate_proof_def inst_m_fst instT_m_fst \<rho>0_def Let_def)
  have tyZ: "typ_of (?ty Z) = tsubst \<rho>0 (typ_of Z)" for Z
    unfolding \<rho>0_def by (rule typ_of_zsubst_instT[OF kT])
  have cv: "zcanon (?ty T)" if "zcanon T" for T
    by (rule zcanon_zsubst_type[OF that]) (use kT in \<open>fastforce simp: map_of_map[symmetric] case_prod_beta'
      intro!: zcanon_ztyp_of dest!: map_of_SomeD\<close>)
  let ?w = "prf_reclass (zprf_tr q) (pclass_map (tsubst \<rho>0) w)"
  have "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps) ?w (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
  proof (rule prf_valid_aeq[OF v])
    fix \<rho> \<sigma>
    have "prf_aeq (map_proof_terms (\<lambda>t. ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 t))) (\<lambda>T. tsubst \<rho> (tsubst \<rho>0 T)) w)
        (prf_ap \<rho> \<sigma> ?w)"
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1)])
      show "zprf_all (\<lambda>t. \<forall>t'. return (zsubst_term ?ty (lookup_zvar zinst) t) = return t' \<longrightarrow>
          ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 (zdec t))))
        (\<lambda>Z. tsubst \<rho> (typ_of (?ty Z)) = tsubst \<rho> (tsubst \<rho>0 (typ_of Z))) pf"
      proof (rule zprf_all_mono[OF c])
        fix t assume ct: "\<forall>(x, T)\<in>zvars t. zcanon T"
        have "erase (zdec (zsubst_term ?ty (lookup_zvar zinst) t)) = erase (vsubst ?\<sigma>r (inst \<rho>0 (zdec t)))"
          by (rule erase_zdec_zinst[OF tyZ zi kt]) (use ct cv in auto)
        from erase_ap_cong[OF this, of \<rho> \<sigma>]
        show "\<forall>t'. return (zsubst_term ?ty (lookup_zvar zinst) t) = return t' \<longrightarrow>
            ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (vsubst ?\<sigma>r (inst \<rho>0 (zdec t)))"
          by simp
      qed (simp add: tyZ)
    qed simp
    then show "prf_aeq (prf_ap \<rho> \<sigma> (instantiate_proof instT insts w)) (prf_ap \<rho> \<sigma> ?w)"
      by (simp add: ip prf_ap_def map_proof_terms_comp comp_def)
  qed
  then show ?thesis by (rule zvalidI[rotated]) simp
qed

end

end
