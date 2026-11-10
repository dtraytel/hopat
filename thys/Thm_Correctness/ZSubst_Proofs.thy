section \<open>Validity of the tight proofs of instantiation\<close>

theory ZSubst_Proofs
  imports ZRule_Proofs
begin

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

context prf_sig
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

context prf_sig
begin

theorem zinstantiate_proof_valid:
  fixes instT :: instT and insts :: inst
  defines "\<rho>0 \<equiv> tab_inst (map (\<lambda>(v, T). (v, (T, -1))) instT)"
    and "\<sigma>0 \<equiv> tab_subst (map (\<lambda>(v, t). (v, (t, -1))) insts)"
  assumes p: "zvalid ax H tps pf \<phi>" and \<rho>0: "cinst \<rho>0" and \<sigma>0: "wt_subst \<sigma>0"
    and H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
    and kT: "\<forall>((v, S), T)\<in>set instT. snd v \<noteq> -1 \<and> tnoneg T"
    and kt: "\<forall>((v, T), t)\<in>set insts. snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    and c: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. zcanon T) (\<lambda>_. True) pf" and zc: "zconsts_ok pf"
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
  have v: "prf_valid ax H (map (\<lambda>(t, u). (vsubst \<sigma>0 (inst \<rho>0 t), vsubst \<sigma>0 (inst \<rho>0 u))) tps)
      (instantiate_proof instT insts w) (vsubst \<sigma>0 (inst \<rho>0 \<phi>))"
    by (rule instantiate_proof_valid[OF w(2) \<rho>0[unfolded \<rho>0_def] \<sigma>0[unfolded \<sigma>0_def] H, folded \<rho>0_def \<sigma>0_def])
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
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1) zc])
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

subsection \<open>Tight generalization\<close>

lemma typ_of_zsubst_gen:
  assumes "tfrees \<noteq> [] \<Longrightarrow> gi \<noteq> -1"
  shows "typ_of (zsubst_type (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None) Z) =
    generalizeT tfrees gi (typ_of Z)"
proof (induction Z)
  case (ZTVar v S)
  obtain a i where v: "v = (a, i)" by (cases v)
  show ?case using assms by (cases "tfrees = []") (auto simp: v)
qed (simp_all add: propT_def)

context prf_sig
begin

lemma erase_zdec_zgen:
  assumes ty: "\<And>Z. typ_of (ty Z) = generalizeT tfrees gi (typ_of Z)" and gi: "frees \<noteq> [] \<Longrightarrow> 0 \<le> gi"
  shows "erase (zdec (zsubst_term ty (\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T)
      else None) t)) = erase (generalize_term tfrees frees gi (zdec t))"
proof (induction t)
  case (ZVar xi T)
  obtain x i where xi: "xi = (x, i)" by (cases xi)
  have "snd (clean_index (x, gi)) \<noteq> -1" if "x \<in> set frees" using that gi clean_index_ge[of gi x] by force
  then show ?case by (auto simp: xi ty)
qed (auto simp: ty Proof_Judgment.of_class_def)

theorem zgeneralize_proof_valid:
  assumes ok: "okT (generalize tfrees frees gi hs th0) th"
    and p: "zvalid ax (set hs) (th_tpairs th0) pf (th_prop th0)"
    and wt: "wt_thm m hs (th_tpairs th0) (th_prop th0)" and mx: "-1 \<le> th_maxidx th0"
    and np: "prf_nolb 0 (zprf_tr pf)" and zc: "zconsts_ok pf" and eqc: "zeq_close_ok"
    and z: "zgeneralize_proof tfrees frees gi pf = return q"
  shows "zvalid ax (set hs) (th_tpairs th) q (th_prop th)"
proof -
  let ?A = "tf_set tfrees" and ?g = "\<lambda>a (S :: psort). (a, gi)"
  let ?\<phi> = "gen_atom ?A ?g"
  let ?tps = "th_tpairs th0" and ?P = "th_prop th0"
  let ?gen = "generalize_term tfrees frees gi" and ?genT = "generalizeT tfrees gi"
  let ?ty = "zsubst_type (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None)"
  let ?var = "\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T) else None"
  have gen: "?gen t = generalize_term [] frees gi (tmap ?\<phi> t)" for t by (rule generalize_term_split)
  have genT: "?genT = map_atyps ?\<phi>" by (rule ext) (rule generalizeT_gen_atom)
  have genF: "?gen = generalize_term [] frees gi \<circ> tmap ?\<phi>" by (rule ext) (simp add: gen)
  have ni: "\<not> gi \<le> th_maxidx th0" and nb: "\<And>h. h \<in> set hs \<Longrightarrow> \<not> bad_term tfrees frees h"
    and th: "th_tpairs th = map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps" "th_prop th = ?gen ?P"
    if "\<not> (tfrees = [] \<and> frees = [])"
    using ok that by (auto simp: generalize_def returnW_def raiseW_def Let_def mk_rep_def split: if_splits)
  have gi0: "0 \<le> gi" if "\<not> (tfrees = [] \<and> frees = [])" using ni[OF that] mx by (simp add: integer_less_eq_iff)
  let ?gtps = "map (\<lambda>(t, u). (?gen t, ?gen u)) ?tps"
  have T: "th_tpairs th = ?gtps" and Pth: "th_prop th = ?gen ?P"
  proof -
    have "th_tpairs th = ?gtps \<and> th_prop th = ?gen ?P"
    proof (cases "tfrees = [] \<and> frees = []")
      case True
      then have "?gen t = t" for t using generalize_term_id[of frees t gi] by (simp add: gen)
      with ok True show ?thesis by (simp add: generalize_def returnW_def case_prod_beta')
    next
      case False
      with th[OF False] show ?thesis by simp
    qed
    then show "th_tpairs th = ?gtps" "th_prop th = ?gen ?P" by simp_all
  qed
  have hs: "\<not> tf_in ?A h \<and> fnames h \<inter> set frees = {}" if "h \<in> set hs" for h
  proof (cases "tfrees = [] \<and> frees = []")
    case True
    then show ?thesis by (simp add: tf_in_def)
  next
    case False
    from bad_term_tf_in[OF nb[OF False that]] bad_term_frees show ?thesis
      by (fastforce simp: fnames_pfrees)
  qed
  have hw: "wtp h \<and> vars h = {} \<and> ttvars h = {}" if "h \<in> set hs" for h using wt that by (simp add: wt_thm_def)
  have tw: "closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)" "closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> u : T)" if "(t, u) \<in> set ?tps" for t u
    using wt that by (fastforce simp: wt_thm_def)+
  have cl: "prf_valid ax (set hs) ?gtps (map_proof_terms ?gen ?genT w) (?gen ?P)"
    if w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax (set hs) ?tps w ?P" for w
  proof -
    have aw: "fnames (close A) = {} \<and> \<not> tf_in ?A (close A)" if "A \<in> prf_atoms w" for A
      using that arg_cong[OF w(1), of prf_atoms] zeq_close_okD[OF eqc] by (fastforce simp: tf_in_def)
    have v1: "prf_valid ax (set hs) (map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) ?tps) (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w) (tmap ?\<phi> ?P)"
    proof (rule prf_valid_gen_tfrees[OF w(2)])
      show "wtp ?P" using wt by (simp add: wt_thm_def)
      show "closed h \<and> vars h = {} \<and> ttvars h = {} \<and> \<not> tf_in ?A h" if "h \<in> set hs" for h
        using hw[OF that] hs[OF that] wtpD(1) by blast
      show "prf_nolb 0 w" using arg_cong[OF w(1), of "prf_nolb 0"] np by simp
    qed (use aw in auto)
    have "prf_valid ax (set hs) (map (\<lambda>(t, u). (generalize_term [] frees gi t, generalize_term [] frees gi u))
        (map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) ?tps)) (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T)
        (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w)) (generalize_term [] frees gi (tmap ?\<phi> ?P))"
      by (rule prf_valid_subst_frees[OF v1]) (use hs aw in auto)
    moreover have "map (\<lambda>(t, u). (generalize_term [] frees gi t, generalize_term [] frees gi u))
        (map (\<lambda>(t, u). (tmap ?\<phi> t, tmap ?\<phi> u)) ?tps) = ?gtps"
      by (simp add: gen split_beta comp_def)
    ultimately have "prf_valid ax (set hs) ?gtps (map_proof_terms (generalize_term [] frees gi) (\<lambda>T. T)
        (map_proof_terms (tmap ?\<phi>) (map_atyps ?\<phi>) w)) (generalize_term [] frees gi (tmap ?\<phi> ?P))"
      by (simp only:)
    then show ?thesis by (simp add: map_proof_terms_comp genF genT comp_def)
  qed
  obtain w where w: "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax (set hs) ?tps w ?P" using p by (rule zvalidE)
  let ?w = "prf_reclass (zprf_tr q) (pclass_map ?genT w)"
  have m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty ?var t)) pf = return q"
    using z by (simp add: zgeneralize_proof_def Let_def)
  have gi': "gi \<noteq> -1" if "tfrees \<noteq> []" using gi0 that by fastforce
  have gi'': "0 \<le> gi" if "frees \<noteq> []" using gi0 that by fastforce
  have tyof: "typ_of (?ty Z) = ?genT (typ_of Z)" for Z by (rule typ_of_zsubst_gen[OF gi'])
  have "prf_valid ax (set hs) ?gtps ?w (?gen ?P)"
  proof (rule prf_valid_aeq[OF cl[OF w]])
    fix \<rho> \<sigma>
    have "prf_aeq (map_proof_terms (\<lambda>t. ap \<rho> \<sigma> (?gen t)) (\<lambda>T. tsubst \<rho> (?genT T)) w) (prf_ap \<rho> \<sigma> ?w)"
    proof (rule map_zproof_aeq_gen[OF m _ _ w(1) zc])
      show "zprf_all (\<lambda>t. \<forall>t'. return (zsubst_term ?ty ?var t) = return t' \<longrightarrow>
          ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (?gen (zdec t)))
        (\<lambda>Z. tsubst \<rho> (typ_of (?ty Z)) = tsubst \<rho> (?genT (typ_of Z))) pf"
      proof (rule zprf_all_true)
        fix t
        have "erase (ap \<rho> \<sigma> (zdec (zsubst_term ?ty ?var t))) = erase (ap \<rho> \<sigma> (?gen (zdec t)))"
          by (rule erase_ap_cong[OF erase_zdec_zgen[OF tyof gi'']])
        then show "\<forall>t'. return (zsubst_term ?ty ?var t) = return t' \<longrightarrow> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (?gen (zdec t))"
          by simp
      qed (simp add: tyof)
    qed simp
    then show "prf_aeq (prf_ap \<rho> \<sigma> (map_proof_terms ?gen ?genT w)) (prf_ap \<rho> \<sigma> ?w)"
      by (simp add: prf_ap_def map_proof_terms_comp comp_def)
  qed
  then show ?thesis unfolding T Pth by (rule zvalidI[rotated]) simp
qed

end

end
