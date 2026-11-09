section \<open>Validity of the tight proofs of the equality rules\<close>

theory ZEq_Proofs
  imports ZSubst_Proofs
begin

text \<open>
  The tight proofs of the equality rules apply the proof constants of the equality axioms
  (\<^const>\<open>zaxiom_proof\<close>), which translate to the classic axioms applied to their instances.
\<close>

subsection \<open>Proof constants of the equality axioms\<close>

lemma Pure_prefix_cancel: "STR ''Pure.'' + a = STR ''Pure.'' + b \<longleftrightarrow> a = b"
proof
  assume "STR ''Pure.'' + a = STR ''Pure.'' + b"
  then have "String.explode (STR ''Pure.'' + a) = String.explode (STR ''Pure.'' + b)" by simp
  then show "a = b" by (simp add: plus_literal.rep_eq literal.explode_inject)
qed simp

lemma eq_names_zeq_vars: "eq_names = fst ` set zeq_vars"
  by (simp add: eq_names_def zeq_vars_def insert_commute)

lemma find_zeq_vars:
  assumes "a \<in> fst ` set zeq_vars"
  shows "find (\<lambda>(b, xs). STR ''Pure.'' + a = STR ''Pure.'' + b) zeq_vars = Some (a, the (map_of zeq_vars a))"
  using assms unfolding Pure_prefix_cancel by (auto simp: zeq_vars_def)

lemma those_map_Some: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = Some (g x)) \<Longrightarrow> those (map f xs) = Some (map g xs)"
  by (induction xs) auto

lemma zv_lookup_fold_update:
  "zv_lookup (fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) vs t) k =
    (if k \<in> set vs then Some (ZVar (fst k) (snd k)) else zv_lookup t k)"
  by (induction vs arbitrary: t) (auto simp: zv_lookup_zv_update)

lemma zequality_axm_tab:
  assumes "a \<in> fst ` set zeq_vars"
  obtains A instT0 tab0 where "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), A), (instT0, tab0))"
    "ztab_names_ok tab0" "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>T. zv_lookup tab0 ((x, -1), T) = Some (ZVar (x, -1) T)"
proof -
  let ?vs = "snd (snd (zequality_axiom a))"
  let ?tab = "fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) ?vs zv_empty"
  have e: "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), fst (zequality_axiom a)),
      (fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (fst (snd (zequality_axiom a))) zt_empty, ?tab))"
    by (simp add: zequality_axm_def split: prod.splits)
  have l: "zv_lookup ?tab k = (if k \<in> set ?vs then Some (ZVar (fst k) (snd k)) else None)" for k
    by (simp add: zv_lookup_fold_update)
  from assms have "a \<in> {STR ''reflexive'', STR ''symmetric'', STR ''transitive'', STR ''equal_intr'',
      STR ''equal_elim'', STR ''abstract_rule'', STR ''combination''}"
    by (simp add: zeq_vars_def)
  then have d: "distinct (map fst ?vs)"
    and v: "\<forall>x\<in>set (the (map_of zeq_vars a)). \<exists>T. ((x, -1), T) \<in> set ?vs"
    by (auto simp: zeq_vars_def zequality_axiom_def Let_def)
  have nok: "ztab_names_ok ?tab"
    unfolding ztab_names_ok_def
  proof (intro allI impI)
    fix k1 k2 assume "zv_lookup ?tab k1 \<noteq> None" "zv_lookup ?tab k2 \<noteq> None" "fst k1 = fst k2"
    then have "k1 \<in> set ?vs" "k2 \<in> set ?vs" "fst k1 = fst k2" by (simp_all add: l split: if_splits)
    with d show "k1 = k2" by (metis distinct_map inj_onD)
  qed
  have lk: "\<exists>T. zv_lookup ?tab ((x, -1), T) = Some (ZVar (x, -1) T)"
    if "x \<in> set (the (map_of zeq_vars a))" for x
    using v that by (force simp: l)
  from that[OF e nok lk] show thesis .
qed

context prf_sig
begin

lemma zaxiom_proof_tr:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> map_of ts x \<noteq> None"
  shows "zconsts_ok p"
    "zprf_tr p = foldl (\<lambda>p t. PAppt p (Some t)) (equality_axm a)
      (map (\<lambda>x. zdec (the (map_of ts x))) (the (map_of zeq_vars a)))"
proof -
  obtain A instT0 tab0 where e: "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), A), (instT0, tab0))"
    and ok: "ztab_names_ok tab0"
    and lk: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>T. zv_lookup tab0 ((x, -1), T) = Some (ZVar (x, -1) T)"
    using zequality_axm_tab[OF a] by blast
  let ?term = "\<lambda>t. return (case t of ZVar (x, _) _ \<Rightarrow> (case map_of ts x of Some u \<Rightarrow> u | None \<Rightarrow> t) | _ \<Rightarrow> t)"
  from z obtain instT' tab' where mi: "map_insts (zsubst_tvar_names (map_of Ts)) ?term (instT0, tab0) = return (instT', tab')"
    and p: "p = ZConstp ((ZAxiom (STR ''Pure.'' + a), A), (instT', tab'))"
    by (auto simp: zaxiom_proof_def make_const_proof_def e bindZ_eq_returnZ)
  show "zconsts_ok p" using map_insts_names(1)[OF mi ok] by (simp add: p)
  have look: "map_option zdec (zv_lookup_name tab' (x, -1)) = Some (zdec (the (map_of ts x)))"
    if "x \<in> set (the (map_of zeq_vars a))" for x
  proof -
    from lk[OF that] obtain T where T: "zv_lookup tab0 ((x, -1), T) = Some (ZVar (x, -1) T)" by blast
    have "zv_lookup_name tab' (x, -1) = Some (the (map_of ts x))"
      using map_insts_names(3)[OF mi ok zv_lookup_name_Some[OF ok T]] xs[OF that] by (auto split: option.splits)
    then show ?thesis by simp
  qed
  then have "those (map (\<lambda>x. map_option zdec (zv_lookup_name tab' (x, -1))) (the (map_of zeq_vars a))) =
      Some (map (\<lambda>x. zdec (the (map_of ts x))) (the (map_of zeq_vars a)))"
    by (rule those_map_Some)
  then show "zprf_tr p = foldl (\<lambda>p t. PAppt p (Some t)) (equality_axm a)
      (map (\<lambda>x. zdec (the (map_of ts x))) (the (map_of zeq_vars a)))"
    by (simp add: p zconst_tr_def zeq_tr_def find_zeq_vars[OF a])
qed

end

context prf_eq
begin

lemma zeq_close_ok: "zeq_close_ok"
  unfolding zeq_close_ok_def
proof
  fix a assume "a \<in> fst ` set zeq_vars"
  then have a: "a \<in> eq_names" by (simp add: eq_names_zeq_vars)
  then show "fnames (close (equality_axiom a)) = {} \<and> (\<forall>b S. TFree b S \<notin> tatoms (close (equality_axiom a)))"
    by (auto simp: eq_close eq_names_def eq_closure_def eq_all_def ax_eq_def ax_aT_def ax_bT_def
        Let_def all_const_def mk_implies_def implies_def imp_type_def propT_def)
qed


lemma zdec_zterm_of_noneg:
  assumes "zterm_of ztargs t = return z" "e \<turnstile> t : T" "noneg t"
  shows "zdec z = t"
proof -
  have "\<exists>z. zterm_of ztargs t = return z \<and> zdec z = t"
    by (rule zterm_of_zdec[OF assms(2)]) (use assms(3) in \<open>auto simp: noneg_def tnoneg_def\<close>)
  with assms(1) show ?thesis by auto
qed

lemma pcerase_PAppt_Some_chain:
  "pcerase (foldl (\<lambda>p t. PAppt p (Some t)) p ts) = foldl (\<lambda>p t. PAppt p (Some t)) (pcerase p) ts"
  by (induction ts arbitrary: p) simp_all

subsection \<open>Reflexivity and the conversions\<close>

lemma zreflexive_conv_proof_valid:
  assumes z: "zreflexive_proof ztargs T t = return p" and c: "closed t" "closed t'"
    and ty: "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> t' : T" and cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" and nt: "noneg t"
  shows "zvalid ax H [] p (eq_const T $ t $ t')" "zconsts_ok p"
proof -
  from z obtain x where x: "zterm_of ztargs t = return x"
    and ax: "zaxiom_proof STR ''reflexive'' [(tvar_a, ztyp_of T)] [(STR ''x'', x)] = return p"
    by (auto simp: zreflexive_proof_def bindZ_eq_returnZ)
  have "\<exists>z. zterm_of ztargs t = return z \<and> zdec z = t"
    by (rule zterm_of_zdec[OF ty(1)[of "\<lambda>_. propT"]]) (use nt in \<open>auto simp: noneg_def tnoneg_def\<close>)
  with x have dx: "zdec x = t" by auto
  have a: "STR ''reflexive'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
  note tr = zaxiom_proof_tr[OF ax a]
  show "zconsts_ok p" by (rule tr(1)) (simp add: zeq_vars_def)
  have zp: "zprf_tr p = PAppt (equality_axm STR ''reflexive'') (Some t)"
    using tr(2) by (simp add: zeq_vars_def dx)
  have v: "prf_valid ax H [] (PAppt (equality_axm STR ''reflexive'') (Some t)) (eq_const T $ t $ t')"
    by (rule reflexive_proof_conv_valid_ann[OF c ty cv]) simp
  show "zvalid ax H [] p (eq_const T $ t $ t')" by (rule zvalidI[OF _ v]) (simp add: zp)
qed

theorem zreflexive_rule_proof_valid:
  assumes ok: "okT (reflexive (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
    and z: "zreflexive_proof ztargs T t = return p" and nt: "noneg t"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain P where P: "ok (mk_equals (t, t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: reflexive_def)
  note r = zreflexive_conv_proof_valid[OF z c c ty ty conv_refl nt]
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    using r(1) mk_equals_ok[OF P c ty] by (simp add: th mk_rep_def)
  show "zconsts_ok p" by (rule r(2))
qed

theorem zbeta_conversion_proof_valid:
  assumes ok: "okT (beta_conversion full (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
    and z: "zreflexive_proof ztargs T t = return p" and nt: "noneg t"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain t' P where r: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and mk: "ok (mk_equals (t, t')) P" and th: "th = mk_rep m [] P"
    by (auto simp: beta_conversion_def returnW_def raiseW_def subst_bound_subst
      dest: beta_norm_reds split: if_splits pterm.splits)
  have c': "closed t'" by (rule beta_reds_closed[OF r c])
  have ty': "e \<turnstile> t' : T" for e by (rule subject_reduction_beta'[OF r ty])
  have "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" by (rule beta_eta_conv[OF beta_reds_sup[OF r]]) (use ty in \<open>auto simp: wt_def\<close>)
  note v = zreflexive_conv_proof_valid[OF z c c' ty ty' this nt]
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    using v(1) mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
  show "zconsts_ok p" by (rule v(2))
qed

theorem zeta_conversion_proof_valid:
  assumes ok: "okT (eta_conversion (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
    and z: "zreflexive_proof ztargs T t = return p" and nt: "noneg t"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain P where mk: "ok (mk_equals (t, eta_contract t)) P" and th: "th = mk_rep m [] P"
    by (auto simp: eta_conversion_def)
  note r = eta_contract_reds[of t]
  have c': "closed (eta_contract t)" by (rule eta_reds_closed[OF r c])
  have ty': "e \<turnstile> eta_contract t : T" for e by (rule eta_reds_typing[OF r ty])
  have "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> eta_contract t" by (rule beta_eta_conv[OF eta_reds_sup[OF r]]) (use ty in \<open>auto simp: wt_def\<close>)
  note v = zreflexive_conv_proof_valid[OF z c c' ty ty' this nt]
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    using v(1) mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
  show "zconsts_ok p" by (rule v(2))
qed

theorem zeta_long_conversion_proof_valid:
  assumes ok: "okT (eta_long_conversion (CTerm t T m)) th" and c: "closed t" and ty: "\<And>e. e \<turnstile> t : T"
    and z: "zreflexive_proof ztargs T t = return p" and nt: "noneg t"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain t' P where el: "ok (Pure_Rules.eta_long [] t) t'" and mk: "ok (mk_equals (t, t')) P"
    and th: "th = mk_rep m [] P"
    by (auto simp: eta_long_conversion_def)
  have bv: "bvok e [] t" for e using c by (simp add: bvok_def closed_iff_loose_bvar1)
  note r = eta_long_correct[OF el HOL.refl ty bv]
  have ty': "e \<turnstile> t' : T" for e using eta_long_correct[OF el HOL.refl ty bv, of e] by blast
  have cv: "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" and lb: "lbsub t' t" using r by blast+
  have c': "closed t'" using c lb by (auto simp: lbsub_def closed_iff_loose_bvar1)
  note v = zreflexive_conv_proof_valid[OF z c c' ty ty' cv nt]
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    using v(1) mk_equals_ok[OF mk c ty] by (simp add: th mk_rep_def)
  show "zconsts_ok p" by (rule v(2))
qed


subsection \<open>Introduction and elimination of equality of propositions\<close>

theorem zequal_intr_proof_valid:
  assumes ok: "okT (equal_intr th1 th2) th"
    and p1: "zvalid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "zvalid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
    and nn: "noneg A" "noneg B" and zc: "zconsts_ok pf1" "zconsts_ok pf2"
    and z: "zequal_intr_proof ztargs A B pf1 pf2 = return p"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain A0 B0 where d1: "dest_imp (th_prop th1) = Some (A0, B0)"
    by (auto simp: equal_intr_def returnW_def raiseW_def split: option.splits if_splits prod.splits)
  note dw1 = dest_imp_wtp[OF d1 w1]
  have AB: "A0 = A" "B0 = B" using dw1(1) P1 by simp_all
  from z obtain a b ax0 where a: "zterm_of ztargs A = return a" and b: "zterm_of ztargs B = return b"
    and ax0: "zaxiom_proof STR ''equal_intr'' [] [(STR ''A'', a), (STR ''B'', b)] = return ax0"
    and p: "p = ZAppp (ZAppp ax0 pf1) pf2"
    by (auto simp: zequal_intr_proof_def bindZ_eq_returnZ)
  have da: "zdec a = A" by (rule zdec_zterm_of_noneg[OF a wtpD(2)[OF dw1(2)[unfolded AB]] nn(1)])
  have db: "zdec b = B" by (rule zdec_zterm_of_noneg[OF b wtpD(2)[OF dw1(3)[unfolded AB]] nn(2)])
  have ae: "STR ''equal_intr'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
  have xs: "map_of [(STR ''A'', a), (STR ''B'', b)] x \<noteq> None"
    if "x \<in> set (the (map_of zeq_vars STR ''equal_intr''))" for x
    using that by (auto simp: zeq_vars_def)
  note tr = zaxiom_proof_tr[OF ax0 ae xs]
  show "zconsts_ok p" using tr(1) zc by (simp add: p)
  have ztr: "zprf_tr ax0 = equality_axm STR ''equal_intr'' %> A %> B"
    using tr(2) by (simp add: zeq_vars_def da db)
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have v: "prf_valid ax H (th_tpairs th) (PAppp (PAppp (equality_axm STR ''equal_intr'' %> A %> B) v1) v2) (th_prop th)"
    by (rule equal_intr_proof_valid_ann[OF ok v1(2) v2(2) w1 w2 P1]) simp_all
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    by (rule zvalidI[OF _ v]) (simp add: p ztr v1(1) v2(1) equality_axm_def)
qed

theorem zequal_elim_proof_valid:
  assumes ok: "okT (equal_elim th1 th2) th"
    and p1: "zvalid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "zvalid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)" and P1: "th_prop th1 = c $ A $ B"
    and nn: "noneg A" "noneg B" and zc: "zconsts_ok pf1" "zconsts_ok pf2"
    and z: "zequal_elim_proof ztargs A B pf1 pf2 = return p"
  shows "zvalid ax H (th_tpairs th) p (th_prop th)" "zconsts_ok p"
proof -
  from ok obtain A0 B0 where d: "dest_eq_any (th_prop th1) = Some (A0, B0)"
    by (auto simp: equal_elim_def returnW_def raiseW_def split: option.splits if_splits)
  obtain T where P: "th_prop th1 = eq_const T $ A0 $ B0" and ty0: "\<And>e. e \<turnstile> A0 : T" "\<And>e. e \<turnstile> B0 : T"
    using dest_eq_any_wtp[OF eq_ok_ctab d w1] by blast
  have AB: "A0 = A" "B0 = B" using P P1 by simp_all
  from z obtain a b ax0 where a: "zterm_of ztargs A = return a" and b: "zterm_of ztargs B = return b"
    and ax0: "zaxiom_proof STR ''equal_elim'' [] [(STR ''A'', a), (STR ''B'', b)] = return ax0"
    and p: "p = ZAppp (ZAppp ax0 pf1) pf2"
    by (auto simp: zequal_elim_proof_def bindZ_eq_returnZ)
  have da: "zdec a = A" by (rule zdec_zterm_of_noneg[OF a ty0(1)[unfolded AB] nn(1)])
  have db: "zdec b = B" by (rule zdec_zterm_of_noneg[OF b ty0(2)[unfolded AB] nn(2)])
  have ae: "STR ''equal_elim'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
  have xs: "map_of [(STR ''A'', a), (STR ''B'', b)] x \<noteq> None"
    if "x \<in> set (the (map_of zeq_vars STR ''equal_elim''))" for x
    using that by (auto simp: zeq_vars_def)
  note tr = zaxiom_proof_tr[OF ax0 ae xs]
  show "zconsts_ok p" using tr(1) zc by (simp add: p)
  have ztr: "zprf_tr ax0 = equality_axm STR ''equal_elim'' %> A %> B"
    using tr(2) by (simp add: zeq_vars_def da db)
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have v: "prf_valid ax H (th_tpairs th) (PAppp (PAppp (equality_axm STR ''equal_elim'' %> A %> B) v1) v2) (th_prop th)"
    by (rule equal_elim_proof_valid_ann[OF ok v1(2) v2(2) w1 w2 P1]) simp_all
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    by (rule zvalidI[OF _ v]) (simp add: p ztr v1(1) v2(1) equality_axm_def)
qed

end

end
