section \<open>Validity of proofs modulo flex-flex pairs\<close>

theory Proof_Valid
  imports Proof_Inst
begin

context prf_csig
begin

text \<open>
  A proof \<open>p\<close> of \<open>\<phi>\<close> is valid modulo the flex-flex pairs \<open>tps\<close> if every well-sorted
  instantiation that solves the pairs, with values in any context of bound variables, turns
  it into a proof of the instance of \<open>\<phi>\<close>.
\<close>

definition prf_valid_ctx :: "algebra \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> pterm set \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> bool" where
  "prf_valid_ctx alg V H tps p \<phi> \<longleftrightarrow> (\<forall>V' Us \<rho> \<theta>. wsinst alg \<rho> \<longrightarrow> inst_typed V V' Us \<rho> \<theta> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)) \<longrightarrow>
    prf_ok V' H Us [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 \<phi>))"

lemma prf_valid_ctxD:
  "prf_valid_ctx alg V H tps p \<phi> \<Longrightarrow> wsinst alg \<rho> \<Longrightarrow> inst_typed V V' Us \<rho> \<theta> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)) \<Longrightarrow>
    prf_ok V' H Us [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 \<phi>)"
  unfolding prf_valid_ctx_def by blast


subsection \<open>Instantiation after lifting\<close>

text \<open>Lifting followed by an instantiation is an instantiation.\<close>

definition lift_tinst :: "integer \<Rightarrow> tinst \<Rightarrow> tinst" where
  "lift_tinst inc \<rho> v S = tsubst \<rho> (TVar (fst v, snd v + inc) S)"

definition lift_sinst :: "integer \<Rightarrow> nat \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> indexname \<Rightarrow> pterm" where
  "lift_sinst inc n \<theta> x = combound (incr_boundvars (integer_of_nat n) (\<theta> (fst x, snd x + inc))) 0 n"

lemma tsubst_incr_tvar: "tsubst \<rho> (incr_tvar inc T) = tsubst (lift_tinst inc \<rho>) T"
  by (induction inc T rule: incr_tvar.induct) (auto simp: lift_tinst_def)

lemma incr_bv_add: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> incr_bv a k (incr_bv b k v) = incr_bv (a + b) k v"
  by (induction b k v rule: incr_bv.induct) (auto simp: algebra_simps)

lemma incr_bv_combound0:
  "0 \<le> n0 \<Longrightarrow> 0 \<le> l \<Longrightarrow> incr_bv l 0 (combound t n0 m) = combound (incr_bv l 0 t) (n0 + l) m"
  by (induction m arbitrary: n0) (auto simp: algebra_simps)

lemma psubst_combound: "psubst \<rho> \<theta> lev (combound t n m) = combound (psubst \<rho> \<theta> lev t) n m"
  by (induction m arbitrary: n) auto

lemma psubst_incr_idx:
  "0 \<le> l \<Longrightarrow> psubst \<rho> \<theta> (integer_of_nat (length Ws) + l) (incr_idx Ws inc l t) =
    psubst (lift_tinst inc \<rho>) (lift_sinst inc (length Ws) \<theta>) l t"
proof (induction Ws inc l t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  have "incr_bv lev 0 (combound (incr_bv (integer_of_nat (length Ts)) 0 (\<theta> (x, i + inc))) 0 (length Ts)) =
      combound (incr_bv (integer_of_nat (length Ts) + lev) 0 (\<theta> (x, i + inc))) lev (length Ts)"
    using 1 by (simp add: incr_bv_combound0 incr_bv_add add.commute)
  then show ?case by (simp add: psubst_combound lift_sinst_def incr_boundvars_eq)
next
  case (3 Ts inc lev x T t)
  then show ?case by (simp add: tsubst_incr_tvar add.assoc)
qed (simp_all add: tsubst_incr_tvar)

lemma hd_set_types_twice[simp]: "hd_set_types (hd_set_types h Ts) Us = hd_set_types h Us"
  by (simp add: hd_set_types_def)

lemma prf_inst_lift_prf:
  "0 \<le> l \<Longrightarrow> prf_inst \<rho> \<theta> (integer_of_nat (length Ws) + l) (lift_prf inc Ws l p) =
    prf_inst (lift_tinst inc \<rho>) (lift_sinst inc (length Ws) \<theta>) l p"
proof (induction inc Ws l p rule: lift_prf.induct)
  case (1 inc Ts lev a T p)
  then show ?case by (cases T) (simp_all add: tsubst_incr_tvar add.assoc)
qed (simp_all add: psubst_incr_idx tsubst_incr_tvar option.map_comp comp_def split: option.split)

lemma tsubst_foldr: "tsubst \<rho> (foldr fun_type Ws T) = foldr fun_type (map (tsubst \<rho>) Ws) (tsubst \<rho> T)"
  by (induction Ws) auto

lemma wsinst_lift_tinst: "wsinst alg \<rho> \<Longrightarrow> wsinst alg (lift_tinst inc \<rho>)"
  by (simp add: wsinst_def lift_tinst_def)

lemma inst_typed_lift:
  assumes \<theta>: "inst_typed V2 V3 Us \<rho> \<theta>" and V2: "lift_venv (rev Ts) inc V V2" and inc: "0 \<le> inc"
  shows "inst_typed V V3 (map (tsubst \<rho>) Ts @ Us) (lift_tinst inc \<rho>) (lift_sinst inc (length Ts) \<theta>)"
  unfolding inst_typed_def
proof (intro allI impI)
  fix x :: indexname assume x: "0 \<le> snd x"
  let ?x = "(fst x, snd x + inc)"
  let ?Ts = "map (tsubst \<rho>) Ts @ Us"
  have w: "wty V3 Us (\<theta> ?x) (tsubst \<rho> (V2 ?x))" using inst_typedD[OF \<theta>] x inc by simp
  have V2x: "V2 ?x = foldr fun_type (rev Ts) (incr_tvar inc (V x))"
    using V2 x unfolding lift_venv_def by (cases x) auto
  have "has_type V3 ?Ts (incr_bv (integer_of_nat (length Ts)) 0 (\<theta> ?x)) (tsubst \<rho> (V2 ?x))"
    using has_type_incr_bv[of V3 Us "\<theta> ?x" "tsubst \<rho> (V2 ?x)" "integer_of_nat (length Ts)" 0 "map (tsubst \<rho>) Ts"] w
    by (simp add: wty_def integer_reps)
  then have "has_type V3 ?Ts (incr_boundvars (integer_of_nat (length Ts)) (\<theta> ?x))
      (foldr fun_type (map (tsubst \<rho>) (rev Ts)) (tsubst (lift_tinst inc \<rho>) (V x)))"
    by (simp add: incr_boundvars_eq V2x tsubst_foldr tsubst_incr_tvar)
  then have "has_type V3 ?Ts (combound (incr_boundvars (integer_of_nat (length Ts)) (\<theta> ?x)) 0
      (length (map (tsubst \<rho>) (rev Ts)))) (tsubst (lift_tinst inc \<rho>) (V x))"
    by (rule has_type_combound) (auto simp: nth_append rev_map)
  moreover have "\<forall>v\<in>vars (\<theta> ?x). 0 \<le> snd v" using w by (simp add: wty_def)
  ultimately show "wty V3 ?Ts (lift_sinst inc (length Ts) \<theta> x) (tsubst (lift_tinst inc \<rho>) (V x))"
    by (simp add: wty_def lift_sinst_def incr_boundvars_eq vars_incr_bv)
qed


subsection \<open>Flex-flex pairs of lifted rules\<close>

lemma length_lift_Ts: "length Ts \<le> length (lift_Ts Ts G)"
  by (induction Ts G rule: lift_Ts.induct) (auto intro: le_SucI dest: Suc_leD)

lemma tr_psubst_lift_abs_aux:
  "tr (psubst \<rho> \<theta> (integer_of_nat (length Ts)) (lift_abs_aux inc Ts G t)) =
    Abs_m (length (lift_Ts Ts G) - length Ts)
      (tr (psubst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (incr_indexes (rev (lift_Ts Ts G)) inc t)))"
proof (induction inc Ts G t rule: lift_abs_aux.induct)
  case (2 inc Ts c U a T B t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    have l: "Suc (length Ts) \<le> length (lift_Ts (T # Ts) B)" using length_lift_Ts[of "T # Ts" B] by simp
    then have "length (lift_Ts (T # Ts) B) - length Ts = Suc (length (lift_Ts (T # Ts) B) - Suc (length Ts))"
      by simp
    with True 2 show ?thesis by (simp add: integer_of_nat_Suc)
  qed (simp add: 2)
qed simp_all

lemma equiv_Abs_inj: "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  assume e: "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t"
  have r: "dB.Abs (lift u (Suc 0)) \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> u" for u
    using beta.beta[of "lift u (Suc 0)" "BVar 0"] by (simp add: subst_lift_0 beta_into_equiv r_into_rtranclp)
  have "lift (dB.Abs s) 0 \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (dB.Abs t) 0 \<degree> BVar 0"
    by (intro equiv_AppL lift_equiv e)
  then have "dB.Abs (lift s (Suc 0)) \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (lift t (Suc 0)) \<degree> BVar 0" by simp
  with r[of s] r[of t] show ?thesis by (meson equiv_sym equiv_trans)
qed

lemma equiv_Abs_m_inj: "Abs_m m s \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m m t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (induction m) (auto dest: equiv_Abs_inj)

lemma lift_abs_solves:
  assumes "tr (psubst \<rho> \<theta> 0 (lift_abs inc G t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 (lift_abs inc G u))"
  shows "tr (psubst (lift_tinst inc \<rho>) (lift_sinst inc (length (lift_Ts [] G)) \<theta>) 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta>
    tr (psubst (lift_tinst inc \<rho>) (lift_sinst inc (length (lift_Ts [] G)) \<theta>) 0 u)"
proof -
  have e: "tr (psubst \<rho> \<theta> 0 (lift_abs inc G t)) =
      Abs_m (length (lift_Ts [] G)) (tr (psubst (lift_tinst inc \<rho>) (lift_sinst inc (length (lift_Ts [] G)) \<theta>) 0 t))"
    for t
    using tr_psubst_lift_abs_aux[of \<rho> \<theta> "[]" inc G t] psubst_incr_idx[of 0 \<rho> \<theta> "rev (lift_Ts [] G)" inc t]
    by (simp add: lift_abs_def incr_indexes_incr_idx)
  from assms show ?thesis unfolding e by (rule equiv_Abs_m_inj)
qed


subsection \<open>Lifting of valid rules\<close>

lemma prf_inst_spine: "prf_inst \<rho> \<theta> lev (spine bs i j c) = spine bs i j c"
proof -
  have "prf_inst \<rho> \<theta> lev (snd (snd (foldr mk_app bs (a, b, PBound c)))) = snd (snd (foldr mk_app bs (a, b, PBound c)))"
    for a b
  proof (induction bs)
    case (Cons x bs)
    show ?case unfolding foldr_mk_app_Cons using Cons by (cases x) simp_all
  qed simp
  then show ?thesis by (simp add: spine_def)
qed

lemma prf_inst_proof_combP:
  "prf_inst \<rho> \<theta> lev (proof_combP p qs) = proof_combP (prf_inst \<rho> \<theta> lev p) (map (prf_inst \<rho> \<theta> lev) qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def)

lemma prf_inst_mk_AbsP: "prf_inst \<rho> \<theta> lev (mk_AbsP xs p) = mk_AbsP xs (prf_inst \<rho> \<theta> lev p)"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma mk_AbsP_funpow: "mk_AbsP xs p = (AbsP (STR ''H'') None ^^ length xs) p"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma mk_AbsP_length: "length xs = length ys \<Longrightarrow> mk_AbsP xs p = mk_AbsP ys p"
  by (simp add: mk_AbsP_funpow)

lemma psubst_list_implies:
  "psubst \<rho> \<theta> lev (list_implies As B) = list_implies (map (psubst \<rho> \<theta> lev) As) (psubst \<rho> \<theta> lev B)"
  by (induction As) simp_all

lemma lift_prems_inst_leaf:
  "j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (incr_indexes (rev Ts) inc (As ! m)))) \<Longrightarrow>
    (\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length Ts)) (lift_prf inc (rev Ts) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length Ts)) (incr_indexes (rev Ts) inc (list_implies As B)))) \<Longrightarrow>
    k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (prf_inst \<rho> \<theta> j (proof_combP (lift_prf inc (rev Ts) 0 pf)
      (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))))
    (psubst \<rho> \<theta> j (incr_indexes (rev Ts) inc B))"
proof -
  assume j: "j = integer_of_nat (length Ts)" and k: "k = integer_of_nat (length As)"
    and sp: "\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (incr_indexes (rev Ts) inc (As ! m)))"
    and leaf: "\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length Ts)) (lift_prf inc (rev Ts) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length Ts)) (incr_indexes (rev Ts) inc (list_implies As B)))"
  let ?f = "\<lambda>A. psubst \<rho> \<theta> j (incr_indexes (rev Ts) inc A)"
  have "map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i) =
      map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As]"
    by (simp add: downto_map k spine_def)
  moreover have "list_all2 (prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs)
      (map (\<lambda>m. spine bs i j (i + k - 1 - integer_of_nat m)) [0..<length As]) (map ?f As)"
    using sp by (auto simp: list_all2_conv_all_nth)
  moreover have "prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs
      (prf_inst \<rho> \<theta> j (lift_prf inc (rev Ts) 0 pf)) (list_implies (map ?f As) (?f B))"
    using leaf j by (simp add: incr_indexes_incr_idx incr_idx_list_implies psubst_list_implies comp_def)
  ultimately show ?thesis
    by (auto simp: prf_inst_proof_combP prf_inst_spine comp_def intro: prf_ok_proof_combP)
qed

lemma lift_prems_inst_leaf_gen:
  assumes leaf: "lift_Ts Ts G = Ts" "\<And>A. lift_all_aux inc Ts G A = incr_indexes (rev Ts) inc A"
      "lift_prems inc k pf Ts bs i j G = proof_combP (lift_prf inc (rev Ts) 0 pf)
        (map (\<lambda>k. snd (snd (foldr mk_app bs (i - 1, j - 1, PBound k)))) (downto (i + k - 1) i))"
  shows "wty V2 Ts G propT \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G (As ! m)))) \<Longrightarrow>
    (\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) (lift_Ts Ts G) @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (lift_prf inc (rev (lift_Ts Ts G)) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (incr_indexes (rev (lift_Ts Ts G)) inc (list_implies As B)))) \<Longrightarrow>
    k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (prf_inst \<rho> \<theta> j (lift_prems inc k pf Ts bs i j G))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G B))"
  unfolding leaf by (rule lift_prems_inst_leaf)

lemma prf_ok_lift_prems_inst:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and \<theta>: "inst_typed V2 V3 Us \<rho> \<theta>"
  shows "wty V2 Ts G propT \<Longrightarrow>
    i = integer_of_nat (length (filter id bs)) \<Longrightarrow> length Ts = length (filter Not bs) \<Longrightarrow>
    j = integer_of_nat (length Ts) \<Longrightarrow>
    (\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (spine bs i j (i + k - 1 - integer_of_nat m))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G (As ! m)))) \<Longrightarrow>
    (\<forall>Hs'. prf_ok V3 H (map (tsubst \<rho>) (lift_Ts Ts G) @ Us) Hs'
      (prf_inst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (lift_prf inc (rev (lift_Ts Ts G)) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat (length (lift_Ts Ts G))) (incr_indexes (rev (lift_Ts Ts G)) inc (list_implies As B)))) \<Longrightarrow>
    k = integer_of_nat (length As) \<Longrightarrow>
    prf_ok V3 H (map (tsubst \<rho>) Ts @ Us) Hs (prf_inst \<rho> \<theta> j (lift_prems inc k pf Ts bs i j G))
      (psubst \<rho> \<theta> j (lift_all_aux inc Ts G B))"
proof (induction inc k pf Ts bs i j G arbitrary: Hs rule: lift_prems.induct)
  case (1 inc k pf Ts bs i j c U A' G')
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    note tA = has_type_imp_E[of V2 Ts U A' G' propT, OF 1(2)[unfolded wty_def True, THEN conjunct1]]
    have wA0: "wty V2 Ts A' propT" "wty V2 Ts G' propT" using 1(2) tA by (auto simp: wty_def True)
    let ?A = "psubst \<rho> \<theta> j A'"
    let ?Ts = "map (tsubst \<rho>) Ts @ Us"
    have wA: "wty V3 ?Ts ?A propT" using wty_psubst[OF wA0(1) \<theta>] 1(5) by (simp add: propT_def)
    have e: "psubst \<rho> \<theta> j (Const STR ''Pure.imp'' U) = implies"
      using tA by (simp add: implies_def propT_def)
    have "prf_ok V3 H ?Ts (?A # Hs) (prf_inst \<rho> \<theta> j (lift_prems inc k pf Ts (True # bs) (i + 1) j G'))
        (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' B))"
    proof (rule 1(1)[OF True])
      show "\<forall>m<length As. prf_ok V3 H ?Ts (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
          (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        have "integer_of_nat (Suc m) \<le> k" using m 1(8) by (simp add: less_eq_integer.rep_eq integer_of_nat.rep_eq)
        then have c0: "0 \<le> i + k - 1 - integer_of_nat m" using 1(3) integer_of_nat_nonneg[of "length (filter id bs)"]
          by (simp only: integer_of_nat_Suc)
        have "prf_ok V3 H ?Ts (take (nat_of_integer 0) Hs @ ?A # drop (nat_of_integer 0) Hs)
            (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (psubst \<rho> \<theta> j (lift_all_aux inc Ts (Const c U $ A' $ G') (As ! m)))"
          using 1(6) m by (intro prf_ok_incr_pbv) (auto simp: integer_reps)
        then have "prf_ok V3 H ?Ts (?A # Hs) (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m)))
            (implies $ ?A $ psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
          using True e by (simp add: integer_reps)
        moreover have "prf_ok V3 H ?Ts (?A # Hs) (PBound 0) ?A"
          using prf_ok.PBound[of 0 "?A # Hs" V3 ?Ts H] wA by (simp add: integer_reps)
        ultimately have "prf_ok V3 H ?Ts (?A # Hs) (PAppp (incr_pbv 0 (spine bs i j (i + k - 1 - integer_of_nat m))) (PBound 0))
            (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))" by (rule prf_ok.PAppp)
        then show "prf_ok V3 H ?Ts (?A # Hs) (spine (True # bs) (i + 1) j (i + 1 + k - 1 - integer_of_nat m))
            (psubst \<rho> \<theta> j (lift_all_aux inc Ts G' (As ! m)))"
          using spine_True[OF 1(3) c0, of j] by (simp add: algebra_simps)
      qed
    qed (use wA0 1(3-5) 1(7-8) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    then have "prf_ok V3 H ?Ts Hs (AbsP (STR ''H'') None (prf_inst \<rho> \<theta> j (lift_prems inc k pf Ts (True # bs) (i + 1) j G')))
        (implies $ ?A $ psubst \<rho> \<theta> j (lift_all_aux inc Ts G' B))" using wA by (auto intro!: prf_ok.AbsP)
    then show ?thesis using True e by simp
  next
    case False
    show ?thesis by (rule lift_prems_inst_leaf_gen[OF _ _ _ 1(2-8)]) (use False in simp_all)
  qed
next
  case (2 inc k pf Ts bs i j c U a T G')
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    note tG = has_type_all_E[of V2 Ts U a T G' propT, OF 2(2)[unfolded wty_def True, THEN conjunct1]]
    have wG: "wty V2 (T # Ts) G' propT" using 2(2) tG by (auto simp: wty_def True)
    let ?Ts = "map (tsubst \<rho>) Ts @ Us"
    let ?T = "tsubst \<rho> T"
    have e: "psubst \<rho> \<theta> j (Const STR ''Pure.all'' U) = all_const ?T"
      using tG by (simp add: all_const_def propT_def)
    have "prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
        (prf_inst \<rho> \<theta> (j + 1) (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) G'))
        (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' B))"
    proof (rule 2(1)[OF True])
      show "\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
          (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m))
          (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' (As ! m)))"
      proof (intro allI impI)
        fix m assume m: "m < length As"
        let ?X = "psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' (As ! m))"
        let ?s = "spine bs i j (i + k - 1 - integer_of_nat m)"
        have sm: "prf_ok V3 H ?Ts Hs ?s (all_const ?T $ Abs a ?T ?X)"
          using 2(6) m True e by simp
        have wX: "wty V3 (?T # ?Ts) ?X propT"
          using prf_ok_wty[OF sm] by (auto simp: wty_def all_const_def dest!: has_type_all_E)
        have Hc: "\<forall>h\<in>H. \<not> loose_bvar h 0" using H by blast
        have "prf_ok V3 H (take (nat_of_integer 0) ?Ts @ ?T # drop (nat_of_integer 0) ?Ts) (map (incr_bv 1 0) Hs)
            (incr_tbv 0 ?s) (incr_bv 1 0 (all_const ?T $ Abs a ?T ?X))"
          using sm by (intro prf_ok_incr_tbv[OF Hc]) (auto simp: integer_reps)
        then have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (incr_tbv 0 ?s) (all_const ?T $ Abs a ?T (incr_bv 1 1 ?X))"
          by (simp add: integer_reps)
        then have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0)))
            (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0)"
          by (rule prf_ok.PAppt) (auto simp: wty_def has_type_Bound_iff integer_reps)
        moreover have "tr (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ?X"
        proof -
          have "proper ?X" using wX by (auto simp: wty_def intro: has_type_proper)
          then have e1: "tr (Abs a ?T (incr_bv 1 1 ?X) $ Bound 0) = dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0"
            by (simp add: tr_incr_bv1 integer_reps)
          have e2: "dB.Abs (lift (tr ?X) (Suc 0)) \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> tr ?X"
            using beta.beta[of "lift (tr ?X) (Suc 0)" "BVar 0"] by (simp only: subst_lift_0)
          show ?thesis unfolding e1 by (rule beta_into_equiv, rule r_into_rtranclp, rule e2)
        qed
        ultimately have "prf_ok V3 H (?T # ?Ts) (map (incr_bv 1 0) Hs) (PAppt (incr_tbv 0 ?s) (Some (Bound 0))) ?X"
          using wX by (rule prf_ok.conv)
        then show "prf_ok V3 H (map (tsubst \<rho>) (T # Ts) @ Us) (map (incr_bv 1 0) Hs)
            (spine (False # bs) i (j + 1) (i + k - 1 - integer_of_nat m)) ?X"
          using spine_False[of j bs i] 2(4,5) by simp
      qed
    qed (use wG 2(3-5) 2(7-8) True in \<open>simp_all add: integer_of_nat_Suc\<close>)
    then have "prf_ok V3 H ?Ts Hs (Abst a None (prf_inst \<rho> \<theta> (j + 1) (lift_prems inc k pf (T # Ts) (False # bs) i (j + 1) G')))
        (all_const ?T $ Abs a ?T (psubst \<rho> \<theta> (j + 1) (lift_all_aux inc (T # Ts) G' B)))"
      by (auto intro!: prf_ok.Abst[where T = None, simplified])
    then show ?thesis using True e by simp
  next
    case False
    show ?thesis by (rule lift_prems_inst_leaf_gen[OF _ _ _ 2(2-8)]) (use False in simp_all)
  qed
qed (rule lift_prems_inst_leaf_gen; (assumption | simp))+

theorem prf_valid_lift_proof:
  assumes H: "\<forall>h\<in>H. vars h = {} \<and> (\<forall>U\<in>tys h. tvars U = {}) \<and> \<not> loose_bvar h 0"
    and inc: "0 \<le> inc" and P: "prf_valid_ctx alg V H tps pf (list_implies As B)"
    and wR: "wty V [] (list_implies As B) propT"
    and G: "wty V2 [] G propT" and V2: "lift_venv (rev (lift_Ts [] G)) inc V V2"
  shows "prf_valid_ctx alg V2 H (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps)
    (lift_proof G inc (map (lift_all inc G) As) pf) (list_implies (map (lift_all inc G) As) (lift_all inc G B))"
  unfolding prf_valid_ctx_def
proof (intro allI impI)
  fix V3 Us \<rho> \<theta>
  assume ws: "wsinst alg \<rho>" and \<theta>: "inst_typed V2 V3 Us \<rho> \<theta>"
    and sol: "\<forall>(t, u)\<in>set (map (\<lambda>(t, u). (lift_abs inc G t, lift_abs inc G u)) tps).
      tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
  let ?L = "lift_Ts [] G"
  let ?n = "length ?L"
  let ?Ps = "map (lift_all inc G) As"
  let ?\<rho> = "lift_tinst inc \<rho>" and ?\<theta> = "lift_sinst inc ?n \<theta>"
  let ?Ctx = "map (tsubst \<rho>) ?L @ Us"
  text \<open>The instance of the rule in the context of the parameters of the subgoal.\<close>
  have leaf0: "prf_ok V3 H ?Ctx [] (prf_inst ?\<rho> ?\<theta> 0 pf) (psubst ?\<rho> ?\<theta> 0 (list_implies As B))"
  proof (rule prf_valid_ctxD[OF P wsinst_lift_tinst[OF ws]])
    show "inst_typed V V3 ?Ctx ?\<rho> ?\<theta>" using inst_typed_lift[OF \<theta> _ inc] V2 by simp
    show "tr (psubst ?\<rho> ?\<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst ?\<rho> ?\<theta> 0 u)" if "(t, u) \<in> set tps" for t u
      using sol that by (intro lift_abs_solves) auto
  qed
  have leaf: "prf_ok V3 H ?Ctx Hs' (prf_inst \<rho> \<theta> (integer_of_nat ?n) (lift_prf inc (rev ?L) 0 pf))
      (psubst \<rho> \<theta> (integer_of_nat ?n) (incr_indexes (rev ?L) inc (list_implies As B)))" for Hs'
    using prf_ok_append[OF leaf0, of Hs'] prf_inst_lift_prf[of 0 \<rho> \<theta> "rev ?L" inc pf]
      psubst_incr_idx[of 0 \<rho> \<theta> "rev ?L" inc "list_implies As B"]
    by (simp add: incr_indexes_incr_idx)
  have wA: "\<forall>A\<in>set As. wty V [] A propT" using wty_list_implies[OF wR] by simp
  have wP: "\<forall>P\<in>set ?Ps. wty V2 [] P propT"
    using wA G V2 inc by (auto simp: lift_all_def intro: wty_lift_all_aux)
  let ?Qs = "map (psubst \<rho> \<theta> 0) ?Ps"
  have "prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
      (prf_inst \<rho> \<theta> 0 (lift_prems inc (integer_of_nat (length As)) pf [] [] 0 0 G)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G B))"
  proof (rule prf_ok_lift_prems_inst[OF H \<theta> G])
    show "\<forall>m<length As. prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
        (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G (As ! m)))"
    proof (intro allI impI)
      fix m assume m: "m < length As"
      have c: "integer_of_nat (length As) - 1 - integer_of_nat m = integer_of_nat (length As - Suc m)"
        using m by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
      have "rev ?Qs ! (length As - Suc m) = psubst \<rho> \<theta> 0 (lift_all inc G (As ! m))" using m by (simp add: rev_nth)
      moreover have "wty V3 Us (psubst \<rho> \<theta> 0 (lift_all inc G (As ! m))) propT"
        using wty_psubst[of V2 "[]" "lift_all inc G (As ! m)" propT V3 Us \<rho> \<theta>] wP m \<theta> by (simp add: propT_def)
      ultimately show "prf_ok V3 H (map (tsubst \<rho>) [] @ Us) (rev ?Qs)
          (spine [] 0 0 (0 + integer_of_nat (length As) - 1 - integer_of_nat m)) (psubst \<rho> \<theta> 0 (lift_all_aux inc [] G (As ! m)))"
        using prf_ok.PBound[of "integer_of_nat (length As - Suc m)" "rev ?Qs" V3 Us H] m
        by (simp add: spine_def c lift_all_def)
    qed
  qed (use leaf in simp_all)
  moreover have "\<forall>Q\<in>set ?Qs. wty V3 Us Q propT"
    using wP \<theta> wty_psubst[of V2 "[]" _ propT V3 Us \<rho> \<theta>] by (auto simp: propT_def)
  ultimately have "prf_ok V3 H Us [] (mk_AbsP ?Qs (prf_inst \<rho> \<theta> 0 (lift_prems inc (integer_of_nat (length As)) pf [] [] 0 0 G)))
      (list_implies ?Qs (psubst \<rho> \<theta> 0 (lift_all inc G B)))"
    by (auto simp: lift_all_def intro!: prf_ok_mk_AbsP)
  then show "prf_ok V3 H Us [] (prf_inst \<rho> \<theta> 0 (lift_proof G inc ?Ps pf)) (psubst \<rho> \<theta> 0 (list_implies ?Ps (lift_all inc G B)))"
    by (simp add: lift_proof_def psubst_list_implies prf_inst_mk_AbsP mk_AbsP_length[of ?Ps ?Qs])
qed

end

end
