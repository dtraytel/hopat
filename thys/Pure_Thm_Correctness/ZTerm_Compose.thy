section \<open>Composition of tight proofs\<close>

theory ZTerm_Compose
  imports ZTerm_Lift
begin

text \<open>
  The parts of the composed proof that \<open>ZTerm.bicompose_proof\<close> builds, with their annotations:
  the proofs of flattened premises and by assumption, and the abstraction over the new premises.
  The lemmas are those of the classic proofs, at the level of instances.
\<close>

context prf_wf_csig
begin

subsection \<open>Proofs of flattened premises\<close>

fun flatten_params_proof_a :: "integer \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm \<times> integer \<Rightarrow> prf" where
  "flatten_params_proof_a i j n (Const c U $ A $ B, k) =
    (if c = STR ''Pure.imp'' then AbsP (STR ''H'') (Some A) (flatten_params_proof_a (i + 1) j n (B, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "flatten_params_proof_a i j n (Const c U $ Abs a T t, k) =
    (if c = STR ''Pure.all'' then Abst a (Some T) (flatten_params_proof_a i (j + 1) n (t, k))
     else proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
       (map PBound (removeAll (i - n) (downto (i - 1) 0))))"
| "flatten_params_proof_a i j n (_, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
      (map PBound (removeAll (i - n) (downto (i - 1) 0)))"

lemma fpp_a_atomic: "atomic C \<Longrightarrow> flatten_params_proof_a i j n (C, k) = leafprf i j n k"
  by (cases "(i, j, n, (C, k))" rule: flatten_params_proof_a.cases) (auto simp: atomic_def leafprf_def)

lemma prf_inst_leafprf: "prf_inst \<rho> \<theta> lev (leafprf i j n k) = leafprf i j n k"
proof -
  have e: "leafprf i j n k = flatten_params_proof i j n (Bound 0, k)" by (simp add: leafprf_def)
  show ?thesis unfolding e by (rule prf_inst_bnd_only[OF bnd_only_flatten_params_proof'])
qed

lemma fpp_a_gen:
  assumes "\<forall>it\<in>set p. litem_ok it" "atomic C" "cok (lift_pre p C)" "closed_inst \<theta> (lift_pre p C)"
    "0 \<le> lev"
  shows "wty V Ts (psubst \<rho> \<theta> 0 (lift_pre p C)) propT \<Longrightarrow> \<forall>h\<in>set Hs. wty V Ts h propT \<Longrightarrow>
    prf_ok V H (ptys \<rho> p @ Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs)
      (leafprf (i + integer_of_nat (nhyp p)) (j + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C) \<Longrightarrow>
    prf_ok V H Ts Hs (prf_inst \<rho> \<theta> lev (flatten_params_proof_a i j n (lift_pre p C, k))) (psubst \<rho> \<theta> 0 (lift_pre p C))"
  using assms
proof (induction p arbitrary: i j Ts Hs lev)
  case Nil
  then show ?case by (simp add: fpp_a_atomic prf_inst_leafprf)
next
  case (Cons it p)
  note items = cok_lift_pre_items[OF Cons.prems(4,6)]
  have cl: "closed_inst \<theta> (lift_pre p C)" using Cons.prems(7) by (cases it) (auto simp: closed_inst_def)
  show ?case
  proof (cases it)
    case (LImp c H')
    then have c: "c = implies" using items by simp
    have cok': "cok (lift_pre p C)" using Cons.prems(6) by (simp add: LImp c)
    have w: "wty V Ts (psubst \<rho> \<theta> 0 H') propT" "wty V Ts (psubst \<rho> \<theta> 0 (lift_pre p C)) propT"
      using Cons.prems(1) by (auto simp: LImp c wty_def has_type_implies)
    have fpp: "flatten_params_proof_a i j n (implies $ H' $ lift_pre p C, k) =
        AbsP (STR ''H'') (Some H') (flatten_params_proof_a (i + 1) j n (lift_pre p C, k))"
      by (simp add: implies_def)
    have eH: "psubst \<rho> \<theta> lev H' = psubst \<rho> \<theta> 0 H'"
      using Cons.prems(7,8) by (intro psubst_closed_lev) (auto simp: closed_inst_def LImp)
    have "prf_ok V H Ts (psubst \<rho> \<theta> 0 H' # Hs) (prf_inst \<rho> \<theta> lev (flatten_params_proof_a (i + 1) j n (lift_pre p C, k)))
        (psubst \<rho> \<theta> 0 (lift_pre p C))"
    proof (rule Cons.IH[OF w(2)])
      show "\<forall>h\<in>set (psubst \<rho> \<theta> 0 H' # Hs). wty V Ts h propT" using w(1) Cons.prems(2) by simp
      show "prf_ok V H (ptys \<rho> p @ Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) (psubst \<rho> \<theta> 0 H' # Hs))
          (leafprf (i + 1 + integer_of_nat (nhyp p)) (j + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C)"
        using Cons.prems(3) by (simp add: LImp integer_of_nat_Suc algebra_simps)
    qed (use Cons.prems(4,5,8) cok' cl in auto)
    then show ?thesis using w(1) by (auto simp: fpp LImp c eH intro: prf_ok.AbsP ann_ok_refl)
  next
    case (LAll c a T)
    then have c: "c = all_const T" using items by simp
    have cok': "cok (lift_pre p C)" using Cons.prems(6) by (simp add: LAll c all_const_def)
    have e1: "psubst \<rho> \<theta> 1 (lift_pre p C) = psubst \<rho> \<theta> 0 (lift_pre p C)"
      using cl psubst_closed_lev[of "lift_pre p C" \<theta> 1 \<rho>] by (simp add: closed_inst_def)
    have w: "wty V (tsubst \<rho> T # Ts) (psubst \<rho> \<theta> 0 (lift_pre p C)) propT"
      using Cons.prems(1) e1 by (auto simp: LAll c wty_def all_const_def dest!: has_type_all_E)
    have fpp: "flatten_params_proof_a i j n (all_const T $ Abs a T (lift_pre p C), k) =
        Abst a (Some T) (flatten_params_proof_a i (j + 1) n (lift_pre p C, k))"
      by (simp add: all_const_def)
    have "prf_ok V H (tsubst \<rho> T # Ts) (map (incr_bv 1 0) Hs)
        (prf_inst \<rho> \<theta> (lev + 1) (flatten_params_proof_a i (j + 1) n (lift_pre p C, k)))
        (psubst \<rho> \<theta> 0 (lift_pre p C))"
    proof (rule Cons.IH[OF w])
      show "\<forall>h\<in>set (map (incr_bv 1 0) Hs). wty V (tsubst \<rho> T # Ts) h propT"
        using Cons.prems(2) wty_incr_bv[of V Ts _ propT 0 "tsubst \<rho> T"] by (auto simp: integer_reps)
      have e: "map (incr_bv (integer_of_nat (npar p)) 0) (map (incr_bv 1 0) Hs) =
          map (incr_bv (integer_of_nat (npar (it # p))) 0) Hs"
        by (simp add: LAll incr_bv_comp0 integer_of_nat_Suc)
      have j: "j + 1 + integer_of_nat (npar p) = j + integer_of_nat (npar (it # p))"
        by (simp add: LAll integer_of_nat_Suc)
      show "prf_ok V H (ptys \<rho> p @ tsubst \<rho> T # Ts) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) (map (incr_bv 1 0) Hs))
          (leafprf (i + integer_of_nat (nhyp p)) (j + 1 + integer_of_nat (npar p)) n k) (psubst \<rho> \<theta> 0 C)"
        unfolding e j using Cons.prems(3) by (simp add: LAll)
    qed (use Cons.prems(4,5,8) cok' cl in auto)
    then have "prf_ok V H Ts Hs (Abst a (Some (tsubst \<rho> T)) (prf_inst \<rho> \<theta> (lev + 1) (flatten_params_proof_a i (j + 1) n (lift_pre p C, k))))
        (all_const (tsubst \<rho> T) $ Abs a (tsubst \<rho> T) (psubst \<rho> \<theta> 0 (lift_pre p C)))"
      by (intro prf_ok.Abst) simp_all
    then show ?thesis using e1 by (simp add: fpp LAll c)
  qed
qed


theorem flatten_params_proof_a_ok:
  assumes cA: "cok A" and cl: "closed_inst \<theta> A" and fl: "ok (flatten_params vl n A) A'"
    and vl: "length (vl (map fst (strip_params A))) = length (strip_params A)"
    and wA: "wty V [] (psubst \<rho> \<theta> 0 A) propT" and wA': "wty V [] (psubst \<rho> \<theta> 0 A') propT"
    and k: "k < length Hs" and wk: "wty V [] (Hs ! k) propT"
    and eA': "tr (Hs ! k) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 A')"
    and wHs: "\<forall>h\<in>set Hs. wty V [] h propT"
  shows "prf_ok V H [] Hs (prf_inst \<rho> \<theta> 0 (flatten_params_proof_a 0 0 n (A, integer_of_nat k))) (psubst \<rho> \<theta> 0 A)"
proof -
  obtain p C where ls: "lsplit A = (p, C)" by (cases "lsplit A")
  from lsplit_ok[OF ls] have A: "A = lift_pre p C" and items: "\<forall>i\<in>set p. litem_ok i" and at: "atomic C"
    by auto
  note it = cok_lift_pre_items[OF items cA[unfolded A]]
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  have lps: "length ?ps = npar p" using length_strip_params_lift_pre[OF items at] by (simp add: A)
  have lv: "length ?vars = npar p" using vl lps by simp
  have sv: "map snd ?vars = map snd ?ps" using vl by (simp add: map_snd_zip)
  from fl obtain A'' where r: "ok (remove_params (ilength ?vars) n A) A''" and A': "A' = list_forall ?vars A''"
    by (auto simp: flatten_params_def Let_def bindM_def return_def split: option.splits res.splits)
  have j: "ilength ?vars = integer_of_nat (npar p)" using lv by (simp add: ilength_eq)
  have nle: "n \<le> integer_of_nat (nhyp p)"
    using remove_params_n_le[OF items at j[symmetric]] r by (simp add: A)
  have impl: "\<forall>i\<in>set p. case i of LImp c H \<Rightarrow> c = implies | _ \<Rightarrow> True"
    using it by (auto split: litem.splits)
  have "remove_params (ilength ?vars) n A = return (list_implies (rmhyps (integer_of_nat (npar p)) n p) C)"
    unfolding j by (simp only: A) (rule remove_params_lift_pre[OF items at HOL.refl nle impl])
  with r have A'': "A'' = list_implies (rmhyps (integer_of_nat (npar p)) n p) C" by (simp add: return_def)
  have clA: "closed_inst \<theta> (lift_pre p C)" using cl by (simp add: A)
  have "prf_ok V H [] Hs (prf_inst \<rho> \<theta> 0 (flatten_params_proof_a 0 0 n (lift_pre p C, integer_of_nat k)))
      (psubst \<rho> \<theta> 0 (lift_pre p C))"
  proof (rule fpp_a_gen[OF items at _ clA])
    show "cok (lift_pre p C)" using cA by (simp add: A)
    show "wty V [] (psubst \<rho> \<theta> 0 (lift_pre p C)) propT" using wA by (simp add: A)
    show "\<forall>h\<in>set Hs. wty V [] h propT" by (rule wHs)
    have sv': "map snd ?vars = map snd (strip_params (lift_pre p C))" using sv by (simp add: A)
    show "prf_ok V H (ptys \<rho> p @ []) (phs \<rho> \<theta> p @ map (incr_bv (integer_of_nat (npar p)) 0) Hs)
        (leafprf (0 + integer_of_nat (nhyp p)) (0 + integer_of_nat (npar p)) n (integer_of_nat k)) (psubst \<rho> \<theta> 0 C)"
      using fpp_leaf[OF items at clA lv sv' k wk] wA' eA' by (simp add: A' A'')
  qed simp
  then show ?thesis by (simp add: A)
qed



subsection \<open>Proofs by assumption\<close>

fun imp_prf_a :: "pterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "imp_prf_a (Const c U $ A $ B) i m =
    (if m = 0 then PBound i
     else if c = STR ''Pure.imp'' then AbsP (STR ''H'') (Some A) (imp_prf_a B (i + 1) (m - 1))
     else PBound i)"
| "imp_prf_a _ i m = PBound i"

fun all_prf_a :: "integer \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> prf" where
  "all_prf_a i m (Const c U $ Abs a T t) =
    (if c = STR ''Pure.all'' then Abst a (Some T) (all_prf_a i m t) else imp_prf_a (Const c U $ Abs a T t) (- i) m)"
| "all_prf_a i m t = imp_prf_a t (- i) m"

definition mk_asm_prf_a :: "pterm \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> prf" where
  "mk_asm_prf_a C i m = all_prf_a i m C"

fun abst_chain_a :: "binders \<Rightarrow> prf \<Rightarrow> prf" where
  "abst_chain_a [] q = q"
| "abst_chain_a ((a, T) # vs) q = Abst a (Some T) (abst_chain_a vs q)"

lemma prf_inst_abst_chain_a:
  "prf_inst \<rho> \<theta> lev (abst_chain_a vs q) =
    abst_chain_a (map (\<lambda>(a, T). (a, tsubst \<rho> T)) vs) (prf_inst \<rho> \<theta> (lev + integer_of_nat (length vs)) q)"
  by (induction vs arbitrary: lev) (auto simp: integer_of_nat_Suc algebra_simps)

lemma imp_prf_a_eq:
  "imp_prf_a B i m = mk_AbsPs (rev (fst (strip_assums_imp m [] B)))
    (PBound (i + integer_of_nat (length (fst (strip_assums_imp m [] B)))))"
proof (induction B i m rule: imp_prf_a.induct)
  case (1 c U A B i m)
  show ?case
  proof (cases "m \<noteq> 0 \<and> c = STR ''Pure.imp''")
    case True
    then have "strip_assums_imp m [] (Const c U $ A $ B) = strip_assums_imp (m - 1) [A] B"
      by (simp add: strip_assums_imp.simps[of m])
    then have "fst (strip_assums_imp m [] (Const c U $ A $ B)) = fst (strip_assums_imp (m - 1) [] B) @ [A]"
      by (subst (asm) strip_assums_imp_acc) simp
    with True "1.IH" show ?thesis by (simp add: integer_of_nat_Suc mk_AbsPs_def algebra_simps)
  next
    case False
    then show ?thesis by (auto simp: strip_assums_imp.simps[of m] mk_AbsPs_def)
  qed
qed (auto simp: strip_assums_imp.simps mk_AbsPs_def)

lemma imp_prf_a_ok:
  assumes "cok B" "wty V Ts (psubst \<rho> \<theta> 0 B) propT" "strip_assums_imp m [] B = (Gs, B0)"
    "0 \<le> i + integer_of_nat (length Gs)" "nat_of_integer (i + integer_of_nat (length Gs)) < length Gs"
    "tr (psubst \<rho> \<theta> 0 (Gs ! nat_of_integer (i + integer_of_nat (length Gs)))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 B0)"
    and cl: "closed_inst \<theta> B" and lev: "0 \<le> lev"
  shows "prf_ok V H Ts Hs (prf_inst \<rho> \<theta> lev (imp_prf_a B i m)) (psubst \<rho> \<theta> 0 B)"
proof -
  let ?k = "nat_of_integer (i + integer_of_nat (length Gs))"
  have B: "B = list_implies (rev Gs) B0" by (rule strip_assums_imp_list_implies[OF assms(3,1)])
  have w: "\<forall>P\<in>set (map (psubst \<rho> \<theta> 0) (rev Gs)). wty V Ts P propT" "wty V Ts (psubst \<rho> \<theta> 0 B0) propT"
    using assms(2) by (simp_all add: B psubst_list_implies' wty_list_implies_iff)
  have "(map (psubst \<rho> \<theta> 0) Gs @ Hs) ! ?k = psubst \<rho> \<theta> 0 (Gs ! ?k)" using assms(5) by (simp add: nth_append)
  moreover have "wty V Ts (psubst \<rho> \<theta> 0 (Gs ! ?k)) propT" using w(1) assms(5) by (simp add: rev_map[symmetric])
  ultimately have "prf_ok V H Ts (map (psubst \<rho> \<theta> 0) Gs @ Hs) (PBound (i + integer_of_nat (length Gs)))
      (psubst \<rho> \<theta> 0 (Gs ! ?k))"
    using prf_ok.PBound[of "i + integer_of_nat (length Gs)" "map (psubst \<rho> \<theta> 0) Gs @ Hs" V Ts H] assms(4,5) by simp
  then have pb: "prf_ok V H Ts (rev (map (psubst \<rho> \<theta> 0) (rev Gs)) @ Hs) (PBound (i + integer_of_nat (length Gs)))
      (psubst \<rho> \<theta> 0 B0)"
    using assms(6) w(2) by (auto simp: rev_map intro: prf_ok.conv)
  have m: "map (psubst \<rho> \<theta> lev) (rev Gs) = map (psubst \<rho> \<theta> 0) (rev Gs)"
    using cl lev by (auto simp: B closed_inst_def vars_list_implies intro!: psubst_closed_lev)
  have ie: "imp_prf_a B i m = mk_AbsPs (rev Gs) (PBound (i + integer_of_nat (length Gs)))"
    using imp_prf_a_eq[of B i m] assms(3) by simp
  have pB: "psubst \<rho> \<theta> 0 B = list_implies (map (psubst \<rho> \<theta> 0) (rev Gs)) (psubst \<rho> \<theta> 0 B0)"
    using B by (simp add: psubst_list_implies')
  show ?thesis unfolding ie pB prf_inst_mk_AbsPs using prf_ok_mk_AbsPs[OF pb w(1)] by (simp add: m)
qed


lemma all_prf_a_eq:
  "all_prf_a i m C = abst_chain_a (rev (fst (strip_assums_all [] C))) (imp_prf_a (snd (strip_assums_all [] C)) (- i) m)"
proof (induction i m C rule: all_prf_a.induct)
  case (1 i m c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    then have "strip_assums_all [] (Const c U $ Abs a T t) = strip_assums_all [(a, T)] t"
      by (simp add: strip_assums_all.simps[of _ "Const STR ''Pure.all'' U $ Abs a T t"])
    then have "strip_assums_all [] (Const c U $ Abs a T t) =
        (fst (strip_assums_all [] t) @ [(a, T)], snd (strip_assums_all [] t))"
      by (subst (asm) strip_assums_all_acc) simp
    with True "1.IH" show ?thesis by simp
  next
    case False
    then show ?thesis by (simp add: strip_assums_all.simps[of _ "Const c U $ Abs a T t"])
  qed
qed (simp_all add: strip_assums_all.simps)

lemma prf_ok_abst_chain_a:
  "prf_ok V H (rev (map (f \<circ> snd) vs) @ Ts) (map (incr_bv (integer_of_nat (length vs)) 0) Hs) q X \<Longrightarrow>
    prf_ok V H Ts Hs (abst_chain_a (map (\<lambda>(a, T). (a, f T)) vs) q) (list_forall (map (\<lambda>(a, T). (a, f T)) vs) X)"
proof (induction vs arbitrary: Ts Hs)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  obtain a T where v: "v = (a, T)" by (cases v)
  have e: "map (incr_bv (integer_of_nat (length vs)) 0) (map (incr_bv 1 0) Hs) =
      map (incr_bv (integer_of_nat (length (v # vs))) 0) Hs"
    by (simp add: incr_bv_comp0 integer_of_nat_Suc)
  have "prf_ok V H (rev (map (f \<circ> snd) vs) @ f T # Ts)
      (map (incr_bv (integer_of_nat (length vs)) 0) (map (incr_bv 1 0) Hs)) q X"
    unfolding e using Cons.prems by (simp add: v comp_def)
  from Cons.IH[OF this]
  have "prf_ok V H (f T # Ts) (map (incr_bv 1 0) Hs) (abst_chain_a (map (\<lambda>(a, T). (a, f T)) vs) q)
      (list_forall (map (\<lambda>(a, T). (a, f T)) vs) X)" .
  then show ?case by (simp add: v) (intro prf_ok.Abst, simp_all)
qed

lemma mk_asm_prf_a_ok:
  assumes "cok A" "closed_inst \<theta> A" "wty V Ts (psubst \<rho> \<theta> 0 A) propT"
    "assum_problems m A = (params, asms, concl)" "1 \<le> n" "n \<le> integer_of_nat (length asms)"
    "tr (psubst \<rho> \<theta> 0 (asms ! (nat_of_integer n - 1))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 concl)"
  shows "prf_ok V H Ts Hs (prf_inst \<rho> \<theta> 0 (mk_asm_prf_a A n m)) (psubst \<rho> \<theta> 0 A)"
proof -
  obtain A' Gs where sa: "strip_assums_all [] A = (params, A')" and si: "strip_assums_imp m [] A' = (Gs, concl)"
    and asms: "asms = rev Gs"
    using assms(4) unfolding assum_problems_def
    by (cases "strip_assums_all [] A"; cases "strip_assums_imp m [] (snd (strip_assums_all [] A))") auto
  from strip_assums_all_list_forall[OF sa assms(1)] have A: "A = list_forall (rev params) A'" and cA': "cok A'"
    by auto
  let ?vs = "rev params"
  have cl: "closed_inst \<theta> A'" using assms(2) by (simp add: closed_inst_def A)
  have psA: "psubst \<rho> \<theta> 0 A = list_forall (map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs) (psubst \<rho> \<theta> 0 A')"
    using cl psubst_closed_lev[of A' \<theta> "integer_of_nat (length ?vs)" \<rho>]
    by (simp add: A psubst_list_forall closed_inst_def)
  let ?Ts = "rev (map (tsubst \<rho> \<circ> snd) ?vs) @ Ts"
  have rv: "rev (map snd (map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs)) = rev (map (tsubst \<rho> \<circ> snd) ?vs)"
    by (induction params) auto
  have wA': "wty V ?Ts (psubst \<rho> \<theta> 0 A') propT"
    using assms(3) has_type_list_forall_body[of V Ts "map (\<lambda>(a, T). (a, tsubst \<rho> T)) ?vs" "psubst \<rho> \<theta> 0 A'"]
    by (simp only: psA rv) (auto simp: wty_def)
  have len: "length asms = length Gs" by (simp add: asms)
  have k: "nat_of_integer (- n + integer_of_nat (length Gs)) = length Gs - nat_of_integer n"
    "nat_of_integer (- n + integer_of_nat (length Gs)) < length Gs"
    using assms(5,6) len by (simp_all add: integer_reps integer_of_nat.rep_eq nat_diff_distrib)
  have "Gs ! (length Gs - nat_of_integer n) = asms ! (nat_of_integer n - 1)"
    using assms(5,6) len by (simp add: asms rev_nth integer_reps integer_of_nat.rep_eq)
  then have "prf_ok V H ?Ts (map (incr_bv (integer_of_nat (length ?vs)) 0) Hs)
      (prf_inst \<rho> \<theta> (integer_of_nat (length ?vs)) (imp_prf_a A' (- n) m)) (psubst \<rho> \<theta> 0 A')"
    using imp_prf_a_ok[OF cA' wA' si, where i = "- n" and lev = "integer_of_nat (length ?vs)"] assms(5,6,7) k len cl
    by (simp add: integer_reps integer_of_nat.rep_eq)
  from prf_ok_abst_chain_a[OF this] show ?thesis
    by (simp add: psA mk_asm_prf_a_def all_prf_a_eq sa prf_inst_abst_chain_a comp_def)
qed




subsection \<open>The composed proof\<close>

lemma prf_ok_compose_a:
  assumes S: "prf_ok V H [] [] sp (list_implies (Bs @ [Bi]) C)"
    and R: "prf_ok V H [] [] rp (list_implies (Pre @ Olds) B)"
    and BBi: "tr B \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr Bi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. wty V [] N propT"
    and NB: "\<forall>j<length Bs. tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Bs ! j)"
    and args: "list_all2 (\<lambda>a P. prf_ok V H [] (rev Ns) a P) qs (Pre @ Olds)"
  shows "prf_ok V H [] [] (mk_AbsPs Ns (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp qs))) (list_implies Ns C)"
proof -
  let ?lb = "length Bs" and ?la = "length As"
  have wS: "\<forall>X\<in>set (Bs @ [Bi]). wty V [] X propT" "wty V [] C propT"
    using wty_list_implies[OF prf_ok_wty[OF S]] by auto
  have wR: "wty V [] B propT" using wty_list_implies[OF prf_ok_wty[OF R]] by auto
  have S': "prf_ok V H [] (rev Ns) sp (list_implies Bs (list_implies [Bi] C))"
    using prf_ok_append[OF S, of "rev Ns"] by (simp add: list_implies_append)
  have "list_all2 (prf_ok V H [] (rev Ns)) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]) Bs"
  proof (rule list_all2_all_nthI)
    fix k assume k: "k < length (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])"
    then have k': "k < ?lb" by simp
    have j: "?lb + ?la - 1 - k < length (rev Ns)" using k' Ns(1) by simp
    then have "rev Ns ! (?lb + ?la - 1 - k) \<in> set Ns" by (metis nth_mem set_rev)
    then have "prf_ok V H [] (rev Ns) (PBound (integer_of_nat (?lb + ?la - 1 - k))) (rev Ns ! (?lb + ?la - 1 - k))"
      using prf_ok.PBound[of "integer_of_nat (?lb + ?la - 1 - k)" "rev Ns" V "[]" H] j Ns(2) by simp
    moreover have "rev Ns ! (?lb + ?la - 1 - k) = Ns ! k" using rev_nth_downto[OF Ns(1) k'] .
    moreover have "tr (Ns ! k) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Bs ! k)" using NB k' by blast
    moreover have "wty V [] (Bs ! k) propT" using wS k' by auto
    ultimately show "prf_ok V H [] (rev Ns) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb] ! k) (Bs ! k)"
      using k' by (auto intro: prf_ok.conv)
  qed simp
  with S' have q: "prf_ok V H [] (rev Ns)
      (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])) (implies $ Bi $ C)"
    by (auto intro: prf_ok_proof_combP)
  have "prf_ok V H [] (rev Ns) (proof_combP rp qs) B"
    using prf_ok_append[OF R, of "rev Ns"] args by (auto intro: prf_ok_proof_combP)
  then have "prf_ok V H [] (rev Ns) (proof_combP rp qs) Bi" using BBi wS by (auto intro: prf_ok.conv)
  with q have "prf_ok V H [] (rev Ns @ []) (PAppp (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]))
      (proof_combP rp qs)) C" by (auto intro: prf_ok.PAppp)
  then show ?thesis using Ns(2) by (auto simp: downto_PBound intro: prf_ok_mk_AbsPs)
qed


end

end
