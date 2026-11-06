section \<open>Composition of tight proofs\<close>

theory ZProof_Bicompose
  imports ZProof_Inst
begin

subsection \<open>Decoding\<close>

lemma class_suffix_imp: "c + STR ''_class'' \<noteq> STR ''Pure.imp''"
proof
  assume "c + STR ''_class'' = STR ''Pure.imp''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.imp''))" by simp
  then show False by (simp add: plus_literal.rep_eq String.Literal.rep_eq zero_literal.rep_eq)
qed

lemma class_suffix_all: "c + STR ''_class'' \<noteq> STR ''Pure.all''"
proof
  assume "c + STR ''_class'' = STR ''Pure.all''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.all''))" by simp
  then show False by (simp add: plus_literal.rep_eq String.Literal.rep_eq zero_literal.rep_eq)
qed

context pure_sig
begin

lemma zprf_tr_ZAbsps: "zprf_tr (ZAbsps ts p) = foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (Some \<circ> zdec) ts) (zprf_tr p)"
  by (induction ts) (simp_all add: ZAbsps_def)

lemma zprf_tr_ZAppts: "zprf_tr (ZAppts p ts) = proof_combt (zprf_tr p) (map zdec ts)"
  by (induction ts arbitrary: p) (simp_all add: ZAppts_def proof_combt_def)

lemma zprf_tr_leaf:
  "zprf_tr (ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0))) (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0))) (map PBound (removeAll (i - n) (downto (i - 1) 0)))"
  by (simp add: zprf_tr_ZAppps zprf_tr_ZAppts comp_def)

lemma match_of_class_App2: "match_of_class (t $ A $ B) = None"
  by (simp add: match_of_class_def split: pterm.splits)

lemma match_of_class_Abs: "match_of_class (t $ Abs a T b) = None"
  by (simp add: match_of_class_def split: pterm.splits)

abbreviation is_imp :: "pterm \<Rightarrow> bool" where
  "is_imp t \<equiv> \<exists>U A B. t = Const STR ''Pure.imp'' U $ A $ B"

abbreviation is_all :: "pterm \<Rightarrow> bool" where
  "is_all t \<equiv> \<exists>U a T b. t = Const STR ''Pure.all'' U $ Abs a T b"

lemma zterm_of_imp:
  assumes "zterm_of ztargs (Const STR ''Pure.imp'' U $ A $ B) = returnZ z"
  shows "\<exists>zA zB. z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zA) zB \<and> zterm_of ztargs A = returnZ zA \<and>
    zterm_of ztargs B = returnZ zB"
proof -
  have nc: "Const STR ''Pure.imp'' U $ A \<noteq> mk_of_class T c" for T c
    using class_suffix_imp[of c] by (auto simp: mk_of_class_def class_suffix_def)
  from assms nc show ?thesis
    by (auto simp: match_of_class_App2 bindZ_eq_returnZ liftMZ_eq_returnZ ztargs_def return_def
      split: option.splits)
qed

lemma zterm_of_all:
  assumes "zterm_of ztargs (Const STR ''Pure.all'' U $ Abs a T b) = returnZ z"
  shows "\<exists>U0 zb. z = ZApp (ZConst1 STR ''Pure.all'' U0) (ZAbs a (ztyp_of T) zb) \<and> zterm_of ztargs b = returnZ zb"
  using assms
  by (auto simp: match_of_class_Abs bindZ_eq_returnZ liftMZ_eq_returnZ ztargs_def return_def raise_def
    split: ptyp.splits list.splits if_splits)

lemma aflatten_leaf:
  "\<not> is_imp t \<Longrightarrow> \<not> is_all t \<Longrightarrow> aflatten_params_proof fA fT i j n (t, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0))) (map PBound (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(fA, fT, i, j, n, (t, k))" rule: aflatten_params_proof.cases) auto

lemma zflatten_leaf:
  "\<not> is_imp (zdec z) \<Longrightarrow> \<not> is_all (zdec z) \<Longrightarrow> zflatten_params_proof i j n (z, k) =
    ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0))) (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(i, j, n, (z, k))" rule: zflatten_params_proof.cases) auto

lemma zprf_tr_zflatten_params_proof:
  "zterm_of ztargs t = returnZ z \<Longrightarrow> zdec z = t \<Longrightarrow>
    zprf_tr (zflatten_params_proof i j n (z, k)) = aflatten_params_proof Some Some i j n (t, k)"
proof (induction t arbitrary: z i j rule: measure_induct_rule[of size])
  case (less t)
  consider (imp) U A B where "t = Const STR ''Pure.imp'' U $ A $ B"
    | (all) U a T b where "t = Const STR ''Pure.all'' U $ Abs a T b"
    | (leaf) "\<not> is_imp t" "\<not> is_all t"
    by blast
  then show ?case
  proof cases
    case imp
    from zterm_of_imp[OF less.prems(1)[unfolded imp]] obtain zA zB where
      z: "z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zA) zB" and zB: "zterm_of ztargs B = returnZ zB" by blast
    have d: "zdec zA = A" "zdec zB = B" using less.prems(2) imp z by simp_all
    have "zprf_tr (zflatten_params_proof (i + 1) j n (zB, k)) = aflatten_params_proof Some Some (i + 1) j n (B, k)"
      by (rule less.IH[OF _ zB d(2)]) (simp add: imp)
    then show ?thesis by (simp add: imp z d(1))
  next
    case all
    from zterm_of_all[OF less.prems(1)[unfolded all]] obtain U0 zb where
      z: "z = ZApp (ZConst1 STR ''Pure.all'' U0) (ZAbs a (ztyp_of T) zb)" and zb: "zterm_of ztargs b = returnZ zb"
      by blast
    have d: "typ_of (ztyp_of T) = T" "zdec zb = b" using less.prems(2) all z by simp_all
    have "zprf_tr (zflatten_params_proof i (j + 1) n (zb, k)) = aflatten_params_proof Some Some i (j + 1) n (b, k)"
      by (rule less.IH[OF _ zb d(2)]) (simp add: all)
    then show ?thesis by (simp add: all z d(1))
  next
    case leaf
    then show ?thesis
      using less.prems(2) by (simp add: zflatten_leaf aflatten_leaf zprf_tr_leaf)
  qed
qed

subsection \<open>Normalisation preserves the outer structure\<close>

lemma beta_norm_term_App:
  "(\<And>a T b. f \<noteq> ZAbs a T b) \<Longrightarrow> beta_norm_term (ZApp f u) = Option.bind (beta_norm_term f) (\<lambda>nf.
    case nf of ZAbs _ _ body \<Rightarrow> beta_norm_term (subst_term_bound u body)
    | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZApp nf nu)))"
  by (subst beta_norm_term.simps) (cases f; auto)

lemma beta_norm_term_Const0: "beta_norm_term (ZConst0 c) = Some (ZConst0 c)"
  by (subst beta_norm_term.simps) simp

lemma beta_norm_term_Const1: "beta_norm_term (ZConst1 c T) = Some (ZConst1 c T)"
  by (subst beta_norm_term.simps) simp

lemma beta_norm_term_Abs: "beta_norm_term (ZAbs a T b) = Option.bind (beta_norm_term b) (\<lambda>b'. Some (ZAbs a T b'))"
  by (subst beta_norm_term.simps) simp

lemma znorm_term_aux_App:
  "(\<And>a T b. f \<noteq> ZAbs a T b) \<Longrightarrow> znorm_term_aux ((ta, env), ZApp f u) = bindZ (znorm_term_aux ((ta, env), f)) (\<lambda>nf.
    case nf of ZAbs _ _ body \<Rightarrow> znorm_term_aux ((ta, env), subst_term_bound u body)
    | _ \<Rightarrow> bindZ (znorm_term_aux ((ta, env), u)) (\<lambda>nu. returnZ (ZApp nf nu)))"
  by (subst znorm_term_aux.simps) (unfold prod.sel, cases f; auto)

lemma znorm_term_aux_Const0: "znorm_term_aux ((ta, env), ZConst0 c) = returnZ (ZConst0 c)"
  by (subst znorm_term_aux.simps) simp

lemma znorm_term_aux_Const1:
  "znorm_term_aux ((ta, env), ZConst1 c T) = bindZ (znorm_type (tyenv env) T) (\<lambda>T'. returnZ (ZConst1 c T'))"
  by (subst znorm_term_aux.simps) simp

lemma znorm_term_aux_Abs:
  "znorm_term_aux ((ta, env), ZAbs a T b) =
    bindZ (znorm_type (tyenv env) T) (\<lambda>T'. bindZ (znorm_term_aux ((ta, env), b)) (\<lambda>b'. returnZ (ZAbs a T' b')))"
  by (subst znorm_term_aux.simps) simp

lemma znorm_term_imp:
  assumes "znorm_term ta env (ZApp (ZApp (ZConst0 c) A) B) = returnZ R"
  shows "\<exists>A' B'. R = ZApp (ZApp (ZConst0 c) A') B' \<and> znorm_term ta env A = returnZ A' \<and>
    znorm_term ta env B = returnZ B'"
proof (cases "env_is_empty env")
  case True
  with assms have "beta_norm_term (ZApp (ZApp (ZConst0 c) A) B) = Some R"
    by (simp add: znorm_term_def liftOZ_eq_returnZ)
  with True show ?thesis
    by (auto simp: beta_norm_term_App beta_norm_term_Const0 bind_eq_Some_conv znorm_term_def liftOZ_eq_returnZ)
next
  case False
  with assms have "znorm_term_aux ((ta, env), ZApp (ZApp (ZConst0 c) A) B) = returnZ R"
    by (simp add: znorm_term_def)
  with False show ?thesis
    by (auto simp: znorm_term_aux_App znorm_term_aux_Const0 bindZ_eq_returnZ znorm_term_def)
qed

lemma znorm_term_all:
  assumes "znorm_term ta env (ZApp (ZConst1 c U) (ZAbs a T b)) = returnZ R"
  shows "\<exists>U' T' b'. R = ZApp (ZConst1 c U') (ZAbs a T' b') \<and> znorm_term ta env b = returnZ b' \<and>
    (if env_is_empty env then T' = T else znorm_type (tyenv env) T = returnZ T')"
proof (cases "env_is_empty env")
  case True
  with assms have "beta_norm_term (ZApp (ZConst1 c U) (ZAbs a T b)) = Some R"
    by (simp add: znorm_term_def liftOZ_eq_returnZ)
  with True show ?thesis
    by (auto simp: beta_norm_term_App beta_norm_term_Const1 beta_norm_term_Abs bind_eq_Some_conv
      znorm_term_def liftOZ_eq_returnZ)
next
  case False
  with assms have "znorm_term_aux ((ta, env), ZApp (ZConst1 c U) (ZAbs a T b)) = returnZ R"
    by (simp add: znorm_term_def)
  with False show ?thesis
    by (auto simp: znorm_term_aux_App znorm_term_aux_Const1 znorm_term_aux_Abs bindZ_eq_returnZ znorm_term_def)
qed

subsection \<open>Proofs by assumption\<close>

lemma zimp_prf_list_implies:
  assumes "zterm_of ztargs (list_implies as B) = returnZ Z" "zdec Z = list_implies as B"
    and "znorm_term ztargs env Z = returnZ Z'"
  shows "\<exists>hs. list_all2 (\<lambda>H H'. \<exists>zH. zterm_of ztargs H = returnZ zH \<and> zdec zH = H \<and>
      znorm_term ztargs env zH = returnZ H') as hs \<and>
    zprf_tr (zimp_prf Z' j (ilength as)) = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map zdec hs) (PBound (j + ilength as))"
  using assms
proof (induction as arbitrary: j Z Z')
  case Nil
  have "zimp_prf Z' j 0 = ZBoundp j" by (cases "(Z', j, 0::integer)" rule: zimp_prf.cases) auto
  then show ?case by simp
next
  case (Cons H as)
  from zterm_of_imp[OF Cons.prems(1)[simplified implies_def list_implies.simps]] obtain zH zR where
    z: "Z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zH) zR" and zH: "zterm_of ztargs H = returnZ zH"
    and zR: "zterm_of ztargs (list_implies as B) = returnZ zR" by blast
  have d: "zdec zH = H" "zdec zR = list_implies as B" using Cons.prems(2) z by (simp_all add: implies_def)
  from znorm_term_imp[OF Cons.prems(3)[unfolded z]] obtain H' R' where
    z': "Z' = ZApp (ZApp (ZConst0 STR ''Pure.imp'') H') R'" and nH: "znorm_term ztargs env zH = returnZ H'"
    and nR: "znorm_term ztargs env zR = returnZ R'" by blast
  from Cons.IH[OF zR d(2) nR, of "j + 1"] obtain hs where hs: "list_all2 (\<lambda>H H'. \<exists>zH. zterm_of ztargs H = returnZ zH \<and>
      zdec zH = H \<and> znorm_term ztargs env zH = returnZ H') as hs"
    and p: "zprf_tr (zimp_prf R' (j + 1) (ilength as)) = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map zdec hs) (PBound (j + 1 + ilength as))"
    by blast
  have "ilength as + 1 \<noteq> 0" using ilength_nonneg[of as] by linarith
  then have "zimp_prf Z' j (ilength (H # as)) = ZAbsp (STR ''H'') H' (zimp_prf R' (j + 1) (ilength as))"
    by (simp add: z')
  with p hs zH d(1) nH show ?case
    by (intro exI[of _ "H' # hs"]) (auto simp: add.commute add.left_commute)
qed

lemma zall_prf_list_forall:
  assumes "zterm_of ztargs (list_forall qs X) = returnZ Z" "zdec Z = list_forall qs X"
    and "znorm_term ztargs env Z = returnZ Z'" and X: "is_imp X"
  shows "\<exists>Ts' X'. list_all2 (\<lambda>T T'. typ_of (ztyp_of T) = T \<and> (if env_is_empty env then T' = ztyp_of T
        else znorm_type (tyenv env) (ztyp_of T) = returnZ T')) (map snd qs) Ts' \<and>
      (\<exists>zX. zterm_of ztargs X = returnZ zX \<and> zdec zX = X \<and> znorm_term ztargs env zX = returnZ X') \<and>
      (\<forall>i k. zprf_tr (zall_prf i k Z') =
        foldr (\<lambda>(a, T) p. Abst a (Some T) p) (zip (map fst qs) (map typ_of Ts')) (zprf_tr (zimp_prf X' (- i) k)))"
  using assms(1-3)
proof (induction qs arbitrary: Z Z')
  case Nil
  from X obtain U A B where XU: "X = Const STR ''Pure.imp'' U $ A $ B" by blast
  from zterm_of_imp[OF Nil.prems(1)[simplified XU list_forall.simps]] obtain zA zB where
    z: "Z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zA) zB" by blast
  from znorm_term_imp[OF Nil.prems(3)[unfolded z]] obtain A' B' where
    z': "Z' = ZApp (ZApp (ZConst0 STR ''Pure.imp'') A') B'" by blast
  have "zall_prf i k Z' = zimp_prf Z' (- i) k" for i k by (simp add: z')
  then show ?case using Nil.prems by (intro exI[of _ "[]"] exI[of _ Z']) auto
next
  case (Cons q qs)
  obtain a T where q: "q = (a, T)" by (cases q)
  from zterm_of_all[OF Cons.prems(1)[simplified q list_forall.simps all_const_def]] obtain U0 zb where
    z: "Z = ZApp (ZConst1 STR ''Pure.all'' U0) (ZAbs a (ztyp_of T) zb)"
    and zb: "zterm_of ztargs (list_forall qs X) = returnZ zb" by blast
  have d: "typ_of (ztyp_of T) = T" "zdec zb = list_forall qs X"
    using Cons.prems(2) z by (simp_all add: q all_const_def)
  from znorm_term_all[OF Cons.prems(3)[unfolded z]] obtain U' T' b' where
    z': "Z' = ZApp (ZConst1 STR ''Pure.all'' U') (ZAbs a T' b')" and nb: "znorm_term ztargs env zb = returnZ b'"
    and T': "if env_is_empty env then T' = ztyp_of T else znorm_type (tyenv env) (ztyp_of T) = returnZ T'"
    by blast
  from Cons.IH[OF zb d(2) nb] obtain Ts' X' where IH: "list_all2 (\<lambda>T T'. typ_of (ztyp_of T) = T \<and>
      (if env_is_empty env then T' = ztyp_of T else znorm_type (tyenv env) (ztyp_of T) = returnZ T')) (map snd qs) Ts'"
    "\<exists>zX. zterm_of ztargs X = returnZ zX \<and> zdec zX = X \<and> znorm_term ztargs env zX = returnZ X'"
    "\<forall>i k. zprf_tr (zall_prf i k b') =
      foldr (\<lambda>(a, T) p. Abst a (Some T) p) (zip (map fst qs) (map typ_of Ts')) (zprf_tr (zimp_prf X' (- i) k))"
    by blast
  show ?case
    using IH d(1) T' by (intro exI[of _ "T' # Ts'"] exI[of _ X']) (simp add: z' q)
qed

end

lemma prf_aeq_foldr_Abst:
  "map snd xs = map snd ys \<Longrightarrow> prf_aeq p q \<Longrightarrow>
    prf_aeq (foldr (\<lambda>(a, T) p. Abst a (Some T) p) xs p) (foldr (\<lambda>(a, T) p. Abst a (Some T) p) ys q)"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then obtain y ys' where "ys = y # ys'" "snd x = snd y" "map snd xs = map snd ys'" by (cases ys) auto
  with Cons show ?case by (cases x; cases y) (auto intro: prf_aeq.Abst)
qed simp

lemma prf_aeq_foldr_AbsP:
  "list_all2 ann_eq ts ts' \<Longrightarrow> prf_aeq p q \<Longrightarrow>
    prf_aeq (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts p) (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts' q)"
  by (induction ts ts' rule: list_all2_induct) (auto intro: prf_aeq.AbsP)

context prf_sig
begin

lemma prf_ap_foldr_Abst:
  "prf_ap \<rho> \<sigma> (foldr (\<lambda>(a, T) p. Abst a (Some T) p) xs p) =
    foldr (\<lambda>(a, T) p. Abst a (Some T) p) (map (\<lambda>(a, T). (a, tsubst \<rho> T)) xs) (prf_ap \<rho> \<sigma> p)"
  by (induction xs) auto

lemma prf_ap_foldr_AbsP_Some:
  "prf_ap \<rho> \<sigma> (foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) As p) =
    foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map (ap \<rho> \<sigma>) As) (prf_ap \<rho> \<sigma> p)"
  by (induction As) auto

text \<open>
  The tight proof of a premise by assumption, built from the normalised premise, agrees with
  the classic one built from the premise:
\<close>

theorem zall_prf_aeq:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and en: "eneg env"
    and Z: "zterm_of ztargs A = returnZ Z" "zdec Z = A" and Z': "znorm_term ztargs env Z = returnZ Z'"
    and A: "A = list_forall qs (list_implies as B)" and as: "as \<noteq> []" "ilength as \<le> m"
      "ilength as < m \<longrightarrow> dest_imp B = None"
    and hyps: "\<forall>H\<in>set as. ap \<rho>' \<sigma>1 H = ap \<rho>' \<sigma>' H"
  shows "prf_aeq (prf_ap \<rho>' \<sigma>1 (aall_prf Some Some i m A)) (prf_ap \<rho> \<sigma> (zprf_tr (zall_prf i (ilength as) Z')))"
proof -
  note i = iextD[OF ie]
  have X: "is_imp (list_implies as B)" using as(1) by (cases as) (auto simp: implies_def)
  from zall_prf_list_forall[OF Z[unfolded A] Z' X] obtain Ts' X' where
    Ts': "list_all2 (\<lambda>T T'. typ_of (ztyp_of T) = T \<and> (if env_is_empty env then T' = ztyp_of T
        else znorm_type (tyenv env) (ztyp_of T) = returnZ T')) (map snd qs) Ts'"
    and zX: "\<exists>zX. zterm_of ztargs (list_implies as B) = returnZ zX \<and> zdec zX = list_implies as B \<and>
      znorm_term ztargs env zX = returnZ X'"
    and ZP: "\<And>i k. zprf_tr (zall_prf i k Z') =
      foldr (\<lambda>(a, T) p. Abst a (Some T) p) (zip (map fst qs) (map typ_of Ts')) (zprf_tr (zimp_prf X' (- i) k))"
    by blast
  from zX obtain zX where zX: "zterm_of ztargs (list_implies as B) = returnZ zX" "zdec zX = list_implies as B"
    "znorm_term ztargs env zX = returnZ X'" by blast
  from zimp_prf_list_implies[OF zX, of "- i"] obtain hs where
    hs: "list_all2 (\<lambda>H H'. \<exists>zH. zterm_of ztargs H = returnZ zH \<and> zdec zH = H \<and> znorm_term ztargs env zH = returnZ H') as hs"
    and IP: "zprf_tr (zimp_prf X' (- i) (ilength as)) = foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) (map zdec hs) (PBound (- i + ilength as))"
    by blast
  have dX: "dest_all (list_implies as B) = None" using as(1) by (cases as) (auto simp: implies_def)
  have cl: "aall_prf Some Some i m A = foldr (\<lambda>(a, T) p. Abst a (Some T) p) qs
      (foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) as (PBound (- i + ilength as)))"
    unfolding A all_prf_list_forall[OF dX] imp_prf_list_implies[OF as(2,3)]
    by (induction qs) auto
  have ty: "map snd (map (\<lambda>(a, T). (a, tsubst \<rho>' T)) qs) =
      map snd (map (\<lambda>(a, T). (a, tsubst \<rho> T)) (zip (map fst qs) (map typ_of Ts')))"
  proof -
    have "length Ts' = length qs" using list_all2_lengthD[OF Ts'] by simp
    moreover have "tsubst \<rho>' (snd (qs ! j)) = tsubst \<rho> (typ_of (Ts' ! j))" if "j < length qs" for j
    proof -
      have r: "typ_of (ztyp_of (snd (qs ! j))) = snd (qs ! j)" and
        n: "if env_is_empty env then Ts' ! j = ztyp_of (snd (qs ! j))
          else znorm_type (tyenv env) (ztyp_of (snd (qs ! j))) = returnZ (Ts' ! j)"
      proof -
        have "j < length (map snd qs)" using that by simp
        from list_all2_nthD[OF Ts' this, unfolded nth_map[OF that]] show
          "typ_of (ztyp_of (snd (qs ! j))) = snd (qs ! j)"
          "if env_is_empty env then Ts' ! j = ztyp_of (snd (qs ! j))
            else znorm_type (tyenv env) (ztyp_of (snd (qs ! j))) = returnZ (Ts' ! j)" by blast+
      qed
      show ?thesis
      proof (cases "env_is_empty env")
        case True
        then have "\<rho>' = \<rho>" by (intro ext) (simp add: i(6) env_is_empty_def vt_is_empty_lookup)
        with True n r show ?thesis by simp
      next
        case False
        with n have "znorm_type (tyenv env) (ztyp_of (snd (qs ! j))) = returnZ (Ts' ! j)" by simp
        from znorm_type_success[OF this tac(1) enegD(1)[OF en]] r
        have "tcons (tyenv env) (snd (qs ! j))" "typ_of (Ts' ! j) = tnorm (tyenv env) (snd (qs ! j))" by simp_all
        then show ?thesis using iext_tnorm[OF ie tac] by simp
      qed
    qed
    ultimately show ?thesis by (auto intro: nth_equalityI simp: case_prod_beta)
  qed
  have an: "list_all2 ann_eq (map (Some \<circ> ap \<rho>' \<sigma>1) as) (map (Some \<circ> ap \<rho> \<sigma> \<circ> zdec) hs)"
  proof (rule list_all2_all_nthI)
    show "length (map (Some \<circ> ap \<rho>' \<sigma>1) as) = length (map (Some \<circ> ap \<rho> \<sigma> \<circ> zdec) hs)"
      using list_all2_lengthD[OF hs] by simp
    fix j assume j: "j < length (map (Some \<circ> ap \<rho>' \<sigma>1) as)"
    from list_all2_nthD[OF hs, of j] j obtain zH where
      zH: "zterm_of ztargs (as ! j) = returnZ zH" "zdec zH = as ! j" "znorm_term ztargs env zH = returnZ (hs ! j)"
      by auto
    have "ap \<rho> \<sigma> (zdec (hs ! j)) \<approx> ap \<rho>' \<sigma>' (zdec zH)" using znorm_term_ok[OF zH(3) ie tac en] by blast
    moreover have "ap \<rho>' \<sigma>1 (as ! j) = ap \<rho>' \<sigma>' (as ! j)" using hyps j by simp
    ultimately show "ann_eq (map (Some \<circ> ap \<rho>' \<sigma>1) as ! j) (map (Some \<circ> ap \<rho> \<sigma> \<circ> zdec) hs ! j)"
      using j zH(2) list_all2_lengthD[OF hs] by (simp add: ann_eq_def ueq_sym)
  qed
  have "prf_aeq (foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (Some \<circ> ap \<rho>' \<sigma>1) as) (PBound (- i + ilength as)))
      (foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (Some \<circ> ap \<rho> \<sigma> \<circ> zdec) hs) (PBound (- i + ilength as)))"
    by (rule prf_aeq_foldr_AbsP[OF an prf_aeq.refl])
  then have "prf_aeq (prf_ap \<rho>' \<sigma>1 (foldr (\<lambda>A p. AbsP (STR ''H'') (Some A) p) as (PBound (- i + ilength as))))
      (prf_ap \<rho> \<sigma> (zprf_tr (zimp_prf X' (- i) (ilength as))))"
    unfolding IP prf_ap_foldr_AbsP_Some by (simp add: foldr_map comp_def)
  from prf_aeq_foldr_Abst[OF ty this] show ?thesis
    by (simp add: cl ZP prf_ap_foldr_Abst)
qed

end

subsection \<open>Validity of tight proofs\<close>

context prf_sig
begin

text \<open>A tight proof is valid if it is valid up to the types of its class proofs:\<close>

definition zvalid :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm set \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> zproof \<Rightarrow> pterm \<Rightarrow> bool" where
  "zvalid ax H tps p \<phi> \<longleftrightarrow> (\<exists>w. pcerase w = pcerase (zprf_tr p) \<and> prf_valid ax H tps w \<phi>)"

lemma ap_tcong: "(\<And>v S. (v, S) \<in> ttvars t \<Longrightarrow> \<rho> v S = \<rho>' v S) \<Longrightarrow> ap \<rho> \<sigma> t = ap \<rho>' \<sigma> t"
  unfolding ap_def by (rule arg_cong[of _ _ "vsubst \<sigma>"], rule inst_cong, rule tsubst_cong) (auto simp: ttvars_def)

lemma ap_zdec_zren_term:
  "-1 \<le> m \<Longrightarrow> ap \<rho> \<sigma> (zdec (zren_term r m t)) = ap \<rho> (rsubst m (fst r) \<sigma>) (zdec t)"
proof (induction r m t rule: zren_term.induct)
  case (1 r m x i T)
  then show ?case by (auto simp: rsubst_def)
qed (simp_all add: of_class_def)

lemma zprf_all_True: "(\<And>t. P t) \<Longrightarrow> zprf_all P (\<lambda>_. True) q"
  by (induction q) auto

lemma zren_proof_aeq:
  assumes "zren_proof rn m q = returnZ q'" "pcerase w = pcerase (zprf_tr q)" "-1 \<le> m"
  shows "prf_aeq (prf_ap \<rho> (rsubst m (fst rn) \<sigma>) w) (prf_ap \<rho> \<sigma> (prf_reclass (zprf_tr q') (pclass_map (\<lambda>T. T) w)))"
proof (rule map_zproof_aeq[OF assms(1)[unfolded zren_proof_def] _ _ _ assms(2)])
  show "zprf_all (\<lambda>t. \<forall>t'. returnZ (zren_term rn m t) = returnZ t' \<longrightarrow>
      ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> (rsubst m (fst rn) \<sigma>) (zdec t)) (\<lambda>_. True) q"
    by (rule zprf_all_True) (simp add: ap_zdec_zren_term[OF assms(3)] ueq_refl)
qed simp_all

lemma pcerase_proof_combP: "pcerase (proof_combP p qs) = proof_combP (pcerase p) (map pcerase qs)"
  by (induction qs arbitrary: p) (simp_all add: proof_combP_def)

lemma pcerase_foldr_AbsP:
  "pcerase (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts p) = foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts (pcerase p)"
  by (induction ts) simp_all

lemma prf_ap_foldr_AbsP_ann:
  "prf_ap \<rho> \<sigma> (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts p) =
    foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (map_option (ap \<rho> \<sigma>)) ts) (prf_ap \<rho> \<sigma> p)"
  by (induction ts) simp_all

lemma list_all2_choice: "\<forall>x\<in>set xs. \<exists>y. P x y \<Longrightarrow> \<exists>ys. list_all2 P xs ys"
  by (induction xs) (auto intro: list_all2_Cons)

lemma zprf_all_ZAppts: "zprf_all P Q (ZAppts p ts) \<longleftrightarrow> zprf_all P Q p \<and> (\<forall>t\<in>set ts. P t)"
  by (induction ts arbitrary: p) (auto simp: ZAppts_def)

lemma zprf_all_ZAppps: "zprf_all P Q (ZAppps p qs) \<longleftrightarrow> zprf_all P Q p \<and> (\<forall>q\<in>set qs. zprf_all P Q q)"
  by (induction qs arbitrary: p) (auto simp: ZAppps_def)

lemma zprf_all_zflatten_params_proof:
  "zprf_all (\<lambda>t. zvars t \<subseteq> zvars z) (\<lambda>_. True) (zflatten_params_proof i j n (z, k))"
proof (induction i j n "(z, k)" arbitrary: z rule: zflatten_params_proof.induct)
  case (1 i j n c A B)
  show ?case using "1.hyps" by (auto simp: zprf_all_ZAppts zprf_all_ZAppps elim!: zprf_all_mono)
next
  case (2 i j n c U a T t)
  show ?case using "2.hyps" by (auto simp: zprf_all_ZAppts zprf_all_ZAppps elim!: zprf_all_mono)
qed (auto simp: zprf_all_ZAppts zprf_all_ZAppps)

lemma zvars_zterm_of:
  "zterm_of ta t = returnZ z \<Longrightarrow> (x, Z) \<in> zvars z \<Longrightarrow> snd x = -1 \<or> (\<exists>T. (x, T) \<in> vars t \<and> Z = ztyp_of T)"
proof (induction t arbitrary: z)
  case (Const c T)
  then obtain Ts where "z = (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))"
    by (auto simp: bindZ_eq_returnZ)
  moreover have "zvars (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts)) = {}"
    by (cases Ts rule: remdups_adj.cases) simp_all
  ultimately show ?case using Const.prems(2) by simp
next
  case (Abs a T t)
  then show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (App t u)
  consider (c) Tc where "z = ZOfclass (ztyp_of (fst Tc)) (snd Tc)"
    | (a) zt zu where "z = ZApp zt zu" "zterm_of ta t = returnZ zt" "zterm_of ta u = returnZ zu"
    using App.prems(1) by (auto simp: bindZ_eq_returnZ split: option.splits if_splits)
  then show ?case
  proof cases
    case c
    then show ?thesis using App.prems(2) by simp
  next
    case a
    then show ?thesis using App.IH App.prems(2) by auto
  qed
qed (auto simp: returnZ_def)

lemma prf_ok_compose_ann:
  assumes S: "prf_ok ax H e [] sp (list_implies (Bs @ [Bi]) C)"
    and R: "prf_ok ax H e [] rp (list_implies (Pre @ Olds) B)"
    and BBi: "B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. e \<turnstile> N : propT"
    and NB: "\<forall>j<length Bs. Ns ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bs ! j"
    and args: "list_all2 (\<lambda>a P. prf_ok ax H e (rev Ns) a P) qs (Pre @ Olds)"
    and ts: "list_all2 ann_ok ts Ns"
  shows "prf_ok ax H e [] (foldr (\<lambda>t p. AbsP (STR ''H'') t p) ts (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp qs))) (list_implies Ns C)"
proof -
  let ?lb = "length Bs" and ?la = "length As"
  have wS: "\<forall>X\<in>set (Bs @ [Bi]). e \<turnstile> X : propT" "e \<turnstile> C : propT"
    using typing_list_implies_iff[OF prf_ok_typing[OF S]] by auto
  have S': "prf_ok ax H e (rev Ns) sp (list_implies Bs (list_implies [Bi] C))"
    using prf_ok_append[OF S, of "rev Ns"] by (simp add: list_implies_append)
  have "list_all2 (prf_ok ax H e (rev Ns)) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]) Bs"
  proof (rule list_all2_all_nthI)
    fix k assume k: "k < length (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])"
    then have k': "k < ?lb" by simp
    have j: "?lb + ?la - 1 - k < length (rev Ns)" using k' Ns(1) by simp
    then have "rev Ns ! (?lb + ?la - 1 - k) \<in> set Ns" by (metis nth_mem set_rev)
    then have "prf_ok ax H e (rev Ns) (PBound (integer_of_nat (?lb + ?la - 1 - k))) (rev Ns ! (?lb + ?la - 1 - k))"
      using prf_ok.PBound[of "integer_of_nat (?lb + ?la - 1 - k)" "rev Ns" e ax H] j Ns(2)
      by (simp add: integer_of_nat_nonneg)
    moreover have "rev Ns ! (?lb + ?la - 1 - k) = Ns ! k" using Ns(1) k' by (simp add: rev_nth)
    moreover have "Ns ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Bs ! k" using NB k' by blast
    moreover have "e \<turnstile> Bs ! k : propT" using wS k' by auto
    ultimately show "prf_ok ax H e (rev Ns) (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb] ! k) (Bs ! k)"
      using k' by (auto intro: prf_ok.conv)
  qed simp
  with S' have q: "prf_ok ax H e (rev Ns)
      (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb])) (implies $ Bi $ C)"
    by (auto intro: prf_ok_proof_combP)
  have "prf_ok ax H e (rev Ns) (proof_combP rp qs) B"
    using prf_ok_append[OF R, of "rev Ns"] args by (auto intro: prf_ok_proof_combP)
  then have "prf_ok ax H e (rev Ns) (proof_combP rp qs) Bi" using BBi wS by (auto intro: prf_ok.conv)
  with q have "prf_ok ax H e (rev Ns @ []) (PAppp (proof_combP sp (map (\<lambda>k. PBound (integer_of_nat (?lb + ?la - 1 - k))) [0..<?lb]))
      (proof_combP rp qs)) C" by (auto intro: prf_ok.PAppp)
  from prf_ok_foldr_AbsP[OF this Ns(2) ts] show ?thesis by (simp add: downto_PBound)
qed

end


subsection \<open>The main theorem\<close>

context prf_sig
begin

text \<open>The variables of a term are visible or not bound by the environment:\<close>

definition zhid :: "pterm list \<Rightarrow> env \<Rightarrow> zterm \<Rightarrow> bool" where
  "zhid vis env t \<longleftrightarrow> (\<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
    (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env) x = None)"

lemma cinst_mix: "cinst \<rho> \<Longrightarrow> cinst \<rho>' \<Longrightarrow> cinst (\<lambda>v S. if P v S then \<rho>' v S else \<rho> v S)"
  by (auto simp: cinst_def wsinst_def cert_inst_def)

lemma rsubst_Nil: "rsubst m [] \<sigma> = \<sigma>"
  by (intro ext) (simp add: rsubst_def ren_name_def)

lemma noneg_iff: "noneg t \<longleftrightarrow> (\<forall>v\<in>vars t. snd (fst v) \<noteq> -1) \<and> (\<forall>U\<in>typs t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1)"
  by (auto simp: noneg_def tnoneg_def)

lemma zterm_of_wtp:
  assumes "wtp A" "noneg A"
  obtains z where "zterm_of ztargs A = returnZ z" "zdec z = A"
  using zterm_of_zdec[OF wtpD(2)[OF assms(1), of "\<lambda>_. propT"]] assms(2) by (auto simp: noneg_iff)

lemma noneg_App: "noneg (s $ t) \<longleftrightarrow> noneg s \<and> noneg t"
  by (auto simp: noneg_def)

lemma noneg_list_implies: "noneg (list_implies As B) \<Longrightarrow> (\<forall>A\<in>set As. noneg A) \<and> noneg B"
  by (induction As) (simp_all add: noneg_App)

lemma ok_zip_eq_D: "ok (zip_eq xs ys) zs \<Longrightarrow> length xs = length ys \<and> zs = zip xs ys"
  by (induction xs ys arbitrary: zs rule: zip_eq.induct) (auto simp: raise_def return_def bind_def split: sum.splits)

theorem zbicompose_proof_valid:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and r: "rchar sp r" and pa: "pinv_all sp"
    and state: "zvalid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" "wtp (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)" "\<forall>(t, u)\<in>set stpairs. ibelow smax t \<and> ibelow smax u"
    and rule: "zvalid ax (set hr) rtpairs rprf (list_implies (rev rAs) B)" "wtp (list_implies (rev rAs) B)"
      "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and nn: "noneg (list_implies (rev rAs) B)" "noneg (list_implies (Bs @ [Bi]) C)"
      "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)). noneg A"
    and vl: "\<And>xs. length (vl xs) = length xs" and m: "-1 \<le> smax"
    and rren: "case na_ren (br_newas r) of None \<Rightarrow> rprf' = rprf | Some rn \<Rightarrow> zren_proof rn smax rprf = returnZ rprf'"
    and vis: "vis \<noteq> []" "\<forall>(x, T)\<in>set (visible_vars vis). snd x \<noteq> -1" "\<forall>(v, S)\<in>set (visible_tvars vis). snd v \<noteq> -1"
      "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> set (visible_tvars vis)"
    and hid: "zprf_all (zhid vis (br_env r)) (\<lambda>_. True) sprf" "zprf_all (zhid vis (br_env r)) (\<lambda>_. True) rprf'"
      "\<forall>A\<in>set (na_oldAs (br_newas r)). \<forall>(x, T)\<in>vars A.
        (x, ztyp_of T) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv (br_env r)) x = None"
    and en: "eneg (br_env r)" and H: "\<forall>h\<in>set (hs @ hr). closed h"
    and res: "zbicompose_proof ztargs (br_env r) smax flatten Bs (na_As (br_newas r)) (br_A r) (na_oldAs (br_newas r))
      (na_n (br_newas r)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) vis rprf' sprf = returnZ p"
  shows "zvalid ax (set (hs @ hr)) (br_tpairs r) p (br_prop r)"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "sp_eres sp = eres_flg" "sp_ctx sp = ctx" "sp_vl sp = vl" "sp_rAs sp = rAs" "sp_env sp = env"
    by (simp_all add: sp')
  obtain A1o na tus env' tps Pre As0 n dps tps1 where its: "itsok sp A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth ctx A1o na (env', tps)) r"
    and rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps" and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "Pre = [] \<and> A1o = None \<and> n = 0 \<or> (\<exists>A1. Pre = [A1] \<and> A1o = Some A1 \<and> 1 \<le> n)"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl asm. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
      nat_of_integer n \<le> length asms \<and> asm = asms ! (nat_of_integer n - 1) \<and>
      (rlist_abs params concl, rlist_abs params asm) \<in> set dps \<and>
      (rlist_abs params asm, rlist_abs params concl) \<in> set tus"
    by (rule rchar_data[OF sp' ctx_def nlift_def r]) blast
  have rr: "br_env r = env' \<and> br_A r = A1o \<and> br_newas r = na"
    using ad by (cases rule: addth_cases) auto
  have wS: "\<forall>X\<in>set Bs. wtp X" "wtp Bi" "wtp C"
    using wtp_list_implies[of "Bs @ [Bi]" "Bs @ [Bi]" C C] state(2) by simp_all
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using state(3) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wtp X" "wtp B"
    using wtp_list_implies[of "rev rAs" "rev rAs" B B] rule(2) by simp_all
  have wP: "\<forall>X\<in>set Pre. wtp X" "\<forall>X\<in>set As0. wtp X" using wR(1) rAs by auto
  have lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (Pre @ As0) B" using rule(3) rAs by simp
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    using lr0 by (induction Pre) (auto dest: lifted_rule_Cons)
  have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
    using iS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
  from ures_inv[OF ur itsok_pwf[OF its pa, unfolded sp_sel(5)]] obtain A' K' X' where ei': "einv A' K' env'" by blast
  have tac: "tacyc (tyenv env')" "tcons_env (tyenv env')" using einvD(6,7)[OF ei'] .
  have lr': "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" using lr by (simp add: ctx_sel)
  have ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" using iS(2) by (simp add: ctx_sel)
  obtain tab where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    and nren: "na_ren na = None \<and> tab = [] \<or> (\<exists>r2. bc_lifted ctx \<and> na_ren na = Some (tab, r2))"
    and oldAs: "list_all2 (\<lambda>A1 A. wtp A1 \<and> wtp A \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> A1) (ap \<rho> (rsubst (bc_smax ctx) tab \<sigma>) A)))
      (na_oldAs na) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    and wN: "\<forall>A\<in>set (na_As na). wtp A"
    by (rule newAs_old[OF na lr' ib wP(2) vl]) blast+
  obtain h where nA: "\<forall>X\<in>set (na_As na). wtp X \<and> ttvars X \<subseteq> (\<Union>A\<in>set As0. ttvars A)"
    by (rule newAs_props[OF na lr' ib wP(2) vl]) blast
  let ?la = "length (na_As na)" and ?lb = "length Bs" and ?m = "nlift + 1"
  let ?VT = "set (visible_tvars vis)"
  have lold: "length (na_oldAs na) = ?la" using list_all2_lengthD[OF flat] by simp
  have lAs0: "length As0 = ?la" using list_all2_lengthD[OF oldAs] lold by simp
  have keep: "ap \<rho> (rsubst smax tab \<sigma>) t = ap \<rho> \<sigma> t"
    if "\<And>v. v \<in> vars t \<Longrightarrow> snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)" for \<rho> \<sigma> t
    using that by (intro ap_rsubst_id) blast
  text \<open>Type variables of the theorems are visible.\<close>
  have VS: "ttvars X \<subseteq> ?VT" if "X = list_implies (Bs @ [Bi]) C \<or> (\<exists>(t, u)\<in>set stpairs. X = t \<or> X = u)" for X
    using that vis(4) by (auto simp: tvars_thm_def)
  have VR: "ttvars X \<subseteq> ?VT" if "X = list_implies (rev rAs) B \<or> (\<exists>(t, u)\<in>set rtpairs. X = t \<or> X = u)" for X
    using that vis(4) by (auto simp: tvars_thm_def)
  have VAs0: "ttvars X \<subseteq> ?VT" if "X \<in> set As0" for X
    using VR[of "list_implies (rev rAs) B"] that rAs ttvars_list_implies(1)[of _ "rev rAs" B] by auto
  have VN: "ttvars X \<subseteq> ?VT" if "X \<in> set (na_As na)" for X using nA that VAs0 by blast
  have mixS: "ap (\<lambda>v S. if (v, S) \<in> ?VT then \<rho>' v S else \<rho> v S) \<sigma> X = ap \<rho>' \<sigma> X"
    if "ttvars X \<subseteq> ?VT" for \<rho> \<rho>' \<sigma> X
    by (rule ap_tcong) (use that in auto)
  text \<open>Witnesses of the proofs of the proof state and of the rule.\<close>
  from state(1) obtain ws0 where ws0: "pcerase ws0 = pcerase (zprf_tr sprf)"
    "prf_valid ax (set hs) stpairs ws0 (list_implies (Bs @ [Bi]) C)" unfolding zvalid_def by blast
  from rule(1) obtain wr0 where wr0: "pcerase wr0 = pcerase (zprf_tr rprf)"
    "prf_valid ax (set hr) rtpairs wr0 (list_implies (rev rAs) B)" unfolding zvalid_def by blast
  obtain wr where wr: "pcerase wr = pcerase (zprf_tr rprf')"
    and wra: "\<And>\<rho> \<sigma>. prf_aeq (prf_ap \<rho> (rsubst smax tab \<sigma>) wr0) (prf_ap \<rho> \<sigma> wr)"
  proof (cases "na_ren na")
    case None
    with nren have "tab = []" by auto
    moreover have "rprf' = rprf" using rren None rr by simp
    ultimately show thesis using wr0(1) by (intro that[of wr0]) (simp_all add: rsubst_Nil prf_aeq.refl)
  next
    case (Some rn)
    with nren have rn: "fst rn = tab" by auto
    have z: "zren_proof rn smax rprf = returnZ rprf'" using rren Some rr by simp
    show thesis
      by (rule that[of "prf_reclass (zprf_tr rprf') (pclass_map (\<lambda>T. T) wr0)"])
        (use zren_proof_aeq[OF z wr0(1) m] rn in simp_all)
  qed
  let ?S = "list_implies (Bs @ [Bi]) C" and ?R = "list_implies (rev rAs) B"
  let ?mix = "\<lambda>\<rho> \<rho>'. \<lambda>v S. if (v, S) \<in> ?VT then \<rho>' v S else \<rho> v S"
  have en': "eneg env'" using en rr by simp
  have hid': "zprf_all (zhid vis env') (\<lambda>_. True) sprf" "zprf_all (zhid vis env') (\<lambda>_. True) rprf'"
    using hid(1,2) rr by simp_all
  have Hs: "\<forall>h\<in>set hs. closed h" "\<forall>h\<in>set hr. closed h" using H by simp_all
  text \<open>The proof state and the rule are valid in the instances that agree on their variables.\<close>
  have Sval: "prf_ok ax (set hs) e [] (prf_ap \<rho>1 \<sigma>1 ws0) (ap \<rho>' \<sigma>' ?S)"
    if "cinst \<rho>1" "gsubst \<sigma>1" and eq: "\<And>X. X = ?S \<or> (\<exists>(t, u)\<in>set stpairs. X = t \<or> X = u) \<Longrightarrow> ap \<rho>1 \<sigma>1 X = ap \<rho>' \<sigma>' X"
      and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho>1 \<sigma>1 \<rho>' \<sigma>'
  proof -
    have "prf_ok ax (set hs) e [] (prf_ap \<rho>1 \<sigma>1 ws0) (ap \<rho>1 \<sigma>1 ?S)"
    proof (rule prf_validD[OF ws0(2) that(1,2)])
      fix t u assume tu: "(t, u) \<in> set stpairs"
      then have "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" using dsol tus by auto
      moreover have "ap \<rho>1 \<sigma>1 t = ap \<rho>' \<sigma>' t" "ap \<rho>1 \<sigma>1 u = ap \<rho>' \<sigma>' u"
        by (rule eq, use tu in blast)+
      ultimately show "ap \<rho>1 \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 \<sigma>1 u" by simp
    qed
    with eq[of ?S] show ?thesis by simp
  qed
  have Rval: "prf_ok ax (set hr) e [] (prf_ap \<rho>1 \<sigma>' wr) (ap \<rho>' (rsubst smax tab \<sigma>') ?R)"
    if "cinst \<rho>1" "gsubst \<sigma>'" and eq: "\<And>X. ttvars X \<subseteq> ?VT \<Longrightarrow> ap \<rho>1 (rsubst smax tab \<sigma>') X = ap \<rho>' (rsubst smax tab \<sigma>') X"
      and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho>1 \<rho>' \<sigma>'
  proof -
    let ?\<sigma>r = "rsubst smax tab \<sigma>'"
    have gr: "gsubst ?\<sigma>r" using that(2) wt_subst_rsubst by (auto simp: gsubst_def rsubst_def)
    have "prf_ok ax (set hr) e [] (prf_ap \<rho>1 ?\<sigma>r wr0) (ap \<rho>1 ?\<sigma>r ?R)"
    proof (rule prf_validD[OF wr0(2) that(1) gr])
      fix t u assume tu: "(t, u) \<in> set rtpairs"
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars t \<union> vars u" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from bspec[OF conjunct2[OF ren[OF this]], of "(t, u)"] tu
        have "fst (fst v) \<notin> vnames t \<and> fst (fst v) \<notin> vnames u" by (simp add: ctx_sel)
        moreover have "fst (fst v) \<in> vnames t \<union> vnames u" using that by blast
        ultimately show False by blast
      qed
      have "ap \<rho>' ?\<sigma>r t = ap \<rho>' \<sigma>' t" "ap \<rho>' ?\<sigma>r u = ap \<rho>' \<sigma>' u"
        by (rule keep; simp add: nr)+
      moreover have "ap \<rho>1 ?\<sigma>r t = ap \<rho>' ?\<sigma>r t" "ap \<rho>1 ?\<sigma>r u = ap \<rho>' ?\<sigma>r u"
        using eq VR tu by blast+
      ultimately show "ap \<rho>1 ?\<sigma>r t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>1 ?\<sigma>r u" using dsol tus tu by auto
    qed
    moreover have "ap \<rho>1 ?\<sigma>r ?R = ap \<rho>' ?\<sigma>r ?R" using eq VR by blast
    ultimately show ?thesis using prf_ok_aeq wra by metis
  qed
  have res': "zbicompose_proof ztargs env' smax flatten Bs (na_As na) A1o (na_oldAs na) n ?m vis rprf' sprf = returnZ p"
    using res by (simp add: rr newAs_n[OF na] nlift_def)
  have SR: "\<exists>sprf'' rprf'' ws wr'. zbicompose_core ztargs env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m vis rprf'' sprf'' = returnZ p \<and>
      pcerase ws = pcerase (zprf_tr sprf'') \<and> pcerase wr' = pcerase (zprf_tr rprf'') \<and>
      (\<forall>e \<rho> \<sigma> \<rho>' \<sigma>'. cinst \<rho> \<longrightarrow> gsubst \<sigma> \<longrightarrow> iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow>
        (\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u) \<longrightarrow>
        prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws) (ap \<rho>' \<sigma>' ?S) \<and>
        prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr') (ap \<rho>' (rsubst smax tab \<sigma>') ?R))"
  proof (cases "env_is_empty env'")
    case True
    have l: "vt_lookup (tyenv env') v = None" "vt_lookup (tenv env') x = None" for v x
      using True by (simp_all add: env_is_empty_def vt_is_empty_lookup)
    have core: "zbicompose_core ztargs env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m vis rprf' sprf = returnZ p"
      using res' True by (simp add: zbicompose_proof_def)
    have "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws0) (ap \<rho>' \<sigma>' ?S) \<and>
        prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr) (ap \<rho>' (rsubst smax tab \<sigma>') ?R)"
      if \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
        and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho> \<sigma> \<rho>' \<sigma>'
    proof -
      have e: "\<rho>' = \<rho>" "\<sigma>' = \<sigma>" by (intro ext; simp add: iextD(6,7)[OF ie] l)+
      have dsol': "\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" using dsol e by simp
      have "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws0) (ap \<rho> \<sigma> ?S)"
        by (rule Sval[OF \<rho> \<sigma> _ dsol']) simp
      moreover have "prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr) (ap \<rho> (rsubst smax tab \<sigma>) ?R)"
        by (rule Rval[OF \<rho> \<sigma> _ dsol']) simp
      ultimately show ?thesis using e by simp
    qed
    with core wr ws0(1) show ?thesis by blast
  next
    case False
    from res' False obtain rprf'' sprf'' where rn: "znorm_proof ztargs env' vis rprf' = returnZ rprf''"
      and sn: "(if above env' smax then returnZ sprf else znorm_proof ztargs env' vis sprf) = returnZ sprf''"
      and core: "zbicompose_core ztargs env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m vis rprf'' sprf'' = returnZ p"
      by (auto simp: zbicompose_proof_def bindZ_eq_returnZ)
    from znorm_proof_ok[OF rn vis(1) tac en' vis(2,3) hid'(2)[unfolded zhid_def] wr Hs(2)]
    obtain wr' where wr': "pcerase wr' = pcerase (zprf_tr rprf'')"
      "\<And>\<rho> \<sigma> \<rho>' \<sigma>' e Hs \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
        prf_ok ax (set hr) e Hs (prf_ap (?mix \<rho> \<rho>') \<sigma>' wr) \<phi> \<Longrightarrow> prf_ok ax (set hr) e Hs (prf_ap \<rho> \<sigma> wr') \<phi>"
      by blast
    have R: "prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr') (ap \<rho>' (rsubst smax tab \<sigma>') ?R)"
      if \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
        and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho> \<sigma> \<rho>' \<sigma>'
    proof -
      note i = iextD[OF ie]
      have "prf_ok ax (set hr) e [] (prf_ap (?mix \<rho> \<rho>') \<sigma>' wr) (ap \<rho>' (rsubst smax tab \<sigma>') ?R)"
        by (rule Rval[OF cinst_mix[OF \<rho> i(1)] i(2) _ dsol]) (rule mixS)
      from wr'(2)[OF ie \<sigma> this] show ?thesis .
    qed
    show ?thesis
    proof (cases "above env' smax")
      case True
      with sn have s: "sprf'' = sprf" by simp
      have "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws0) (ap \<rho>' \<sigma>' ?S)"
        if \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
          and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho> \<sigma> \<rho>' \<sigma>'
      proof (rule Sval[OF \<rho> \<sigma> _ dsol])
        fix X assume X: "X = ?S \<or> (\<exists>(t, u)\<in>set stpairs. X = t \<or> X = u)"
        have "ibelow smax X" using X state(3,4) by auto
        from iext_unb[OF ie above_unb[OF True this]] show "ap \<rho> \<sigma> X = ap \<rho>' \<sigma>' X" by simp
      qed
      with R core s wr'(1) ws0(1) show ?thesis by blast
    next
      case False
      with sn have sn': "znorm_proof ztargs env' vis sprf = returnZ sprf''" by simp
      from znorm_proof_ok[OF sn' vis(1) tac en' vis(2,3) hid'(1)[unfolded zhid_def] ws0(1) Hs(1)]
      obtain ws where ws: "pcerase ws = pcerase (zprf_tr sprf'')"
        "\<And>\<rho> \<sigma> \<rho>' \<sigma>' e Hs \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
          prf_ok ax (set hs) e Hs (prf_ap (?mix \<rho> \<rho>') \<sigma>' ws0) \<phi> \<Longrightarrow> prf_ok ax (set hs) e Hs (prf_ap \<rho> \<sigma> ws) \<phi>"
        by blast
      have "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws) (ap \<rho>' \<sigma>' ?S)"
        if \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
          and dsol: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" for e \<rho> \<sigma> \<rho>' \<sigma>'
      proof -
        note i = iextD[OF ie]
        have "prf_ok ax (set hs) e [] (prf_ap (?mix \<rho> \<rho>') \<sigma>' ws0) (ap \<rho>' \<sigma>' ?S)"
        proof (rule Sval[OF cinst_mix[OF \<rho> i(1)] i(2) _ dsol])
          fix X assume "X = ?S \<or> (\<exists>(t, u)\<in>set stpairs. X = t \<or> X = u)"
          then show "ap (?mix \<rho> \<rho>') \<sigma>' X = ap \<rho>' \<sigma>' X" by (intro mixS VS)
        qed
        from ws(2)[OF ie \<sigma> this] show ?thesis .
      qed
      with R core ws(1) wr'(1) show ?thesis by blast
    qed
  qed
  from SR obtain sprf'' rprf'' ws wr' where
    core: "zbicompose_core ztargs env' flatten Bs (na_As na) A1o (na_oldAs na) n ?m vis rprf'' sprf'' = returnZ p"
    and wsE: "pcerase ws = pcerase (zprf_tr sprf'')" and wrE: "pcerase wr' = pcerase (zprf_tr rprf'')"
    and SRok: "\<And>e \<rho> \<sigma> \<rho>' \<sigma>'. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow>
        (\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u) \<Longrightarrow>
        prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws) (ap \<rho>' \<sigma>' ?S) \<and>
        prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr') (ap \<rho>' (rsubst smax tab \<sigma>') ?R)"
    by blast
  text \<open>The tight composition.\<close>
  let ?normt = "\<lambda>t. bindZ (zterm_of ztargs t) (znorm_term ztargs env')"
  let ?bnd = "downto (integer_of_nat ?lb + integer_of_nat ?la - 1) (integer_of_nat ?la)"
  obtain ZNs asmL Os ks fs where
    ZNs: "mapZ ?normt (Bs @ na_As na) = returnZ ZNs"
    and asm: "(if 0 < n then (case A1o of None \<Rightarrow> raiseZ ZOption
      | Some C \<Rightarrow> bindZ (?normt C) (\<lambda>C'. returnZ [zmk_asm_prf C' n (zasm_count ?m C)])) else returnZ []) = returnZ asmL"
    and Os: "mapZ (zterm_of ztargs) (na_oldAs na) = returnZ Os"
    and ks: "liftMZ (zip_eq Os (downto (integer_of_nat ?la - 1) 0)) = returnZ ks"
    and fs: "(if flatten then mapZ (\<lambda>x. znorm_proof ztargs env' vis (zflatten_params_proof 0 0 n x)) ks
      else returnZ (map (\<lambda>x. ZBoundp (snd x)) ks)) = returnZ fs"
    and p: "p = ZAbsps ZNs (ZAppp (ZAppps sprf'' (map ZBoundp ?bnd)) (ZAppps rprf'' (asmL @ fs)))"
    using core unfolding zbicompose_core_def Let_def by (auto simp: bindZ_eq_returnZ)
  have ZNs': "list_all2 (\<lambda>X N. \<exists>z. zterm_of ztargs X = returnZ z \<and> znorm_term ztargs env' z = returnZ N)
      (Bs @ na_As na) ZNs"
    using ZNs by (auto simp: mapZ_eq_returnZ bindZ_eq_returnZ elim!: list_all2_mono)
  have Os': "list_all2 (\<lambda>A z. zterm_of ztargs A = returnZ z) (na_oldAs na) Os"
    using Os by (simp add: mapZ_eq_returnZ)
  have lOs: "length Os = ?la" using list_all2_lengthD[OF Os'] lold by simp
  let ?ks = "downto (integer_of_nat ?la - 1) 0"
  have lks: "length ?ks = ?la" by (simp add: length_downto0)
  have ks': "ks = zip Os ?ks" using ok_zip_eq_D[OF ks[unfolded liftMZ_eq_returnZ]] by simp
  have wO: "wtp (na_oldAs na ! j)" if "j < ?la" for j
    using list_all2_nthD[OF oldAs, of j] that lold by simp
  have Odec: "zterm_of ztargs (na_oldAs na ! j) = returnZ (Os ! j)" "zdec (Os ! j) = na_oldAs na ! j"
    if j: "j < ?la" for j
  proof -
    have "noneg (na_oldAs na ! j)" using nn(3) j lold rr by (simp add: nth_mem)
    from zterm_of_wtp[OF wO[OF j] this] obtain z where "zterm_of ztargs (na_oldAs na ! j) = returnZ z" "zdec z = na_oldAs na ! j" .
    moreover have "zterm_of ztargs (na_oldAs na ! j) = returnZ (Os ! j)" using list_all2_nthD[OF Os', of j] j lold by simp
    ultimately show "zterm_of ztargs (na_oldAs na ! j) = returnZ (Os ! j)" "zdec (Os ! j) = na_oldAs na ! j" by simp_all
  qed
  have lfs: "length fs = ?la"
    using fs list_all2_lengthD[of _ ks fs] ks' lOs lks by (auto simp: mapZ_eq_returnZ split: if_splits)
  have "\<exists>wfs. list_all2 (\<lambda>j wf. pcerase wf = pcerase (zprf_tr (fs ! j)) \<and>
      (flatten \<longrightarrow> (\<forall>e \<rho> \<sigma> \<rho>' \<sigma>' Hs' \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> gsubst \<sigma> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap (?mix \<rho> \<rho>') \<sigma>' (aflatten_params_proof Some Some 0 0 n (na_oldAs na ! j, ?ks ! j))) \<phi> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap \<rho> \<sigma> wf) \<phi>)) \<and>
      (\<not> flatten \<longrightarrow> wf = PBound (?ks ! j))) [0..<?la] wfs"
  proof (rule list_all2_choice, intro ballI)
    fix j assume "j \<in> set [0..<?la]"
    then have j: "j < ?la" by simp
    have ksj: "ks ! j = (Os ! j, ?ks ! j)" using ks' lOs lks j by simp
    show "\<exists>wf. pcerase wf = pcerase (zprf_tr (fs ! j)) \<and>
      (flatten \<longrightarrow> (\<forall>e \<rho> \<sigma> \<rho>' \<sigma>' Hs' \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> gsubst \<sigma> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap (?mix \<rho> \<rho>') \<sigma>' (aflatten_params_proof Some Some 0 0 n (na_oldAs na ! j, ?ks ! j))) \<phi> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap \<rho> \<sigma> wf) \<phi>)) \<and>
      (\<not> flatten \<longrightarrow> wf = PBound (?ks ! j))"
    proof (cases flatten)
      case True
      with fs have "list_all2 (\<lambda>x f. znorm_proof ztargs env' vis (zflatten_params_proof 0 0 n x) = returnZ f) ks fs"
        by (simp add: mapZ_eq_returnZ)
      from list_all2_nthD[OF this, of j] have fj:
        "znorm_proof ztargs env' vis (zflatten_params_proof 0 0 n (Os ! j, ?ks ! j)) = returnZ (fs ! j)"
        using ks' lOs lks j ksj by simp
      have dec: "zprf_tr (zflatten_params_proof 0 0 n (Os ! j, ?ks ! j)) = aflatten_params_proof Some Some 0 0 n (na_oldAs na ! j, ?ks ! j)"
        by (rule zprf_tr_zflatten_params_proof[OF Odec[OF j]])
      have hx: "(x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env') x = None"
        if xZ: "(x, Z) \<in> zvars (Os ! j)" and x: "snd x \<noteq> -1" for x :: indexname and Z
      proof -
        from zvars_zterm_of[OF Odec(1)[OF j] xZ] x obtain T where
          "(x, T) \<in> vars (na_oldAs na ! j)" "Z = ztyp_of T" by blast
        moreover have "na_oldAs na ! j \<in> set (na_oldAs (br_newas r))" using j lold rr by simp
        ultimately show ?thesis using hid(3) rr by fastforce
      qed
      have hj: "zprf_all (\<lambda>t. \<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
          (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env') x = None)
        (\<lambda>_. True) (zflatten_params_proof 0 0 n (Os ! j, ?ks ! j))"
      proof (rule zprf_all_mono[OF zprf_all_zflatten_params_proof])
        fix t assume sub: "zvars t \<subseteq> zvars (Os ! j)"
        show "\<forall>(x, Z)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
          (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env') x = None"
        proof (rule ballI)
          fix xZ assume xZ: "xZ \<in> zvars t"
          obtain x Z where e: "xZ = (x, Z)" by (cases xZ)
          show "case xZ of (x, Z) \<Rightarrow> snd x \<noteq> -1 \<longrightarrow>
            (x, Z) \<in> (\<lambda>(a, T). (a, ztyp_of T)) ` set (visible_vars vis) \<or> vt_lookup (tenv env') x = None"
            unfolding e case_prod_conv using hx[OF subsetD[OF sub xZ[unfolded e]]] by blast
        qed
      qed simp
      from znorm_proof_ok[OF fj vis(1) tac en' vis(2,3) hj HOL.refl, of "set (hs @ hr)" ax] H
      obtain wf where "pcerase wf = pcerase (zprf_tr (fs ! j))"
        "\<And>\<rho> \<sigma> \<rho>' \<sigma>' e Hs' \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
          prf_ok ax (set (hs @ hr)) e Hs' (prf_ap (?mix \<rho> \<rho>') \<sigma>' (zprf_tr (zflatten_params_proof 0 0 n (Os ! j, ?ks ! j)))) \<phi> \<Longrightarrow>
          prf_ok ax (set (hs @ hr)) e Hs' (prf_ap \<rho> \<sigma> wf) \<phi>"
        by blast
      with True show ?thesis unfolding dec by blast
    next
      case False
      with fs have "fs = map (\<lambda>x. ZBoundp (snd x)) ks" by simp
      then have "fs ! j = ZBoundp (?ks ! j)" using ks' lOs lks j by simp
      with False show ?thesis by simp
    qed
  qed
  then obtain wfs where wfs: "list_all2 (\<lambda>j wf. pcerase wf = pcerase (zprf_tr (fs ! j)) \<and>
      (flatten \<longrightarrow> (\<forall>e \<rho> \<sigma> \<rho>' \<sigma>' Hs' \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> gsubst \<sigma> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap (?mix \<rho> \<rho>') \<sigma>' (aflatten_params_proof Some Some 0 0 n (na_oldAs na ! j, ?ks ! j))) \<phi> \<longrightarrow>
        prf_ok ax (set (hs @ hr)) e Hs' (prf_ap \<rho> \<sigma> wf) \<phi>)) \<and>
      (\<not> flatten \<longrightarrow> wf = PBound (?ks ! j))) [0..<?la] wfs"
    by blast
  have lwfs: "length wfs = ?la" using list_all2_lengthD[OF wfs] by simp
  text \<open>The witness of the new proof.\<close>
  define wp where "wp = foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (Some \<circ> zdec) ZNs)
    (PAppp (proof_combP ws (map PBound ?bnd)) (proof_combP wr' (map zprf_tr asmL @ wfs)))"
  have pc: "pcerase wp = pcerase (zprf_tr p)"
  proof -
    have "map pcerase wfs = map pcerase (map zprf_tr fs)"
      by (rule nth_equalityI) (use list_all2_nthD[OF wfs] lfs lwfs in auto)
    then show ?thesis
      by (simp add: wp_def p zprf_tr_ZAbsps zprf_tr_ZAppps pcerase_foldr_AbsP pcerase_proof_combP wsE wrE comp_def)
  qed
  show ?thesis unfolding zvalid_def
  proof (intro exI[of _ wp] conjI[OF pc] prf_validI)
    fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (br_tpairs r) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
      and dsol0: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
      by (rule bresult_inst[OF its pa ur[folded sp_sel(5)] ad[folded sp_sel(2)] \<rho> \<sigma>]) (use sol in auto)
    note i = iextD[OF ie]
    have dsol: "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
      using dsol0 that by blast
    let ?\<sigma>r = "rsubst smax tab \<sigma>'" and ?H = "set (hs @ hr)" and ?\<rho>1 = "?mix \<rho> \<rho>'"
    have gr: "gsubst ?\<sigma>r" using i(2) wt_subst_rsubst by (auto simp: gsubst_def rsubst_def)
    have c1: "cinst ?\<rho>1" by (rule cinst_mix[OF \<rho> i(1)])
    from SRok[OF \<rho> \<sigma> ie dsol0] have S0: "prf_ok ax (set hs) e [] (prf_ap \<rho> \<sigma> ws) (ap \<rho>' \<sigma>' ?S)"
      and R0: "prf_ok ax (set hr) e [] (prf_ap \<rho> \<sigma> wr') (ap \<rho>' ?\<sigma>r ?R)" by blast+
    have S: "prf_ok ax ?H e [] (prf_ap \<rho> \<sigma> ws)
        (list_implies (map (ap \<rho>' \<sigma>') Bs @ [ap \<rho>' \<sigma>' Bi]) (ap \<rho>' \<sigma>' C))"
      using prf_ok_mono_H[OF S0, of ?H] by (simp add: ap_list_implies)
    have R: "prf_ok ax ?H e [] (prf_ap \<rho> \<sigma> wr')
        (list_implies (map (ap \<rho>' ?\<sigma>r) Pre @ map (ap \<rho>' ?\<sigma>r) As0) (ap \<rho>' ?\<sigma>r B))"
      using prf_ok_mono_H[OF R0, of ?H] rAs by (simp add: ap_list_implies)
    text \<open>The conclusion of the rule is convertible to the subgoal.\<close>
    have BBi_sol: "ap \<rho>' \<sigma>' (fst BBi) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' (snd BBi)"
      using dsol[of "fst BBi" "snd BBi"] tus by simp
    have cB: "ap \<rho>' ?\<sigma>r B \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' Bi"
    proof (cases lifted)
      case True
      from lr0[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars B0" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from ren[OF this] dps have "case BBi of (t, u) \<Rightarrow> fst (fst v) \<notin> vnames t" by blast
        with that BBi show False by auto
      qed
      have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B"
        by (rule keep) (use pv[OF ls] nr in \<open>auto simp: B vars_lift_pre\<close>)
      moreover have "ap \<rho>' \<sigma>' (lift_pre p B0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' (lift_pre p Bi0)"
        by (rule conv_lift_pre_ap[OF ok typing_ap_wtp[OF _ i(1,2)] typing_ap_wtp[OF _ i(1,2)]])
          (use wR(2) wS(2) BBi_sol BBi B Bi in simp_all)
      ultimately show ?thesis by (simp add: B Bi)
    next
      case False
      then have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B" using nren by (auto simp: ctx_sel rsubst_Nil)
      moreover have "BBi = (B, Bi)" using False by (simp add: BBi_def)
      ultimately show ?thesis using BBi_sol by simp
    qed
    text \<open>The new theorem and its relation to the instance.\<close>
    have wSc: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtp X \<and> ibelow (bc_smax ctx) X"
      using wS iS by (simp add: ctx_sel)
    have sk: "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
        \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
      if "bc_lifted ctx"
    proof -
      from that have lf: lifted by (simp add: ctx_sel)
      have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> typs H = typs H0"
        using newAs_skip[OF na _ _ vl n(4)] lf lr n(3) by (simp add: ctx_sel)
      then show ?thesis
        using ibelow_spine_hyps[OF iS(2)] n(4) by (fastforce simp: ctx_sel ibelow_def ttvars_def)
    qed
    obtain Hs C' where P: "br_prop r = list_implies Hs C'"
      and rs: "list_all2 (\<lambda>X Y. gterm (ap \<rho> \<sigma> Y) propT \<and> ap \<rho> \<sigma> Y \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
      and rc: "gterm (ap \<rho> \<sigma> C') propT \<and> ap \<rho> \<sigma> C' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' C"
      by (rule addth_rel[OF ad ie \<sigma> wSc wN sk]) (simp_all add: ctx_sel)
    define Ng where "Ng = map (ap \<rho> \<sigma>) Hs"
    have lHs: "length Hs = ?lb + ?la" using list_all2_lengthD[OF rs] by simp
    have relk: "gterm (Ng ! k) propT \<and> Ng ! k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ((Bs @ na_As na) ! k)" if "k < ?lb + ?la" for k
      using list_all2_nthD[OF rs, of k] that lHs by (simp add: Ng_def)
    have lNs: "length Ng = length (map (ap \<rho>' \<sigma>') Bs) + length (map (ap \<rho>' \<sigma>') (na_As na))"
      using lHs by (simp add: Ng_def)
    have tNs: "\<forall>N\<in>set Ng. e \<turnstile> N : propT"
      using relk lNs by (auto simp: in_set_conv_nth gterm_def)
    have NB: "\<forall>j<length (map (ap \<rho>' \<sigma>') Bs). Ng ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> map (ap \<rho>' \<sigma>') Bs ! j"
    proof (intro allI impI)
      fix j assume "j < length (map (ap \<rho>' \<sigma>') Bs)"
      with relk[of j] show "Ng ! j \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> map (ap \<rho>' \<sigma>') Bs ! j" by (simp add: nth_append)
    qed
    text \<open>The proofs of the premises of the rule.\<close>
    have wH: "\<forall>h\<in>set (rev Ng). e \<turnstile> h : propT" using tNs by simp
    have olds: "list_all2 (\<lambda>a P. prf_ok ax ?H e (rev Ng) a P) (map (prf_ap \<rho> \<sigma>) wfs) (map (ap \<rho>' ?\<sigma>r) As0)"
    proof (rule list_all2_all_nthI)
      show "length (map (prf_ap \<rho> \<sigma>) wfs) = length (map (ap \<rho>' ?\<sigma>r) As0)" using lwfs lAs0 by simp
      fix j assume "j < length (map (prf_ap \<rho> \<sigma>) wfs)"
      then have j: "j < ?la" using lwfs by simp
      let ?Ao = "na_oldAs na ! j" and ?An = "na_As na ! j" and ?Ar = "As0 ! j" and ?k = "?la - 1 - j"
      have kj: "?ks ! j = integer_of_nat ?k" using nth_downto0[OF j] .
      have wfj: "flatten \<longrightarrow> (\<forall>e \<rho> \<sigma> \<rho>' \<sigma>' Hs' \<phi>. iext env' \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> gsubst \<sigma> \<longrightarrow>
          prf_ok ax ?H e Hs' (prf_ap (?mix \<rho> \<rho>') \<sigma>' (aflatten_params_proof Some Some 0 0 n (?Ao, ?ks ! j))) \<phi> \<longrightarrow>
          prf_ok ax ?H e Hs' (prf_ap \<rho> \<sigma> (wfs ! j)) \<phi>)" "\<not> flatten \<longrightarrow> wfs ! j = PBound (?ks ! j)"
        using list_all2_nthD[OF wfs, of j] j by simp_all
      have oj: "wtp ?Ao \<and> wtp ?Ar \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> ?Ao) (ap \<rho> (rsubst smax tab \<sigma>) ?Ar))"
        using list_all2_nthD[OF oldAs, of j] j lold by (simp add: ctx_sel)
      have fj: "if flatten then ok (flatten_params vl n ?Ao) ?An else ?Ao = ?An"
        using list_all2_nthD[OF flat, of j] j lold by (simp add: ctx_sel)
      have wA: "wtp ?An" using wN j by simp
      have kl: "?k < length (rev Ng)" using j lNs by simp
      have rk: "rev Ng ! ?k = Ng ! (?lb + j)" using j lNs by (simp add: rev_nth)
      have relj: "gterm (rev Ng ! ?k) propT \<and> rev Ng ! ?k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' ?An"
        using relk[of "?lb + j"] j rk by (simp add: nth_append)
      have Ar: "?Ar \<in> set As0" using j lAs0 by simp
      have cv0: "ap ?\<rho>1 \<sigma>' ?Ao \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' ?\<sigma>r ?Ar"
      proof -
        have "aconv_term (ap ?\<rho>1 \<sigma>' ?Ao) (ap ?\<rho>1 ?\<sigma>r ?Ar)" using oj by blast
        moreover have "ap ?\<rho>1 ?\<sigma>r ?Ar = ap \<rho>' ?\<sigma>r ?Ar" by (rule mixS[OF VAs0[OF Ar]])
        ultimately show ?thesis by (simp add: aconv_term_conv)
      qed
      have t0: "e \<turnstile> ap \<rho>' ?\<sigma>r ?Ar : propT" using oj typing_ap_wtp[OF _ i(1) gr] by blast
      have "prf_ok ax ?H e (rev Ng) (prf_ap \<rho> \<sigma> (wfs ! j)) (ap ?\<rho>1 \<sigma>' ?Ao)"
      proof (cases flatten)
        case True
        with fj have fl: "ok (flatten_params vl n ?Ao) ?An" by simp
        have eA: "rev Ng ! ?k \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho>1 \<sigma>' ?An"
          using relj mixS[OF VN[of ?An]] j by simp
        have "prf_ok ax ?H e (rev Ng) (prf_ap ?\<rho>1 \<sigma>' (aflatten_params_proof Some Some 0 0 n (?Ao, integer_of_nat ?k))) (ap ?\<rho>1 \<sigma>' ?Ao)"
          by (rule aflatten_params_proof_ok[OF c1 i(2) conjunct1[OF oj] _ _ fl wA vl kl _ _ wH eA])
            (use relj in \<open>auto simp: gterm_def\<close>)
        with wfj(1) True ie \<sigma> kj show ?thesis by simp
      next
        case False
        with fj have "?Ao = ?An" by simp
        moreover have "prf_ok ax ?H e (rev Ng) (PBound (integer_of_nat ?k)) (rev Ng ! ?k)"
          using prf_ok.PBound[of "integer_of_nat ?k" "rev Ng" e ax ?H] kl wH nth_mem[OF kl]
          by (simp add: integer_of_nat_nonneg)
        moreover have "ap \<rho>' \<sigma>' ?An = ap ?\<rho>1 \<sigma>' ?An" using mixS[OF VN[of ?An]] j by simp
        ultimately show ?thesis
          using False relj wfj(2) kj typing_ap_wtp[OF wA c1 i(2)] by (auto intro: prf_ok.conv)
      qed
      then have "prf_ok ax ?H e (rev Ng) (prf_ap \<rho> \<sigma> (wfs ! j)) (ap \<rho>' ?\<sigma>r ?Ar)"
        using cv0 t0 by (blast intro: prf_ok.conv)
      then show "prf_ok ax ?H e (rev Ng) (map (prf_ap \<rho> \<sigma>) wfs ! j) (map (ap \<rho>' ?\<sigma>r) As0 ! j)"
        using j lwfs lAs0 by simp
    qed
    have pres: "list_all2 (\<lambda>a P. prf_ok ax ?H e (rev Ng) a P) (map (prf_ap \<rho> \<sigma> \<circ> zprf_tr) asmL) (map (ap \<rho>' ?\<sigma>r) Pre)"
      using A1o
    proof (elim disjE exE conjE)
      assume "Pre = []" "A1o = None" "n = 0"
      moreover from this have "asmL = []" using asm by simp
      ultimately show ?thesis by simp
    next
      fix A1 assume Pre: "Pre = [A1]" and A: "A1o = Some A1" and n1: "1 \<le> n"
      from asm A n1 obtain Z C' where Z: "zterm_of ztargs A1 = returnZ Z" and C': "znorm_term ztargs env' Z = returnZ C'"
        and aL: "asmL = [zmk_asm_prf C' n (zasm_count ?m A1)]"
        by (auto simp: bindZ_eq_returnZ)
      from pre[of A1] Pre obtain params asms concl asm' where er: "eres_flg"
        and apb: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and asm': "asm' \<in> set asms"
        and nl: "nat_of_integer n \<le> length asms" and asmn: "asm' = asms ! (nat_of_integer n - 1)"
        and ac: "(rlist_abs params asm', rlist_abs params concl) \<in> set tus"
        and cd: "(rlist_abs params concl, rlist_abs params asm') \<in> set dps"
        by auto
      have wA1: "wtp A1" using wP(1) Pre by simp
      have nnA1: "noneg A1" using noneg_list_implies[OF nn(1)] rAs Pre by auto
      from zterm_of_wtp[OF wA1 nnA1] Z have dZ: "zdec Z = A1" by auto
      have cvA: "ap \<rho>' \<sigma>' (rlist_abs params asm') \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' (rlist_abs params concl)" by (rule dsol[OF ac])
      have c: "ap \<rho>' ?\<sigma>r (rlist_abs params concl) = ap \<rho>' \<sigma>' (rlist_abs params concl)"
      proof (rule keep)
        fix v assume v: "v \<in> vars (rlist_abs params concl)"
        show "snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)"
        proof (rule disjI2, rule ccontr)
          assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
          from bspec[OF conjunct1[OF ren[OF this]] cd]
          have "fst (fst v) \<notin> vnames (rlist_abs params concl)" by simp
          moreover have "fst (fst v) \<in> vnames (rlist_abs params concl)" using v by blast
          ultimately show False by blast
        qed
      qed
      have aH: "ap \<rho>' ?\<sigma>r X = ap \<rho>' \<sigma>' X" if "vars X \<subseteq> (\<Union>H\<in>set asms. vars H)" for X
      proof (cases lifted)
        case True
        from lr0[OF True] obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
          and As: "Pre @ As0 = map (lift_pre p) As0'" by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        from As Pre obtain X1 where A1': "A1 = lift_pre p X1" by (cases As0') auto
        have "nlift + 1 = count_prems (strip_all_body Bi)" using er by (simp add: nlift_def)
        then have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ apb[unfolded A1']] Bi n(4) by simp
        then have "vars X \<subseteq> pvars p" using that vars_phyps by blast
        with pv[OF ls] show ?thesis by (intro keep) auto
      next
        case False
        then show ?thesis using nren by (auto simp: ctx_sel rsubst_Nil)
      qed
      have a: "ap \<rho>' ?\<sigma>r (rlist_abs params asm') = ap \<rho>' \<sigma>' (rlist_abs params asm')"
        by (rule aH) (use asm' in auto)
      have nb: "n \<le> ilength asms" using nl n(1) by (simp add: ilength_eq integer_reps)
      have AP: "prf_ok ax ?H e (rev Ng) (prf_ap \<rho>' ?\<sigma>r (aall_prf Some Some n ?m A1)) (ap \<rho>' ?\<sigma>r A1)"
        by (rule amk_asm_prf_ok[OF i(1) gr wA1 _ _ apb _ n1 nb]) (use n(4) cvA a c asmn in simp_all)
      text \<open>The structure of the premise.\<close>
      obtain A'' Hs0 where s1: "strip_assums_all [] A1 = (params, A'')" and s2: "strip_assums_imp ?m [] A'' = (Hs0, concl)"
        and asms: "asms = rev Hs0"
        using apb by (auto simp: assum_problems_def split: prod.splits)
      let ?e0 = "\<lambda>_::integer. propT"
      from strip_assums_all_list_forall[OF s1 wtpD(2)[OF wA1, of ?e0]] obtain qs where
        A1q: "A1 = list_forall qs A''" and tA'': "pushes ?e0 (map snd qs) \<turnstile> A'' : propT" by blast
      from strip_assums_imp_list_implies[OF s2 tA''] n(4) obtain as where
        A'': "A'' = list_implies as concl" and Hs0: "Hs0 = rev as @ []" and il: "ilength as \<le> ?m"
        and di: "ilength as < ?m \<longrightarrow> dest_imp concl = None" by auto
      have as_eq: "asms = as" using asms Hs0 by simp
      have ne: "as \<noteq> []" using nb n1 as_eq by auto
      have aeq: "prf_aeq (prf_ap \<rho>' ?\<sigma>r (aall_prf Some Some n ?m A1)) (prf_ap \<rho> \<sigma> (zprf_tr (zall_prf n (ilength as) C')))"
      proof (rule zall_prf_aeq[OF ie tac en' Z dZ C' A1q[unfolded A''] ne il di])
        show "\<forall>H\<in>set as. ap \<rho>' ?\<sigma>r H = ap \<rho>' \<sigma>' H"
        proof
          fix H assume "H \<in> set as"
          then have "vars H \<subseteq> (\<Union>H\<in>set asms. vars H)" using as_eq by blast
          then show "ap \<rho>' ?\<sigma>r H = ap \<rho>' \<sigma>' H" by (rule aH)
        qed
      qed
      have ze: "zmk_asm_prf C' n (zasm_count ?m A1) = zall_prf n (ilength as) C'"
        using apb as_eq by (simp add: zmk_asm_prf_def zasm_count_def ilength_eq)
      have "prf_ok ax ?H e (rev Ng) (prf_ap \<rho> \<sigma> (zprf_tr (zmk_asm_prf C' n (zasm_count ?m A1)))) (ap \<rho>' ?\<sigma>r A1)"
        unfolding ze using prf_ok_aeq[OF AP aeq] .
      then have "list_all2 (\<lambda>a P. prf_ok ax ?H e (rev Ng) a P)
          [prf_ap \<rho> \<sigma> (zprf_tr (zmk_asm_prf C' n (zasm_count ?m A1)))] [ap \<rho>' ?\<sigma>r A1]"
        by (rule list_all2_Cons[THEN iffD2, OF conjI[OF _ list_all2_Nil[THEN iffD2, OF HOL.refl]]])
      then show ?thesis unfolding aL Pre list.map comp_def .
    qed
    have args: "list_all2 (\<lambda>a P. prf_ok ax ?H e (rev Ng) a P) (map (prf_ap \<rho> \<sigma>) (map zprf_tr asmL @ wfs))
        (map (ap \<rho>' ?\<sigma>r) Pre @ map (ap \<rho>' ?\<sigma>r) As0)"
      using list_all2_appendI[OF pres olds] by (simp add: comp_def)
    text \<open>The annotations of the new premises.\<close>
    have lZ: "length ZNs = ?lb + ?la" using list_all2_lengthD[OF ZNs'] by simp
    have ann: "list_all2 ann_ok (map (map_option (ap \<rho> \<sigma>)) (map (Some \<circ> zdec) ZNs)) Ng"
    proof (rule list_all2_all_nthI)
      show "length (map (map_option (ap \<rho> \<sigma>)) (map (Some \<circ> zdec) ZNs)) = length Ng"
        using lZ lHs by (simp add: Ng_def)
      fix k assume "k < length (map (map_option (ap \<rho> \<sigma>)) (map (Some \<circ> zdec) ZNs))"
      then have k: "k < ?lb + ?la" using lZ by simp
      let ?X = "(Bs @ na_As na) ! k"
      from list_all2_nthD[OF ZNs', of k] k obtain z where
        z: "zterm_of ztargs ?X = returnZ z" "znorm_term ztargs env' z = returnZ (ZNs ! k)" by auto
      have "?X \<in> set (Bs @ na_As na)" using k by (intro nth_mem) simp
      then have nnX: "noneg ?X" using noneg_list_implies[OF nn(2)] nn(3) rr by auto
      have "ap \<rho> \<sigma> (zdec (ZNs ! k)) \<approx> ap \<rho>' \<sigma>' (zdec z)" using znorm_term_ok[OF z(2) ie tac en'] by blast
      moreover have "erase (ap \<rho>' \<sigma>' (zdec z)) = erase (ap \<rho>' \<sigma>' ?X)" by (rule erase_ap_zdec_zterm_of[OF z(1) nnX])
      moreover have "Ng ! k \<approx> ap \<rho>' \<sigma>' ?X" using relk[OF k] conv_ueq by blast
      ultimately have "ap \<rho> \<sigma> (zdec (ZNs ! k)) \<approx> Ng ! k" by (metis ueq_sym ueq_trans)
      then show "ann_ok (map (map_option (ap \<rho> \<sigma>)) (map (Some \<circ> zdec) ZNs) ! k) (Ng ! k)"
        using k lZ by (simp add: ann_ok_def)
    qed
    from prf_ok_compose_ann[OF S R cB lNs tNs NB args ann]
    have "prf_ok ax ?H e [] (prf_ap \<rho> \<sigma> wp) (list_implies Ng (ap \<rho>' \<sigma>' C))"
      by (simp add: wp_def prf_ap_foldr_AbsP_ann prf_ap_proof_combP comp_def)
    moreover have "list_implies Ng (ap \<rho>' \<sigma>' C) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (br_prop r)"
    proof -
      have "e \<turnstile> list_implies Ng (ap \<rho>' \<sigma>' C) : propT" by (rule prf_ok_typing[OF calculation(1)])
      moreover have "e \<turnstile> list_implies Ng (ap \<rho> \<sigma> C') : propT"
        using tNs rc by (auto simp: gterm_def intro!: typing_list_impliesI)
      ultimately show ?thesis
        using conv_list_implies[OF conv_sym[OF conjunct2[OF rc]]] by (simp add: P Ng_def ap_list_implies)
    qed
    moreover have "e \<turnstile> ap \<rho> \<sigma> (br_prop r) : propT"
      using tNs rc by (auto simp: P Ng_def ap_list_implies gterm_def intro!: typing_list_impliesI)
    ultimately show "prf_ok ax ?H e [] (prf_ap \<rho> \<sigma> wp) (ap \<rho> \<sigma> (br_prop r))" by (auto intro: prf_ok.conv)
  qed
qed

end

end
