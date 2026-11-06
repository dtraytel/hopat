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

end
