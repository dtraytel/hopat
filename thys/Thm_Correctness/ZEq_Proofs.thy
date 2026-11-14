section \<open>Validity of the tight proofs of the equality rules\<close>

theory ZEq_Proofs
  imports ZSubst_Proofs
begin

text \<open>
  The tight proofs of the equality rules apply the proof constants of the equality axioms
  (\<^const>\<open>zaxiom_proof\<close>), which translate to the classic axioms applied to their instances.
\<close>

subsection \<open>Proof constants of the equality axioms\<close>

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

lemma zt_lookup_fold_update:
  "zt_lookup (fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) vs t) k =
    (if k \<in> set vs then Some (ZTVar (fst k) (snd k)) else zt_lookup t k)"
  by (induction vs arbitrary: t) auto

text \<open>
  The type arguments that the proof constant \<open>zaxiom_proof a Ts ts\<close> records, as the types of the
  classic axiom: the instance of each type variable of the axiom by \<open>Ts\<close>.
\<close>

definition zeq_typs :: "name \<Rightarrow> (name \<times> ztyp) list \<Rightarrow> ptyp list" where
  "zeq_typs a Ts = map (\<lambda>v. if v \<in> set (fst (snd (zequality_axiom a)))
      then typ_of (zsubst_tvar_names (map_of Ts) (ZTVar (fst v) (snd v))) else propT) zeq_tvars"

lemma zequality_axm_tab:
  assumes "a \<in> fst ` set zeq_vars"
  obtains A instT0 tab0 where "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), A), (instT0, tab0))"
    "ztab_names_ok tab0" "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>T. zv_lookup tab0 ((x, -1), T) = Some (ZVar (x, -1) T)"
    "\<And>k. zt_lookup instT0 k =
      (if k \<in> set (fst (snd (zequality_axiom a))) then Some (ZTVar (fst k) (snd k)) else None)"
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
  from that[OF e nok lk] show thesis by (simp add: zt_lookup_fold_update)
qed

context prf_sig
begin

lemma zaxiom_proof_tr:
  assumes z: "zaxiom_proof a Ts ts = return p" and a: "a \<in> fst ` set zeq_vars"
    and xs: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> map_of ts x \<noteq> None"
  shows "zconsts_ok p"
    "zprf_tr p = foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a (zeq_typs a Ts))
      (map (\<lambda>x. zdec (the (map_of ts x))) (the (map_of zeq_vars a)))"
proof -
  obtain A instT0 tab0 where e: "zequality_axm a = ((ZAxiom (STR ''Pure.'' + a), A), (instT0, tab0))"
    and ok: "ztab_names_ok tab0"
    and lk: "\<And>x. x \<in> set (the (map_of zeq_vars a)) \<Longrightarrow> \<exists>T. zv_lookup tab0 ((x, -1), T) = Some (ZVar (x, -1) T)"
    and lT: "\<And>k. zt_lookup instT0 k =
      (if k \<in> set (fst (snd (zequality_axiom a))) then Some (ZTVar (fst k) (snd k)) else None)"
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
  moreover have "zeq_const (STR ''Pure.'' + a) A"
    using a e by (auto simp: zeq_const_def zequality_axm_def split: prod.splits)
  moreover have "zinst_typs instT' zeq_tvars = zeq_typs a Ts"
  proof -
    have "instT' = zt_map (zsubst_tvar_names (map_of Ts)) instT0"
      using mi by (auto simp: map_insts_def bindZ_eq_returnZ)
    then show ?thesis by (simp add: zinst_typs_def zeq_typs_def lT)
  qed
  ultimately show "zprf_tr p = foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a (zeq_typs a Ts))
      (map (\<lambda>x. zdec (the (map_of ts x))) (the (map_of zeq_vars a)))"
    by (simp add: p zconst_trT_def zeq_tr_def find_zeq_vars[OF a])
qed

end

text \<open>The type of a term without type variables of index \<open>-1\<close> has none either:\<close>

lemma (in prf_sig) typing_tnoneg:
  "e \<turnstile> t : T \<Longrightarrow> noneg t \<Longrightarrow> (\<And>i. tnoneg (e i)) \<Longrightarrow> tnoneg T"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  have T: "tnoneg T" and nt: "noneg t" using Abs.prems(1) unfolding noneg_def by simp_all
  have "tnoneg U"
  proof (rule Abs.IH[OF nt])
    show "tnoneg ((e\<langle>0:T\<rangle>) i)" for i using T Abs.prems(2) by (simp add: shift_def)
  qed
  with T show ?case unfolding tnoneg_def by auto
next
  case (App e s T U t)
  have "noneg s" using App.prems(1) unfolding noneg_def by simp
  from App.IH(1)[OF this App.prems(2)] show ?case unfolding tnoneg_def by auto
next
  case (Var T e x)
  then show ?case unfolding noneg_def by simp
next
  case (Free T e x)
  then show ?case unfolding noneg_def by simp
next
  case (Const c T e)
  then show ?case unfolding noneg_def by simp
next
  case (Bound i e T)
  then show ?case by auto
qed

lemma (in prf_sig) closed_typing_tnoneg: "(\<And>e. e \<turnstile> t : T) \<Longrightarrow> noneg t \<Longrightarrow> tnoneg T"
  by (rule typing_tnoneg[of "\<lambda>_. propT"]) (simp_all add: tnoneg_def propT_def)

context prf_eq
begin

text \<open>The type arguments that the proof constants of the equality rules record:\<close>

lemma zeq_typs_a:
  "a \<in> {STR ''reflexive'', STR ''symmetric'', STR ''transitive''} \<Longrightarrow> tnoneg T \<Longrightarrow>
    zeq_typs a [(tvar_a, ztyp_of T)] = [T, propT]"
  by (elim insertE emptyE)
    (simp_all add: zeq_typs_def zeq_tvars_def zequality_axiom_def Let_def typ_of_ztyp_of_tnoneg tvar_b_ne_a)

lemma zeq_typs_none:
  "a \<in> {STR ''equal_intr'', STR ''equal_elim''} \<Longrightarrow> zeq_typs a [] = [propT, propT]"
  by (elim insertE emptyE) (simp_all add: zeq_typs_def zeq_tvars_def zequality_axiom_def Let_def)

lemma zeq_typs_ab:
  "a \<in> {STR ''abstract_rule'', STR ''combination''} \<Longrightarrow> tnoneg T \<Longrightarrow> tnoneg U \<Longrightarrow>
    zeq_typs a [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)] = [T, U]"
  by (elim insertE emptyE)
    (simp_all add: zeq_typs_def zeq_tvars_def zequality_axiom_def Let_def typ_of_ztyp_of_tnoneg tvar_b_ne_a)

end

context prf_eq
begin

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

text \<open>A missing classic proof is not valid:\<close>

lemma prf_ok_not_MinProof: "prf_ok ax H E e Hs p \<phi> \<Longrightarrow> p \<noteq> MinProof"
  by (induction rule: prf_ok.induct) auto

lemma prf_valid_MinProof: "prf_valid ax H tps MinProof \<phi> \<Longrightarrow> prf_valid ax H tps' q \<psi>"
  unfolding prf_valid_def using prf_ok_not_MinProof by (fastforce simp: prf_ap_def)

text \<open>The reflexivity axiom in tight and classic proofs:\<close>

lemma zeq_tr_not_PAxm: "zeq_tr n Ts look \<noteq> PAxm b A Us"
proof
  assume e: "zeq_tr n Ts look = PAxm b A Us"
  then obtain a xs ts where f: "find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars = Some (a, xs)"
    and t: "those (map look xs) = Some ts" and c: "foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a Ts) ts = PAxm b A Us"
    by (auto simp: zeq_tr_def split: option.splits prod.splits)
  have "(a, xs) \<in> set zeq_vars" using f by (metis find_Some_iff nth_mem)
  then have "xs \<noteq> []" by (auto simp: zeq_vars_def)
  with t have "ts \<noteq> []" by (cases xs) (auto split: option.splits)
  then obtain ts' t0 where "ts = ts' @ [t0]" by (cases ts rule: rev_cases) auto
  with c show False by simp
qed

lemma zax_tr_PAxm:
  assumes "zax_tr n A Ts look = PAxm b B Us"
  shows "b = n" "B = A" "term_variables A = []"
proof -
  have "foldl PAppt (PAxm n A (Some Ts)) xs = PAxm b B Us \<Longrightarrow> xs = [] \<and> b = n \<and> B = A" for xs
    by (induction xs rule: rev_induct) auto
  with assms show "b = n" "B = A" "term_variables A = []" by (auto simp: zax_tr_def)
qed

lemma zax_tr_PAppt_PAxm:
  assumes "zax_tr n A Ts look = PAppt (PAxm b B Us) t"
  shows "b = n" "B = A" "length (term_variables A) = 1"
proof -
  have "foldl PAppt (PAxm n A (Some Ts)) xs = PAppt (PAxm b B Us) t \<Longrightarrow> length xs = 1 \<and> b = n \<and> B = A" for xs
  proof (induction xs rule: rev_induct)
    case (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) auto
  qed simp
  from this[of "map _ (term_variables A)"] assms show "b = n" "B = A" "length (term_variables A) = 1"
    by (auto simp: zax_tr_def)
qed

lemma foldl_PAppt_PThm_shape:
  "foldl PAppt (PThm h) xs = PAxm b B Us \<Longrightarrow> False"
  "foldl PAppt (PThm h) xs = PAppt (PAxm b B Us) t \<Longrightarrow> False"
proof -
  have H: "\<forall>t. foldl PAppt (PThm h) xs \<noteq> PAxm b B Us \<and> foldl PAppt (PThm h) xs \<noteq> PAppt (PAxm b B Us) t"
  proof (induction xs rule: rev_induct)
    case (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) auto
  qed simp
  show "foldl PAppt (PThm h) xs = PAxm b B Us \<Longrightarrow> False" using H by blast
  show "foldl PAppt (PThm h) xs = PAppt (PAxm b B Us) t \<Longrightarrow> False" using H by blast
qed

lemma zthm_tr_not_PAxm: "zthm_tr A Ts look \<noteq> PAxm b B Us"
  unfolding zthm_tr_def using foldl_PAppt_PThm_shape(1) by blast

lemma zthm_tr_not_reflexive: "\<not> is_reflexive_proof (zthm_tr A Ts look)"
proof
  assume "is_reflexive_proof (zthm_tr A Ts look)"
  then obtain b B Us t where "zthm_tr A Ts look = PAppt (PAxm b B Us) t"
    by (cases "zthm_tr A Ts look" rule: is_reflexive_proof.cases) auto
  then show False unfolding zthm_tr_def using foldl_PAppt_PThm_shape(2) by blast
qed

lemma term_variables_refl_axiom: "length (term_variables (equality_axiom STR ''reflexive'')) = 1"
  by (simp add: term_variables_def equality_axiom_def ax_eq_def ax_var_def ax_aT_def ax_bT_def Let_def)

lemma zprf_tr_PAxm:
  assumes "zprf_tr q = PAxm b B Us"
  shows "B \<noteq> equality_axiom STR ''reflexive''"
proof (cases q)
  case (ZConstp c)
  obtain nm A instT tab where c: "c = ((nm, A), instT, tab)" by (cases c) auto
  show ?thesis
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      with assms ZConstp c ZAxiom have "zeq_tr n (zinst_typs instT zeq_tvars)
          (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1))) = PAxm b B Us"
        by (simp add: zconst_trT_def)
      with zeq_tr_not_PAxm show ?thesis by blast
    next
      case False
      with assms ZConstp c ZAxiom have "zax_tr n (zdec A) (zinst_typs instT (tyargs (zdec A)))
          (\<lambda>xi. map_option zdec (zv_lookup_name tab xi)) = PAxm b B Us"
        by (simp add: zconst_trT_def)
      from zax_tr_PAxm[OF this] term_variables_refl_axiom show ?thesis by auto
    qed
  qed (use assms ZConstp c zthm_tr_not_PAxm in \<open>simp_all add: zconst_trT_def\<close>)
qed (use assms in simp_all)

lemma is_reflexive_proof_pcerase [simp]: "is_reflexive_proof (pcerase p) = is_reflexive_proof p"
  by (cases p rule: is_reflexive_proof.cases) simp_all

lemma refl_ok_pcerase:
  assumes "refl_ok w" "pcerase w = pcerase p"
  shows "refl_ok p"
  unfolding refl_ok_def
proof (intro allI impI)
  fix A Ts t assume p: "p = PAppt (PAxm (STR ''Pure.reflexive'') A Ts) t"
  with assms(2) obtain w1 where "w = PAppt w1 t" "pcerase w1 = PAxm (STR ''Pure.reflexive'') A Ts"
    by (cases w) auto
  then have "w = PAppt (PAxm (STR ''Pure.reflexive'') A Ts) t" by (cases w1) auto
  with assms(1) show "A = equality_axiom STR ''reflexive''" by (simp add: refl_ok_def)
qed

lemma is_reflexive_chain:
  assumes "is_reflexive_proof (foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a Us) ts)"
  shows "STR ''Pure.'' + a = STR ''Pure.reflexive''"
proof (cases ts rule: rev_cases)
  case Nil
  with assms show ?thesis by (simp add: equality_axmT_def)
next
  case (snoc ts' t0)
  with assms show ?thesis by (cases ts' rule: rev_cases) (simp_all add: equality_axmT_def)
qed

lemma is_reflexive_zprf_tr:
  assumes r: "is_reflexive_proof (zprf_tr q)" and rf: "refl_ok (zprf_tr q)"
  shows "zis_reflexive_proof q"
proof (cases q)
  case (ZAppt q' t)
  have "is_reflexive_proof (PAppt (zprf_tr q') x) = False" for x
  proof (cases "zprf_tr q'")
    case (PAxm b B Us)
    with rf ZAppt have "b = STR ''Pure.reflexive'' \<Longrightarrow> B = equality_axiom STR ''reflexive''"
      by (simp add: refl_ok_def)
    with zprf_tr_PAxm[OF PAxm] PAxm show ?thesis by auto
  qed simp_all
  with r ZAppt show ?thesis by simp
next
  case (ZConstp c)
  obtain nm A instT tab where c: "c = ((nm, A), instT, tab)" by (cases c) auto
  show ?thesis
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      let ?l = "\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1))" and ?U = "zinst_typs instT zeq_tvars"
      from r True have ir: "is_reflexive_proof (zeq_tr n ?U ?l)" by (simp add: ZConstp c ZAxiom zconst_trT_def)
      then obtain a xs ts where f: "find (\<lambda>(a, xs). n = STR ''Pure.'' + a) zeq_vars = Some (a, xs)"
        and ch: "zeq_tr n ?U ?l = foldl (\<lambda>p t. PAppt p (Some t)) (equality_axmT a ?U) ts"
        by (auto simp: zeq_tr_def split: option.splits prod.splits)
      have n: "n = STR ''Pure.'' + a" using f by (auto simp: find_Some_iff)
      from is_reflexive_chain[OF ir[unfolded ch]] n show ?thesis by (simp add: ZConstp c ZAxiom)
    next
      case False
      let ?k = "\<lambda>xi. map_option zdec (zv_lookup_name tab xi)" and ?V = "zinst_typs instT (tyargs (zdec A))"
      from r False have ir: "is_reflexive_proof (zax_tr n (zdec A) ?V ?k)" by (simp add: ZConstp c ZAxiom zconst_trT_def)
      then obtain b B Us t where bt: "zax_tr n (zdec A) ?V ?k = PAppt (PAxm b B Us) t" "b = STR ''Pure.reflexive''"
        by (cases "zax_tr n (zdec A) ?V ?k" rule: is_reflexive_proof.cases) auto
      have "n = STR ''Pure.reflexive''" using zax_tr_PAppt_PAxm(1)[OF bt(1)] bt(2) by simp
      then show ?thesis by (simp add: ZConstp c ZAxiom)
    qed
  qed (use r ZConstp c zthm_tr_not_reflexive in \<open>simp_all add: zconst_trT_def\<close>)
qed (use r in simp_all)

lemma zis_reflexive_zprf_tr:
  assumes "zis_reflexive_proof q"
  shows "zprf_tr q = MinProof \<or> (\<exists>s Us. zprf_tr q = PAppt (equality_axmT STR ''reflexive'' Us) (Some s)) \<or>
    (\<exists>B Us us. zprf_tr q = foldl PAppt (PAxm (STR ''Pure.reflexive'') B (Some Us)) us \<and>
      length us = length (term_variables B))"
proof -
  from assms obtain A insts where q: "q = ZConstp ((ZAxiom (STR ''Pure.reflexive''), A), insts)"
    by (cases q rule: zis_reflexive_proof.cases) auto
  obtain instT tab where i: "insts = (instT, tab)" by (cases insts)
  show ?thesis
  proof (cases "zeq_const (STR ''Pure.reflexive'') A")
    case True
    have a: "STR ''reflexive'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
    have f: "find (\<lambda>(b, xs). STR ''Pure.reflexive'' = STR ''Pure.'' + b) zeq_vars = Some (STR ''reflexive'', [STR ''x''])"
      using find_zeq_vars[OF a] by (simp add: Pure_reflexive zeq_vars_def)
    show ?thesis
      by (cases "zv_lookup_name tab (STR ''x'', -1)") (auto simp: q i zconst_trT_def zeq_tr_def f True)
  next
    case False
    let ?us = "map (\<lambda>v. case v of Var xi _ \<Rightarrow> map_option zdec (zv_lookup_name tab xi) | _ \<Rightarrow> None)
      (term_variables (zdec A))"
    have "zprf_tr q = foldl PAppt (PAxm (STR ''Pure.reflexive'') (zdec A) (Some (zinst_typs instT (tyargs (zdec A))))) ?us"
      using False by (simp add: q i zconst_trT_def zax_tr_def)
    moreover have "length ?us = length (term_variables (zdec A))" by simp
    ultimately show ?thesis by blast
  qed
qed

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
  have tT: "tnoneg T" by (rule closed_typing_tnoneg[OF ty(1) nt])
  have zp: "zprf_tr p = PAppt (equality_axmT STR ''reflexive'' [T, propT]) (Some t)"
    using tr(2) by (simp add: zeq_vars_def dx zeq_typs_a[OF _ tT])
  have v: "prf_valid ax H [] (PAppt (eqax STR ''reflexive'' (Some [T, propT])) (Some t)) (eq_const T $ t $ t')"
    by (rule reflexive_proof_conv_valid_ann[OF c ty cv _ _ cert_propT]) simp_all
  show "zvalid ax H [] p (eq_const T $ t $ t')" by (rule zvalidI[OF _ v]) (simp add: zp eqax_Some)
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
  have ztr: "zprf_tr ax0 = equality_axmT STR ''equal_intr'' [propT, propT] %> A %> B"
    using tr(2) by (simp add: zeq_vars_def da db zeq_typs_none)
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have v: "prf_valid ax H (th_tpairs th)
      (PAppp (PAppp (eqax STR ''equal_intr'' (Some [propT, propT]) %> A %> B) v1) v2) (th_prop th)"
    by (rule equal_intr_proof_valid_ann[OF ok v1(2) v2(2) w1 w2 P1]) simp_all
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    by (rule zvalidI[OF _ v]) (simp add: p ztr v1(1) v2(1) eqax_def equality_axmT_def)
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
  have ztr: "zprf_tr ax0 = equality_axmT STR ''equal_elim'' [propT, propT] %> A %> B"
    using tr(2) by (simp add: zeq_vars_def da db zeq_typs_none)
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have v: "prf_valid ax H (th_tpairs th)
      (PAppp (PAppp (eqax STR ''equal_elim'' (Some [propT, propT]) %> A %> B) v1) v2) (th_prop th)"
    by (rule equal_elim_proof_valid_ann[OF ok v1(2) v2(2) w1 w2 P1]) simp_all
  show "zvalid ax H (th_tpairs th) p (th_prop th)"
    by (rule zvalidI[OF _ v]) (simp add: p ztr v1(1) v2(1) eqax_def equality_axmT_def)
qed


subsection \<open>Symmetry\<close>

text \<open>
  A valid proof that agrees with the translation of a tight proof of reflexivity is a proof of
  reflexivity (the name \<open>Pure.reflexive\<close> stands for the reflexivity axiom):
\<close>

lemma prf_ok_chain_axm_name:
  "prf_ok ax H E e Hs (foldl PAppt (PAxm n B Ts) us) \<phi> \<Longrightarrow> axm_name_ok n B"
proof (induction us arbitrary: \<phi> rule: rev_induct)
  case Nil
  from prf_ok_PAxm_inv[OF Nil[simplified] HOL.refl] show ?case by blast
next
  case (snoc u us)
  from prf_ok_PAppt_inv[OF snoc.prems] obtain U f where "prf_ok ax H E e Hs (foldl PAppt (PAxm n B Ts) us) (all_const U $ f)"
    by auto
  then show ?case by (rule snoc.IH)
qed

lemma zrefl_witness:
  assumes "zis_reflexive_proof pf" "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax H tps w \<phi>"
  shows "w = MinProof \<or> is_reflexive_proof w"
proof -
  consider "zprf_tr pf = MinProof" | s Us where "zprf_tr pf = PAppt (equality_axmT STR ''reflexive'' Us) (Some s)"
    | B Us us where "zprf_tr pf = foldl PAppt (PAxm (STR ''Pure.reflexive'') B (Some Us)) us"
      "length us = length (term_variables B)"
    using zis_reflexive_zprf_tr[OF assms(1)] by blast
  then show ?thesis
  proof cases
    case 1
    with assms(2) show ?thesis by (cases w) auto
  next
    case (2 s Us)
    have "w = PAppt (equality_axmT STR ''reflexive'' Us) (Some s)"
      using pcerase_chain[of w _ _ _ "[s]"] assms(2) 2 by (simp add: equality_axmT_def)
    then show ?thesis by (simp add: equality_axmT_def Pure_reflexive)
  next
    case (3 B Us us)
    have w: "w = foldl PAppt (PAxm (STR ''Pure.reflexive'') B (Some Us)) us"
      by (rule pcerase_chain') (use assms(2) 3(1) in simp)
    have "axm_name_ok (STR ''Pure.reflexive'') B"
      by (rule prf_ok_chain_axm_name[OF prf_valid_generic[OF assms(3)[unfolded w]]])
    then have "B = equality_axiom STR ''reflexive''" by (simp add: axm_name_ok_def refl_axiom_eq)
    with 3(2) term_variables_refl_axiom obtain u where "us = [u]" by (cases us) auto
    with w show ?thesis by simp
  qed
qed

lemma not_refl_witness:
  assumes "\<not> zis_reflexive_proof pf" "pcerase w = pcerase (zprf_tr pf)" "prf_valid ax H tps w \<phi>"
  shows "\<not> is_reflexive_proof w"
proof
  assume "is_reflexive_proof w"
  then have "is_reflexive_proof (zprf_tr pf)" using arg_cong[OF assms(2), of is_reflexive_proof] by simp
  moreover have "refl_ok (zprf_tr pf)" by (rule refl_ok_pcerase[OF prf_valid_refl_ok[OF assms(3)] assms(2)])
  ultimately show False using assms(1) is_reflexive_zprf_tr by blast
qed

theorem zsymmetric_proof_valid:
  assumes ok: "okT (symmetric th0) th" and p: "zvalid ax H (th_tpairs th0) pf (th_prop th0)"
    and w: "wtp (th_prop th0)" and P0: "th_prop th0 = eq_const T $ t $ u"
    and nn: "noneg t" "noneg u" and zc: "zconsts_ok pf"
    and z: "zsymmetric_proof ztargs T t u pf = return q"
  shows "zvalid ax H (th_tpairs th) q (th_prop th)" "zconsts_ok q"
proof -
  obtain w0 where w0: "pcerase w0 = pcerase (zprf_tr pf)" "prf_valid ax H (th_tpairs th0) w0 (th_prop th0)"
    using p by (rule zvalidE)
  have rf: "refl_ok w0" by (rule prf_valid_refl_ok[OF w0(2)])
  have tps: "th_tpairs th = th_tpairs th0"
    using ok by (auto simp: symmetric_def returnW_def raiseW_def mk_rep_def split: pterm.splits option.splits)
  have "dest_eq_any (th_prop th0) = Some (t, u)" by (simp add: P0)
  from dest_eq_any_wtp[OF eq_ok_ctab this w] obtain U where PU: "th_prop th0 = eq_const U $ t $ u"
    and ty: "\<And>e. e \<turnstile> t : U" "\<And>e. e \<turnstile> u : U" by blast
  have UT: "U = T" using P0 PU by simp
  have tT: "tnoneg T" using closed_typing_tnoneg[OF ty(1) nn(1)] UT by simp
  have "zvalid ax H (th_tpairs th) q (th_prop th) \<and> zconsts_ok q"
  proof (cases "zis_reflexive_proof pf")
    case True
    with z have q: "q = pf" by (simp add: zsymmetric_proof_def)
    have "prf_valid ax H (th_tpairs th) w0 (th_prop th)"
    proof (cases "w0 = MinProof")
      case True
      with w0(2) tps show ?thesis by (auto intro: prf_valid_MinProof)
    next
      case False
      with zrefl_witness[OF \<open>zis_reflexive_proof pf\<close> w0(1,2)] have "is_reflexive_proof w0" by simp
      with symmetric_proof_valid_ann[OF ok w0(2) w rf P0, where ?a1.0 = None and ?a2.0 = None and Ts = None
          and V = propT, unfolded eqax_None]
      show ?thesis by simp
    qed
    with w0(1) zc show ?thesis by (simp add: q zvalidI)
  next
    case False
    from z False obtain x y ax0 where x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
      and ax0: "zaxiom_proof STR ''symmetric'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y)] = return ax0"
      and q: "q = ZAppp ax0 pf"
      by (auto simp: zsymmetric_proof_def bindZ_eq_returnZ)
    have dx: "zdec x = t" by (rule zdec_zterm_of_noneg[OF x ty(1) nn(1)])
    have dy: "zdec y = u" by (rule zdec_zterm_of_noneg[OF y ty(2) nn(2)])
    have ae: "STR ''symmetric'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
    have xs: "map_of [(STR ''x'', x), (STR ''y'', y)] v \<noteq> None"
      if "v \<in> set (the (map_of zeq_vars STR ''symmetric''))" for v
      using that by (auto simp: zeq_vars_def)
    note tr = zaxiom_proof_tr[OF ax0 ae xs]
    have ztr: "zprf_tr ax0 = equality_axmT STR ''symmetric'' [T, propT] %> t %> u"
      using tr(2) by (simp add: zeq_vars_def dx dy zeq_typs_a[OF _ tT])
    have nr: "\<not> is_reflexive_proof w0" by (rule not_refl_witness[OF False w0(1,2)])
    from symmetric_proof_valid_ann[OF ok w0(2) w rf P0, where ?a1.0 = "Some t" and ?a2.0 = "Some u"
        and Ts = "Some [T, propT]" and TA = T and V = propT and ?e0.0 = "\<lambda>_. propT"] nr ty(1)[unfolded UT]
    have v: "prf_valid ax H (th_tpairs th) (PAppp (eqax STR ''symmetric'' (Some [T, propT]) %> t %> u) w0) (th_prop th)"
      by simp
    have "zvalid ax H (th_tpairs th) q (th_prop th)"
      by (rule zvalidI[OF _ v]) (simp add: q ztr w0(1) eqax_def equality_axmT_def)
    with tr(1) zc show ?thesis by (simp add: q)
  qed
  then show "zvalid ax H (th_tpairs th) q (th_prop th)" "zconsts_ok q" by simp_all
qed


subsection \<open>Transitivity\<close>

theorem ztransitive_proof_valid:
  assumes ok: "okT (transitive th1 th2) th"
    and p1: "zvalid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "zvalid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
    and P1: "th_prop th1 = eq_const T $ t $ u" and P2: "dest_eq_any (th_prop th2) = Some (u', v)"
    and nn: "noneg t" "noneg u" "noneg v" and zc: "zconsts_ok pf1" "zconsts_ok pf2"
    and z: "ztransitive_proof ztargs T t u v pf1 pf2 = return q"
  shows "zvalid ax H (th_tpairs th) q (th_prop th)" "zconsts_ok q"
proof -
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have r1: "refl_ok v1" by (rule prf_valid_refl_ok[OF v1(2)])
  have r2: "refl_ok v2" by (rule prf_valid_refl_ok[OF v2(2)])
  have d1: "dest_eq_any (th_prop th1) = Some (t, u)" by (simp add: P1)
  have tps: "th_tpairs th = union_tpairs (th_tpairs th1) (th_tpairs th2)"
    using ok by (auto simp: transitive_def returnW_def raiseW_def mk_rep_def
      split: pterm.splits option.splits prod.splits if_splits)
  from dest_eq_any_wtp[OF eq_ok_ctab d1 w1] obtain U where PU: "th_prop th1 = eq_const U $ t $ u"
    and ty1: "\<And>e. e \<turnstile> t : U" "\<And>e. e \<turnstile> u : U" by blast
  have UT: "U = T" using P1 PU by simp
  have tT: "tnoneg T" using closed_typing_tnoneg[OF ty1(1) nn(1)] UT by simp
  note va = transitive_proof_valid_ann[OF ok v1(2) v2(2) w1 w2 r1 r2 d1 P2, where V = propT and TA = T
      and ?e0.0 = "\<lambda>_. propT"]
  from dest_eq_any_wtp[OF eq_ok_ctab P2 w2] obtain U' where ty2: "\<And>e. e \<turnstile> v : U'" by blast
  have "zvalid ax H (th_tpairs th) q (th_prop th) \<and> zconsts_ok q"
  proof (cases "zis_reflexive_proof pf1")
    case True
    with z have q: "q = pf2" by (simp add: ztransitive_proof_def)
    have "prf_valid ax H (th_tpairs th) v2 (th_prop th)"
    proof (cases "v1 = MinProof")
      case True
      with v1(2) show ?thesis by (auto intro: prf_valid_MinProof)
    next
      case False
      with zrefl_witness[OF \<open>zis_reflexive_proof pf1\<close> v1(1,2)] have "is_reflexive_proof v1" by simp
      with va[where ?a1.0 = None and ?a2.0 = None and ?a3.0 = None and Ts = None, unfolded eqax_None]
      show ?thesis by simp
    qed
    with v2(1) zc show ?thesis by (simp add: q zvalidI)
  next
    case nr1: False
    note nv1 = not_refl_witness[OF nr1 v1(1,2)]
    show ?thesis
    proof (cases "zis_reflexive_proof pf2")
      case True
      with z nr1 have q: "q = pf1" by (simp add: ztransitive_proof_def)
      have "prf_valid ax H (th_tpairs th) v1 (th_prop th)"
      proof (cases "v2 = MinProof")
        case True
        with v2(2) show ?thesis by (auto intro: prf_valid_MinProof)
      next
        case False
        with zrefl_witness[OF \<open>zis_reflexive_proof pf2\<close> v2(1,2)] have "is_reflexive_proof v2" by simp
        with va[where ?a1.0 = None and ?a2.0 = None and ?a3.0 = None and Ts = None, unfolded eqax_None] nv1
        show ?thesis by simp
      qed
      with v1(1) zc show ?thesis by (simp add: q zvalidI)
    next
      case nr2: False
      note nv2 = not_refl_witness[OF nr2 v2(1,2)]
      from z nr1 nr2 obtain x y w ax0 where x: "zterm_of ztargs t = return x"
        and y: "zterm_of ztargs u = return y" and w: "zterm_of ztargs v = return w"
        and ax0: "zaxiom_proof STR ''transitive'' [(tvar_a, ztyp_of T)] [(STR ''x'', x), (STR ''y'', y), (STR ''z'', w)] = return ax0"
        and q: "q = ZAppp (ZAppp ax0 pf1) pf2"
        by (auto simp: ztransitive_proof_def bindZ_eq_returnZ)
      have dx: "zdec x = t" by (rule zdec_zterm_of_noneg[OF x ty1(1) nn(1)])
      have dy: "zdec y = u" by (rule zdec_zterm_of_noneg[OF y ty1(2) nn(2)])
      have dw: "zdec w = v" by (rule zdec_zterm_of_noneg[OF w ty2 nn(3)])
      have ae: "STR ''transitive'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
      have xs: "map_of [(STR ''x'', x), (STR ''y'', y), (STR ''z'', w)] a \<noteq> None"
        if "a \<in> set (the (map_of zeq_vars STR ''transitive''))" for a
        using that by (auto simp: zeq_vars_def)
      note tr = zaxiom_proof_tr[OF ax0 ae xs]
      have ztr: "zprf_tr ax0 = equality_axmT STR ''transitive'' [T, propT] %> t %> u %> v"
        using tr(2) by (simp add: zeq_vars_def dx dy dw zeq_typs_a[OF _ tT])
      have v: "prf_valid ax H (th_tpairs th)
          (PAppp (PAppp (eqax STR ''transitive'' (Some [T, propT]) %> t %> u %> v) v1) v2) (th_prop th)"
        using va[where ?a1.0 = "Some t" and ?a2.0 = "Some u" and ?a3.0 = "Some v" and Ts = "Some [T, propT]"]
          nv1 nv2 ty1(1)[unfolded UT] by simp
      have "zvalid ax H (th_tpairs th) q (th_prop th)"
        by (rule zvalidI[OF _ v]) (simp add: q ztr v1(1) v2(1) eqax_def equality_axmT_def)
      with tr(1) zc show ?thesis by (simp add: q)
    qed
  qed
  then show "zvalid ax H (th_tpairs th) q (th_prop th)" "zconsts_ok q" by simp_all
qed


subsection \<open>Combination\<close>

theorem zcombination_proof_valid:
  assumes ok: "okT (combination th1 th2) th"
    and p1: "zvalid ax H (th_tpairs th1) pf1 (th_prop th1)" and p2: "zvalid ax H (th_tpairs th2) pf2 (th_prop th2)"
    and w1: "wtp (th_prop th1)" and w2: "wtp (th_prop th2)"
    and d: "okT (combination_data th1 th2) (T1, U, f, g, t, u)"
    and nn: "noneg f" "noneg g" "noneg t" "noneg u" and zc: "zconsts_ok pf1" "zconsts_ok pf2"
    and z: "zcombination_proof ztargs T1 U f g t u pf1 pf2 = return q"
  shows "zvalid ax H (th_tpairs th) q (th_prop th)" "zconsts_ok q"
proof -
  obtain v1 where v1: "pcerase v1 = pcerase (zprf_tr pf1)" "prf_valid ax H (th_tpairs th1) v1 (th_prop th1)"
    using p1 by (rule zvalidE)
  obtain v2 where v2: "pcerase v2 = pcerase (zprf_tr pf2)" "prf_valid ax H (th_tpairs th2) v2 (th_prop th2)"
    using p2 by (rule zvalidE)
  have d1: "dest_eq_fun (th_prop th1) = Some (T1 \<rightarrow>\<^sub>T U, f, g)" and d2: "dest_eq_fun (th_prop th2) = Some (T1, t, u)"
    by (rule combination_data_ok[OF d])+
  from dest_eq_any_wtp[OF eq_ok_ctab dest_eq_any_dest_eq_fun[OF d1] w1]
  obtain A where PA: "th_prop th1 = eq_const A $ f $ g" and tyf: "\<And>e. e \<turnstile> f : A" "\<And>e. e \<turnstile> g : A" by blast
  from d1 PA have AT: "A = T1 \<rightarrow>\<^sub>T U" by (simp add: propT_def)
  have "tnoneg (T1 \<rightarrow>\<^sub>T U)" using closed_typing_tnoneg[OF tyf(1) nn(1)] AT by simp
  then have tT1: "tnoneg T1" and tU: "tnoneg U" by (simp_all add: tnoneg_def)
  from dest_eq_any_wtp[OF eq_ok_ctab dest_eq_any_dest_eq_fun[OF d2] w2]
  obtain B where tyt: "\<And>e. e \<turnstile> t : B" "\<And>e. e \<turnstile> u : B" by blast
  from z obtain f' g' x y ax0 where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
    and x: "zterm_of ztargs t = return x" and y: "zterm_of ztargs u = return y"
    and ax0: "zaxiom_proof STR ''combination'' [(tvar_a, ztyp_of T1), (tvar_b, ztyp_of U)]
      [(STR ''f'', f'), (STR ''g'', g'), (STR ''x'', x), (STR ''y'', y)] = return ax0"
    and q: "q = ZAppp (ZAppp ax0 pf1) pf2"
    by (auto simp: zcombination_proof_def bindZ_eq_returnZ)
  have df: "zdec f' = f" by (rule zdec_zterm_of_noneg[OF f' tyf(1) nn(1)])
  have dg: "zdec g' = g" by (rule zdec_zterm_of_noneg[OF g' tyf(2) nn(2)])
  have dx: "zdec x = t" by (rule zdec_zterm_of_noneg[OF x tyt(1) nn(3)])
  have dy: "zdec y = u" by (rule zdec_zterm_of_noneg[OF y tyt(2) nn(4)])
  have ae: "STR ''combination'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
  have xs: "map_of [(STR ''f'', f'), (STR ''g'', g'), (STR ''x'', x), (STR ''y'', y)] a \<noteq> None"
    if "a \<in> set (the (map_of zeq_vars STR ''combination''))" for a
    using that by (auto simp: zeq_vars_def)
  note tr = zaxiom_proof_tr[OF ax0 ae xs]
  have ztr: "zprf_tr ax0 = equality_axmT STR ''combination'' [T1, U] %> f %> g %> t %> u"
    using tr(2) by (simp add: zeq_vars_def df dg dx dy zeq_typs_ab[OF _ tT1 tU])
  have v: "prf_valid ax H (th_tpairs th)
      (PAppp (PAppp (eqax STR ''combination'' (Some [T1, U]) %> f %> g %> t %> u) v1) v2) (th_prop th)"
    by (rule combination_proof_valid_gen[OF ok v1(2) v2(2) w1 w2 d]) (auto simp: ann_ok_def)
  show "zvalid ax H (th_tpairs th) q (th_prop th)"
    by (rule zvalidI[OF _ v]) (simp add: q ztr v1(1) v2(1) eqax_def equality_axmT_def)
  show "zconsts_ok q" using tr(1) zc by (simp add: q)
qed


subsection \<open>Abstraction\<close>

lemma zconsts_ok_zabstract_proof: "zconsts_ok p \<Longrightarrow> zconsts_ok (zabstract_proof z i p)"
proof (induction p arbitrary: i)
  case (ZConstp c)
  then show ?case by (cases c) simp
qed simp_all

theorem zabstract_rule_proof_valid:
  assumes ok: "okT (abstract_rule b hs (CTerm x T m) th0) th"
    and p: "zvalid ax (set hs) (th_tpairs th0) prf (th_prop th0)"
    and wt: "wt_thm (th_maxidx th0) hs (th_tpairs th0) (th_prop th0)" and tx: "\<And>e. e \<turnstile> x : T"
    and ad: "okT (abstract_rule_data b hs (CTerm x T m) th0) (U, f, g)"
    and nn: "noneg x" "noneg f" "noneg g" and zc: "zconsts_ok prf"
    and cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) prf"
    and eqc: "zeq_close_ok"
    and z: "zabstract_rule_proof ztargs T U b x f g prf = return q"
  shows "zvalid ax (set hs) (th_tpairs th) q (th_prop th)" "zconsts_ok q"
proof -
  from z obtain f' g' ax0 zx where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
    and ax0: "zaxiom_proof STR ''abstract_rule'' [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)]
      [(STR ''f'', f'), (STR ''g'', g')] = return ax0"
    and zx: "zterm_of ztargs x = return zx" and q: "q = ZAppp ax0 (ZAbst b (ztyp_of T) (zabstract_proof zx 0 prf))"
    by (auto simp: zabstract_rule_proof_def zforall_intr_proof_def bindZ_eq_returnZ)
  obtain t u a z' where d: "dest_eq_fun (th_prop th0) = Some (U, t, u)"
    and f: "f = Abs b T (abstract_over x t)" and g: "g = Abs b T (abstract_over x u)"
    and xc: "(x = Free a T \<and> \<not> occs_hyps x hs (th_tpairs th0)) \<or> (x = Var z' T \<and> \<not> occs_hyps x [] (th_tpairs th0))"
    by (rule abstract_rule_data_ok[OF ad tx])
  have xa: "x = Free a T \<or> x = Var z' T" using xc by blast
  have tT: "typ_of (ztyp_of T) = T" using nn(1) xa by (auto simp: noneg_def typ_of_ztyp_of_tnoneg)
  have dx: "zdec zx = x" by (rule zdec_zterm_of_noneg[OF zx tx[of "\<lambda>_. propT"] nn(1)])
  have "\<exists>xi. zx = ZVar xi (ztyp_of T)" using xa zx by (auto simp: return_def)
  then obtain xi where xv: "zx = ZVar xi (ztyp_of T)" by blast
  have wP: "wtp (th_prop th0)" using wt by (simp add: wt_thm_def)
  from dest_eq_any_wtp[OF eq_ok_ctab dest_eq_any_dest_eq_fun[OF d] wP] obtain A where
    P0: "th_prop th0 = eq_const A $ t $ u" and c: "closed t" "closed u" and ty: "\<And>e. e \<turnstile> t : A" "\<And>e. e \<turnstile> u : A"
    by blast
  have tQ: "e\<langle>0:T\<rangle> \<turnstile> abstract_over x s : A" if "closed s" "\<And>e. e \<turnstile> s : A" for s e
    unfolding abstract_over_def
    by (rule typing_abstract_over_aux[OF xa that(2)]) (use that(1) in \<open>simp_all add: closed_def\<close>)
  have cT: "cert_typ alg ar T" using tx[of "\<lambda>_. propT"] xa by auto
  have tf: "e \<turnstile> f : T \<rightarrow>\<^sub>T A" "e \<turnstile> g : T \<rightarrow>\<^sub>T A" for e
    using tQ[OF c(1) ty(1)] tQ[OF c(2) ty(2)] cT by (auto simp: f g)
  have df: "zdec f' = f" by (rule zdec_zterm_of_noneg[OF f' tf(1) nn(2)])
  have dg: "zdec g' = g" by (rule zdec_zterm_of_noneg[OF g' tf(2) nn(3)])
  have ae: "STR ''abstract_rule'' \<in> fst ` set zeq_vars" by (simp add: zeq_vars_def)
  have xs: "map_of [(STR ''f'', f'), (STR ''g'', g')] v \<noteq> None"
    if "v \<in> set (the (map_of zeq_vars STR ''abstract_rule''))" for v
    using that by (auto simp: zeq_vars_def)
  note tr = zaxiom_proof_tr[OF ax0 ae xs]
  from d P0 have UA: "U = A" by (simp add: propT_def)
  have nT: "tnoneg T" using nn(1) xa by (auto simp: noneg_def)
  have "tnoneg (T \<rightarrow>\<^sub>T A)" by (rule closed_typing_tnoneg[OF tf(1) nn(2)])
  then have nU: "tnoneg U" by (simp add: tnoneg_def UA)
  have ztr: "zprf_tr ax0 = equality_axmT STR ''abstract_rule'' [T, U] %> f %> g"
    using tr(2) by (simp add: zeq_vars_def df dg zeq_typs_ab[OF _ nT nU])
  obtain w where w: "pcerase w = pcerase (zprf_tr prf)" "prf_valid ax (set hs) (th_tpairs th0) w (th_prop th0)"
    using p by (rule zvalidE)
  have aw: "a \<notin> fnames (close A)" if "A \<in> prf_atoms w" for A a
    using that arg_cong[OF w(1), of prf_atoms] zeq_close_okD(1)[OF eqc] by fastforce
  have v: "prf_valid ax (set hs) (th_tpairs th) (PAppp (eqax STR ''abstract_rule'' (Some [T, U]) %> f %> g)
      (Abst b (Some T) (prf_abstract_over x w))) (th_prop th)"
    by (rule abstract_rule_proof_valid_ann[OF ok w(2) wt tx _ ad]) (use aw in auto)
  have cz': "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = typ_of (ztyp_of T) \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) prf"
    using cz by (simp only: tT)
  have "pcerase (PAppp (eqax STR ''abstract_rule'' (Some [T, U]) %> f %> g) (Abst b (Some T) (prf_abstract_over x w))) =
      pcerase (zprf_tr q)"
    using zprf_tr_zabstract_proof[OF xv cz', of 0]
    by (simp add: q ztr tT dx prf_abstract_over_def pcerase_prf_abstract_over_aux w(1) eqax_def equality_axmT_def)
  from zvalidI[OF this v] show "zvalid ax (set hs) (th_tpairs th) q (th_prop th)" .
  show "zconsts_ok q" using tr(1) zconsts_ok_zabstract_proof[OF zc] by (simp add: q)
qed

end

end
