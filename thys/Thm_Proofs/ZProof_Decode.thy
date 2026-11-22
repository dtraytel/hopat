section \<open>Decoding tight terms and proofs\<close>

theory ZProof_Decode
  imports Proof_Bicompose
begin

text \<open>
  The tight terms of \<open>ZTerm\<close> do not carry the types of constants: a constant is converted with
  the instances of the type variables of its declared type (\<open>Consts.typargs\<close>). Decoding
  recovers the term from these type arguments and the declared types of the signature. The
  conversion \<^const>\<open>zterm_of\<close> is parametric in the type arguments of constants; here they are
  computed from the declared types (\<open>ztargs\<close>). With fix \<open>zterm-ofclass\<close>, only proper class
  membership propositions become \<open>OFCLASS\<close>, so that decoding inverts the conversion on all
  well-typed terms. A tight proof stands for the classic proof with the decoded terms and types as
  annotations (\<open>zprf_tr\<close>).
\<close>

context pure_sig_gen
begin

subsection \<open>Tight proofs\<close>

text \<open>
  The proof constants of the equality axioms (\<^const>\<open>zaxiom_proof\<close>) are translated to the
  classic axioms with the type instances that the constant records for \<open>'a\<close> and \<open>'b\<close>
  (\<^const>\<open>equality_axmT\<close>), applied to the instances of their variables, in the order of their
  quantification in the closure of the axiom (\<open>Logic.close_form\<close>). The instances of the variables
  are looked up by the names of the variables (index \<open>-1\<close>), since their types are instantiated.
  The proof constants of other axioms (\<open>ZTerm.axiom_proof\<close>) are translated to the classic axioms
  with their propositions and with the type instances that the constant records for the type
  arguments \<open>ta\<close> of the proposition, applied to the instances of their variables, in the order of
  their quantification in the closure of the axiom (\<open>Proofterm.forall_intr_variables_term\<close>),
  looked up by name; the proof boxes of theorems likewise to classic proof boxes
  (\<^const>\<open>zthm_tr\<close>); oracles have no translation. The list of type arguments of a proposition
  is a parameter (the locale \<open>prf_sig\<close> of the proof judgment fixes it).
\<close>

definition zconst_trT :: "(pterm \<Rightarrow> (indexname \<times> psort) list) \<Rightarrow> zproof_const \<Rightarrow> prf" where
  "zconst_trT ta c =
    (case c of ((ZAxiom n, A), (instT, tab)) \<Rightarrow>
      if zeq_const n A then
        zeq_tr n (zinst_typs instT zeq_tvars) (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1)))
      else zax_tr n (zdec A) (zinst_typs instT (ta (zdec A))) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))
    | ((ZThm _, A), (instT, tab)) \<Rightarrow>
        zthm_tr (zdec A) (zinst_typs instT (ta (zdec A))) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))
    | _ \<Rightarrow> MinProof)"

fun zprf_trT :: "(pterm \<Rightarrow> (indexname \<times> psort) list) \<Rightarrow> zproof \<Rightarrow> prf" where
  "zprf_trT ta ZNop = MinProof"
| "zprf_trT ta (ZConstp c) = zconst_trT ta c"
| "zprf_trT ta (ZBoundp i) = PBound i"
| "zprf_trT ta (ZAbst a T p) = Abst a (Some (typ_of T)) (zprf_trT ta p)"
| "zprf_trT ta (ZAbsp a t p) = AbsP a (Some (zdec t)) (zprf_trT ta p)"
| "zprf_trT ta (ZAppt p t) = PAppt (zprf_trT ta p) (Some (zdec t))"
| "zprf_trT ta (ZAppp p q) = PAppp (zprf_trT ta p) (zprf_trT ta q)"
| "zprf_trT ta (ZHyp t) = Hyp (zdec t)"
| "zprf_trT ta (OFCLASSp T c) = PClass (typ_of T) c"

end

context prf_sig_gen
begin

abbreviation zconst_tr :: "zproof_const \<Rightarrow> prf" where "zconst_tr \<equiv> zconst_trT tyargs"
abbreviation zprf_tr :: "zproof \<Rightarrow> prf" where "zprf_tr \<equiv> zprf_trT tyargs"

end

text \<open>A map of classic proofs that maps the terms of applications maps the translations:\<close>

lemma those_map_option: "those (map (\<lambda>x. map_option g (f x)) xs) = map_option (map g) (those (map f xs))"
  by (induction xs) (auto simp: option.map_comp comp_def split: option.splits)

lemma foldl_PAppt_map:
  assumes "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))"
  shows "F (foldl (\<lambda>p t. PAppt p (Some t)) p0 ts) = foldl (\<lambda>p t. PAppt p (Some t)) (F p0) (map g ts)"
  by (induction ts arbitrary: p0) (simp_all add: assms)

lemma zeq_tr_map:
  assumes "F MinProof = MinProof" "\<And>a. F (equality_axmT a Us) = equality_axmT a Us'"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))"
  shows "F (zeq_tr n Us look) = zeq_tr n Us' (\<lambda>x. map_option g (look x))"
  by (simp add: zeq_tr_def those_map_option foldl_PAppt_map[OF assms(3)] assms(1,2)
      split: option.splits prod.splits)

lemma foldl_PAppt_map_option:
  assumes "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (foldl PAppt p0 us) = foldl PAppt (F p0) (map (map_option g) us)"
proof (induction us arbitrary: p0)
  case (Cons u us)
  have "F (PAppt p0 u) = PAppt (F p0) (map_option g u)" by (cases u) (simp_all add: assms)
  with Cons show ?case by simp
qed simp

lemma zax_tr_map:
  assumes "F (PAxm n A (Some Us)) = PAxm n A (Some Us')"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (zax_tr n A Us look) = zax_tr n A Us' (\<lambda>x. map_option g (look x))"
proof -
  have m: "map (map_option g) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A)) =
      map (\<lambda>v. case v of Var xi _ \<Rightarrow> map_option g (look xi) | _ \<Rightarrow> None) (term_variables A)"
    by (simp add: map_eq_conv split: pterm.splits)
  show ?thesis unfolding zax_tr_def foldl_PAppt_map_option[OF assms(2,3)] assms(1) m by (rule HOL.refl)
qed

lemma zthm_tr_map:
  assumes "F (PThm (zthm_head A Us)) = PThm (zthm_head A Us')"
    "\<And>p t. F (PAppt p (Some t)) = PAppt (F p) (Some (g t))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
  shows "F (zthm_tr A Us look) = zthm_tr A Us' (\<lambda>x. map_option g (look x))"
proof -
  have m: "map (map_option g) (map (\<lambda>v. case v of Var xi _ \<Rightarrow> look xi | _ \<Rightarrow> None) (term_variables A)) =
      map (\<lambda>v. case v of Var xi _ \<Rightarrow> map_option g (look xi) | _ \<Rightarrow> None) (term_variables A)"
    by (simp add: map_eq_conv split: pterm.splits)
  show ?thesis unfolding zthm_tr_def foldl_PAppt_map_option[OF assms(2,3)] assms(1) m by (rule HOL.refl)
qed

lemma zv_lookup_zv_map [simp]: "zv_lookup (zv_map f t) k = map_option f (zv_lookup t k)"
  by transfer simp

lemma zv_map_ident [simp]: "zv_map (\<lambda>x. x) t = t"
  by transfer (simp add: comp_def option.map_ident)

lemma zv_lookup_name_zv_map [simp]: "zv_lookup_name (zv_map f t) xi = map_option f (zv_lookup_name t xi)"
  by (simp add: zv_lookup_name_def)

text \<open>
  The names of the variables of the instances of proof constants are distinct (the constants of
  the equality axioms are built so, and maps of the types of the variables keep this):
\<close>

definition ztab_names_ok :: "'a zvtab \<Rightarrow> bool" where
  "ztab_names_ok t \<longleftrightarrow> (\<forall>k1 k2. zv_lookup t k1 \<noteq> None \<longrightarrow> zv_lookup t k2 \<noteq> None \<longrightarrow> fst k1 = fst k2 \<longrightarrow> k1 = k2)"

fun zconsts_ok :: "zproof \<Rightarrow> bool" where
  "zconsts_ok (ZConstp (c, instT, tab)) = ztab_names_ok tab"
| "zconsts_ok (ZAbst a T p) = zconsts_ok p"
| "zconsts_ok (ZAbsp a t p) = zconsts_ok p"
| "zconsts_ok (ZAppt p t) = zconsts_ok p"
| "zconsts_ok (ZAppp p q) = (zconsts_ok p \<and> zconsts_ok q)"
| "zconsts_ok _ = True"

lemma zv_lookup_name_Some:
  assumes "ztab_names_ok t" "zv_lookup t (xi, T) = Some v"
  shows "zv_lookup_name t xi = Some v"
proof -
  have u: "\<exists>!T. zv_lookup t (xi, T) \<noteq> None"
  proof (rule ex1I[of _ T])
    show "zv_lookup t (xi, T) \<noteq> None" using assms(2) by simp
    fix T' assume "zv_lookup t (xi, T') \<noteq> None"
    with assms(1,2) have "(xi, T') = (xi, T)" unfolding ztab_names_ok_def by fastforce
    then show "T' = T" by simp
  qed
  then have "(THE T. zv_lookup t (xi, T) \<noteq> None) = T"
    using assms(2) by (intro the1_equality) auto
  with u assms(2) show ?thesis by (simp add: zv_lookup_name_def)
qed

lemma zv_lookup_name_None:
  "ztab_names_ok t \<Longrightarrow> zv_lookup_name t xi = None \<longleftrightarrow> (\<forall>T. zv_lookup t (xi, T) = None)"
  by (metis option.distinct(1) zv_lookup_name_Some zv_lookup_name_def not_None_eq)

lemma zv_lookup_nameD: "zv_lookup_name t xi = Some v \<Longrightarrow> \<exists>T. zv_lookup t (xi, T) = Some v"
  by (auto simp: zv_lookup_name_def split: if_splits)

lemma ztab_names_ok_zv_map [simp]: "ztab_names_ok (zv_map f t) = ztab_names_ok t"
  by (simp add: ztab_names_ok_def)

subsection \<open>Instances of proof constants\<close>

lemma zv_lookup_zv_update: "zv_lookup (zv_update (k, x) t) k' = (if k' = k then Some x else zv_lookup t k')"
  by transfer simp

lemma zv_lookup_zv_empty [simp]: "zv_lookup zv_empty k = None"
  by transfer simp

lemma zv_insert_list_distinct:
  assumes "distinct (map fst xs)" "\<And>k. k \<in> fst ` set xs \<Longrightarrow> zv_lookup t k = None"
  shows "\<exists>t'. zv_insert_list xs t = Some t' \<and> (\<forall>k. zv_lookup t' k = (case map_of xs k of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup t k))"
  using assms
proof (induction xs arbitrary: t)
  case (Cons kx xs)
  obtain k x where kx: "kx = (k, x)" by (cases kx)
  have "zv_lookup (zv_update (k, x) t) k' = None" if "k' \<in> fst ` set xs" for k'
    using Cons.prems that kx by (auto simp: zv_lookup_zv_update)
  from Cons.IH[of "zv_update (k, x) t"] Cons.prems this obtain t' where
    "zv_insert_list xs (zv_update (k, x) t) = Some t'"
    "\<forall>k'. zv_lookup t' k' = (case map_of xs k' of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup (zv_update (k, x) t) k')"
    by (auto simp: kx)
  moreover have "zv_lookup t k = None" using Cons.prems kx by simp
  moreover have "map_of xs k = None" using Cons.prems(1) kx by (simp add: map_of_eq_None_iff)
  ultimately show ?case by (auto simp: kx zv_lookup_zv_update split: option.splits)
qed simp

lemma map_insts_names:
  assumes m: "map_insts typ term (instT, tab) = return (instT', tab')" and ok: "ztab_names_ok tab"
  shows "ztab_names_ok tab'" "zv_lookup_name tab' xi = None \<longleftrightarrow> zv_lookup_name tab xi = None"
    "zv_lookup_name tab xi = Some t \<Longrightarrow> \<exists>t'. term t = return t' \<and> zv_lookup_name tab' xi = Some t'"
proof -
  let ?d = "zv_dest tab"
  from m obtain xs where xs: "mapM (\<lambda>((x, T), t). do {t' \<leftarrow> term t; return ((x, typ T), t')}) ?d = return xs"
    and mk: "make_inst xs = return tab'"
    by (auto simp: map_insts_def bindZ_eq_returnZ)
  have l2: "list_all2 (\<lambda>(k, t) (k', t'). k' = (fst k, typ (snd k)) \<and> term t = return t') ?d xs"
    using xs unfolding mapZ_eq_returnZ
    by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
  have ds: "distinct (map fst ?d)" "set ?d = {(k, x). zv_lookup tab k = Some x}" using zv_dest_spec[of tab] by simp_all
  have fx: "map fst xs = map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d)"
    using l2 by (induction rule: list_all2_induct) auto
  have inj: "inj_on (\<lambda>k. (fst k, typ (snd k))) (fst ` set ?d)"
    using ok ds(2) by (auto simp: inj_on_def ztab_names_ok_def)
  have "distinct (map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d))"
    by (rule distinct_map[THEN iffD2]) (simp add: ds(1) inj)
  then have dx: "distinct (map fst xs)" by (simp only: fx)
  from zv_insert_list_distinct[OF dx zv_lookup_zv_empty] obtain t0 where
    t0: "zv_insert_list xs zv_empty = Some t0"
      "\<forall>k. zv_lookup t0 k = (case map_of xs k of Some x \<Rightarrow> Some x | None \<Rightarrow> zv_lookup zv_empty k)"
    by blast
  have t0': "\<forall>k. zv_lookup t0 k = map_of xs k"
  proof
    fix k show "zv_lookup t0 k = map_of xs k" using spec[OF t0(2), of k] by (cases "map_of xs k") auto
  qed
  have tab': "tab' = t0" using mk t0(1) by (simp add: make_inst_def return_def)
  have xsl: "\<exists>x. (k, x) \<in> set ?d \<and> (\<forall>t'. term x = return t' \<longrightarrow> map_of xs (fst k, typ (snd k)) = Some t')"
    if "(k, x) \<in> set ?d" for k x
  proof -
    from that obtain i where i: "i < length ?d" "?d ! i = (k, x)" by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF l2 i(1)] i obtain t' where xi: "xs ! i = ((fst k, typ (snd k)), t')" "term x = return t'"
      by (cases "xs ! i") auto
    have "i < length xs" using i(1) list_all2_lengthD[OF l2] by simp
    then have "map_of xs (fst k, typ (snd k)) = Some t'" using dx xi(1)
      by (metis map_of_is_SomeI nth_mem)
    with xi(2) that show ?thesis by auto
  qed
  have keys': "zv_lookup tab' k' \<noteq> None \<longleftrightarrow> (\<exists>k. k' = (fst k, typ (snd k)) \<and> zv_lookup tab k \<noteq> None)" for k'
  proof -
    have "zv_lookup tab' k' \<noteq> None \<longleftrightarrow> k' \<in> set (map fst xs)" by (simp add: tab' t0' map_of_eq_None_iff)
    also have "\<dots> \<longleftrightarrow> (\<exists>k. k' = (fst k, typ (snd k)) \<and> zv_lookup tab k \<noteq> None)" using ds(2) by (force simp: fx)
    finally show ?thesis .
  qed
  show ok': "ztab_names_ok tab'"
    unfolding ztab_names_ok_def
  proof (intro allI impI)
    fix k1 k2 assume "zv_lookup tab' k1 \<noteq> None" "zv_lookup tab' k2 \<noteq> None" "fst k1 = fst k2"
    then obtain j1 j2 where j: "k1 = (fst j1, typ (snd j1))" "zv_lookup tab j1 \<noteq> None"
      "k2 = (fst j2, typ (snd j2))" "zv_lookup tab j2 \<noteq> None" using keys' by blast
    with \<open>fst k1 = fst k2\<close> have "fst j1 = fst j2" by simp
    with j(2,4) ok have "j1 = j2" unfolding ztab_names_ok_def by blast
    with j(1,3) show "k1 = k2" by simp
  qed
  have "(\<forall>T. zv_lookup tab' (xi, T) = None) \<longleftrightarrow> (\<forall>T. zv_lookup tab (xi, T) = None)"
  proof
    assume a: "\<forall>T. zv_lookup tab' (xi, T) = None"
    show "\<forall>T. zv_lookup tab (xi, T) = None"
    proof (rule ccontr)
      assume "\<not> (\<forall>T. zv_lookup tab (xi, T) = None)"
      then obtain T where "zv_lookup tab (xi, T) \<noteq> None" by blast
      then have "zv_lookup tab' (xi, typ T) \<noteq> None" using keys'[of "(xi, typ T)"] by fastforce
      then show False by (simp add: a)
    qed
  next
    assume a: "\<forall>T. zv_lookup tab (xi, T) = None"
    show "\<forall>T. zv_lookup tab' (xi, T) = None"
    proof (rule ccontr)
      assume "\<not> (\<forall>T. zv_lookup tab' (xi, T) = None)"
      then obtain T where "zv_lookup tab' (xi, T) \<noteq> None" by blast
      then obtain k where "(xi, T) = (fst k, typ (snd k))" "zv_lookup tab k \<noteq> None" using keys' by blast
      then have "zv_lookup tab (xi, snd k) \<noteq> None" by (cases k) auto
      then show False by (simp add: a)
    qed
  qed
  then show "zv_lookup_name tab' xi = None \<longleftrightarrow> zv_lookup_name tab xi = None"
    by (simp add: zv_lookup_name_None[OF ok] zv_lookup_name_None[OF ok'])
  assume "zv_lookup_name tab xi = Some t"
  then obtain T where T: "zv_lookup tab (xi, T) = Some t" by (blast dest: zv_lookup_nameD)
  then have "((xi, T), t) \<in> set ?d" using ds(2) by simp
  from xsl[OF this] obtain x where x: "((xi, T), x) \<in> set ?d"
    "\<forall>t'. term x = return t' \<longrightarrow> map_of xs (xi, typ T) = Some t'" by auto
  from x(1) ds(2) have "zv_lookup tab (xi, T) = Some x" by simp
  with T have "x = t" by simp
  from x(1) obtain t' where "term t = return t'"
    using l2 \<open>x = t\<close> by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  with x(2) \<open>x = t\<close> have "zv_lookup tab' (xi, typ T) = Some t'" by (simp add: tab' t0')
  with \<open>term t = return t'\<close> show "\<exists>t'. term t = return t' \<and> zv_lookup_name tab' xi = Some t'"
    using zv_lookup_name_Some[OF ok'] by blast
qed

lemma map_insts_values:
  assumes m: "map_insts typ term (instT, tab) = return (instT', tab')" and ok: "ztab_names_ok tab"
    and l: "zv_lookup tab' k = Some t'"
  shows "\<exists>k0 t. zv_lookup tab k0 = Some t \<and> term t = return t'"
proof -
  obtain xi T where k: "k = (xi, T)" by (cases k)
  have ok': "ztab_names_ok tab'" by (rule map_insts_names(1)[OF m ok])
  have n': "zv_lookup_name tab' xi = Some t'" using zv_lookup_name_Some[OF ok'] l k by simp
  then obtain t where n: "zv_lookup_name tab xi = Some t" using map_insts_names(2)[OF m ok, of xi] by auto
  from map_insts_names(3)[OF m ok n] n' have "term t = return t'" by auto
  moreover from zv_lookup_nameD[OF n] obtain U where "zv_lookup tab (xi, U) = Some t" by blast
  ultimately show ?thesis by blast
qed

text \<open>Instances mapped by a total function:\<close>

lemma map_insts_return:
  assumes ok: "ztab_names_ok tab"
  shows "\<exists>tab'. map_insts typ (\<lambda>t. return (f t)) (instT, tab) = return (zt_map typ instT, tab') \<and>
    ztab_names_ok tab' \<and> (\<forall>xi. zv_lookup_name tab' xi = map_option f (zv_lookup_name tab xi))"
proof -
  let ?d = "zv_dest tab"
  let ?xs = "map (\<lambda>((x, T), t). ((x, typ T), f t)) ?d"
  have ds: "distinct (map fst ?d)" "set ?d = {(k, x). zv_lookup tab k = Some x}"
    using zv_dest_spec[of tab] by simp_all
  have m: "mapM (\<lambda>((x, T), t). return ((x, typ T), f t)) ?d = return ?xs"
    unfolding mapZ_eq_returnZ list.rel_map by (rule list.rel_refl) auto
  have fx: "map fst ?xs = map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d)" by (auto split: prod.splits)
  have inj: "inj_on (\<lambda>k. (fst k, typ (snd k))) (fst ` set ?d)"
    using ok ds(2) by (auto simp: inj_on_def ztab_names_ok_def)
  have "distinct (map (\<lambda>k. (fst k, typ (snd k))) (map fst ?d))"
    by (rule distinct_map[THEN iffD2]) (simp add: ds(1) inj)
  then have dx: "distinct (map fst ?xs)" by (simp only: fx)
  from zv_insert_list_distinct[OF dx zv_lookup_zv_empty] obtain t0 where
    "zv_insert_list ?xs zv_empty = Some t0" by blast
  then have mi: "map_insts typ (\<lambda>t. return (f t)) (instT, tab) = return (zt_map typ instT, t0)"
    by (simp add: map_insts_def m make_inst_def)
  have "zv_lookup_name t0 xi = map_option f (zv_lookup_name tab xi)" for xi
  proof (cases "zv_lookup_name tab xi")
    case None
    then show ?thesis using map_insts_names(2)[OF mi ok, of xi] by simp
  next
    case (Some t)
    then show ?thesis using map_insts_names(3)[OF mi ok Some] by simp
  qed
  with mi map_insts_names(1)[OF mi ok] show ?thesis by blast
qed

context pure_sig_gen
begin

text \<open>
  A map of classic proofs that maps the type arguments of atoms by \<open>h\<close> and the terms of
  applications by \<open>g\<close> maps the translation of a proof constant to the translation of the
  constant with the mapped tables:
\<close>

lemma zconst_tr_map_tab:
  assumes "F MinProof = MinProof" "\<And>a Us. F (equality_axmT a Us) = equality_axmT a (map h Us)"
    "\<And>p u. F (PAppt p (Some u)) = PAppt (F p) (Some (g u))"
    "\<And>xi. zv_lookup_name tab' xi = map_option f (zv_lookup_name tab xi)"
    "\<And>k t. zv_lookup tab k = Some t \<Longrightarrow> g (zdec t) = zdec (f t)"
    "\<And>n A Us. F (PAxm n A (Some Us)) = PAxm n A (Some (map h Us))" "\<And>p. F (PAppt p None) = PAppt (F p) None"
    "\<And>A Us. F (PThm (zthm_head A Us)) = PThm (zthm_head A (map h Us))"
    "\<And>vs. map h (zinst_typs instT vs) = zinst_typs instT' vs"
  shows "F (zconst_trT ta (c, instT, tab)) = zconst_trT ta (c, instT', tab')"
proof -
  obtain nm A where c: "c = (nm, A)" by (cases c)
  have l: "map_option g (map_option zdec (zv_lookup_name tab xi)) =
      map_option zdec (zv_lookup_name tab' xi)" for xi
  proof (cases "zv_lookup_name tab xi")
    case (Some t)
    from zv_lookup_nameD[OF Some] obtain T where "zv_lookup tab (xi, T) = Some t" by blast
    with Some assms(4,5) show ?thesis by simp
  qed (simp add: assms(4))
  show ?thesis
  proof (cases nm)
    case (ZAxiom n)
    show ?thesis
    proof (cases "zeq_const n A")
      case True
      have "F (zeq_tr n (zinst_typs instT zeq_tvars) (\<lambda>x. map_option zdec (zv_lookup_name tab (x, -1)))) =
          zeq_tr n (zinst_typs instT' zeq_tvars) (\<lambda>x. map_option g (map_option zdec (zv_lookup_name tab (x, -1))))"
        by (rule zeq_tr_map[OF assms(1) _ assms(3)]) (simp add: assms(2,9))
      then show ?thesis using True by (simp add: zconst_trT_def c ZAxiom l)
    next
      case False
      have "F (zax_tr n (zdec A) (zinst_typs instT (ta (zdec A))) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))) =
          zax_tr n (zdec A) (zinst_typs instT' (ta (zdec A))) (\<lambda>xi. map_option g (map_option zdec (zv_lookup_name tab xi)))"
        by (rule zax_tr_map[OF _ assms(3,7)]) (simp add: assms(6,9))
      then show ?thesis using False by (simp add: zconst_trT_def c ZAxiom l)
    qed
  next
    case (ZThm n)
    have "F (zthm_tr (zdec A) (zinst_typs instT (ta (zdec A))) (\<lambda>xi. map_option zdec (zv_lookup_name tab xi))) =
        zthm_tr (zdec A) (zinst_typs instT' (ta (zdec A))) (\<lambda>xi. map_option g (map_option zdec (zv_lookup_name tab xi)))"
      by (rule zthm_tr_map[OF _ assms(3,7)]) (simp add: assms(8,9))
    then show ?thesis by (simp add: zconst_trT_def c ZThm l)
  qed (simp_all add: zconst_trT_def c assms(1))
qed

text \<open>For a map that leaves the type arguments of atoms as they are:\<close>

lemma zconst_tr_map:
  assumes "F MinProof = MinProof" "\<And>a Us. F (equality_axmT a Us) = equality_axmT a Us"
    "\<And>p u. F (PAppt p (Some u)) = PAppt (F p) (Some (g u))"
    "\<And>k t. zv_lookup tab k = Some t \<Longrightarrow> g (zdec t) = zdec (f t)"
    "\<And>n A Us. F (PAxm n A (Some Us)) = PAxm n A (Some Us)" "\<And>p. F (PAppt p None) = PAppt (F p) None"
    "\<And>A Us. F (PThm (zthm_head A Us)) = PThm (zthm_head A Us)"
  shows "F (zconst_trT ta (c, instT, tab)) = zconst_trT ta (c, instT, zv_map f tab)"
  by (rule zconst_tr_map_tab[where F = F and g = g and tab' = "zv_map f tab" and f = f and tab = tab
        and h = "\<lambda>T. T"])
    (use assms in simp_all)

end

end
