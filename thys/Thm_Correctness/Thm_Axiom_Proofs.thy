section \<open>Proofs: Thm_Axiom\<close>

theory Thm_Axiom_Proofs
  imports "Thm_Soundness.Thm_Axiom" Thm_Rules4_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Axiom\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

context prf_sig
begin

lemma all_var_typing:
  assumes R: "e \<turnstile> R : propT" "closed R" and T: "cert_typ alg ar T"
  shows "e \<turnstile> all_var (Var (x, i) T) R : propT" "closed (all_var (Var (x, i) T) R)"
proof -
  let ?b = "abstract_over_aux (Var (x, i) T) 0 R"
  have "e\<langle>0:T\<rangle> \<turnstile> ?b : propT"
    by (rule typing_abstract_over_aux[of _ _ T]) (use R in \<open>simp_all add: closed_def shift_def\<close>)
  then show "e \<turnstile> all_var (Var (x, i) T) R : propT"
    using T by (simp add: all_var_def abstract_over_def typing_all_const all_type_def cert_typ_fun)
  have "\<not> loose_bvar ?b 1"
    by (rule loose_bvar_abstract_over_aux) (use R(2) loose_bvar_mono in \<open>auto simp: closed_def\<close>)
  then show "closed (all_var (Var (x, i) T) R)"
    by (simp add: all_var_def abstract_over_def closed_def all_const_def)
qed

lemma all_var_beta:
  assumes R: "e \<turnstile> R : propT" "closed R" and T: "cert_typ alg ar T"
  obtains a f where "all_var (Var (x, i) T) R = all_const T $ f" "f $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R"
proof -
  let ?b = "abstract_over_aux (Var (x, i) T) 0 R" and ?a = "if x = STR '''' then STR ''uu'' else x"
  have "e \<turnstile> all_var (Var (x, i) T) R : propT" by (rule all_var_typing[OF R T])
  then have tb: "e \<turnstile> Abs ?a T ?b : T \<rightarrow>\<^sub>T propT"
    by (auto simp: all_var_def abstract_over_def all_const_def)
  have "Abs ?a T ?b $ Var (x, i) T \<rightarrow>\<^sub>\<beta> ?b[Var (x, i) T/0]" by (rule beta.beta)
  moreover have "?b[Var (x, i) T/0] = R"
    by (rule subst_abstract_over_aux_Var) (use R(2) in \<open>simp_all add: closed_def\<close>)
  moreover have "wt (Abs ?a T ?b $ Var (x, i) T)"
    using tb T unfolding wt_def by (blast intro: typing.App typing.Var)
  ultimately have "Abs ?a T ?b $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R" using conv_beta by metis
  then show thesis by (intro that[of "Abs ?a T ?b"]) (simp_all add: all_var_def abstract_over_def)
qed

end

context prf_sig
begin

lemma closure_typing:
  assumes "\<forall>v\<in>set vs. \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T" "e \<turnstile> B : propT" "closed B"
  shows "e \<turnstile> foldr all_var vs B : propT \<and> closed (foldr all_var vs B)"
  using assms(1)
proof (induction vs)
  case (Cons w ws)
  from Cons.prems obtain y j U where w: "w = Var (y, j) U" and U: "cert_typ alg ar U" by force
  from Cons.IH Cons.prems have "e \<turnstile> foldr all_var ws B : propT" "closed (foldr all_var ws B)" by simp_all
  from all_var_typing[OF this U] show ?case by (simp add: w)
qed (use assms in simp)

end

context prf_sig
begin

text \<open>A proof of the closure applied to the variables, or to no arguments, proves the proposition:\<close>

lemma prf_ok_closure_chain:
  assumes "prf_ok ax H E e Hs p (foldr all_var vs B)"
    and vs: "\<forall>v\<in>set vs. \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T"
    and B: "e \<turnstile> B : propT" "closed B"
    and os: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us vs"
  shows "prf_ok ax H E e Hs (foldl PAppt p us) B"
  using os assms(1) vs
proof (induction us vs arbitrary: p rule: list_all2_induct)
  case (Cons u us v vs)
  from Cons.prems(2) obtain x i T where v: "v = Var (x, i) T" and T: "cert_typ alg ar T" by force
  let ?R = "foldr all_var vs B"
  from closure_typing[OF _ B] Cons.prems(2) have tR: "e \<turnstile> ?R : propT" "closed ?R" by simp_all
  obtain f where f: "all_var (Var (x, i) T) ?R = all_const T $ f" "f $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?R"
    by (rule all_var_beta[OF tR T])
  have "prf_ok ax H E e Hs p (all_const T $ f)" using Cons.prems(1) f(1) v by simp
  then have "prf_ok ax H E e Hs (PAppt p u) (f $ Var (x, i) T)"
    by (rule prf_ok.PAppt) (use Cons.hyps T v in \<open>auto simp: ann_ok_def ueq_refl intro: typing.Var\<close>)
  then have "prf_ok ax H E e Hs (PAppt p u) ?R" by (rule prf_ok.conv[OF _ f(2) tR(1)])
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed (simp add: assms)

text \<open>
  The proof constant of an axiom whose closure is that of \<open>Proofterm\<close>, applied to its variables
  (or to no arguments), proves the axiom:
\<close>

lemma prf_ok_axiom_chain:
  assumes ax: "ax B" and nm: "axm_name_ok n B" and cl: "close B = forall_closure B"
    and ta: "\<forall>(v, S)\<in>set (tyargs B). sort_ok alg S"
    and wB: "wtp B" and fB: "fnames B = {}"
    and us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us (variables_of B)"
    and tn: "Ts = None \<or> Ts = Some (map (\<lambda>(v, S). TVar v S) (tyargs B))"
  shows "prf_ok ax H E e Hs (foldl PAppt (PAxm n B Ts) us) B"
proof -
  let ?Us = "map (\<lambda>(v, S). TVar v S) (tyargs B)"
  have vc: "\<forall>v\<in>set (variables_of B). \<exists>xi T. v = Var xi T \<and> cert_typ alg ar T"
  proof
    fix v assume "v \<in> set (variables_of B)"
    then obtain xi T where "v = Var xi T" "(xi, T) \<in> vars B" by (rule variables_of_Var[OF fB])
    with typing_vars_cert'[OF wtpD(2)[OF wB, of e]] show "\<exists>xi T. v = Var xi T \<and> cert_typ alg ar T" by blast
  qed
  have ct: "e \<turnstile> close B : propT"
    using closure_typing[OF vc wtpD(2)[OF wB] wtpD(1)[OF wB]] by (simp add: cl forall_closure_def)
  have ap: "atom_prop B ?Us = close B" by (simp add: atom_prop_def tyinst_ident)
  have "atom_ok B None ?Us"
    unfolding atom_ok_def list_all2_map2 option.case(1)
    using ta by (auto intro!: list.rel_refl_strong simp: cert_typ_TVar simp del: has_sort.simps)
  then have ao: "atom_ok B Ts ?Us" using tn by (auto simp: atom_ok_def)
  have "prf_ok ax H E e Hs (PAxm n B Ts) (atom_prop B ?Us)"
    by (rule prf_ok.PAxm[of ax B, OF ax ao]) (use ct ap nm in simp_all)
  then have "prf_ok ax H E e Hs (PAxm n B Ts) (foldr all_var (variables_of B) B)"
    by (simp add: ap cl forall_closure_def)
  from prf_ok_closure_chain[OF this vc wtpD(2)[OF wB] wtpD(1)[OF wB] us] show ?thesis .
qed

end

lemma zterm_ok_types: "zterm_ok z \<Longrightarrow> Z \<in> set (zterm_types z) \<Longrightarrow> ztyp_ok Z"
  by (induction z) auto

lemma ztyp_ok_ztvar: "ztyp_ok Z \<Longrightarrow> (v, S) \<in> set (ztyp_tvars Z) \<Longrightarrow> ztyp_ok (ZTVar v S)"
  using ztyp_tvars_typ_of[of v S Z] unfolding ztyp_ok_def by (cases v) (fastforce split: if_splits)

lemma prf_idx_foldl_PAppt:
  "prf_idx P (foldl PAppt q us) \<longleftrightarrow> prf_idx P q \<and> (\<forall>u\<in>set us. \<forall>t\<in>set_option u. \<forall>v\<in>vars t. P (snd (fst v)))"
  by (induction us arbitrary: q) auto


lemma proofs_ok_axiom:
  assumes A: "sg_axioms c a = Some A" and sa: "sign_axioms invent c"
  shows "is_prf_sig (th_sign (axiom_data invent c a A)) \<Longrightarrow>
    proofs_ok (axiom_data invent c a A)"
proof -
  have ao: "ax_ok invent c a A" using sa A by (simp add: sign_axioms_def)
  have inv: "n \<le> length (invent (integer_of_nat n))" "distinct (invent (integer_of_nat n))" for n
    using sa by (simp_all add: sign_axioms_def)
  have nnv: "\<forall>v\<in>vars A. 0 \<le> snd (fst v)" and nnt: "\<forall>v\<in>ttvars A. 0 \<le> snd (fst v)" and fA: "fnames A = {}"
    and sf: "\<forall>U\<in>tatoms A. \<exists>v. U = TVar v []" and vc: "pure_sig_gen.vtcons (vars A)"
    using ao by (simp_all add: ax_ok_def)
  have wtA: "pure_sig_gen.wtp (sg_alg c) (sg_ar c) (sg_consts c) A" using ao by (simp add: ax_ok_def)
  assume psig: "is_prf_sig (th_sign (axiom_data invent c a A))"
  then have psig': "is_prf_sig c" by simp
  interpret prf_sig "sg_alg c" "sg_ar c" "sg_consts c" "sg_close c" "sg_tyargs c"
    using psig' by (simp add: is_prf_sig_def)
  have pA: "sg_ax c A" "axm_name_ok a A" "sg_close c A = forall_closure A" "\<forall>v\<in>set (sg_tyargs c A). v \<in> ttvars A"
    and pB: "\<And>outer B. ok (unconstrainT invent A) (outer, B) \<Longrightarrow> sg_ax c B \<and> axm_name_ok a B \<and>
      sg_close c B = forall_closure B \<and> (\<forall>v\<in>set (sg_tyargs c B). v \<in> ttvars B)"
    using ao psig' by (simp_all add: ax_ok_def)
  have wA: "wtp A" using wtA by simp
  have H: "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
  have nul: "\<And>P. prf_ok (sg_ax c) {} {} e [] P \<phi> = prf_ok (sg_ax c) {} (set []) e [] P \<phi>" for e \<phi> by simp
  show "proofs_ok (axiom_data invent c a A)" unfolding proofs_ok_def Let_def axiom_data_sel
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (axiom_data invent c a A) = returnW p"
    then have "ok (axiom_proof invent a A) p"
      by (auto simp: axiom_data_def liftMP_def returnW_def split: option.splits)
    then obtain args outer B where args: "ok (prop_args A) args" and un: "ok (unconstrainT invent A) (outer, B)"
      and p: "p = proof_combP (foldl PAppt (PAxm a B None) args) (map (\<lambda>(T, c). PClass T c) outer)"
      by (auto simp: axiom_proof_def split: prod.splits)
    obtain f \<rho> where o: "outer = []" and B: "B = map_types (map_atyps f) A"
      and fr: "\<And>U. U \<in> tatoms A \<Longrightarrow> tsubst \<rho> (f U) = U" and fv: "\<And>U. U \<in> tatoms A \<Longrightarrow> \<exists>a. f U = TVar (a, 0) []"
      and \<rho>: "\<And>v S. \<rho> v S = TVar v S \<or> (S = [] \<and> \<rho> v S \<in> tatoms A)" and fo: "\<And>U. U \<notin> tatoms A \<Longrightarrow> f U = U"
      by (rule unconstrainT_sortfree[OF sf inv(1) distinct_take[OF inv(2)] un]) blast
    have p': "p = foldl PAppt (PAxm a B None) args" by (simp add: p o proof_combP_def)
    note pb = pB[OF un]
    let ?\<rho>' = "\<lambda>v S. f (TVar v S)"
    have sfv: "\<And>U. U \<in> tatoms A \<Longrightarrow> \<exists>v S. U = TVar v S" using sf by blast
    have BI: "B = inst ?\<rho>' A" unfolding B by (rule map_types_inst[OF sfv])
    have ci': "cert_inst ?\<rho>'"
      unfolding cert_inst_def
    proof (intro allI impI)
      fix v S assume "sort_ok (sg_alg c) S"
      show "cert_typ (sg_alg c) (sg_ar c) (f (TVar v S))"
      proof (cases "TVar v S \<in> tatoms A")
        case True
        with fv obtain a' where "f (TVar v S) = TVar (a', 0) []" by blast
        then show ?thesis by (simp add: cert_typ_TVar sort_ok_def)
      next
        case False
        with \<open>sort_ok (sg_alg c) S\<close> show ?thesis by (simp add: fo cert_typ_TVar)
      qed
    qed
    have tyA: "\<And>e. e \<turnstile> A : propT" "closed A" using wtpD[OF wA] by blast+
    have "(\<lambda>j. tsubst ?\<rho>' ((\<lambda>_. propT) j)) \<turnstile> inst ?\<rho>' A : tsubst ?\<rho>' propT"
      by (rule typing_inst[OF tyA(1) cert_inst_inst_ok[OF ci']])
    then have tyB: "(\<lambda>j. tsubst ?\<rho>' ((\<lambda>_. propT) j)) \<turnstile> B : propT" by (simp add: BI propT_def)
    have wB: "wtp B" by (rule wtpI[OF _ tyB]) (use tyA(2) in \<open>simp add: BI closed_inst\<close>)
    have fB: "fnames B = {}" using fA by (simp add: B)
    have finj: "U = U'" if "U \<in> tatoms A" "U' \<in> tatoms A" "f U = f U'" for U U'
      using fr[OF that(1)] fr[OF that(2)] that(3) by metis
    have fat: "\<exists>v S. f U = TVar v S" if "U \<in> tatoms A" for U using fv[OF that] by blast
    have taB: "\<forall>(v, S)\<in>set (sg_tyargs c B). sort_ok (sg_alg c) S"
    proof (clarify)
      fix v S assume "(v, S) \<in> set (sg_tyargs c B)"
      with pb have "TVar v S \<in> tatoms B" by (auto intro: ttvars_tatoms)
      then obtain U where "U \<in> tatoms A" "TVar v S \<in> set (atyps (f U))"
        unfolding B tatoms_map_types_atyps by blast
      with fv show "sort_ok (sg_alg c) S" by (force simp: sort_ok_def)
    qed
    let ?g = "map_types (map_atyps f)"
    have vB: "variables_of B = map ?g (variables_of A)"
      by (rule variables_of_map[OF inj_map_types_aterms[OF finj fat] map_types_var_shape])
        (simp_all add: B aterms_map_types)
    let ?usB = "map (map_option ?g) args"
    have usB: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) ?usB (variables_of B)"
      using prop_args_vars[OF args] unfolding vB list_all2_map1 list_all2_map2
      by (rule list_all2_mono) auto
    have idv: "prf_valid (sg_ax c) {} [] (foldl PAppt (PAxm a B None) ?usB) B"
    proof (rule prf_valid_genericI)
      show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
      fix e
      show "prf_ok (sg_ax c) {} (set []) e [] (foldl PAppt (PAxm a B None) ?usB) B"
        by (rule prf_ok_axiom_chain[of "sg_ax c" B a, OF _ _ _ taB wB fB usB]) (use pb in simp_all)
    qed
    have c\<rho>: "cinst \<rho>"
      unfolding cinst_def wsinst_def cert_inst_def
    proof (intro conjI allI impI)
      fix v S
      show "has_sort (sg_alg c) (\<rho> v S) S" using \<rho>[of v S] by (metis has_sort_Nil has_sort_TVar_refl)
      assume "sort_ok (sg_alg c) S"
      consider "\<rho> v S = TVar v S" | "\<rho> v S \<in> tatoms A" using \<rho>[of v S] by blast
      then show "cert_typ (sg_alg c) (sg_ar c) (\<rho> v S)"
      proof cases
        case 1
        with \<open>sort_ok (sg_alg c) S\<close> show ?thesis by (simp add: cert_typ_TVar)
      next
        case 2
        with sf obtain w where "\<rho> v S = TVar w []" by blast
        then show ?thesis by (simp add: cert_typ_TVar sort_ok_def)
      qed
    qed
    have apv: "prf_valid (sg_ax c) {} [] (prf_ap \<rho> Var (foldl PAppt (PAxm a B None) ?usB)) (ap \<rho> Var B)"
      using prf_valid_ap[OF idv c\<rho> gsubst_Var H] by simp
    have iA: "inst \<rho> B = A" unfolding B by (rule inst_map_types_atyps[OF fr])
    have ia: "ap \<rho> Var (?g v) = v" if "v \<in> set (aterms A)" for v
      unfolding ap_def by (simp, rule inst_map_types_atyps[OF fr], use tatoms_aterms[OF that] in blast)
    have avs: "v \<in> set (variables_of A)" if "Some v \<in> set args" for v
    proof -
      from that obtain i where i: "i < length args" "args ! i = Some v" by (auto simp: in_set_conv_nth)
      have l: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) args (variables_of A)" by (rule prop_args_vars[OF args])
      from list_all2_nthD[OF l i(1)] i(2) have "v = variables_of A ! i" by simp
      moreover have "i < length (variables_of A)" using i(1) l by (simp add: list_all2_lengthD)
      ultimately show "v \<in> set (variables_of A)" by simp
    qed
    have aA: "v \<in> set (aterms A)" if "Some v \<in> set args" for v
      using avs[OF that] by (simp add: set_variables_of)
    have av: "\<exists>xi T. v = Var xi T \<and> (xi, T) \<in> vars A" if "Some v \<in> set args" for v
      using avs[OF that] by (blast elim: variables_of_Var[OF fA])
    have "map (map_option (ap \<rho> Var)) ?usB = args"
      unfolding map_map
    proof (rule map_idI)
      fix u assume "u \<in> set args"
      show "(map_option (ap \<rho> Var) \<circ> map_option ?g) u = u"
      proof (cases u)
        case (Some v)
        with \<open>u \<in> set args\<close> have "v \<in> set (aterms A)" by (intro aA) simp
        then show ?thesis using Some by (simp add: ia)
      qed simp
    qed
    then have pe: "prf_ap \<rho> Var (foldl PAppt (PAxm a B None) ?usB) = p"
      unfolding p' prf_ap_def by (subst foldl_PAppt_map_option[where g = "ap \<rho> Var"]) simp_all
    have "prf_valid (sg_ax c) (set []) [] p A" using apv by (simp add: pe iA ap_def)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) p"
    proof -
      have "\<forall>u\<in>set args. \<forall>t\<in>set_option u. \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
      proof (intro ballI)
        fix u t v assume "u \<in> set args" "t \<in> set_option u" "v \<in> vars t"
        then have "Some t \<in> set args" "v \<in> vars t" by auto
        with av nnv show "0 \<le> snd (fst v)" by fastforce
      qed
      then show ?thesis by (simp add: p' prf_idx_foldl_PAppt)
    qed
    moreover have "prf_nolb 0 p"
    proof -
      have "\<forall>u\<in>set args. \<forall>t. u = Some t \<longrightarrow> \<not> loose_bvar t 0"
        using av by fastforce
      then show ?thesis by (simp add: p' prf_nolb_foldl_PAppt')
    qed
    ultimately show "prf_valid (sg_ax c) (set []) [] p A \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" by blast
  next
    fix z assume "th_zproof (axiom_data invent c a A) = return z"
    then obtain zA where zA: "zterm_of ztargs A = return zA" and z: "z = ZConstp (zproof_const (ZAxiom a) zA)"
      by (auto simp: axiom_data_def zaxiom_proof_of_def bindZ_eq_returnZ)
    have tyA: "\<And>e. e \<turnstile> A : propT" "closed A" using wtpD[OF wA] by blast+
    have nA: "noneg A" using nnv nnt
      by (fastforce simp: noneg_def tnoneg_def ttvars_def integer_nonneg_ne_m1)
    have dz: "zdec zA = A"
      using zterm_of_zdec[OF tyA(1)] nA zA by (auto simp: noneg_def tnoneg_def)
    have zvA: "\<exists>T. (fst v, T) \<in> vars A \<and> snd v = ztyp_of T" if "v \<in> set (zterm_vars zA)" for v
      by (rule zterm_vars_zterm_of[OF zA fA that])
    have nz: "\<not> zeq_const a zA"
      by (rule not_zeq_const) (use zvA nnv in fastforce)
    define tab where "tab = fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) (zterm_vars zA) zv_empty"
    define instT where "instT = fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (concat (map ztyp_tvars (zterm_types zA))) zt_empty"
    have zc: "z = ZConstp ((ZAxiom a, zA), (instT, tab))" by (simp add: z zproof_const_def tab_def instT_def)
    have lk: "zv_lookup tab k = (if k \<in> set (zterm_vars zA) then Some (ZVar (fst k) (snd k)) else None)" for k
      by (simp add: tab_def zv_lookup_fold_update)
    let ?look = "\<lambda>xi. map_option zdec (zv_lookup_name tab xi)"
    let ?Us = "map (\<lambda>(v, S). TVar v S) (sg_tyargs c A)"
    have lT: "zt_lookup instT k = (if k \<in> set (concat (map ztyp_tvars (zterm_types zA)))
        then Some (ZTVar (fst k) (snd k)) else None)" for k
      by (simp add: instT_def zt_lookup_fold_update)
    have iU: "zinst_typs instT (sg_tyargs c A) = ?Us"
    proof (rule zinst_typs_ident[OF lT])
      show "set (sg_tyargs c A) \<subseteq> set (concat (map ztyp_tvars (zterm_types zA)))"
        using pA(4) ttvars_zdec[of _ _ zA] by (auto simp: dz)
      show "snd v \<noteq> -1" if "(v, S) \<in> set (sg_tyargs c A)" for v S
        using pA(4) that ttvars_zdec[of v S zA] by (auto simp: dz)
    qed
    have ztr: "zprf_tr z = zax_tr a A ?Us ?look" by (simp add: zc zconst_trT_def nz dz iU)
    have look: "?look xi = None \<or> ?look xi = Some (Var xi T)" if "(xi, T) \<in> vars A" for xi T
    proof (cases "zv_lookup_name tab xi")
      case (Some u)
      from zv_lookup_nameD[OF Some] obtain T' where "zv_lookup tab (xi, T') = Some u" by blast
      then have u: "(xi, T') \<in> set (zterm_vars zA)" "u = ZVar xi T'" by (simp_all add: lk split: if_splits)
      from zvA[OF u(1)] obtain T0 where "(xi, T0) \<in> vars A" "T' = ztyp_of T0" by auto
      moreover have "T0 = T" using vc \<open>(xi, T0) \<in> vars A\<close> that unfolding vtcons_def by blast
      ultimately have T': "T' = ztyp_of T" by simp
      have "snd xi \<noteq> -1" using nnv that by fastforce
      moreover have "typ_of (ztyp_of T) = T"
      proof (rule typ_of_ztyp_of)
        show "\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1"
          using nnt that by (fastforce simp: ttvars_def integer_nonneg_ne_m1 dest: vars_typs)
      qed
      ultimately show ?thesis by (simp add: Some u T')
    qed simp
    have us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v)
        (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of A)) (variables_of A)"
      unfolding list_all2_map1
      by (rule list.rel_refl_strong) (auto elim!: variables_of_Var[OF fA] dest: look)
    have taA: "\<forall>(v, S)\<in>set (sg_tyargs c A). sort_ok (sg_alg c) S"
      using pA(4) sf by (force dest: ttvars_tatoms simp: sort_ok_def)
    have v: "prf_valid (sg_ax c) {} [] (zprf_tr z) A"
      unfolding ztr zax_tr_def term_variables_eq
    proof (rule prf_valid_genericI)
      show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
      fix e
      show "prf_ok (sg_ax c) {} (set []) e [] (foldl PAppt (PAxm a A (Some ?Us))
          (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of A))) A"
        by (rule prf_ok_axiom_chain[of "sg_ax c" A a, OF pA(1,2,3) taA wA fA us]) simp
    qed
    have "zvalid (sg_ax c) (set []) [] z A" by (rule zvalidI[OF HOL.refl]) (use v in simp)
    moreover have "zinv z"
    proof -
      have "ztab_names_ok tab"
        unfolding ztab_names_ok_def
      proof (intro allI impI)
        fix k1 k2 assume "zv_lookup tab k1 \<noteq> None" "zv_lookup tab k2 \<noteq> None" "fst k1 = fst k2"
        then have "k1 \<in> set (zterm_vars zA)" "k2 \<in> set (zterm_vars zA)" "fst k1 = fst k2"
          by (simp_all add: lk split: if_splits)
        then obtain T1 T2 where "(fst k1, T1) \<in> vars A" "snd k1 = ztyp_of T1" "(fst k2, T2) \<in> vars A"
            "snd k2 = ztyp_of T2" "fst k1 = fst k2"
          using zvA by blast
        moreover from this(1,3,5) have "T1 = T2" using vc unfolding vtcons_def by metis
        ultimately show "k1 = k2" by (simp add: prod_eq_iff)
      qed
      moreover have "zterm_ok t" if "zv_lookup tab k = Some t" for k t
      proof -
        from that have k: "k \<in> set (zterm_vars zA)" "t = ZVar (fst k) (snd k)" by (simp_all add: lk split: if_splits)
        from zvA[OF k(1)] obtain T where T: "(fst k, T) \<in> vars A" "snd k = ztyp_of T" by blast
        have "tnn T" using nnt T(1) by (fastforce simp: tnn_def ttvars_def dest: vars_typs)
        with T nnv show ?thesis by (fastforce simp: k(2) ztyp_ok_ztyp_of)
      qed
      moreover have "ztyp_ok T" if "zt_lookup instT k = Some T" for k T
      proof -
        from that have k: "k \<in> set (concat (map ztyp_tvars (zterm_types zA)))" "T = ZTVar (fst k) (snd k)"
          by (simp_all add: lT split: if_splits)
        then obtain Z where Z: "Z \<in> set (zterm_types zA)" "(fst k, snd k) \<in> set (ztyp_tvars Z)" by auto
        have "pnn A" using nnv nnt by (fastforce simp: pnn_def tnn_def ttvars_def)
        then have "zterm_ok zA" by (rule zterm_ok_zterm_of_pnn[OF zA])
        then have "ztyp_ok Z" by (rule zterm_ok_types[OF _ Z(1)])
        from ztyp_ok_ztvar[OF this Z(2)] show ?thesis by (simp add: k(2))
      qed
      ultimately show ?thesis by (simp add: zc)
    qed
    moreover have "znolb 0 z" by (simp add: zc lk)
    moreover have "zhyps_ok z" by (simp add: zc zhyps_ok_def)
    ultimately show "zvalid (sg_ax c) (set []) [] z A \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z" by blast
  qed
qed

end
