section \<open>Proofs: Thm_Unconstrain\<close>

theory Thm_Unconstrain_Proofs
  imports "Thm_Soundness.Thm_Unconstrain" Thm_Strip_Shyps_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Unconstrain\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

context prf_sig
begin

lemma all_var_Free:
  assumes R: "e \<turnstile> R : propT" "closed R" and T: "cert_typ alg ar T"
  shows "e \<turnstile> all_var (Free x T) R : propT \<and> closed (all_var (Free x T) R) \<and>
    (\<exists>f. all_var (Free x T) R = all_const T $ f \<and> f $ Free x T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R)"
proof -
  let ?b = "abstract_over_aux (Free x T) 0 R" and ?a = "if x = STR '''' then STR ''uu'' else x"
  have hb: "e\<langle>0:T\<rangle> \<turnstile> ?b : propT"
    by (rule typing_abstract_over_aux[of _ _ T]) (use R in \<open>simp_all add: closed_def shift_def\<close>)
  then have tb: "e \<turnstile> Abs ?a T ?b : T \<rightarrow>\<^sub>T propT" using T by auto
  have ty: "e \<turnstile> all_var (Free x T) R : propT"
    using hb T by (simp add: all_var_def abstract_over_def typing_all_const all_type_def cert_typ_fun)
  have "\<not> loose_bvar ?b 1"
    by (rule Forall_Intr_Sound.loose_bvar_abstract_over_aux) (use R(2) loose_bvar_mono in \<open>auto simp: closed_def\<close>)
  then have cl: "closed (all_var (Free x T) R)"
    by (simp add: all_var_def abstract_over_def closed_def all_const_def)
  have "Abs ?a T ?b $ Free x T \<rightarrow>\<^sub>\<beta> ?b[Free x T/0]" by (rule beta.beta)
  moreover have "?b[Free x T/0] = R"
    by (rule subst_abstract_over_aux_Free) (use R(2) in \<open>simp_all add: closed_def\<close>)
  moreover have "wt (Abs ?a T ?b $ Free x T)"
    using tb T unfolding wt_def by blast
  ultimately have "Abs ?a T ?b $ Free x T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R" using conv_beta by metis
  then show ?thesis using ty cl by (auto simp: all_var_def abstract_over_def)
qed

lemma all_var_atom:
  assumes v: "(\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)" and R: "e \<turnstile> R : propT" "closed R"
    and T: "cert_typ alg ar T"
  shows "e \<turnstile> all_var v R : propT \<and> closed (all_var v R) \<and> (\<exists>f. all_var v R = all_const T $ f \<and> f $ v \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R)"
  using v
proof (elim disjE exE)
  fix x i assume v: "v = Var (x, i) T"
  obtain f where "all_var (Var (x, i) T) R = all_const T $ f" "f $ Var (x, i) T \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> R"
    by (rule all_var_beta[OF R T])
  then show ?thesis using all_var_typing[OF R T, of x i] v by blast
next
  fix x assume v: "v = Free x T"
  show ?thesis unfolding v by (rule all_var_Free[OF R T])
qed

lemma closure_typing':
  assumes "\<forall>v\<in>set vs. \<exists>T. ((\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)) \<and> cert_typ alg ar T"
    and "e \<turnstile> B : propT" "closed B"
  shows "e \<turnstile> foldr all_var vs B : propT \<and> closed (foldr all_var vs B)"
  using assms(1)
proof (induction vs)
  case (Cons w ws)
  from Cons.prems obtain U where w: "(\<exists>x i. w = Var (x, i) U) \<or> (\<exists>x. w = Free x U)"
    and U: "cert_typ alg ar U" by auto
  from Cons.IH Cons.prems have "e \<turnstile> foldr all_var ws B : propT" "closed (foldr all_var ws B)" by simp_all
  from all_var_atom[OF w this U] show ?case by simp
qed (use assms in simp)

lemma prf_ok_closure_chain':
  assumes "prf_ok ax H E e Hs p (foldr all_var vs B)"
    and vs: "\<forall>v\<in>set vs. \<exists>T. ((\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)) \<and> cert_typ alg ar T"
    and B: "e \<turnstile> B : propT" "closed B"
    and os: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us vs"
  shows "prf_ok ax H E e Hs (foldl PAppt p us) B"
  using os assms(1) vs
proof (induction us vs arbitrary: p rule: list_all2_induct)
  case (Cons u us v vs)
  from Cons.prems(2) obtain T where v: "(\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)"
    and T: "cert_typ alg ar T" by auto
  let ?R = "foldr all_var vs B"
  from closure_typing'[OF _ B] Cons.prems(2) have tR: "e \<turnstile> ?R : propT" "closed ?R" by simp_all
  from all_var_atom[OF v tR T] obtain f where f: "all_var v ?R = all_const T $ f" "f $ v \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ?R"
    by blast
  have tv: "e \<turnstile> v : T" using v T by auto
  have "prf_ok ax H E e Hs p (all_const T $ f)" using Cons.prems(1) f(1) by simp
  then have "prf_ok ax H E e Hs (PAppt p u) (f $ v)"
    by (rule prf_ok.PAppt[OF _ tv]) (use Cons.hyps in \<open>auto simp: ann_ok_def ueq_refl\<close>)
  then have "prf_ok ax H E e Hs (PAppt p u) ?R" by (rule prf_ok.conv[OF _ f(2) tR(1)])
  from Cons.IH[OF this] Cons.prems(2) show ?case by simp
qed (simp add: assms)

text \<open>
  A proof box of a well-typed proposition that the signature admits, whose closure is that of
  \<open>Proofterm\<close>, applied to its variables (or to no arguments), proves the proposition:
\<close>

lemma prf_ok_thm_chain:
  assumes ax: "ax B" and h: "hd_prop h = B"
    and ht: "hd_types h = None \<or> hd_types h = Some (map (\<lambda>(v, S). TVar v S) (tyargs B))"
    and cl: "close B = forall_closure B"
    and ta: "\<forall>(v, S)\<in>set (tyargs B). sort_ok alg S" and wB: "wtp B"
    and us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) us (variables_of B)"
  shows "prf_ok ax H E e Hs (foldl PAppt (PThm (h, b)) us) B"
proof -
  let ?Us = "map (\<lambda>(v, S). TVar v S) (tyargs B)"
  have vc: "\<forall>v\<in>set (variables_of B). \<exists>T. ((\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)) \<and> cert_typ alg ar T"
  proof
    fix v assume "v \<in> set (variables_of B)"
    then have v: "v \<in> set (aterms B)" "(\<exists>xi T. v = Var xi T) \<or> (\<exists>x T. v = Free x T)"
      by (simp_all add: set_variables_of)
    then obtain T where T: "(\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)" by auto
    have "T \<in> typs v" using T by auto
    then have "T \<in> typs B" using typs_aterms[OF v(1)] by blast
    then have "cert_typ alg ar T" by (rule typing_typs[OF wtpD(2)[OF wB, of e]])
    with T show "\<exists>T. ((\<exists>x i. v = Var (x, i) T) \<or> (\<exists>x. v = Free x T)) \<and> cert_typ alg ar T" by blast
  qed
  have ct: "e \<turnstile> close B : propT"
    using closure_typing'[OF vc wtpD(2)[OF wB] wtpD(1)[OF wB]] by (simp add: cl forall_closure_def)
  have ap: "atom_prop B ?Us = close B" by (simp add: atom_prop_def tyinst_ident)
  have "atom_ok B None ?Us"
    unfolding atom_ok_def list_all2_map2 option.case(1)
    using ta by (auto intro!: list.rel_refl_strong simp: cert_typ_TVar simp del: has_sort.simps)
  then have ao: "atom_ok B (hd_types h) ?Us" using ht by (auto simp: atom_ok_def)
  have "prf_ok ax H E e Hs (PThm (h, b)) (atom_prop (hd_prop h) ?Us)"
    by (rule prf_ok.PThm) (use ax ao ct ap h in simp_all)
  then have "prf_ok ax H E e Hs (PThm (h, b)) (foldr all_var (variables_of B) B)"
    by (simp add: h ap cl forall_closure_def)
  from prf_ok_closure_chain'[OF this vc wtpD(2)[OF wB] wtpD(1)[OF wB] us] show ?thesis .
qed

end

context pure_sig
begin

text \<open>The decoded \<open>\<beta>\<close>-normal form of a term is a \<open>\<beta>\<close>-reduct of the decoded term:\<close>

lemma beta_norm_term_reds:
  assumes "beta_norm_term t = Some t'"
  shows "zdec t \<rightarrow>\<^sub>\<beta>\<^sup>* zdec t'"
  using assms
proof (induction t t' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t t')
  note h = "1.hyps" and IH = "1.IH"
  have redex: "Abs b U (zdec body) $ zdec u \<rightarrow>\<^sub>\<beta>\<^sup>* zdec t'"
    if "bn (subst_term_bound u body) = Some t'" for b U body u
  proof -
    have "Abs b U (zdec body) $ zdec u \<rightarrow>\<^sub>\<beta>\<^sup>* subst_bound (zdec u) (zdec body)"
      by (rule r_into_rtranclp) (simp add: subst_bound_subst)
    with IH[OF that] show ?thesis by (simp add: zdec_subst_term_bound)
  qed
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where b': "bn b = Some b'" and t': "t' = ZAbs a T b'" by (auto simp: bind_eq_Some_conv)
    show ?thesis unfolding ZAbs t' zdec.simps by (rule rtrancl_beta_Abs[OF IH[OF b']])
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "bn (subst_term_bound u body) = Some t'" using h ZApp g by simp
      from redex[OF this] show ?thesis by (simp only: ZApp g zdec.simps)
    next
      case False
      with h ZApp obtain nf where hf: "bn g = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some t'"
        by (cases g) (auto simp: bind_eq_Some_conv)
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "bn (subst_term_bound u body) = Some t'" using rest nfb by simp
        then have R: "zdec nf $ zdec u \<rightarrow>\<^sub>\<beta>\<^sup>* zdec t'"
          unfolding nfb zdec.simps by (rule redex)
        have "zdec t \<rightarrow>\<^sub>\<beta>\<^sup>* zdec nf $ zdec u"
          unfolding ZApp zdec.simps by (rule rtrancl_beta_AppL[OF IHf])
        from rtranclp_trans[OF this R] show ?thesis .
      next
        case False
        with rest obtain nu where hu: "bn u = Some nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        show ?thesis unfolding ZApp t' zdec.simps by (rule rtrancl_beta_App[OF IHf IH[OF hu]])
      qed
    qed
  qed (use h in auto)
qed

end

context prf_sig
begin

lemma tyargs_sort_ok:
  assumes w: "wtp B" and t: "\<forall>v\<in>set (tyargs B). v \<in> ttvars B"
  shows "\<forall>(v, S)\<in>set (tyargs B). sort_ok alg S"
proof clarify
  fix v S assume "(v, S) \<in> set (tyargs B)"
  with t have "TVar v S \<in> tatoms B" by (auto intro: ttvars_tatoms)
  then obtain T where "T \<in> typs B" "TVar v S \<in> set (atyps T)" by (auto simp: tatoms_def)
  then have "cert_typ alg ar (TVar v S)" using cert_atyps typing_typs[OF wtpD(2)[OF w]] by blast
  then show "sort_ok alg S" by (simp add: cert_typ_TVar)
qed

end


theorem proofs_ok_unconstrainT:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (unconstrainT_rep invent (shyps_list (shyps_of th)) (hyps_of th) (rep_of th)) r"
    and fin: "finite (shyps_of th)"
    and uo: "unc_ok box zn invent (sign_of th) (shyps_list (shyps_of th)) (th_prop (rep_of th)) r"
  shows "is_prf_sig (th_sign (unconstrainT_data box zn invent th r)) \<Longrightarrow>
    proofs_ok (unconstrainT_data box zn invent th r)"
proof -
  let ?c = "sign_of th" and ?shyps = "shyps_list (shyps_of th)" and ?P = "th_prop (rep_of th)"
  have sl: "set ?shyps = shyps_of th" by (rule set_shyps_list[OF fin])
  have inv: "\<And>k. k \<le> length (invent (integer_of_nat k))" and dis: "\<And>k. distinct (invent (integer_of_nat k))"
    and bx: "\<And>B. hd_prop (fst (box B)) = B" "\<And>B. hd_types (fst (box B)) = None"
    and so: "\<forall>S\<in>set ?shyps. sort_ok (sg_alg ?c) S" and soc: "sign_ofclass ?c" and vcP: "vars_consistent ?P"
    using uo by (simp_all add: unc_ok_def)
  from ok have h: "hyps_of th = []" "th_tpairs (rep_of th) = []"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def split: if_splits)
  from ok h obtain args pm cm P1 where args: "ok (prop_args ?P) args"
    and u: "ok (unconstrain_prop invent ?shyps ?P) ((pm, cm), P1)" and r: "r = mk_rep (maxidx_of_term P1) [] P1"
    by (auto simp: unconstrainT_rep_def raiseW_def returnW_def liftMT_def liftM_def liftWT_def Let_def
      split: if_splits option.splits xres.splits prod.splits)
  have rs: "th_maxidx r = maxidx_of_term P1" "th_tpairs r = []" "th_prop r = P1" by (simp_all add: r mk_rep_def)
  have oc: "pure_sig_gen.class_const (sg_alg ?c) (sg_consts ?c) (cl + STR ''_class'') cl"
    if "cl \<in> classes (sg_alg ?c)" for cl
    using soc that unfolding sign_ofclass_def by blast
  have ocw: "\<forall>cl\<in>classes (sg_alg ?c). \<forall>a. pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (mk_of_class (TVar a []) cl)"
    using soc by (simp add: sign_ofclass_def)
  assume psig: "is_prf_sig (th_sign (unconstrainT_data box zn invent th r))"
  then have psig': "is_prf_sig ?c" by simp
  interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    using psig' by (simp add: is_prf_sig_def)
  have ub1: "unc_box_ok ?c P1"
    and ubz: "\<And>z. zunconstrain_proof ztargs zn invent ?shyps ?P = return z \<Longrightarrow> unc_box_ok ?c (zdec (zbox_prop z))"
    using uo psig' by (simp_all add: unc_ok_def rs)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig' by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) [] [] ?P" using pure_thm_wf[of th] h ps by simp
  note uw = unconstrain_prop_wf[OF u inv w0 so ocw]
  let ?\<phi> = "unc_atyp pm"
  let ?g = "tmap ?\<phi>"
  let ?P' = "tmap ?\<phi> ?P"
  note ctx = uw(2)
  have P1e: "P1 = list_implies (ctx_constraints cm) ?P'" by (rule uw(1))
  have wP: "wtp ?P" and nnv: "\<forall>v\<in>vars ?P. 0 \<le> snd (fst v)"
    using w0 by (simp_all add: thm_wf_def wt_thm_def vars_thm_def)
  have w1: "wtp P1" and nnv1: "\<forall>v\<in>vars P1. 0 \<le> snd (fst v)" and nnt1: "\<forall>v\<in>ttvars P1. 0 \<le> snd (fst v)"
    using uw(4) by (simp_all add: thm_wf_def wt_thm_def vars_thm_def tvars_thm_def)
  have csa: "\<not> ((\<exists>xi T. a = Var xi T) \<or> (\<exists>x T. a = Free x T))" if "A \<in> set (ctx_constraints cm)" "a \<in> set (aterms A)" for A a
    using ctx_constraints_mem[OF that(1)] that(2) by (auto simp: mk_of_class_def)
  \<comment> \<open>the variables of the new proposition\<close>
  have finj: "U = U'" if "U \<in> tatoms ?P" "U' \<in> tatoms ?P" "?\<phi> U = ?\<phi> U'" for U U'
    by (rule unc_atyp_inj[OF ctx inv dis that])
  have fat: "\<exists>v S. ?\<phi> U = TVar v S" if "U \<in> tatoms ?P" for U
    using unc_atyp_atom[OF ctx inv that] by metis
  have vP': "variables_of ?P' = map ?g (variables_of ?P)"
    by (rule variables_of_map[OF inj_map_types_aterms[OF finj fat] map_types_var_shape])
      (simp_all add: aterms_map_types)
  have vP1: "variables_of P1 = map ?g (variables_of ?P)"
    unfolding P1e by (subst variables_of_list_implies) (use csa vP' in blast)+
  have avs: "v \<in> set (variables_of ?P)" if "Some v \<in> set args" for v
  proof -
    from that obtain i where i: "i < length args" "args ! i = Some v" by (auto simp: in_set_conv_nth)
    have l: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) args (variables_of ?P)" by (rule prop_args_vars[OF args])
    from list_all2_nthD[OF l i(1)] i(2) have "v = variables_of ?P ! i" by simp
    moreover have "i < length (variables_of ?P)" using i(1) l by (simp add: list_all2_lengthD)
    ultimately show "v \<in> set (variables_of ?P)" by simp
  qed
  show "proofs_ok (unconstrainT_data box zn invent th r)" unfolding proofs_ok_def Let_def unconstrainT_data_sel rs
  proof (rule conjI; intro allI impI)
    fix p assume "th_proof (unconstrainT_data box zn invent th r) = returnW p"
    then have "ok (unconstrain_thm_proof box invent ?shyps ?P) p"
      by (auto simp: unconstrainT_data_def bindP_eq_returnP liftMP_eq_returnP)
    then obtain argst where at: "list_all2 (\<lambda>a b. ok (case a of None \<Rightarrow> return None
        | Some t \<Rightarrow> do {t' \<leftarrow> unconstrain_term pm cm t; return (Some t')}) b) args argst"
      and p: "p = foldl PAppt (PThm (box P1)) argst"
      using args u by (auto simp: unconstrain_thm_proof_def ok_mapM)
    have "list_all2 (\<lambda>a b. b = map_option ?g a) args argst"
    proof (rule list.rel_mono_strong[OF at])
      fix a b assume a: "a \<in> set args"
        and ab: "ok (case a of None \<Rightarrow> return None | Some t \<Rightarrow> do {t' \<leftarrow> unconstrain_term pm cm t; return (Some t')}) b"
      show "b = map_option ?g a"
      proof (cases a)
        case (Some t)
        have "t \<in> set (aterms ?P)" using avs[of t] a Some by (simp add: set_variables_of)
        then have "tatoms t \<subseteq> tatoms ?P" by (rule tatoms_aterms)
        from unconstrain_term_ok'[OF ctx inv this] ab Some show ?thesis by simp
      qed (use ab in simp)
    qed
    then have argst: "argst = map (map_option ?g) args"
      by (induction rule: list_all2_induct) simp_all
    have usP1: "list_all2 (\<lambda>u v. u = None \<or> u = Some v) argst (variables_of P1)"
      using prop_args_vars[OF args] unfolding argst vP1 list_all2_map1 list_all2_map2
      by (rule list_all2_mono) auto
    obtain hb bb where hb: "box P1 = (hb, bb)" by (cases "box P1")
    have h1: "hd_prop hb = P1" "hd_types hb = None" using bx[of P1] hb by simp_all
    have ta1: "\<forall>(v, S)\<in>set (sg_tyargs ?c P1). sort_ok (sg_alg ?c) S"
      by (rule tyargs_sort_ok[OF w1]) (use ub1 in \<open>simp add: unc_box_ok_def\<close>)
    have "prf_valid (sg_ax ?c) {} [] p P1"
      unfolding p hb
    proof (rule prf_valid_genericI)
      show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
      fix e
      show "prf_ok (sg_ax ?c) {} (set []) e [] (foldl PAppt (PThm (hb, bb)) argst) P1"
        by (rule prf_ok_thm_chain[OF _ h1(1) disjI1[OF h1(2)] _ ta1 w1 usP1]) (use ub1 in \<open>simp_all add: unc_box_ok_def\<close>)
    qed
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) p"
    proof -
      have "\<forall>u\<in>set argst. \<forall>t\<in>set_option u. \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
      proof (intro ballI)
        fix u t v assume "u \<in> set argst" "t \<in> set_option u" "v \<in> vars t"
        from \<open>u \<in> set argst\<close> obtain x where x: "x \<in> set args" "u = map_option ?g x" by (auto simp: argst)
        with \<open>t \<in> set_option u\<close> obtain t0 where "x = Some t0" "t = ?g t0" by (cases x) auto
        with x have t0: "Some t0 \<in> set args" "t = ?g t0" by simp_all
        have "t0 \<in> set (aterms ?P)" using avs[OF t0(1)] by (simp add: set_variables_of)
        then have sub: "vars t0 \<subseteq> vars ?P" by (rule vars_aterms)
        have "v \<in> (\<lambda>(x, T). (x, map_atyps ?\<phi> T)) ` vars t0" using \<open>v \<in> vars t\<close> t0(2) by (simp add: vars_map_types)
        then obtain w where "w \<in> vars t0" "fst v = fst w" by auto
        with sub nnv show "0 \<le> snd (fst v)" by auto
      qed
      then show ?thesis by (simp add: p hb prf_idx_foldl_PAppt)
    qed
    moreover have "prf_nolb 0 p"
    proof -
      have "\<forall>u\<in>set argst. \<forall>t. u = Some t \<longrightarrow> \<not> loose_bvar t 0"
      proof (intro ballI allI impI)
        fix u t assume "u \<in> set argst" "u = Some t"
        from \<open>u \<in> set argst\<close> obtain x where x: "x \<in> set args" "u = map_option ?g x" by (auto simp: argst)
        with \<open>u = Some t\<close> obtain t0 where "x = Some t0" "t = ?g t0" by (cases x) auto
        with x have t0: "Some t0 \<in> set args" "t = ?g t0" by simp_all
        from avs[OF t0(1)] have "(\<exists>xi T. t0 = Var xi T) \<or> (\<exists>x T. t0 = Free x T)" by (simp add: set_variables_of)
        with t0(2) show "\<not> loose_bvar t 0" by auto
      qed
      then show ?thesis by (simp add: p prf_nolb_foldl_PAppt')
    qed
    ultimately show "prf_valid (sg_ax ?c) (set []) [] p P1 \<and> prf_idx (\<lambda>i. 0 \<le> i) p \<and> prf_nolb 0 p" by simp
  next
    fix z assume "th_zproof (unconstrainT_data box zn invent th r) = return z"
    then have zu: "zunconstrain_proof ztargs zn invent ?shyps ?P = return z"
      by (auto simp: unconstrainT_data_def bindZ_eq_returnZ)
    then obtain prems C A where pr: "list_all2 (\<lambda>X y. zterm_of ztargs X = return y) (ctx_constraints cm) prems"
      and C: "zterm_of ztargs ?P' = return C" and A: "beta_norm_term (close_zprop prems C) = Some A"
      and z: "z = ZConstp (zproof_const (ZThm zn) A)"
      using u unconstrain_term_ok[OF ctx inv]
      by (auto simp: zunconstrain_proof_def bindZ_eq_returnZ liftMZ_eq_returnZ liftOZ_eq_returnZ mapZ_eq_returnZ)
    have ub: "unc_box_ok ?c (zdec A)" using ubz[OF zu] by (simp add: z zproof_const_def zbox_prop_def)
    \<comment> \<open>the decoded proposition of the box\<close>
    have nn: "noneg X" if "vars X \<subseteq> vars P1" "ttvars X \<subseteq> ttvars P1" for X
      using that nnv1 nnt1 by (fastforce simp: noneg_def tnoneg_def ttvars_def integer_nonneg_ne_m1)
    have dX: "zdec y = X" if "zterm_of ztargs X = return y" "e \<turnstile> X : T" "noneg X" for X y e T
      using zterm_of_zdec[OF that(2)] that(1,3) by (auto simp: noneg_def tnoneg_def)
    have cw: "wtp X" if "X \<in> set (ctx_constraints cm)" for X
      using uw(5) that by blast
    have dprems: "map zdec prems = ctx_constraints cm"
    proof -
      have "list_all2 (\<lambda>X y. zdec y = X) (ctx_constraints cm) prems"
      proof (rule list.rel_mono_strong[OF pr])
        fix X y assume X: "X \<in> set (ctx_constraints cm)" and y: "zterm_of ztargs X = return y"
        show "zdec y = X"
        proof (rule dX[OF y wtpD(2)[OF cw[OF X]]], rule nn)
          show "vars X \<subseteq> vars P1" using X by (auto simp: P1e vars_list_implies)
          show "ttvars X \<subseteq> ttvars P1" using X unfolding P1e by (rule ttvars_list_implies)
        qed
      qed
      then show ?thesis by (induction rule: list_all2_induct) simp_all
    qed
    have dC: "zdec C = ?P'"
    proof (rule dX[OF C wtpD(2)[OF uw(6)]], rule nn)
      show "vars ?P' \<subseteq> vars P1" by (auto simp: P1e vars_list_implies)
      show "ttvars ?P' \<subseteq> ttvars P1" unfolding P1e by (rule ttvars_list_implies)
    qed
    have red: "P1 \<rightarrow>\<^sub>\<beta>\<^sup>* zdec A" using beta_norm_term_reds[OF A] by (simp add: dprems dC P1e)
    have wB: "wtp (zdec A)"
      by (rule wtpI[OF closed_beta_reds[OF red wtpD(1)[OF w1]] subject_reduction_beta'[OF red wtpD(2)[OF w1]]])
    have cv: "zdec A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> P1"
    proof (rule conv_sym, rule beta_eta_conv)
      show "(sup beta eta)\<^sup>*\<^sup>* P1 (zdec A)" using red by (rule mono_rtranclp[rule_format, rotated]) simp
      show "wt P1" using wtpD(2)[OF w1] unfolding wt_def by blast
    qed
    have pn: "pnn X" if "vars X \<subseteq> vars P1" "ttvars X \<subseteq> ttvars P1" for X
      using that nnv1 nnt1 by (fastforce simp: pnn_def tnn_def ttvars_def)
    have zoA: "zterm_ok A"
    proof (rule zterm_ok_beta_norm_term[OF A])
      have "zterm_ok C"
      proof (rule zterm_ok_zterm_of_pnn[OF C], rule pn)
        show "vars ?P' \<subseteq> vars P1" by (auto simp: P1e vars_list_implies)
        show "ttvars ?P' \<subseteq> ttvars P1" unfolding P1e by (rule ttvars_list_implies)
      qed
      moreover have "zterm_ok y" if "y \<in> set prems" for y
      proof -
        from that obtain i where i: "i < length prems" "prems ! i = y" by (auto simp: in_set_conv_nth)
        have l: "length (ctx_constraints cm) = length prems" using pr by (rule list_all2_lengthD)
        from list_all2_nthD2[OF pr i(1)] have "zterm_of ztargs (ctx_constraints cm ! i) = return y" by (simp add: i(2))
        moreover have "ctx_constraints cm ! i \<in> set (ctx_constraints cm)" using i(1) l by simp
        ultimately obtain X where X: "X \<in> set (ctx_constraints cm)" "zterm_of ztargs X = return y" by blast
        show ?thesis
        proof (rule zterm_ok_zterm_of_pnn[OF X(2)], rule pn)
          show "vars X \<subseteq> vars P1" using X(1) by (auto simp: P1e vars_list_implies)
          show "ttvars X \<subseteq> ttvars P1" using X(1) unfolding P1e by (rule ttvars_list_implies)
        qed
      qed
      ultimately show "zterm_ok (close_zprop prems C)" by (induction prems) auto
    qed
    \<comment> \<open>the table of the box\<close>
    define tab where "tab = fold (\<lambda>v. zv_update (v, ZVar (fst v) (snd v))) (zterm_vars A) zv_empty"
    define instT where "instT = fold (\<lambda>v. zt_update (v, ZTVar (fst v) (snd v))) (concat (map ztyp_tvars (zterm_types A))) zt_empty"
    have zc: "z = ZConstp ((ZThm zn, A), (instT, tab))" by (simp add: z zproof_const_def tab_def instT_def)
    have lk: "zv_lookup tab k = (if k \<in> set (zterm_vars A) then Some (ZVar (fst k) (snd k)) else None)" for k
      by (simp add: tab_def zv_lookup_fold_update)
    have kv: "\<exists>T. snd k = ztyp_of T \<and> (Var (fst k) T \<in> set (aterms ?P') \<or>
        (snd (fst k) = -1 \<and> Free (fst (fst k)) T \<in> set (aterms ?P')))" if "k \<in> set (zterm_vars A)" for k
    proof -
      have "k \<in> set (zterm_vars (close_zprop prems C))" using zterm_vars_beta_norm[OF A] that by blast
      moreover have "k \<notin> set (zterm_vars y)" if "y \<in> set prems" for y
      proof
        assume k: "k \<in> set (zterm_vars y)"
        from that pr obtain X where X: "X \<in> set (ctx_constraints cm)" "zterm_of ztargs X = return y"
          by (auto simp: list_all2_iff in_set_zip set_zip dest: list_all2_lengthD) (metis in_set_conv_nth)
        from zterm_vars_zterm_of'[OF X(2) k] obtain T where
          "Var (fst k) T \<in> set (aterms X) \<or> Free (fst (fst k)) T \<in> set (aterms X)" by blast
        with csa[OF X(1)] show False by blast
      qed
      ultimately have "k \<in> set (zterm_vars C)" by (auto simp: zterm_vars_close_zprop)
      from zterm_vars_zterm_of'[OF C this] show ?thesis .
    qed
    have nv: "0 \<le> snd xi" if "Var xi T \<in> set (aterms ?P')" for xi T
    proof -
      have "(xi, T) \<in> vars P1" using Var_aterms_vars[OF that] by (simp add: P1e vars_list_implies)
      from bspec[OF nnv1 this] show ?thesis by simp
    qed
    have vcV: "T = U" if "Var xi T \<in> set (aterms ?P')" "Var xi U \<in> set (aterms ?P')" for xi T U
      using vars_consistent_map_types[OF vcP] that unfolding vars_consistent_def by blast
    have vcF: "T = U" if "Free x T \<in> set (aterms ?P')" "Free x U \<in> set (aterms ?P')" for x T U
      using vars_consistent_map_types[OF vcP] that unfolding vars_consistent_def by blast
    have vc': "vars_consistent ?P'" by (rule vars_consistent_map_types[OF vcP])
    have nok: "ztab_names_ok tab"
      unfolding ztab_names_ok_def
    proof (intro allI impI)
      fix k1 k2 assume "zv_lookup tab k1 \<noteq> None" "zv_lookup tab k2 \<noteq> None" and f: "fst k1 = fst k2"
      then have k: "k1 \<in> set (zterm_vars A)" "k2 \<in> set (zterm_vars A)" by (simp_all add: lk split: if_splits)
      from kv[OF k(1)] obtain T1 where T1: "snd k1 = ztyp_of T1" "Var (fst k1) T1 \<in> set (aterms ?P') \<or>
          (snd (fst k1) = -1 \<and> Free (fst (fst k1)) T1 \<in> set (aterms ?P'))" by blast
      from kv[OF k(2)] obtain T2 where T2: "snd k2 = ztyp_of T2" "Var (fst k2) T2 \<in> set (aterms ?P') \<or>
          (snd (fst k2) = -1 \<and> Free (fst (fst k2)) T2 \<in> set (aterms ?P'))" by blast
      have "T1 = T2"
      proof (cases "snd (fst k1) = -1")
        case True
        have "\<not> Var (fst k1) T1 \<in> set (aterms ?P')" "\<not> Var (fst k2) T2 \<in> set (aterms ?P')"
          using nv[of "fst k1" T1] nv[of "fst k2" T2] True f by auto
        with T1(2) T2(2) have "Free (fst (fst k1)) T1 \<in> set (aterms ?P')" "Free (fst (fst k1)) T2 \<in> set (aterms ?P')"
          using f by auto
        then show ?thesis by (rule vcF)
      next
        case False
        with T1(2) T2(2) f have "Var (fst k1) T1 \<in> set (aterms ?P')" "Var (fst k1) T2 \<in> set (aterms ?P')"
          by auto
        then show ?thesis by (rule vcV)
      qed
      with T1(1) T2(1) f show "k1 = k2" by (simp add: prod_eq_iff)
    qed
    let ?look = "\<lambda>xi. map_option zdec (zv_lookup_name tab xi)"
    let ?Us = "map (\<lambda>(v, S). TVar v S) (sg_tyargs ?c (zdec A))"
    have lT: "zt_lookup instT k = (if k \<in> set (concat (map ztyp_tvars (zterm_types A)))
        then Some (ZTVar (fst k) (snd k)) else None)" for k
      by (simp add: instT_def zt_lookup_fold_update)
    have tyB: "\<forall>v\<in>set (sg_tyargs ?c (zdec A)). v \<in> ttvars (zdec A)" using ub by (simp add: unc_box_ok_def)
    have iU: "zinst_typs instT (sg_tyargs ?c (zdec A)) = ?Us"
    proof (rule zinst_typs_ident[OF lT])
      show "set (sg_tyargs ?c (zdec A)) \<subseteq> set (concat (map ztyp_tvars (zterm_types A)))"
        using tyB ttvars_zdec[of _ _ A] by auto
      show "snd v \<noteq> -1" if "(v, S) \<in> set (sg_tyargs ?c (zdec A))" for v S
        using tyB that ttvars_zdec[of v S A] by auto
    qed
    have ztr: "zprf_tr z = zthm_tr (zdec A) ?Us ?look" by (simp add: zc zconst_trT_def iU)
    have look: "?look xi = None \<or> ?look xi = Some (Var xi T)" if "Var xi T \<in> set (aterms (zdec A))" for xi T
    proof (cases "zv_lookup_name tab xi")
      case (Some u)
      from aterms_zdec_Var[OF that] obtain T' where T': "(xi, T') \<in> set (zterm_vars A)" "T = typ_of T'" "snd xi \<noteq> -1"
        by blast
      from zv_lookup_nameD[OF Some] obtain T'' where l: "zv_lookup tab (xi, T'') = Some u" by blast
      then have u: "(xi, T'') \<in> set (zterm_vars A)" "u = ZVar xi T''" by (simp_all add: lk split: if_splits)
      have "zv_lookup tab (xi, T') \<noteq> None" using T'(1) by (simp add: lk)
      with nok l have "(xi, T'') = (xi, T')" unfolding ztab_names_ok_def by (metis fst_conv option.simps(3))
      then show ?thesis using Some u T' by simp
    qed simp
    have us: "list_all2 (\<lambda>u v. u = None \<or> u = Some v)
        (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of (zdec A))) (variables_of (zdec A))"
      unfolding list_all2_map1
      by (rule list.rel_refl_strong) (auto simp: set_variables_of dest: look split: pterm.splits)
    have taB: "\<forall>(v, S)\<in>set (sg_tyargs ?c (zdec A)). sort_ok (sg_alg ?c) S"
      by (rule tyargs_sort_ok[OF wB]) (use ub in \<open>simp add: unc_box_ok_def\<close>)
    have v: "prf_valid (sg_ax ?c) {} [] (zprf_tr z) P1"
      unfolding ztr zthm_tr_def term_variables_eq
    proof (rule prf_valid_genericI)
      show "\<And>h. h \<in> {} \<Longrightarrow> vars h = {} \<and> ttvars h = {}" by simp
      fix e
      have "prf_ok (sg_ax ?c) {} (set []) e [] (foldl PAppt (PThm (zthm_head (zdec A) ?Us))
          (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of (zdec A)))) (zdec A)"
        unfolding zthm_head_def
        by (rule prf_ok_thm_chain[OF _ _ _ _ taB wB us]) (use ub in \<open>simp_all add: unc_box_ok_def\<close>)
      then show "prf_ok (sg_ax ?c) {} (set []) e [] (foldl PAppt (PThm (zthm_head (zdec A) ?Us))
          (map (\<lambda>v. case v of Var xi _ \<Rightarrow> ?look xi | _ \<Rightarrow> None) (variables_of (zdec A)))) P1"
        by (rule prf_ok.conv[OF _ cv wtpD(2)[OF w1]])
    qed
    have "zvalid (sg_ax ?c) (set []) [] z P1" by (rule zvalidI[OF HOL.refl]) (use v in simp)
    moreover have "zinv z"
    proof -
      have "zterm_ok t" if "zv_lookup tab k = Some t" for k t
      proof -
        from that have k: "k \<in> set (zterm_vars A)" "t = ZVar (fst k) (snd k)" by (simp_all add: lk split: if_splits)
        from kv[OF k(1)] obtain T where T: "snd k = ztyp_of T" "Var (fst k) T \<in> set (aterms ?P') \<or>
            (snd (fst k) = -1 \<and> Free (fst (fst k)) T \<in> set (aterms ?P'))" by blast
        have tT: "T \<in> typs ?P'" using T(2) typs_aterms by fastforce
        have "tnn T"
          unfolding tnn_def
        proof clarify
          fix v S assume "(v, S) \<in> tvars T"
          then have "(v, S) \<in> ttvars P1" using tT ttvars_list_implies(2)[of ?P' "ctx_constraints cm"]
            by (auto simp: P1e ttvars_def)
          with nnt1 show "0 \<le> snd v" by fastforce
        qed
        moreover have "0 \<le> snd (fst k) \<or> snd (fst k) = -1" using T(2) nv[of "fst k" T] by auto
        ultimately show ?thesis by (simp add: k(2) T(1) ztyp_ok_ztyp_of)
      qed
      moreover have "ztyp_ok T" if "zt_lookup instT k = Some T" for k T
      proof -
        from that have k: "k \<in> set (concat (map ztyp_tvars (zterm_types A)))" "T = ZTVar (fst k) (snd k)"
          by (simp_all add: lT split: if_splits)
        then obtain Z where Z: "Z \<in> set (zterm_types A)" "(fst k, snd k) \<in> set (ztyp_tvars Z)" by auto
        from ztyp_ok_ztvar[OF zterm_ok_types[OF zoA Z(1)] Z(2)] show ?thesis by (simp add: k(2))
      qed
      ultimately show ?thesis using nok by (simp add: zc)
    qed
    moreover have "znolb 0 z" by (simp add: zc lk)
    moreover have "zhyps_ok z" by (simp add: zc zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c) (set []) [] z P1 \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z" by blast
  qed
qed

end
