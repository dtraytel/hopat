section \<open>Normalizing tight terms\<close>

theory ZProof_Norm
  imports ZProof_Lift Proof_Beta
begin

text \<open>
  The normalization of tight types and terms with respect to an environment is correct for its
  successful computations, like the classic one (theory \<^theory>\<open>Thm_Correctness.Proof_Norm\<close>):
  a normalized term is, at an instance, equivalent up to erasure to the original term at the
  extension of the instance through a solution of the environment. Variables of index \<open>-1\<close>
  stand for free variables in tight terms; the environment binds none and its values have none.
\<close>

subsection \<open>The monad\<close>

lemma bindZ_eq_returnZ: "bindZ m f = returnZ y \<longleftrightarrow> (\<exists>x. m = returnZ x \<and> f x = returnZ y)"
  by (auto simp: bindZ_def returnZ_def split: option.splits zres.splits)

lemma liftMZ_eq_returnZ: "liftMZ m = returnZ x \<longleftrightarrow> ok m x"
  by (auto simp: liftMZ_def returnZ_def split: option.splits res.splits)

lemma liftOZ_eq_returnZ: "liftOZ m = returnZ x \<longleftrightarrow> m = Some x"
  by (auto simp: liftOZ_def returnZ_def)

lemma mapZ_eq_returnZ: "mapZ f xs = returnZ ys \<longleftrightarrow> list_all2 (\<lambda>x y. f x = returnZ y) xs ys"
  by (induction xs arbitrary: ys) (auto simp: bindZ_eq_returnZ list_all2_Cons1)

text \<open>The same with \<^const>\<open>returnZ\<close> unfolded:\<close>

lemmas Z_ok_simps = bindZ_eq_returnZ[unfolded returnZ_def] liftMZ_eq_returnZ[unfolded returnZ_def]
  liftOZ_eq_returnZ[unfolded returnZ_def] mapZ_eq_returnZ[unfolded returnZ_def]


subsection \<open>Types\<close>

text \<open>Schematic type variables do not have the index \<open>-1\<close> of free ones:\<close>

definition tnoneg :: "ptyp \<Rightarrow> bool" where
  "tnoneg T \<longleftrightarrow> (\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1)"

definition tyenv_ok :: "tyenv \<Rightarrow> bool" where
  "tyenv_ok \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> snd v \<noteq> -1 \<and> tnoneg U)"

lemma tnoneg_typ_of [simp]: "tnoneg (typ_of T)"
  by (induction T) (auto simp: tnoneg_def propT_def)

lemma typ_of_ztyp_of_tnoneg: "tnoneg T \<Longrightarrow> typ_of (ztyp_of T) = T"
  using typ_of_ztyp_of by (auto simp: tnoneg_def)

lemma znorm_type_aux_success:
  assumes "znorm_type_aux \<theta> T = Some r"
  shows "r = ZOk T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tyenv_ok \<theta> \<Longrightarrow> tcons \<theta> (typ_of T) \<and> typ_of T' = tnorm \<theta> (typ_of T)"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: znorm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nta \<theta> T r)
  note ac = "1.prems"(2) and to = "1.prems"(3)
  have IH: "tcons \<theta> (typ_of U) \<and> U' = tnorm \<theta> (typ_of U)" if "nta \<theta> U = Some (ZOk U'')" "typ_of U'' = U'" for U U' U''
    using "1.IH"[OF that(1) HOL.refl ac to] that(2) by simp
  show ?case
  proof (cases T)
    case (ZTVar v S)
    show ?thesis
    proof (cases "snd v = -1")
      case True
      have "snd v \<noteq> -1" if "vt_lookup \<theta> v = Some (S0, U0)" for S0 U0
        using to that unfolding tyenv_ok_def by blast
      with True have "vt_lookup \<theta> v = None" by (cases "vt_lookup \<theta> v") auto
      with "1.hyps" "1.prems"(1) ZTVar True show ?thesis
        by (auto simp: type_lookup_def returnZ_def bindZ_def liftMZ_def return_def tcons_def)
    next
      case False
      from "1.hyps" "1.prems"(1) ZTVar obtain lr where lk: "ok (type_lookup \<theta> v S) lr"
        and rest: "(case lr of Some U \<Rightarrow> nta \<theta> (ztyp_of U) | None \<Rightarrow> Some (ZOk (ZTVar v S))) = Some (ZOk T')"
        by (auto simp: Z_ok_simps returnZ_def)
      show ?thesis
      proof (cases "vt_lookup \<theta> v")
        case None
        with lk rest ZTVar False show ?thesis by (auto simp: ok_type_lookup tcons_TVar tnorm_TVar[OF ac])
      next
        case (Some b)
        obtain S' U where b: "b = (S', U)" by force
        with lk Some have "S' = S" "lr = Some U" by (auto simp: ok_type_lookup)
        with rest have "nta \<theta> (ztyp_of U) = Some (ZOk T')" by simp
        from IH[OF this HOL.refl] have "tcons \<theta> (typ_of (ztyp_of U))" "typ_of T' = tnorm \<theta> (typ_of (ztyp_of U))"
          by auto
        moreover have "typ_of (ztyp_of U) = U"
          using to Some b unfolding tyenv_ok_def by (intro typ_of_ztyp_of_tnoneg) blast
        ultimately show ?thesis using ZTVar False Some b \<open>S' = S\<close> by (auto simp: tcons_TVar tnorm_TVar[OF ac])
      qed
    qed
  next
    case (ZFun U V)
    from "1.hyps" "1.prems"(1) ZFun obtain U' V' where "nta \<theta> U = Some (ZOk U')" "nta \<theta> V = Some (ZOk V')"
      "T' = ZFun U' V'"
      by (auto simp: Z_ok_simps returnZ_def)
    with IH[of U U' "typ_of U'"] IH[of V V' "typ_of V'"] ZFun show ?thesis by auto
  next
    case (ZType1 a U)
    from "1.hyps" "1.prems"(1) ZType1 obtain U' where "nta \<theta> U = Some (ZOk U')" "T' = ZType1 a U'"
      by (auto simp: Z_ok_simps returnZ_def)
    with IH[of U U' "typ_of U'"] ZType1 show ?thesis by auto
  next
    case (ZType a Us)
    from "1.hyps" "1.prems"(1) ZType obtain Us' where m: "list_all2 (\<lambda>x y. nta \<theta> x = Some (ZOk y)) Us Us'"
      and T': "T' = ZType a Us'"
      by (auto simp: Z_ok_simps returnZ_def)
    from m have "list_all2 (\<lambda>x y. tcons \<theta> (typ_of x) \<and> typ_of y = tnorm \<theta> (typ_of x)) Us Us'"
      by (rule list.rel_mono_strong) (use IH in blast)
    then show ?thesis using T' ZType
      by (auto simp: list_all2_conv_all_nth in_set_conv_nth intro!: nth_equalityI)
  qed (use "1.hyps" "1.prems" in \<open>auto simp: returnZ_def propT_def\<close>)
qed

lemma znorm_type_success:
  "znorm_type \<theta> T = returnZ T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tyenv_ok \<theta> \<Longrightarrow> tcons \<theta> (typ_of T) \<and> typ_of T' = tnorm \<theta> (typ_of T)"
  by (auto simp: znorm_type_def tcons_empty tnorm_empty returnZ_def split: if_splits
    dest: znorm_type_aux_success[OF _ HOL.refl])


subsection \<open>Conversion of terms\<close>

text \<open>
  Converting a term and decoding it changes at most the types of constants, if the term has no
  schematic (type) variables of index \<open>-1\<close>:
\<close>

definition noneg :: "pterm \<Rightarrow> bool" where
  "noneg t \<longleftrightarrow> (\<forall>v\<in>vars t. snd (fst v) \<noteq> -1) \<and> (\<forall>U\<in>typs t. tnoneg U)"

context prf_sig
begin

lemma zdec_zterm_of:
  "zterm_of ta t = returnZ z \<Longrightarrow> noneg t \<Longrightarrow> remove_types (zdec z) = remove_types t"
proof (induction ta t arbitrary: z rule: zterm_of.induct)
  case (1 ta x T)
  then show ?case by (auto simp: returnZ_def noneg_def typ_of_ztyp_of_tnoneg)
next
  case (2 ta xi T)
  then show ?case by (cases xi) (auto simp: returnZ_def noneg_def typ_of_ztyp_of_tnoneg)
next
  case (4 ta c T)
  then obtain Ts where "z = (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))"
    by (auto simp: Z_ok_simps returnZ_def)
  then show ?case by (cases Ts rule: remdups_adj.cases) simp_all
next
  case (5 ta a T b)
  then show ?case by (auto simp: Z_ok_simps returnZ_def noneg_def typ_of_ztyp_of_tnoneg)
next
  case (6 ta t u)
  have nt: "noneg t" "noneg u" using "6.prems"(2) by (auto simp: noneg_def)
  show ?case
  proof (cases "match_of_class (t $ u)")
    case None
    with "6.prems"(1) obtain zt zu where "zterm_of ta t = returnZ zt" "zterm_of ta u = returnZ zu" "z = ZApp zt zu"
      by (auto simp: Z_ok_simps returnZ_def)
    with "6.IH"(1,2)[OF None] nt show ?thesis by (auto simp: returnZ_def)
  next
    case (Some Tc)
    show ?thesis
    proof (cases "t $ u = mk_of_class (fst Tc) (snd Tc)")
      case True
      have "zterm_of ta (t $ u) = returnZ (ZOfclass (ztyp_of (fst Tc)) (snd Tc))"
        by (subst zterm_of.simps) (simp only: Some option.case if_P[OF True])
      with "6.prems"(1) have "z = ZOfclass (ztyp_of (fst Tc)) (snd Tc)" by simp
      with True show ?thesis by (simp add: of_class_def mk_of_class_def class_suffix_def propT_def)
    next
      case False
      with "6.prems"(1) Some obtain zt zu where "zterm_of ta t = returnZ zt" "zterm_of ta u = returnZ zu" "z = ZApp zt zu"
        by (auto simp: Z_ok_simps returnZ_def)
      with "6.IH"(3,4)[OF Some False] nt show ?thesis by (auto simp: returnZ_def)
    qed
  qed
qed (simp add: returnZ_def)

lemma erase_ap_zdec_zterm_of:
  "zterm_of ta t = returnZ z \<Longrightarrow> noneg t \<Longrightarrow> erase (ap \<rho> \<sigma> (zdec z)) = erase (ap \<rho> \<sigma> t)"
  by (metis erase_ap_remove_types zdec_zterm_of)

end


subsection \<open>Bound variables\<close>

context pure_sig
begin

lemma zdec_zincr_bv: "zdec (zincr_bv inc lev t) = incr_bv inc lev (zdec t)"
  by (induction inc lev t rule: zincr_bv.induct) (simp_all add: of_class_def)

lemma zdec_zsubst_bound: "zdec (zsubst_bound arg lev t) = subst_bound_aux (zdec arg) lev (zdec t)"
  by (induction arg lev t rule: zsubst_bound.induct)
    (simp_all add: of_class_def zincr_boundvars_def incr_boundvars_def zdec_zincr_bv)

lemma zdec_subst_term_bound: "zdec (subst_term_bound u body) = subst_bound (zdec u) (zdec body)"
  by (simp add: subst_term_bound_def subst_bound_def zdec_zsubst_bound)

subsection \<open>Terms\<close>

text \<open>The environment binds no variables of index \<open>-1\<close>, and its values have none:\<close>

definition eneg :: "env \<Rightarrow> bool" where
  "eneg env \<longleftrightarrow> tyenv_ok (tyenv env) \<and> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<noteq> -1 \<and> noneg u)"

lemma enegD:
  "eneg env \<Longrightarrow> tyenv_ok (tyenv env)"
  "eneg env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> snd x \<noteq> -1 \<and> noneg u"
  unfolding eneg_def by blast+

lemma tvars_zconst_typ: "tvars (zconst_typ c Us) \<subseteq> (\<Union>U\<in>set Us. tvars U)"
proof -
  have "tvars (tsubst (\<lambda>v S. case map_of (zip xs Us) (v, S) of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) U) \<subseteq> (\<Union>U\<in>set Us. tvars U)"
    for xs U
  proof (induction U)
    case (TVar v S)
    then show ?case
      by (auto simp: dummyT_def split: option.splits dest: map_of_SomeD set_zip_rightD)
  qed (auto simp: dummyT_def)
  then show ?thesis
    by (auto simp: zconst_typ_def imp_type_def propT_def dummyT_def split: option.splits list.splits)
qed

end

context prf_sig
begin

lemma zlookup_success:
  assumes "zlookup ta env x T = returnZ r" "tacyc (tyenv env)"
  obtains (None) "vt_lookup (tenv env) x = None" "r = None"
  | (Some) U u u' where "vt_lookup (tenv env) x = Some (U, u)" "r = Some u'" "zterm_of ta u = returnZ u'"
      "tcons (tyenv env) (typ_of T)" "tcons (tyenv env) U" "tnorm (tyenv env) (typ_of T) = tnorm (tyenv env) U"
proof (cases "vt_is_empty (tenv env)")
  case True
  with assms have "r = None" by (simp add: zlookup_def)
  with True show thesis by (intro that(1)) (simp_all add: vt_is_empty_lookup)
next
  case False
  with assms(1) obtain lr where lk: "ok (lookup env x (typ_of T)) lr"
    and rest: "(case lr of None \<Rightarrow> returnZ None | Some u \<Rightarrow> bindZ (zterm_of ta u) (\<lambda>u'. returnZ (Some u'))) = returnZ r"
    by (auto simp: zlookup_def bindZ_eq_returnZ liftMZ_eq_returnZ)
  from lk assms(2) show thesis
  proof (cases rule: lookup_success)
    case None
    with rest show thesis by (intro that(1)) simp_all
  next
    case (Some U u)
    with rest obtain u' where "zterm_of ta u = returnZ u'" "r = Some u'" by (auto simp: bindZ_eq_returnZ)
    with Some show thesis by (intro that(2)[of U u u']) simp_all
  qed
qed

lemma iext_lookup_ueq:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and lk: "vt_lookup (tenv env) x = Some (U, u)"
    and cT: "tcons (tyenv env) T" "tcons (tyenv env) U" and eq: "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' (Var x T)"
proof -
  have "vt_lookup (tenv (remove_types_env env)) x = Some (U, remove_types u)" using lk by simp
  from iext_remove_types_lookup[OF ie tac this cT eq]
  show ?thesis unfolding erase_ap_remove_types .
qed

lemma tnormal_zdec_type:
  "typ_of T' = tnorm \<theta> T \<Longrightarrow> tacyc \<theta> \<Longrightarrow> \<forall>(w, S)\<in>tvars (typ_of T'). vt_lookup \<theta> w = None"
  using tnorm_unbound by fastforce

lemma znorm_term_aux_ok:
  assumes "znorm_term_aux x = Some r"
  shows "r = ZOk t' \<Longrightarrow> snd (fst x) = env \<Longrightarrow> iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow>
    tcons_env (tyenv env) \<Longrightarrow> eneg env \<Longrightarrow> nout env (zdec t') \<and> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec (snd x))"
  using assms
proof (induction x r arbitrary: t' rule: znorm_term_aux.raw_induct[rotated, consumes 1])
  case (1 nt x r)
  let ?\<theta> = "tyenv env"
  note r = "1.prems"(1) and E = "1.prems"(2) and ie = "1.prems"(3) and tac = "1.prems"(4,5) and en = "1.prems"(6)
  obtain ta t where x: "x = ((ta, env), t)" using E by (metis prod.collapse)
  note i = iextD[OF ie]
  have h: "(case t of
      ZVar xi T \<Rightarrow> do {
        r \<leftarrow> zlookup ta env xi T;
        case r of
          Some u \<Rightarrow> nt ((ta, env), u)
        | None \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZVar xi T')}}
    | ZConst1 a T \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZConst1 a T')}
    | ZConst a Ts \<Rightarrow> do {Ts' \<leftarrow> mapZ (znorm_type ?\<theta>) Ts; returnZ (ZConst a Ts')}
    | ZAbs a T b \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; b' \<leftarrow> nt ((ta, env), b); returnZ (ZAbs a T' b')}
    | ZApp g u \<Rightarrow>
        (case g of
          ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
        | _ \<Rightarrow> do {
            nf \<leftarrow> nt ((ta, env), g);
            case nf of
              ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
            | _ \<Rightarrow> do {nu \<leftarrow> nt ((ta, env), u); returnZ (ZApp nf nu)}})
    | ZOfclass T c \<Rightarrow> do {T' \<leftarrow> znorm_type ?\<theta> T; returnZ (ZOfclass T' c)}
    | t \<Rightarrow> returnZ t) = returnZ t'"
    using "1.hyps" r unfolding x prod.sel by (simp add: returnZ_def)
  have IH: "nout env (zdec u') \<and> ap \<rho> \<sigma> (zdec u') \<approx> ap \<rho>' \<sigma>' (zdec u)" if "nt ((ta, env), u) = returnZ u'" for u u'
  proof -
    have "snd (fst ((ta, env), u)) = env" by simp
    from "1.IH"[OF that[unfolded returnZ_def] HOL.refl this ie tac en] show ?thesis by (simp only: prod.sel)
  qed
  have to: "tyenv_ok ?\<theta>" by (rule enegD(1)[OF en])
  have nT: "tcons ?\<theta> (typ_of T) \<and> typ_of T' = tnorm ?\<theta> (typ_of T)" if "znorm_type ?\<theta> T = returnZ T'" for T T'
    by (rule znorm_type_success[OF that tac(1) to])
  have tyeq: "tsubst \<rho> (tnorm ?\<theta> T) = tsubst \<rho>' T" if "tcons ?\<theta> T" for T
    by (rule iext_tnorm[OF ie tac that])
  have ap_unb: "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" if "nout env s" for s by (rule iext_unb[OF ie nout_unb[OF that]])
  have redex: "nout env (zdec t') \<and> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (Abs b U (zdec body) $ zdec u)"
    if "nt ((ta, env), subst_term_bound u body) = returnZ t'" for b U body u
    using IH[OF that] ueq_trans[OF _ ueq_sym[OF ap_beta_ueq[OF i(2)]]] by (simp add: zdec_subst_term_bound)
  have tn: "tnormal ?\<theta> (Const cn (zconst_typ cn (map typ_of Us)))" if "\<forall>U\<in>set Us. \<exists>V. typ_of U = tnorm ?\<theta> V" for cn Us
    using that tvars_zconst_typ[of cn "map typ_of Us"] tnorm_unbound[OF tac(1)]
    by (fastforce simp: tnormal_def)
  have "nout env (zdec t') \<and> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec t)"
  proof (cases t)
    case (ZVar xi T)
    from h ZVar obtain lr where lk: "zlookup ta env xi T = returnZ lr"
      and rest: "(case lr of Some u \<Rightarrow> nt ((ta, env), u)
        | None \<Rightarrow> bindZ (znorm_type ?\<theta> T) (\<lambda>T'. returnZ (ZVar xi T'))) = returnZ t'"
      by (auto simp: bindZ_eq_returnZ)
    from lk tac(1) show ?thesis
    proof (cases rule: zlookup_success)
      case None
      from rest None obtain T' where T': "znorm_type ?\<theta> T = returnZ T'" and t': "t' = ZVar xi T'"
        by (auto simp: bindZ_eq_returnZ)
      from nT[OF T'] have cT: "tcons ?\<theta> (typ_of T)" and T'': "typ_of T' = tnorm ?\<theta> (typ_of T)" by auto
      show ?thesis
      proof (cases "snd xi = -1")
        case True
        have "nout env (zdec t')" using True T'' tnorm_unbound[OF tac(1)]
          by (fastforce simp: t' nout_def tnormal_def)
        moreover have "ap \<rho> \<sigma> (zdec t') = ap \<rho>' \<sigma>' (zdec t)" using True tyeq[OF cT] by (simp add: t' ZVar T'')
        ultimately show ?thesis by (simp add: ueq_refl)
      next
        case False
        have "nout env (zdec t')" using False nout_Var[OF tac(1) None(1)] by (simp add: t' T'')
        moreover have "ap \<rho> \<sigma> (zdec t') = ap \<rho>' \<sigma>' (zdec t)"
          using False tyeq[OF cT] i(7)[OF None(1)] by (simp add: t' ZVar T'')
        ultimately show ?thesis by (simp add: ueq_refl)
      qed
    next
      case (Some U u u')
      have xn: "snd xi \<noteq> -1" and nu: "noneg u" using enegD(2)[OF en Some(1)] by auto
      from rest Some(2) have "nt ((ta, env), u') = returnZ t'" by simp
      note IHu = IH[OF this]
      have "erase (ap \<rho>' \<sigma>' (zdec u')) = erase (ap \<rho>' \<sigma>' u)" by (rule erase_ap_zdec_zterm_of[OF Some(3) nu])
      moreover have "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' (Var xi (typ_of T))"
        by (rule iext_lookup_ueq[OF ie tac Some(1,4,5,6)])
      ultimately have "ap \<rho>' \<sigma>' (zdec u') \<approx> ap \<rho>' \<sigma>' (zdec t)" using xn by (simp add: ZVar)
      from conjunct1[OF IHu] ueq_trans[OF conjunct2[OF IHu] this] show ?thesis by (rule conjI)
    qed
  next
    case (ZConst1 a T)
    from h ZConst1 obtain T' where T': "znorm_type ?\<theta> T = returnZ T'" and t': "t' = ZConst1 a T'"
      by (auto simp: bindZ_eq_returnZ)
    from nT[OF T'] have "nout env (zdec t')" using tn[of "[T']"] by (auto simp: t' nout_def)
    then show ?thesis by (simp add: t' ZConst1 ueq_refl)
  next
    case (ZConst a Ts)
    from h ZConst obtain Ts' where Ts': "list_all2 (\<lambda>x y. znorm_type ?\<theta> x = returnZ y) Ts Ts'" and t': "t' = ZConst a Ts'"
      by (auto simp: bindZ_eq_returnZ mapZ_eq_returnZ)
    have "\<forall>U\<in>set Ts'. \<exists>V. typ_of U = tnorm ?\<theta> V"
      using Ts' nT by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
    then have "nout env (zdec t')" using tn[of Ts'] by (auto simp: t' nout_def)
    then show ?thesis by (simp add: t' ZConst ueq_refl)
  next
    case (ZOfclass T c)
    from h ZOfclass obtain T' where T': "znorm_type ?\<theta> T = returnZ T'" and t': "t' = ZOfclass T' c"
      by (auto simp: bindZ_eq_returnZ)
    from nT[OF T'] have "nout env (zdec t')"
      using tnorm_unbound[OF tac(1)] by (fastforce simp: t' nout_def tnormal_def of_class_def propT_def)
    then show ?thesis by (simp add: t' ZOfclass of_class_def ueq_refl)
  next
    case (ZAbs a T b)
    from h ZAbs obtain T' b' where T': "znorm_type ?\<theta> T = returnZ T'" and b': "nt ((ta, env), b) = returnZ b'"
      and t': "t' = ZAbs a T' b'"
      by (auto simp: bindZ_eq_returnZ)
    from nT[OF T'] have T'': "typ_of T' = tnorm ?\<theta> (typ_of T)" by auto
    note IHb = IH[OF b']
    have "nout env (zdec t')" using IHb T'' tnorm_unbound[OF tac(1)] by (fastforce simp: t' nout_def tnormal_def)
    moreover have "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec t)"
      unfolding ZAbs t' zdec.simps ap_simps by (rule ueq_Abs) (use IHb in blast)
    ultimately show ?thesis by blast
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>b U body. g = ZAbs b U body")
      case True
      then obtain b U body where g: "g = ZAbs b U body" by blast
      have "nt ((ta, env), subst_term_bound u body) = returnZ t'" using h ZApp g by simp
      from redex[OF this] show ?thesis by (simp add: ZApp g)
    next
      case False
      with h ZApp obtain nf where hf: "nt ((ta, env), g) = returnZ nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> nt ((ta, env), subst_term_bound u body)
          | _ \<Rightarrow> bindZ (nt ((ta, env), u)) (\<lambda>nu. returnZ (ZApp nf nu))) = returnZ t'"
        by (cases g) (auto simp: bindZ_eq_returnZ)
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "\<exists>b U body. nf = ZAbs b U body")
        case True
        then obtain b U body where nfb: "nf = ZAbs b U body" by blast
        have "nt ((ta, env), subst_term_bound u body) = returnZ t'" using rest nfb by simp
        then have R: "nout env (zdec t') \<and> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec nf $ zdec u)"
          unfolding nfb zdec.simps by (rule redex)
        have "ap \<rho>' \<sigma>' (zdec nf $ zdec u) \<approx> ap \<rho>' \<sigma>' (zdec t)"
          unfolding ZApp zdec.simps ap_simps ap_unb[OF conjunct1[OF IHf]]
          by (rule ueq_App) (use IHf in \<open>blast intro: ueq_refl\<close>)+
        from conjunct1[OF R] ueq_trans[OF conjunct2[OF R] this] show ?thesis by (rule conjI)
      next
        case False
        with rest obtain nu where hu: "nt ((ta, env), u) = returnZ nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bindZ_eq_returnZ)
        note IHu = IH[OF hu]
        have "nout env (zdec t')" using IHf IHu t' by (auto simp: nout_def tnormal_def)
        moreover have "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec t)"
          unfolding ZApp t' zdec.simps ap_simps by (rule ueq_App) (use IHf IHu in blast)+
        ultimately show ?thesis by blast
      qed
    qed
  next
    case (ZBound i)
    with h show ?thesis by (auto simp: nout_def tnormal_def ueq_refl)
  next
    case (ZConst0 c)
    with h have t': "t' = ZConst0 c" by simp
    have "nout env (zdec t')" using tn[of "[]"] by (auto simp: t' nout_def)
    then show ?thesis by (simp add: t' ZConst0 ueq_refl)
  qed
  then show ?case by (simp only: x prod.sel)
qed

lemma beta_norm_term_ok:
  assumes "beta_norm_term t = Some t'" and gs: "gsubst \<sigma>"
  shows "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (zdec t)"
  using assms(1)
proof (induction t t' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t t')
  note h = "1.hyps" and IH = "1.IH"
  have redex: "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (Abs b U (zdec body) $ zdec u)"
    if "bn (subst_term_bound u body) = Some t'" for b U body u
    using ueq_trans[OF IH[OF that, unfolded zdec_subst_term_bound] ueq_sym[OF ap_beta_ueq[OF gs]]] by simp
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where b': "bn b = Some b'" and t': "t' = ZAbs a T b'" by (auto simp: bind_eq_Some_conv)
    show ?thesis unfolding ZAbs t' zdec.simps ap_simps by (rule ueq_Abs) (rule IH[OF b'])
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
        then have R: "ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho> \<sigma> (zdec nf $ zdec u)"
          unfolding nfb zdec.simps by (rule redex)
        have "ap \<rho> \<sigma> (zdec nf $ zdec u) \<approx> ap \<rho> \<sigma> (zdec t)"
          unfolding ZApp zdec.simps ap_simps by (rule ueq_App[OF IHf ueq_refl])
        from ueq_trans[OF R this] show ?thesis .
      next
        case False
        with rest obtain nu where hu: "bn u = Some nu" and t': "t' = ZApp nf nu"
          by (cases nf) (auto simp: bind_eq_Some_conv)
        show ?thesis unfolding ZApp t' zdec.simps ap_simps by (rule ueq_App[OF IHf IH[OF hu]])
      qed
    qed
  qed (use h in \<open>auto intro: ueq_refl\<close>)
qed

theorem znorm_term_ok:
  assumes nt: "znorm_term ta env t = returnZ t'" and ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
    and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and en: "eneg env"
  shows "nout env (zdec t') \<and> ap \<rho> \<sigma> (zdec t') \<approx> ap \<rho>' \<sigma>' (zdec t)"
proof (cases "env_is_empty env")
  case True
  then have bn: "beta_norm_term t = Some t'" using nt by (simp add: znorm_term_def liftOZ_eq_returnZ)
  have l: "vt_lookup (tenv env) x = None" "vt_lookup (tyenv env) v = None" for x v
    using vt_is_empty_lookup[of "tenv env" x] vt_is_empty_lookup[of "tyenv env" v] True
    by (simp_all add: env_is_empty_def)
  then have no: "nout env s" for s by (simp add: nout_def tnormal_def)
  have u: "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" for s by (rule iext_unb[OF ie]) (simp add: unb_def l)
  from beta_norm_term_ok[OF bn iextD(2)[OF ie], of \<rho>'] no show ?thesis by (simp only: u)
next
  case False
  with nt have "znorm_term_aux ((ta, env), t) = Some (ZOk t')" by (simp add: znorm_term_def returnZ_def)
  from znorm_term_aux_ok[OF this HOL.refl _ ie tac en] show ?thesis by simp
qed

end

end
