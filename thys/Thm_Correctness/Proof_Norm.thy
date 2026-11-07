section \<open>Normalizing proofs\<close>

theory Proof_Norm
  imports Proof_Flatten
begin

text \<open>
  \<^const>\<open>norm_proof\<close> normalizes the annotations of a proof with respect to an environment. Its
  successful computations are correct without any assumption on the annotations: the lookups
  and the normalization of types check that the types of the variables they visit are consistent
  with the environment. At every instance, the normalized proof is equivalent to the original
  one at the extension of the instance through a solution of the environment.
\<close>

subsection \<open>Types\<close>

lemma tcons_empty: "vt_is_empty \<theta> \<Longrightarrow> tcons \<theta> T"
  by (simp add: tcons_def vt_is_empty_lookup)

lemma ok_type_lookup:
  "ok (type_lookup \<theta> v S) r \<longleftrightarrow> vt_lookup \<theta> v = None \<and> r = None \<or> (\<exists>U. vt_lookup \<theta> v = Some (S, U) \<and> r = Some U)"
  by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)

lemma devar_success:
  assumes "devar \<theta> T = Some r"
  shows "r = Ok U \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tnorm \<theta> U = tnorm \<theta> T \<and> (tcons \<theta> U \<longrightarrow> tcons \<theta> T) \<and> \<not> tbound \<theta> U"
  using assms
proof (induction \<theta> T r arbitrary: U rule: devar.raw_induct[rotated, consumes 1])
  case (1 dv \<theta> T r)
  note ac = "1.prems"(2)
  show ?case
  proof (cases T)
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain lr where lk: "ok (type_lookup \<theta> v S) lr"
      and rest: "ok (case lr of Some U \<Rightarrow> dv \<theta> U | None \<Rightarrow> return (TVar v S)) U"
      by auto
    show ?thesis
    proof (cases "vt_lookup \<theta> v")
      case None
      with lk have "lr = None" by (simp add: ok_type_lookup)
      with rest TVar None show ?thesis by (auto simp: tcons_TVar tnorm_TVar[OF ac])
    next
      case (Some b)
      obtain S' U0 where b: "b = (S', U0)" by force
      with lk Some have "S' = S" "lr = Some U0" by (auto simp: ok_type_lookup)
      with rest have "dv \<theta> U0 = Some (Ok U)" by simp
      from "1.IH"[OF this HOL.refl ac] show ?thesis
        using TVar Some b \<open>S' = S\<close> by (auto simp: tcons_TVar tnorm_TVar[OF ac])
    qed
  qed (use "1.hyps" "1.prems" in auto)
qed

lemma allM_true: "ok (allM P xs) True \<Longrightarrow> \<forall>x\<in>set xs. ok (P x) True"
  by (induction xs) (auto split: if_splits)

lemma unified_aux_success:
  assumes "unified_aux \<theta> T T' = Some r"
  shows "r = Ok True \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<and> tcons \<theta> T' \<and> tnorm \<theta> T = tnorm \<theta> T'"
  using assms
proof (induction \<theta> T T' r rule: unified_aux.raw_induct[rotated, consumes 1])
  case (1 ua \<theta> T T' r)
  note ac = "1.prems"(2)
  from "1.hyps" "1.prems"(1) obtain U U' where dU: "ok (devar \<theta> T) U" and dU': "ok (devar \<theta> T') U'"
    and rest: "ok (case (U, U') of
        (Type s Ts, Type s' Ts') \<Rightarrow>
          if s = s' then do {
            b \<leftarrow> allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Ts');
            return (b \<and> length Ts = length Ts')}
          else return False
      | _ \<Rightarrow> return (U = U')) True"
    by auto
  note d = devar_success[OF dU HOL.refl ac] and d' = devar_success[OF dU' HOL.refl ac]
  have "tcons \<theta> U \<and> tcons \<theta> U' \<and> tnorm \<theta> U = tnorm \<theta> U'"
  proof (cases "\<exists>s Ts s' Ts'. U = Type s Ts \<and> U' = Type s' Ts'")
    case True
    then obtain s Ts s' Ts' where UU: "U = Type s Ts" "U' = Type s' Ts'" by blast
    from rest UU have s: "s = s'" and al: "ok (allM (\<lambda>(T, T'). ua \<theta> T T') (zip Ts Ts')) True"
      and l: "length Ts = length Ts'"
      by (auto split: if_splits)
    have IH: "tcons \<theta> A \<and> tcons \<theta> B \<and> tnorm \<theta> A = tnorm \<theta> B" if "(A, B) \<in> set (zip Ts Ts')" for A B
    proof -
      from allM_true[OF al] that have "ua \<theta> A B = Some (Ok True)" by fastforce
      from "1.IH"[OF this HOL.refl ac] show ?thesis .
    qed
    have "\<forall>A\<in>set Ts. tcons \<theta> A" "\<forall>B\<in>set Ts'. tcons \<theta> B"
      using IH l by (fastforce simp: in_set_conv_nth set_zip)+
    moreover have "map (tnorm \<theta>) Ts = map (tnorm \<theta>) Ts'"
      by (rule nth_equalityI) (use IH l in \<open>auto simp: set_zip\<close>)
    ultimately show ?thesis using UU s by simp
  next
    case False
    with rest have UU: "U = U'" by (cases U; cases U'; auto)
    have nb: "\<not> tbound \<theta> U" using d by blast
    have "tcons \<theta> U"
    proof (cases U)
      case (Type s Ts)
      with UU False show ?thesis by blast
    next
      case (TVar v S)
      with nb show ?thesis by (auto simp: tcons_TVar)
    qed simp
    with UU show ?thesis by simp
  qed
  with d d' show ?case by auto
qed

lemma unified_success:
  "ok (unified \<theta> T T') True \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<and> tcons \<theta> T' \<and> tnorm \<theta> T = tnorm \<theta> T'"
  by (auto simp: unified_def tcons_empty tnorm_empty split: if_splits dest: unified_aux_success[OF _ HOL.refl])

lemma lookup_success:
  assumes lk: "ok (lookup env x T) r" and ac: "tacyc (tyenv env)"
  obtains (None) "vt_lookup (tenv env) x = None" "r = None"
  | (Some) U u where "vt_lookup (tenv env) x = Some (U, u)" "r = Some u" "tcons (tyenv env) T"
      "tcons (tyenv env) U" "tnorm (tyenv env) T = tnorm (tyenv env) U"
proof (cases "vt_lookup (tenv env) x")
  case None
  with lk show thesis by (intro that(1)) (auto simp: lookup_def)
next
  case (Some b)
  obtain U u where b: "b = (U, u)" by force
  from lk Some b have u: "ok (unified (tyenv env) T U) True" "r = Some u"
    by (auto simp: lookup_def var_clash_def split: if_splits)
  with unified_success[OF u(1) ac] Some b show thesis by (intro that(2)) auto
qed

lemma lookup1_success:
  "ok (lookup1 te x T) r \<Longrightarrow> vt_lookup te x = None \<and> r = None \<or> (\<exists>u. vt_lookup te x = Some (T, u) \<and> r = Some u)"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

lemma norm_type_aux_success:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<and> T' = tnorm \<theta> T"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nta \<theta> T r)
  note ac = "1.prems"(2)
  show ?case
  proof (cases T)
    case (Type a Ts)
    from "1.hyps" "1.prems"(1) Type obtain Ts' where m: "ok (mapM (nta \<theta>) Ts) Ts'" and T': "T' = Type a Ts'"
      by auto
    from m have "list_all2 (\<lambda>x y. ok (nta \<theta> x) y) Ts Ts'" by (simp add: ok_mapM)
    then have "list_all2 (\<lambda>x y. tcons \<theta> x \<and> y = tnorm \<theta> x) Ts Ts'"
      by (rule list.rel_mono_strong) (auto dest: "1.IH"[OF _ HOL.refl ac])
    then show ?thesis using T' Type
      by (auto simp: list_all2_conv_all_nth in_set_conv_nth intro!: nth_equalityI)
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain lr where lk: "ok (type_lookup \<theta> v S) lr"
      and rest: "ok (case lr of Some U \<Rightarrow> nta \<theta> U | None \<Rightarrow> return (TVar v S)) T'"
      by auto
    show ?thesis
    proof (cases "vt_lookup \<theta> v")
      case None
      with lk have "lr = None" by (simp add: ok_type_lookup)
      with rest TVar None show ?thesis by (auto simp: tcons_TVar tnorm_TVar[OF ac])
    next
      case (Some b)
      obtain S' U0 where b: "b = (S', U0)" by force
      with lk Some have "S' = S" "lr = Some U0" by (auto simp: ok_type_lookup)
      with rest have "nta \<theta> U0 = Some (Ok T')" by simp
      from "1.IH"[OF this HOL.refl ac] show ?thesis
        using TVar Some b \<open>S' = S\<close> by (auto simp: tcons_TVar tnorm_TVar[OF ac])
    qed
  qed (use "1.hyps" "1.prems" in auto)
qed

lemma norm_type_aux_ok_success: "ok (norm_type_aux \<theta> T) T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<and> T' = tnorm \<theta> T"
  by (rule norm_type_aux_success[OF _ HOL.refl])

lemma norm_type_success: "ok (norm_type \<theta> T) T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<and> T' = tnorm \<theta> T"
  by (auto simp: norm_type_def tcons_empty tnorm_empty split: if_splits dest: norm_type_aux_ok_success)


subsection \<open>Terms\<close>

definition tnormal :: "tyenv \<Rightarrow> pterm \<Rightarrow> bool" where
  "tnormal \<theta> t \<longleftrightarrow> (\<forall>U\<in>typs t. \<forall>(w, S)\<in>tvars U. vt_lookup \<theta> w = None)"

text \<open>The results of normalization: the variables are unbound and the types normal.\<close>

definition nout :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "nout env t \<longleftrightarrow> tnormal (tyenv env) t \<and> (\<forall>v\<in>vars t. vt_lookup (tenv env) (fst v) = None)"

lemma nout_Var:
  assumes "tacyc (tyenv env)" "vt_lookup (tenv env) x = None"
  shows "nout env (Var x (tnorm (tyenv env) T))"
  using assms tnorm_unbound[OF assms(1)] by (fastforce simp: nout_def tnormal_def)

lemma ueq_cong:
  assumes "\<And>x y. sup beta eta x y \<Longrightarrow> sup beta eta (f x) (f y)"
  shows "equivclp (sup beta eta) x y \<Longrightarrow> equivclp (sup beta eta) (f x) (f y)"
proof (induction rule: equivclp_induct)
  case (step y z)
  have "sup beta eta (f y) (f z) \<or> sup beta eta (f z) (f y)" using step(2) assms by blast
  from equivclp_into_equivclp[OF step(3) this] show ?case .
qed simp

lemma ueq_App: "s \<approx> s' \<Longrightarrow> t \<approx> t' \<Longrightarrow> s $ t \<approx> s' $ t'"
proof -
  assume a: "s \<approx> s'" "t \<approx> t'"
  have "equivclp (sup beta eta) (erase s $ erase t) (erase s' $ erase t)"
    by (rule ueq_cong[OF _ a(1), of "\<lambda>x. x $ erase t"]) auto
  moreover have "equivclp (sup beta eta) (erase s' $ erase t) (erase s' $ erase t')"
    by (rule ueq_cong[OF _ a(2), of "\<lambda>x. erase s' $ x"]) auto
  ultimately show ?thesis by (simp add: equivclp_trans)
qed

lemma ueq_Abs: "s \<approx> s' \<Longrightarrow> Abs a T s \<approx> Abs b U s'"
  using ueq_cong[of "\<lambda>x. Abs STR '''' dummyT x" "erase s" "erase s'"] by auto

lemma ueq_trans: "s \<approx> t \<Longrightarrow> t \<approx> u \<Longrightarrow> s \<approx> u"
  by (rule equivclp_trans)

lemma ueq_sym: "s \<approx> t \<Longrightarrow> t \<approx> s"
  by (rule equivclp_sym)

lemma ueq_refl: "s \<approx> s"
  by (rule equivclp_refl)

lemma ueq_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<approx> t"
proof (induction rule: rtranclp_induct)
  case (step y z)
  then have "sup beta eta (erase y) (erase z)" by (simp add: erase_beta)
  from equivclp_into_equivclp[OF step(3)] this show ?case by blast
qed simp

context prf_sig
begin

lemma remove_types_env_simps [simp]:
  "tyenv (remove_types_env env) = tyenv env" "maxidx (remove_types_env env) = maxidx env"
  "vt_lookup (tenv (remove_types_env env)) x = map_option (\<lambda>(T, t). (T, remove_types t)) (vt_lookup (tenv env) x)"
  by (simp_all add: remove_types_env_def)

lemma erase_ap_remove_types: "erase (ap \<rho> \<sigma> (remove_types t)) = erase (ap \<rho> \<sigma> t)"
  by (induction t) simp_all

lemma nout_unb: "nout env t \<Longrightarrow> unb env t"
  by (fastforce simp: nout_def unb_def tnormal_def ttvars_def)

lemma iext_tnorm:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and T: "tcons (tyenv env) T"
  shows "tsubst \<rho> (tnorm (tyenv env) T) = tsubst \<rho>' T"
proof -
  have "tsubst \<rho>' (tnorm (tyenv env) T) = tsubst \<rho> (tnorm (tyenv env) T)"
    by (rule tsubst_cong) (use iextD(6)[OF ie] tnorm_unbound[OF tac(1)] in force)
  with tsubst_tnorm[OF tac iextD(5)[OF ie] T] show ?thesis by simp
qed

lemma ap_beta_ueq: "gsubst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> (Abs b U body $ u) \<approx> ap \<rho> \<sigma> (subst_bound u body)"
proof -
  assume \<sigma>: "gsubst \<sigma>"
  have "Abs b U body $ u \<rightarrow>\<^sub>\<beta>\<^sup>* subst_bound u body" by (rule r_into_rtranclp) (simp add: subst_bound_subst)
  from beta_reds_ap[OF this gsubstD(1)[OF \<sigma>]] show ?thesis by (rule ueq_beta_reds)
qed

text \<open>The bindings of the type-erased environment are solved up to erasure:\<close>

lemma iext_remove_types_lookup:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and lk: "vt_lookup (tenv (remove_types_env env)) x = Some (U, u)"
    and cT: "tcons (tyenv env) T" "tcons (tyenv env) U" and eq: "tnorm (tyenv env) T = tnorm (tyenv env) U"
  shows "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' (Var x T)"
proof -
  note i = iextD[OF ie]
  from lk have "\<exists>u0. vt_lookup (tenv env) x = Some (U, u0) \<and> u = remove_types u0"
    by (cases "vt_lookup (tenv env) x") auto
  then obtain u0 where lk0: "vt_lookup (tenv env) x = Some (U, u0)" and u: "u = remove_types u0" by blast
  have s: "\<sigma>' x (tsubst \<rho>' U) \<approx> ap \<rho>' \<sigma>' u0" by (rule conv_ueq[OF solutionD(4)[OF i(3) lk0]])
  have "tsubst \<rho>' T = tsubst \<rho>' U" using tsubst_tnorm[OF tac i(5)] cT eq by metis
  then have v: "ap \<rho>' \<sigma>' (Var x T) = \<sigma>' x (tsubst \<rho>' U)" by simp
  have "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' u0" unfolding u erase_ap_remove_types by (rule ueq_refl)
  from ueq_trans[OF this ueq_sym[OF s]] show ?thesis unfolding v .
qed

lemma norm_term2_ok:
  assumes "norm_term2 E t = Some r"
  shows "r = Ok t' \<Longrightarrow> E = remove_types_env env \<Longrightarrow> iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow>
    tcons_env (tyenv env) \<Longrightarrow> nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
  using assms
proof (induction E t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt E t r)
  let ?\<theta> = "tyenv env"
  note h = "1.hyps" and r = "1.prems"(1) and E = "1.prems"(2) and ie = "1.prems"(3)
    and tac = "1.prems"(4,5)
  note i = iextD[OF ie]
  have IH: "nout env u' \<and> ap \<rho> \<sigma> u' \<approx> ap \<rho>' \<sigma>' u" if "nt E u = Some (Ok u')" for u u'
    using "1.IH"[OF that HOL.refl E ie tac] .
  have tE: "tyenv E = ?\<theta>" using E by simp
  have nT: "tcons ?\<theta> T \<and> T' = tnorm ?\<theta> T" if "ok (norm_type_aux (tyenv E) T) T'" for T T'
    using norm_type_aux_ok_success[OF that[unfolded tE] tac(1)] .
  have tyeq: "tsubst \<rho> (tnorm ?\<theta> T) = tsubst \<rho>' T" if "tcons ?\<theta> T" for T
    by (rule iext_tnorm[OF ie tac that])
  have ap_unb: "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" if "nout env s" for s by (rule iext_unb[OF ie nout_unb[OF that]])
  have redex: "nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' (Abs b U body $ u)"
    if "nt E (subst_bound u body) = Some (Ok t')" for b U body u
    using IH[OF that] ueq_trans[OF _ ueq_sym[OF ap_beta_ueq[OF i(2)]]] by blast
  show ?case
  proof (cases t)
    case (Const a T)
    from h r Const obtain T' where T': "ok (norm_type_aux (tyenv E) T) T'" and t': "t' = Const a T'" by auto
    from nT[OF T'] t' tnorm_unbound[OF tac(1)] show ?thesis
      unfolding Const by (fastforce simp: nout_def tnormal_def)
  next
    case (Free a T)
    from h r Free obtain T' where T': "ok (norm_type_aux (tyenv E) T) T'" and t': "t' = Free a T'" by auto
    from nT[OF T'] have cT: "tcons ?\<theta> T" and T'': "T' = tnorm ?\<theta> T" by auto
    have "ap \<rho> \<sigma> t' = ap \<rho>' \<sigma>' t" using tyeq[OF cT] by (simp add: Free t' T'')
    then show ?thesis using t' T'' tnorm_unbound[OF tac(1)]
      by (auto simp: nout_def tnormal_def intro: ueq_refl)
  next
    case (Var x T)
    from h r Var obtain lr where lk: "ok (lookup E x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt E u | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv E) T; return (Var x T')}) t'"
      by auto
    have tacE: "tacyc (tyenv E)" using tac(1) tE by simp
    from lk tacE show ?thesis
    proof (cases rule: lookup_success)
      case None
      have xn: "vt_lookup (tenv env) x = None" using None(1) E by simp
      from rest None obtain T' where T': "ok (norm_type_aux (tyenv E) T) T'" and t': "t' = Var x T'" by auto
      from nT[OF T'] have cT: "tcons ?\<theta> T" and T'': "T' = tnorm ?\<theta> T" by auto
      have "ap \<rho> \<sigma> t' = ap \<rho>' \<sigma>' t" using tyeq[OF cT] i(7)[OF xn] by (simp add: Var t' T'')
      then show ?thesis using nout_Var[OF tac(1) xn] t' T'' by (auto intro: ueq_refl)
    next
      case (Some U u)
      from rest Some(2) have "nt E u = Some (Ok t')" by simp
      note IHu = IH[OF this]
      have "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' (Var x T)"
        by (rule iext_remove_types_lookup[OF ie tac Some(1)[unfolded E]]) (use Some(3-5) tE in simp_all)
      from conjunct1[OF IHu] ueq_trans[OF conjunct2[OF IHu] this] show ?thesis unfolding Var by (rule conjI)
    qed
  next
    case (Bound i)
    with h r show ?thesis by (auto simp: nout_def tnormal_def intro: ueq_refl)
  next
    case (Abs a T body)
    from h r Abs obtain T' b' where T': "ok (norm_type_aux (tyenv E) T) T'" and b': "nt E body = Some (Ok b')"
      and t': "t' = Abs a T' b'"
      by auto
    from nT[OF T'] have T'': "T' = tnorm ?\<theta> T" by auto
    note IHb = IH[OF b']
    have "nout env t'" using IHb t' T'' tnorm_unbound[OF tac(1)] by (fastforce simp: nout_def tnormal_def)
    moreover have "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
      unfolding Abs t' ap_simps by (rule ueq_Abs) (use IHb in blast)
    ultimately show ?thesis by blast
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt E (subst_bound u body) = Some (Ok t')" using h r App f by simp
      from redex[OF this] show ?thesis unfolding App f .
    next
      case False
      with h r App obtain nf where hf: "nt E f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt E (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt E u; return (nf $ nu)}) t'"
        by (cases f) auto
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have "nt E (subst_bound u body) = Some (Ok t')" using rest nfb by simp
        then have R: "nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' (nf $ u)" unfolding nfb by (rule redex)
        have "ap \<rho>' \<sigma>' (nf $ u) \<approx> ap \<rho>' \<sigma>' (f $ u)"
          unfolding ap_simps ap_unb[OF conjunct1[OF IHf]] by (rule ueq_App) (use IHf in \<open>blast intro: ueq_refl\<close>)+
        from conjunct1[OF R] ueq_trans[OF conjunct2[OF R] this] show ?thesis unfolding App by (rule conjI)
      next
        case False
        with rest obtain nu where hu: "nt E u = Some (Ok nu)" and t': "t' = nf $ nu"
          by (cases nf) auto
        note IHu = IH[OF hu]
        have "nout env t'" using IHf IHu t' by (auto simp: nout_def tnormal_def)
        moreover have "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
          unfolding App t' ap_simps by (rule ueq_App) (use IHf IHu in blast)+
        ultimately show ?thesis by blast
      qed
    qed
  qed
qed

lemma norm_term1_ok:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv (remove_types_env env) \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow>
    iext env \<rho> \<sigma> \<rho>' \<sigma>' \<Longrightarrow> nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps" and r = "1.prems"(1) and te = "1.prems"(2) and em = "1.prems"(3) and ie = "1.prems"(4)
  note i = iextD[OF ie]
  have IH: "nout env u' \<and> ap \<rho> \<sigma> u' \<approx> ap \<rho>' \<sigma>' u" if "nt te u = Some (Ok u')" for u u'
    using "1.IH"[OF that HOL.refl te em ie] .
  have nl: "vt_lookup (tyenv env) v = None" for v using em by (rule vt_is_empty_lookup)
  have rho: "\<rho>' = \<rho>" by (intro ext) (simp add: i(6) nl)
  have tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    using em by (auto simp: tacyc_def tdep_def tcons_env_def nl acyclic_def)
  have ap_unb: "ap \<rho>' \<sigma>' s = ap \<rho> \<sigma> s" if "nout env s" for s by (rule iext_unb[OF ie nout_unb[OF that]])
  have redex: "nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' (Abs b U body $ u)"
    if "nt te (subst_bound u body) = Some (Ok t')" for b U body u
    using IH[OF that] ueq_trans[OF _ ueq_sym[OF ap_beta_ueq[OF i(2)]]] by blast
  have nout0: "nout env s" if "vars s = {}" for s using that by (simp add: nout_def tnormal_def nl)
  show ?case
  proof (cases t)
    case (Var x T)
    from h r Var obtain lr where lk: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return (Var x T)) t'"
      by auto
    from lookup1_success[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume xn0: "vt_lookup te x = None" and "lr = None"
      with rest have t': "t' = Var x T" by simp
      have xn: "vt_lookup (tenv env) x = None" using xn0 te by simp
      have "ap \<rho> \<sigma> t' = ap \<rho>' \<sigma>' t" using i(7)[OF xn] by (simp add: Var t' rho)
      then show ?thesis using xn t' by (auto simp: nout_def tnormal_def nl intro: ueq_refl)
    next
      fix u assume lku: "vt_lookup te x = Some (T, u)" and "lr = Some u"
      with rest have "nt te u = Some (Ok t')" by simp
      note IHu = IH[OF this]
      have "ap \<rho>' \<sigma>' u \<approx> ap \<rho>' \<sigma>' (Var x T)"
        by (rule iext_remove_types_lookup[OF ie tac lku[unfolded te]]) (simp_all add: tcons_empty[OF em])
      from conjunct1[OF IHu] ueq_trans[OF conjunct2[OF IHu] this] show ?thesis unfolding Var by (rule conjI)
    qed
  next
    case (Abs a T body)
    from h r Abs obtain b' where b': "nt te body = Some (Ok b')" and t': "t' = Abs a T b'" by auto
    note IHb = IH[OF b']
    have "nout env t'" using IHb t' by (auto simp: nout_def tnormal_def nl)
    moreover have "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
      unfolding Abs t' ap_simps by (rule ueq_Abs) (use IHb in blast)
    ultimately show ?thesis by blast
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt te (subst_bound u body) = Some (Ok t')" using h r App f by simp
      from redex[OF this] show ?thesis unfolding App f .
    next
      case False
      with h r App obtain nf where hf: "nt te f = Some (Ok nf)"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      note IHf = IH[OF hf]
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have "nt te (subst_bound u body) = Some (Ok t')" using rest nfb by simp
        then have R: "nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' (nf $ u)" unfolding nfb by (rule redex)
        have "ap \<rho>' \<sigma>' (nf $ u) \<approx> ap \<rho>' \<sigma>' (f $ u)"
          unfolding ap_simps ap_unb[OF conjunct1[OF IHf]] by (rule ueq_App) (use IHf in \<open>blast intro: ueq_refl\<close>)+
        from conjunct1[OF R] ueq_trans[OF conjunct2[OF R] this] show ?thesis unfolding App by (rule conjI)
      next
        case False
        with rest obtain nu where hu: "nt te u = Some (Ok nu)" and t': "t' = nf $ nu"
          by (cases nf) auto
        note IHu = IH[OF hu]
        have "nout env t'" using IHf IHu t' by (auto simp: nout_def tnormal_def)
        moreover have "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
          unfolding App t' ap_simps by (rule ueq_App) (use IHf IHu in blast)+
        ultimately show ?thesis by blast
      qed
    qed
  qed (use h r rho nout0 in \<open>auto intro: ueq_refl\<close>)
qed

text \<open>
  A normalized annotation is normal and equivalent to the original one at an instance and its
  extension through a solution of the environment:
\<close>

theorem norm_term_prf_ok:
  assumes nt: "ok (norm_term (remove_types_env env) t) t'" and ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
    and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
  shows "nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
proof -
  let ?E = "remove_types_env env"
  consider (id) "env_is_empty ?E \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty ?E \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv ?E)"
    | (n2) "\<not> (env_is_empty ?E \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv ?E)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have t': "t' = t" using nt by (simp add: norm_term_def)
    have l: "vt_lookup (tenv env) x = None" "vt_lookup (tyenv env) v = None" for x v
      using vt_is_empty_lookup[of "tenv ?E" x] vt_is_empty_lookup[of "tyenv env" v] id
      by (simp_all add: env_is_empty_def)
    then have "nout env t" by (simp add: nout_def tnormal_def)
    moreover have "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" by (rule iext_unb[OF ie]) (simp add: unb_def l)
    ultimately show ?thesis using t' by (simp add: ueq_refl)
  next
    case n1
    with nt have "norm_term1 (tenv ?E) t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term1_ok[OF this HOL.refl HOL.refl _ ie] n1(2) show ?thesis by simp
  next
    case n2
    with nt have "norm_term2 ?E t = Some (Ok t')" by (simp add: norm_term_def)
    from norm_term2_ok[OF this HOL.refl HOL.refl ie tac] show ?thesis .
  qed
qed

end


subsection \<open>Proofs\<close>

text \<open>The annotations and the types of a proof:\<close>

fun prf_terms :: "prf \<Rightarrow> pterm set" where
  "prf_terms (Abst a T p) = prf_terms p"
| "prf_terms (AbsP a t p) = set_option t \<union> prf_terms p"
| "prf_terms (PAppt p t) = prf_terms p \<union> set_option t"
| "prf_terms (PAppp p q) = prf_terms p \<union> prf_terms q"
| "prf_terms p = {}"

fun prf_typs :: "prf \<Rightarrow> ptyp set" where
  "prf_typs (Abst a T p) = set_option T \<union> prf_typs p"
| "prf_typs (AbsP a t p) = prf_typs p"
| "prf_typs (PAppt p t) = prf_typs p"
| "prf_typs (PAppp p q) = prf_typs p \<union> prf_typs q"
| "prf_typs (PAxm a A Us) = (case Us of None \<Rightarrow> {} | Some Us \<Rightarrow> set Us)"
| "prf_typs (Oracle a A Us) = (case Us of None \<Rightarrow> {} | Some Us \<Rightarrow> set Us)"
| "prf_typs (PThm (h, b)) = (case hd_types h of None \<Rightarrow> {} | Some Us \<Rightarrow> set Us)"
| "prf_typs (PClass T c) = {T}"
| "prf_typs p = {}"

text \<open>Computations without warnings or exceptions:\<close>

lemma returnP_inj [simp]: "returnP x = returnP y \<longleftrightarrow> x = y"
  by (simp add: returnP_def)

lemma bindP_eq_returnP: "bindP m f = returnP y \<longleftrightarrow> (\<exists>x. m = returnP x \<and> f x = returnP y)"
  by (auto simp: bindP_def returnP_def split: option.splits res.splits prod.splits)

lemma map_optionP_eq_returnP:
  "map_optionP f x = returnP y \<longleftrightarrow> x = None \<and> y = None \<or> (\<exists>a b. x = Some a \<and> y = Some b \<and> f a = returnP b)"
  by (auto simp: map_optionP_def bindP_eq_returnP split: option.splits)

lemma handleP_liftMP_returnP: "handleP (liftMP m) h = returnP x \<Longrightarrow> (\<And>e. h e \<noteq> returnP x) \<Longrightarrow> ok m x"
  by (auto simp: handleP_def liftMP_def returnP_def split: option.splits res.splits prod.splits)

lemma warnP_bindP: "bindP (warnP s) g \<noteq> returnP x"
  by (auto simp: bindP_def warnP_def returnP_def split: option.splits)

lemma raiseP_returnP: "raiseP e \<noteq> returnP x"
  by (simp add: raiseP_def returnP_def)

lemma norm_term_P_returnP: "norm_term_P E t = returnP t' \<Longrightarrow> ok (norm_term E t) t'"
  unfolding norm_term_P_def
  by (erule handleP_liftMP_returnP) (auto simp: warnP_bindP raiseP_returnP split: exn.splits)

lemma norm_type_P_returnP:
  assumes "norm_type_P \<theta> T = returnP T'" "tacyc \<theta>"
  shows "tcons \<theta> T \<and> T' = tnorm \<theta> T"
proof -
  from assms(1) have "ok (norm_type \<theta> T) T'"
    unfolding norm_type_P_def
    by (rule handleP_liftMP_returnP) (auto simp: warnP_bindP raiseP_returnP split: exn.splits)
  from norm_type_success[OF this assms(2)] show ?thesis .
qed

lemma norm_types_P_returnP:
  assumes "norm_types_P \<theta> Ts = returnP Ts'" "tacyc \<theta>"
  shows "(\<forall>T\<in>set Ts. tcons \<theta> T) \<and> Ts' = map (tnorm \<theta>) Ts"
proof -
  from assms(1) have m: "ok (if vt_is_empty \<theta> then return Ts else mapM (norm_type_aux \<theta>) Ts) Ts'"
    unfolding norm_types_P_def
    by (rule handleP_liftMP_returnP) (auto simp: warnP_bindP raiseP_returnP split: exn.splits)
  show ?thesis
  proof (cases "vt_is_empty \<theta>")
    case True
    with m show ?thesis by (simp add: tcons_empty tnorm_empty map_idI)
  next
    case False
    with m have "list_all2 (\<lambda>x y. ok (norm_type_aux \<theta> x) y) Ts Ts'" by (simp add: ok_mapM)
    then have "list_all2 (\<lambda>x y. tcons \<theta> x \<and> y = tnorm \<theta> x) Ts Ts'"
      by (rule list.rel_mono_strong) (auto dest: norm_type_aux_ok_success[OF _ assms(2)])
    then show ?thesis by (auto simp: list_all2_conv_all_nth in_set_conv_nth intro!: nth_equalityI)
  qed
qed

context prf_sig
begin

text \<open>
  The normalized proof is, at every instance, equivalent to the original proof at the extension
  of the instance through a solution of the environment:
\<close>

definition nrel :: "env \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> bool" where
  "nrel env q q' \<longleftrightarrow> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>'. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> prf_aeq (prf_ap \<rho>' \<sigma>' q) (prf_ap \<rho> \<sigma> q'))"

theorem norm_proof_ok:
  assumes tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
  shows "norm_proof (remove_types_env env) q = returnP q' \<Longrightarrow> nrel env q q'"
proof (induction q arbitrary: q')
  let ?E = "remove_types_env env" and ?\<theta> = "tyenv env"
  have tyopt: "map_option (tsubst \<rho>) T' = map_option (tsubst \<rho>') T"
    if "map_optionP (norm_type_P ?\<theta>) T = returnP T'" "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for T T' \<rho> \<sigma> \<rho>' \<sigma>'
  proof -
    from that(1) consider "T = None" "T' = None"
      | a b where "T = Some a" "T' = Some b" "norm_type_P ?\<theta> a = returnP b"
      by (auto simp: map_optionP_eq_returnP)
    then show ?thesis
    proof cases
      case 2
      with norm_type_P_returnP[OF 2(3) tac(1)] iext_tnorm[OF that(2) tac] show ?thesis by auto
    qed simp
  qed
  have tysopt: "map_option (map (tsubst \<rho>)) Ts' = map_option (map (tsubst \<rho>')) Ts"
    if "map_optionP (norm_types_P ?\<theta>) Ts = returnP Ts'" "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for Ts Ts' \<rho> \<sigma> \<rho>' \<sigma>'
  proof -
    from that(1) consider "Ts = None" "Ts' = None"
      | a b where "Ts = Some a" "Ts' = Some b" "norm_types_P ?\<theta> a = returnP b"
      by (auto simp: map_optionP_eq_returnP)
    then show ?thesis
    proof cases
      case 2
      from norm_types_P_returnP[OF 2(3) tac(1)] have "\<forall>T\<in>set a. tcons ?\<theta> T" "b = map (tnorm ?\<theta>) a" by auto
      then have "map (tsubst \<rho>) b = map (tsubst \<rho>') a"
        unfolding map_map by (auto intro!: map_cong iext_tnorm[OF that(2) tac])
      with 2 show ?thesis by simp
    qed simp
  qed
  have tmopt: "ann_eq (map_option (ap \<rho>' \<sigma>') t) (map_option (ap \<rho> \<sigma>) t')"
    if "map_optionP (norm_term_P ?E) t = returnP t'" "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for t t' \<rho> \<sigma> \<rho>' \<sigma>'
  proof -
    from that(1) consider "t = None" "t' = None"
      | u u' where "t = Some u" "t' = Some u'" "norm_term_P ?E u = returnP u'"
      by (auto simp: map_optionP_eq_returnP)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (simp add: ann_eq_def)
    next
      case 2
      from norm_term_prf_ok[OF norm_term_P_returnP[OF 2(3)] that(2) tac]
      have "ap \<rho> \<sigma> u' \<approx> ap \<rho>' \<sigma>' u" by blast
      then have "ap \<rho>' \<sigma>' u \<approx> ap \<rho> \<sigma> u'" by (rule ueq_sym)
      then show ?thesis using 2(1,2) unfolding ann_eq_def by simp
    qed
  qed
  {
    case (Abst a T q)
    from Abst.prems obtain T' q0 where T': "map_optionP (norm_type_P ?\<theta>) T = returnP T'"
      and q0: "norm_proof ?E q = returnP q0" and q': "q' = Abst a T' q0"
      by (auto simp: bindP_eq_returnP)
    show ?case using Abst.IH[OF q0] tyopt[OF T'] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro: prf_aeq.Abst)
  next
    case (AbsP a t q)
    from AbsP.prems obtain t' q0 where t': "map_optionP (norm_term_P ?E) t = returnP t'"
      and q0: "norm_proof ?E q = returnP q0" and q': "q' = AbsP a t' q0"
      by (auto simp: bindP_eq_returnP)
    show ?case using AbsP.IH[OF q0] tmopt[OF t'] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.AbsP)
  next
    case (PAppt q t)
    from PAppt.prems obtain t' q0 where t': "map_optionP (norm_term_P ?E) t = returnP t'"
      and q0: "norm_proof ?E q = returnP q0" and q': "q' = PAppt q0 t'"
      by (auto simp: bindP_eq_returnP)
    show ?case using PAppt.IH[OF q0] tmopt[OF t'] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.PAppt)
  next
    case (PAppp q1 q2)
    from PAppp.prems obtain p1 p2 where p1: "norm_proof ?E q1 = returnP p1"
      and p2: "norm_proof ?E q2 = returnP p2" and q': "q' = PAppp p1 p2"
      by (auto simp: bindP_eq_returnP)
    show ?case using PAppp.IH(1)[OF p1] PAppp.IH(2)[OF p2] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.PAppp)
  next
    case (PAxm a A Ts)
    from PAxm.prems obtain Ts' where Ts': "map_optionP (norm_types_P ?\<theta>) Ts = returnP Ts'"
      and q': "q' = PAxm a A Ts'"
      by (auto simp: bindP_eq_returnP)
    show ?case using tysopt[OF Ts'] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro: prf_aeq.refl)
  next
    case (Oracle a A Ts)
    from Oracle.prems obtain Ts' where Ts': "map_optionP (norm_types_P ?\<theta>) Ts = returnP Ts'"
      and q': "q' = Oracle a A Ts'"
      by (auto simp: bindP_eq_returnP)
    show ?case using tysopt[OF Ts'] unfolding q'
      by (auto simp: nrel_def prf_ap_def intro: prf_aeq.refl)
  next
    case (PThm hb)
    obtain h b where hb: "hb = (h, b)" by (cases hb)
    from PThm.prems obtain Ts' where Ts': "map_optionP (norm_types_P ?\<theta>) (hd_types h) = returnP Ts'"
      and q': "q' = PThm (hd_set_types h Ts', b)"
      by (auto simp: hb bindP_eq_returnP)
    show ?case using tysopt[OF Ts'] unfolding q' hb
      by (auto simp: nrel_def prf_ap_def intro: prf_aeq.refl)
  next
    case (PClass T c)
    from PClass.prems obtain T' where T': "norm_type_P ?\<theta> T = returnP T'" and q': "q' = PClass T' c"
      by (auto simp: bindP_eq_returnP)
    from norm_type_P_returnP[OF T' tac(1)] iext_tnorm[OF _ tac] show ?case unfolding q'
      by (auto simp: nrel_def prf_ap_def intro: prf_aeq.refl)
  }
qed (auto simp: nrel_def prf_ap_def intro: prf_aeq.refl)

end

end
