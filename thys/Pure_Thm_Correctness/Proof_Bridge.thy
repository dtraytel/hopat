section \<open>Closed instances and environments\<close>

theory Proof_Bridge
  imports Proof_Flatten Thm_Type
begin

context prf_csig
begin

subsection \<open>Closed instances as substitutions\<close>

text \<open>
  A closed instantiation \<open>\<theta>\<close> of the variables is the substitution \<open>isubst \<theta>\<close> of the codes of the
  variables in the semantics; it is rigid.
\<close>

definition isubst :: "(indexname \<Rightarrow> pterm) \<Rightarrow> nat \<Rightarrow> dB" where
  "isubst \<theta> n = (case atom_of n of AVar x \<Rightarrow> tr (\<theta> x) | _ \<Rightarrow> dB.Var n)"

lemma isubst_code[simp]:
  "isubst \<theta> (code (AVar x)) = tr (\<theta> x)"
  "isubst \<theta> (code (AConst a T)) = dB.Var (code (AConst a T))"
  "isubst \<theta> (code (AFree a T)) = dB.Var (code (AFree a T))"
  by (simp_all add: isubst_def)

lemma rigid_isubst: "rigid_subst (isubst \<theta>)"
  by (auto simp: rigid_subst_def rigid_code_def)

lemma closed_isubst:
  assumes "\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0"
  shows "closed_on UNIV (isubst \<theta>)"
proof -
  have "no_loose_bound (isubst \<theta> n) 0" for n
  proof (cases "atom_of n")
    case (AVar x)
    from assms have "proper (\<theta> x)" "\<not> loose_bvar (\<theta> x) 0" by blast+
    then have "no_loose_bound (tr (\<theta> x)) 0"
      using loose_bvar_tr[of "\<theta> x" 0] by simp
    with AVar show ?thesis by (simp add: isubst_def)
  qed (simp_all add: isubst_def)
  then show ?thesis by (simp add: closed_on_def)
qed

lemma tr_psubst_sm:
  assumes "\<forall>x\<in>vars t. \<not> loose_bvar (\<theta> x) 0"
  shows "tr (psubst \<rho> \<theta> 0 t) = sm \<rho> (isubst \<theta>) t"
  using assms
proof (induction t)
  case (Abs a T t)
  then show ?case using psubst_closed_lev[of t \<theta> 1 \<rho>] by simp
qed (simp_all add: sm_def incr_boundvars_eq)

text \<open>Substitutions that agree up to equivalence give equivalent instances.\<close>

lemma mk_subst_cong_equiv:
  "(\<And>F. F \<in> FV t \<Longrightarrow> \<sigma> F \<equiv>\<^sub>\<beta>\<^sub>\<eta> \<sigma>' F) \<Longrightarrow> mk_subst \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' t"
  by (induction t) (auto intro: equiv_App equiv_Abs)


subsection \<open>Erasing the types of constants\<close>

definition erc :: "nat \<Rightarrow> nat" where
  "erc n = (case atom_of n of AConst a T \<Rightarrow> code (AConst a dummyT) | _ \<Rightarrow> n)"

lemma tr_remove_types: "tr (remove_types t) = mk_subst (dB.Var \<circ> erc) (tr t)"
  by (induction t rule: remove_types.induct) (simp_all add: erc_def)

lemma remove_types_equiv:
  "tr s \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<Longrightarrow> tr (remove_types s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types t)"
  unfolding tr_remove_types by (rule mk_subst_equiv) (simp_all add: closed_on_def)

lemma remove_types_idem[simp]: "remove_types (remove_types t) = remove_types t"
  by (induction t rule: remove_types.induct) simp_all

lemma remove_types_incr_boundvars:
  "remove_types (incr_boundvars n t) = incr_boundvars n (remove_types t)"
  by (simp add: incr_boundvars_eq remove_types_incr_bv)

lemma remove_types_subst_bound_aux:
  "remove_types (subst_bound_aux u lev t) = subst_bound_aux (remove_types u) lev (remove_types t)"
  by (induction u lev t rule: subst_bound_aux.induct) (simp_all add: remove_types_incr_boundvars)

lemma remove_types_subst_bound:
  "remove_types (subst_bound u t) = subst_bound (remove_types u) (remove_types t)"
  by (simp add: subst_bound_def remove_types_subst_bound_aux)

lemma tys_subst_bound_aux: "tys (subst_bound_aux u lev t) \<subseteq> tys u \<union> tys t"
  by (induction u lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_eq tys_incr_bv)

lemma tys_subst_bound: "tys (subst_bound u t) \<subseteq> tys u \<union> tys t"
  by (simp add: subst_bound_def tys_subst_bound_aux)

lemma tys_remove_types: "tys (remove_types t) \<subseteq> insert dummyT (tys t)"
  by (induction t rule: remove_types.induct) auto

lemma could_beta_contract_remove_types[simp]:
  "could_beta_contract (remove_types t) \<longleftrightarrow> could_beta_contract t"
  by (induction t rule: could_beta_contract.induct) (auto elim: remove_types.elims)

lemma remove_types_eq_iff:
  "remove_types t = Const a T \<longleftrightarrow> T = dummyT \<and> (\<exists>U. t = Const a U)"
  "remove_types t = Free a T \<longleftrightarrow> t = Free a T"
  "remove_types t = Var x T \<longleftrightarrow> t = Var x T"
  "remove_types t = Bound i \<longleftrightarrow> t = Bound i"
  "remove_types t = Abs a T b \<longleftrightarrow> T = dummyT \<and> (\<exists>U b'. t = Abs a U b' \<and> remove_types b' = b)"
  "remove_types t = f $ u \<longleftrightarrow> (\<exists>f' u'. t = f' $ u' \<and> remove_types f' = f \<and> remove_types u' = u)"
  by (cases t; auto)+

lemma is_Abs_remove_types[simp]: "is_Abs (remove_types t) \<longleftrightarrow> is_Abs t"
  by (cases t) auto


subsection \<open>Normalization in the environment without types\<close>

text \<open>
  \<open>norm_proof_remove_types\<close> normalizes the terms of a proof in the environment whose terms have
  no types (\<^const>\<open>remove_types_env\<close>). On a term that agrees up to the types of its
  constants and abstractions with a term that is normalized in the environment, it computes
  the same, if the types of the term are consistent with the sorts of the type environment.
\<close>

lemma tenv_remove_types_env[simp]:
  "vt_lookup (tenv (remove_types_env env)) x = map_option (\<lambda>(T, t). (T, remove_types t)) (vt_lookup (tenv env) x)"
  "tyenv (remove_types_env env) = tyenv env"
  by (simp_all add: remove_types_env_def)

lemma lookup_remove_types_env:
  "ok (lookup env xi T) r \<Longrightarrow> ok (lookup (remove_types_env env) xi T) (map_option remove_types r)"
proof -
  assume a: "ok (lookup env xi T) r"
  show ?thesis
  proof (cases "vt_lookup (tenv env) xi")
    case None
    with a show ?thesis by (simp add: lookup_def)
  next
    case (Some Uu)
    obtain U u where Uu: "Uu = (U, u)" by (cases Uu)
    from a Some Uu obtain b where b: "ok (unified (tyenv env) T U) b"
      and r: "ok (if b then return (Some u) else var_clash xi T U) r"
      by (auto simp: lookup_def)
    then have "b" "r = Some u" by (auto simp: var_clash_def raise_def split: if_splits)
    with b Some Uu show ?thesis by (simp add: lookup_def)
  qed
qed

lemma lookup1_remove_types_env:
  "ok (lookup1 (tenv env) xi T) r \<Longrightarrow> ok (lookup1 (tenv (remove_types_env env)) xi T) (map_option remove_types r)"
  by (auto simp: lookup1_def var_clash_def raise_def split: option.splits if_splits)

lemma ok_lookup_Some: "ok (lookup env xi T) (Some u) \<Longrightarrow> \<exists>U. vt_lookup (tenv env) xi = Some (U, u)"
  by (auto simp: lookup_def var_clash_def raise_def split: option.splits if_splits)

lemma ok_lookup1_Some: "ok (lookup1 te xi T) (Some u) \<Longrightarrow> \<exists>U. vt_lookup te xi = Some (U, u)"
  by (auto simp: lookup1_def var_clash_def raise_def split: option.splits if_splits)

lemma tcons_dummyT[simp]: "tcons \<theta> dummyT"
  by (simp add: tcons_def dummyT_def)

lemma tcons_tys_remove_types:
  "\<forall>U\<in>tys u. tcons \<theta> U \<Longrightarrow> \<forall>U\<in>tys (remove_types u). tcons \<theta> U"
  using tys_remove_types[of u] by auto

lemma norm_term2_rt:
  assumes "norm_term2 env t0 = Some r"
  shows "r = Ok t0' \<Longrightarrow> remove_types t = remove_types t0 \<Longrightarrow> \<forall>U\<in>tys t. tcons (tyenv env) U \<Longrightarrow>
    tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> \<forall>U\<in>etys env. tcons (tyenv env) U \<Longrightarrow>
    \<exists>t'. ok (norm_term2 (remove_types_env env) t) t' \<and> remove_types t' = remove_types t0' \<and>
      (\<forall>U\<in>tys t'. tcons (tyenv env) U)"
  using assms
proof (induction env t0 r arbitrary: t t0' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t0 r)
  note t0' = "1.hyps"[unfolded "1.prems"(1)]
  let ?e = "remove_types_env env" and ?\<theta> = "tyenv env"
  have ac: "tacyc ?\<theta>" and tc: "tcons_env ?\<theta>" and et: "\<forall>U\<in>etys env. tcons ?\<theta> U"
    using "1.prems"(4-6) by auto
  have IH: "\<exists>s'. ok (norm_term2 ?e s) s' \<and> remove_types s' = remove_types s0' \<and> (\<forall>U\<in>tys s'. tcons ?\<theta> U)"
    if "nt env s0 = Some (Ok s0')" "remove_types s = remove_types s0" "\<forall>U\<in>tys s. tcons ?\<theta> U" for s s0 s0'
    using "1.IH"[OF that(1) HOL.refl that(2,3) ac tc et] .
  have nta: "norm_type_aux ?\<theta> T = return (tnorm ?\<theta> T)" if "tcons ?\<theta> T" for T
    by (rule norm_type_aux_ok[OF ac tc that])
  note tn = tcons_tnorm[OF ac]
  note rt = "1.prems"(2) and tt = "1.prems"(3)
  show ?case
  proof (cases t0)
    case (Const a T0)
    with rt obtain T where t: "t = Const a T" by (auto simp: remove_types_eq_iff)
    with tt have "tcons ?\<theta> T" by simp
    then have "ok (norm_term2 ?e t) (Const a (tnorm ?\<theta> T))"
      unfolding t by (subst norm_term2.simps) (simp add: nta)
    with t0' Const tn show ?thesis by auto
  next
    case (Free a T)
    with rt have t: "t = Free a T" by (simp add: remove_types_eq_iff)
    with tt have "tcons ?\<theta> T" by simp
    then have "ok (norm_term2 ?e t) (Free a (tnorm ?\<theta> T))"
      unfolding t by (subst norm_term2.simps) (simp add: nta)
    with t0' Free tn show ?thesis by (auto simp: nta[OF \<open>tcons ?\<theta> T\<close>])
  next
    case (Bound i)
    with rt have t: "t = Bound i" by (simp add: remove_types_eq_iff)
    have "ok (norm_term2 ?e t) (Bound i)" unfolding t by (subst norm_term2.simps) simp
    with t0' Bound show ?thesis by auto
  next
    case (Var xi T)
    with rt have t: "t = Var xi T" by (simp add: remove_types_eq_iff)
    with tt have tT: "tcons ?\<theta> T" by simp
    from t0' Var obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Var xi T'))) t0'"
      by auto
    note lk' = lookup_remove_types_env[OF lk]
    show ?thesis
    proof (cases r')
      case None
      with rest have "t0' = Var xi (tnorm ?\<theta> T)" by (simp add: nta[OF tT])
      moreover have "ok (norm_term2 ?e t) (Var xi (tnorm ?\<theta> T))"
        unfolding t using lk' None by (subst norm_term2.simps) (simp add: nta[OF tT])
      ultimately show ?thesis using tn by auto
    next
      case (Some u)
      from ok_lookup_Some[OF lk[unfolded Some]] obtain U where "vt_lookup (tenv env) xi = Some (U, u)" by blast
      then have "\<forall>V\<in>tys u. tcons ?\<theta> V" using et etysI[of env xi U u] by blast
      then have tu: "\<forall>V\<in>tys (remove_types u). tcons ?\<theta> V" by (rule tcons_tys_remove_types)
      from rest Some have "nt env u = Some (Ok t0')" by simp
      from IH[OF this _ tu] obtain s' where "ok (norm_term2 ?e (remove_types u)) s'"
        "remove_types s' = remove_types t0'" "\<forall>U\<in>tys s'. tcons ?\<theta> U"
        by auto
      moreover have "norm_term2 ?e t = norm_term2 ?e (remove_types u)"
        unfolding t using lk' Some by (subst norm_term2.simps) simp
      ultimately show ?thesis by auto
    qed
  next
    case (Abs a T0 b0)
    with rt obtain T b where t: "t = Abs a T b" and b: "remove_types b = remove_types b0"
      by (auto simp: remove_types_eq_iff)
    with tt have tT: "tcons ?\<theta> T" and tb: "\<forall>U\<in>tys b. tcons ?\<theta> U" by auto
    from t0' Abs obtain T0' b0' where nb: "nt env b0 = Some (Ok b0')" and r0: "t0' = Abs a T0' b0'"
      by auto
    from IH[OF nb b tb] obtain b' where "ok (norm_term2 ?e b) b'" "remove_types b' = remove_types b0'"
      "\<forall>U\<in>tys b'. tcons ?\<theta> U"
      by blast
    moreover from this(1) have "ok (norm_term2 ?e t) (Abs a (tnorm ?\<theta> T) b')"
      unfolding t by (subst norm_term2.simps) (simp add: nta[OF tT])
    ultimately show ?thesis using r0 tn by auto
  next
    case (App f0 u0)
    with rt obtain f u where t: "t = f $ u" and f: "remove_types f = remove_types f0"
      and u: "remove_types u = remove_types u0"
      by (auto simp: remove_types_eq_iff)
    from tt t have tf: "\<forall>U\<in>tys f. tcons ?\<theta> U" and tu: "\<forall>U\<in>tys u. tcons ?\<theta> U" by auto
    have sb: "\<exists>s'. ok (norm_term2 ?e (subst_bound u body)) s' \<and> remove_types s' = remove_types t0' \<and>
        (\<forall>U\<in>tys s'. tcons ?\<theta> U)"
      if "nt env (subst_bound u0 body0) = Some (Ok t0')" "remove_types body = remove_types body0"
        "\<forall>U\<in>tys body. tcons ?\<theta> U" for body body0
    proof (rule IH[OF that(1)])
      show "remove_types (subst_bound u body) = remove_types (subst_bound u0 body0)"
        by (simp add: remove_types_subst_bound that(2) u)
      show "\<forall>U\<in>tys (subst_bound u body). tcons ?\<theta> U"
        using tys_subst_bound[of u body] that(3) tu by auto
    qed
    show ?thesis
    proof (cases "is_Abs f0")
      case True
      then obtain x T0 body0 where f0: "f0 = Abs x T0 body0" by (cases f0) auto
      with f obtain T body where fa: "f = Abs x T body" and bd: "remove_types body = remove_types body0"
        by (auto simp: remove_types_eq_iff)
      from t0' App f0 have n: "nt env (subst_bound u0 body0) = Some (Ok t0')" by simp
      have "norm_term2 ?e t = norm_term2 ?e (subst_bound u body)"
        unfolding t fa by (subst norm_term2.simps) simp
      with sb[OF n bd] tf fa show ?thesis by auto
    next
      case False
      have nA: "\<not> is_Abs f" using False f is_Abs_remove_types by metis
      from t0' App False obtain nf0 where nf0: "nt env f0 = Some (Ok nf0)"
        and rest: "ok (case nf0 of Abs _ _ body \<Rightarrow> nt env (subst_bound u0 body)
          | _ \<Rightarrow> nt env u0 \<bind> (\<lambda>nu. return (nf0 $ nu))) t0'"
        by (cases f0) auto
      from IH[OF nf0 f tf] obtain nf where nf: "ok (norm_term2 ?e f) nf"
        and rnf: "remove_types nf = remove_types nf0" and tnf: "\<forall>U\<in>tys nf. tcons ?\<theta> U"
        by blast
      have unf: "norm_term2 ?e t = (case nf of Abs _ _ body \<Rightarrow> norm_term2 ?e (subst_bound u body)
          | _ \<Rightarrow> norm_term2 ?e u \<bind> (\<lambda>nu. return (nf $ nu)))"
        unfolding t using nA nf by (subst norm_term2.simps) (cases f; simp)
      show ?thesis
      proof (cases "is_Abs nf0")
        case True
        then obtain x T0 body0 where nf0A: "nf0 = Abs x T0 body0" by (cases nf0) auto
        with rnf obtain T body where nfA: "nf = Abs x T body" and bd: "remove_types body = remove_types body0"
          by (auto simp: remove_types_eq_iff)
        from rest nf0A have n: "nt env (subst_bound u0 body0) = Some (Ok t0')" by simp
        from sb[OF n bd] tnf nfA unf show ?thesis by auto
      next
        case False
        have nfA: "\<not> is_Abs nf" using False rnf is_Abs_remove_types by metis
        from rest False obtain nu0 where nu0: "nt env u0 = Some (Ok nu0)" and r0: "t0' = nf0 $ nu0"
          by (cases nf0) auto
        from IH[OF nu0 u tu] obtain nu where "ok (norm_term2 ?e u) nu"
          "remove_types nu = remove_types nu0" "\<forall>U\<in>tys nu. tcons ?\<theta> U"
          by blast
        moreover from this(1) have "ok (norm_term2 ?e t) (nf $ nu)"
          using unf nfA by (cases nf) auto
        ultimately show ?thesis using r0 rnf tnf by auto
      qed
    qed
  qed
qed


lemma norm_term1_rt:
  assumes "norm_term1 te t0 = Some r"
  shows "r = Ok t0' \<Longrightarrow> remove_types t = remove_types t0 \<Longrightarrow> te = tenv env \<Longrightarrow>
    \<exists>t'. ok (norm_term1 (tenv (remove_types_env env)) t) t' \<and> remove_types t' = remove_types t0'"
  using assms
proof (induction te t0 r arbitrary: t t0' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t0 r)
  note t0' = "1.hyps"[unfolded "1.prems"(1)]
  let ?te = "tenv (remove_types_env env)"
  have IH: "\<exists>s'. ok (norm_term1 ?te s) s' \<and> remove_types s' = remove_types s0'"
    if "nt te s0 = Some (Ok s0')" "remove_types s = remove_types s0" for s s0 s0'
    using "1.IH"[OF that(1) HOL.refl that(2) "1.prems"(3)] .
  note rt = "1.prems"(2) and te = "1.prems"(3)
  show ?case
  proof (cases t0)
    case (Var xi T)
    with rt have t: "t = Var xi T" by (simp add: remove_types_eq_iff)
    from t0' Var obtain r' where lk: "ok (lookup1 te xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t0) t0'"
      by auto
    note lk' = lookup1_remove_types_env[OF lk[unfolded te]]
    show ?thesis
    proof (cases r')
      case None
      with rest Var have "t0' = Var xi T" by simp
      moreover have "ok (norm_term1 ?te t) (Var xi T)"
        unfolding t using lk' None by (subst norm_term1.simps) simp
      ultimately show ?thesis by auto
    next
      case (Some u)
      from rest Some have "nt te u = Some (Ok t0')" by simp
      from IH[OF this, of "remove_types u"] obtain s' where "ok (norm_term1 ?te (remove_types u)) s'"
        "remove_types s' = remove_types t0'"
        by auto
      moreover have "norm_term1 ?te t = norm_term1 ?te (remove_types u)"
        unfolding t using lk' Some by (subst norm_term1.simps) simp
      ultimately show ?thesis by auto
    qed
  next
    case (Abs a T0 b0)
    with rt obtain T b where t: "t = Abs a T b" and b: "remove_types b = remove_types b0"
      by (auto simp: remove_types_eq_iff)
    from t0' Abs obtain b0' where nb: "nt te b0 = Some (Ok b0')" and r0: "t0' = Abs a T0 b0'"
      by auto
    from IH[OF nb b] obtain b' where "ok (norm_term1 ?te b) b'" "remove_types b' = remove_types b0'"
      by blast
    moreover from this(1) have "ok (norm_term1 ?te t) (Abs a T b')"
      unfolding t by (subst norm_term1.simps) simp
    ultimately show ?thesis using r0 by auto
  next
    case (App f0 u0)
    with rt obtain f u where t: "t = f $ u" and f: "remove_types f = remove_types f0"
      and u: "remove_types u = remove_types u0"
      by (auto simp: remove_types_eq_iff)
    have sb: "\<exists>s'. ok (norm_term1 ?te (subst_bound u body)) s' \<and> remove_types s' = remove_types t0'"
      if "nt te (subst_bound u0 body0) = Some (Ok t0')" "remove_types body = remove_types body0" for body body0
      by (rule IH[OF that(1)]) (simp add: remove_types_subst_bound that(2) u)
    show ?thesis
    proof (cases "is_Abs f0")
      case True
      then obtain x T0 body0 where f0: "f0 = Abs x T0 body0" by (cases f0) auto
      with f obtain T body where fa: "f = Abs x T body" and bd: "remove_types body = remove_types body0"
        by (auto simp: remove_types_eq_iff)
      from t0' App f0 have n: "nt te (subst_bound u0 body0) = Some (Ok t0')" by simp
      have "norm_term1 ?te t = norm_term1 ?te (subst_bound u body)"
        unfolding t fa by (subst norm_term1.simps) simp
      with sb[OF n bd] show ?thesis by auto
    next
      case False
      have nA: "\<not> is_Abs f" using False f is_Abs_remove_types by metis
      from t0' App False obtain nf0 where nf0: "nt te f0 = Some (Ok nf0)"
        and rest: "ok (case nf0 of Abs _ _ body \<Rightarrow> nt te (subst_bound u0 body)
          | _ \<Rightarrow> nt te u0 \<bind> (\<lambda>nu. return (nf0 $ nu))) t0'"
        by (cases f0) auto
      from IH[OF nf0 f] obtain nf where nf: "ok (norm_term1 ?te f) nf"
        and rnf: "remove_types nf = remove_types nf0"
        by blast
      have unf: "norm_term1 ?te t = (case nf of Abs _ _ body \<Rightarrow> norm_term1 ?te (subst_bound u body)
          | _ \<Rightarrow> norm_term1 ?te u \<bind> (\<lambda>nu. return (nf $ nu)))"
        unfolding t using nA nf by (subst norm_term1.simps) (cases f; simp)
      show ?thesis
      proof (cases "is_Abs nf0")
        case True
        then obtain x T0 body0 where nf0A: "nf0 = Abs x T0 body0" by (cases nf0) auto
        with rnf obtain T body where nfA: "nf = Abs x T body" and bd: "remove_types body = remove_types body0"
          by (auto simp: remove_types_eq_iff)
        from rest nf0A have n: "nt te (subst_bound u0 body0) = Some (Ok t0')" by simp
        from sb[OF n bd] nfA unf show ?thesis by auto
      next
        case False
        have nfA: "\<not> is_Abs nf" using False rnf is_Abs_remove_types by metis
        from rest False obtain nu0 where nu0: "nt te u0 = Some (Ok nu0)" and r0: "t0' = nf0 $ nu0"
          by (cases nf0) auto
        from IH[OF nu0 u] obtain nu where "ok (norm_term1 ?te u) nu"
          "remove_types nu = remove_types nu0"
          by blast
        moreover from this(1) have "ok (norm_term1 ?te t) (nf $ nu)"
          using unf nfA by (cases nf) auto
        ultimately show ?thesis using r0 rnf by auto
      qed
    qed
  next
    case (Const a T0)
    with rt obtain U where t: "t = Const a U" by (auto simp: remove_types_eq_iff)
    from t0' Const have "t0' = t0" by simp
    moreover have "ok (norm_term1 ?te t) t" unfolding t by (subst norm_term1.simps) simp
    ultimately show ?thesis using rt by auto
  next
    case (Free a T)
    with rt have t: "t = Free a T" by (simp add: remove_types_eq_iff)
    from t0' Free have "t0' = t0" by simp
    moreover have "ok (norm_term1 ?te t) t" unfolding t by (subst norm_term1.simps) simp
    ultimately show ?thesis using rt by auto
  next
    case (Bound i)
    with rt have t: "t = Bound i" by (simp add: remove_types_eq_iff)
    from t0' Bound have "t0' = t0" by simp
    moreover have "ok (norm_term1 ?te t) t" unfolding t by (subst norm_term1.simps) simp
    ultimately show ?thesis using rt by auto
  qed
qed

lemma vt_is_empty_iff: "vt_is_empty t \<longleftrightarrow> (\<forall>k. vt_lookup t k = None)"
  by transfer auto

lemma env_is_empty_remove_types_env[simp]: "env_is_empty (remove_types_env env) \<longleftrightarrow> env_is_empty env"
  by (simp add: env_is_empty_def vt_is_empty_iff remove_types_env_def)

lemma tcons_empty: "vt_is_empty \<theta> \<Longrightarrow> tcons \<theta> T"
  by (simp add: tcons_def vt_is_empty_lookup)

lemma norm_term_rt:
  assumes "ok (norm_term env t0) t0'" "remove_types t = remove_types t0" "\<forall>U\<in>tys t. tcons (tyenv env) U"
    "tacyc (tyenv env)" "tcons_env (tyenv env)" "\<forall>U\<in>etys env. tcons (tyenv env) U"
  shows "\<exists>t'. ok (norm_term (remove_types_env env) t) t' \<and> remove_types t' = remove_types t0' \<and>
    (\<forall>U\<in>tys t'. tcons (tyenv env) U)"
proof (cases "env_is_empty env \<and> \<not> could_beta_contract t0")
  case True
  moreover have "\<not> could_beta_contract t"
    using True assms(2) could_beta_contract_remove_types by metis
  ultimately show ?thesis using assms(1-3) by (simp add: norm_term_def)
next
  case nb: False
  then have nb': "\<not> (env_is_empty (remove_types_env env) \<and> \<not> could_beta_contract t)"
    using assms(2) could_beta_contract_remove_types by (metis env_is_empty_remove_types_env)
  show ?thesis
  proof (cases "vt_is_empty (tyenv env)")
    case True
    with nb assms(1) have "ok (norm_term1 (tenv env) t0) t0'" by (simp add: norm_term_def)
    from norm_term1_rt[OF this HOL.refl assms(2) HOL.refl] True nb' show ?thesis
      by (auto simp: norm_term_def tcons_empty)
  next
    case False
    with nb assms(1) have "ok (norm_term2 env t0) t0'" by (simp add: norm_term_def)
    from norm_term2_rt[OF this HOL.refl assms(2-6)] False nb' show ?thesis
      by (simp add: norm_term_def)
  qed
qed


subsection \<open>Normalization of proofs\<close>

text \<open>All terms of a proof satisfy \<open>P\<close>, and all its types \<open>Q\<close>.\<close>

fun prf_all :: "(pterm \<Rightarrow> bool) \<Rightarrow> (ptyp \<Rightarrow> bool) \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_all P Q (Abst a T p) \<longleftrightarrow> (\<forall>U\<in>set_option T. Q U) \<and> prf_all P Q p"
| "prf_all P Q (AbsP a t p) \<longleftrightarrow> (\<forall>u\<in>set_option t. P u) \<and> prf_all P Q p"
| "prf_all P Q (PAppt p t) \<longleftrightarrow> prf_all P Q p \<and> (\<forall>u\<in>set_option t. P u)"
| "prf_all P Q (PAppp p q) \<longleftrightarrow> prf_all P Q p \<and> prf_all P Q q"
| "prf_all P Q (PAxm a A Ts) \<longleftrightarrow> (\<forall>Us\<in>set_option Ts. \<forall>U\<in>set Us. Q U)"
| "prf_all P Q (PClass T c) \<longleftrightarrow> Q T"
| "prf_all P Q (Oracle a A Ts) \<longleftrightarrow> (\<forall>Us\<in>set_option Ts. \<forall>U\<in>set Us. Q U)"
| "prf_all P Q (PThm (h, b)) \<longleftrightarrow> (\<forall>Us\<in>set_option (hd_types h). \<forall>U\<in>set Us. Q U)"
| "prf_all P Q MinProof \<longleftrightarrow> True"
| "prf_all P Q (PBound i) \<longleftrightarrow> True"
| "prf_all P Q (Hyp t) \<longleftrightarrow> True"

lemma prf_all_mono: "prf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> P' t) \<Longrightarrow> (\<And>T. Q T \<Longrightarrow> Q' T) \<Longrightarrow> prf_all P' Q' p"
  by (induction P Q p rule: prf_all.induct) auto

text \<open>A proof and its normalization: the terms are related by \<open>R\<close>, the types are mapped by \<open>f\<close>.\<close>

inductive prf_rel :: "(pterm \<Rightarrow> pterm \<Rightarrow> bool) \<Rightarrow> (ptyp \<Rightarrow> ptyp) \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> bool" for R f where
  Abst: "prf_rel R f p p' \<Longrightarrow> prf_rel R f (Abst a T p) (Abst a (map_option f T) p')"
| AbsP: "rel_option R t t' \<Longrightarrow> prf_rel R f p p' \<Longrightarrow> prf_rel R f (AbsP a t p) (AbsP a t' p')"
| PAppt: "prf_rel R f p p' \<Longrightarrow> rel_option R t t' \<Longrightarrow> prf_rel R f (PAppt p t) (PAppt p' t')"
| PAppp: "prf_rel R f p p' \<Longrightarrow> prf_rel R f q q' \<Longrightarrow> prf_rel R f (PAppp p q) (PAppp p' q')"
| PAxm: "prf_rel R f (PAxm a A Ts) (PAxm a A (map_option (map f) Ts))"
| PClass: "prf_rel R f (PClass T c) (PClass (f T) c)"
| Oracle: "prf_rel R f (Oracle a A Ts) (Oracle a A (map_option (map f) Ts))"
| PThm: "prf_rel R f (PThm (h, b)) (PThm (hd_set_types h (map_option (map f) (hd_types h)), b))"
| MinProof: "prf_rel R f MinProof MinProof"
| PBound: "prf_rel R f (PBound i) (PBound i)"
| Hyp: "prf_rel R f (Hyp t) (Hyp t)"

lemma map_optionP_returnP:
  assumes "\<And>y. x = Some y \<Longrightarrow> \<exists>z. g y = returnP z \<and> R y z"
  shows "\<exists>x'. map_optionP g x = returnP x' \<and> rel_option R x x'"
  using assms by (cases x) (auto simp: map_optionP_def)

lemma norm_proof_ok:
  assumes "prf_all P Q p"
    and "\<And>t. P t \<Longrightarrow> \<exists>t'. norm_term_P env t = returnP t' \<and> R t t'"
    and "\<And>T. Q T \<Longrightarrow> norm_type_P (tyenv env) T = returnP (f T)"
    and "\<And>Ts. \<forall>T\<in>set Ts. Q T \<Longrightarrow> norm_types_P (tyenv env) Ts = returnP (map f Ts)"
  shows "\<exists>p'. norm_proof env p = returnP p' \<and> prf_rel R f p p'"
  using assms(1)
proof (induction p)
  case (Abst a T p)
  have m: "map_optionP (norm_type_P (tyenv env)) T = returnP (map_option f T)"
    using Abst.prems by (cases T) (auto simp: map_optionP_def assms(3))
  from Abst obtain p' where p': "norm_proof env p = returnP p'" "prf_rel R f p p'" by auto
  with m show ?case by (auto intro: prf_rel.Abst)
next
  case (AbsP a t p)
  from AbsP obtain p' where p': "norm_proof env p = returnP p'" "prf_rel R f p p'" by auto
  from AbsP.prems assms(2) obtain t' where m: "map_optionP (norm_term_P env) t = returnP t'" "rel_option R t t'"
    using map_optionP_returnP[of t "norm_term_P env" R] by fastforce
  with p' show ?case by (auto intro: prf_rel.AbsP)
next
  case (PAppt p t)
  from PAppt obtain p' where p': "norm_proof env p = returnP p'" "prf_rel R f p p'" by auto
  from PAppt.prems assms(2) obtain t' where m: "map_optionP (norm_term_P env) t = returnP t'" "rel_option R t t'"
    using map_optionP_returnP[of t "norm_term_P env" R] by fastforce
  with p' show ?case by (auto intro: prf_rel.PAppt)
next
  case (PAppp p q)
  then obtain p' q' where "norm_proof env p = returnP p'" "prf_rel R f p p'"
    "norm_proof env q = returnP q'" "prf_rel R f q q'"
    by auto
  then show ?case by (auto intro: prf_rel.PAppp)
next
  case (PAxm a A Ts)
  then have "map_optionP (norm_types_P (tyenv env)) Ts = returnP (map_option (map f) Ts)"
    by (cases Ts) (auto simp: map_optionP_def assms(4))
  then show ?case by (auto intro: prf_rel.PAxm)
next
  case (PClass T c)
  then show ?case by (auto simp: assms(3) intro: prf_rel.PClass)
next
  case (Oracle a A Ts)
  then have "map_optionP (norm_types_P (tyenv env)) Ts = returnP (map_option (map f) Ts)"
    by (cases Ts) (auto simp: map_optionP_def assms(4))
  then show ?case by (auto intro: prf_rel.Oracle)
next
  case (PThm hb)
  obtain h b where hb: "hb = (h, b)" by (cases hb)
  with PThm have "map_optionP (norm_types_P (tyenv env)) (hd_types h) = returnP (map_option (map f) (hd_types h))"
    by (cases "hd_types h") (auto simp: map_optionP_def assms(4))
  then show ?case unfolding hb by (auto intro: prf_rel.PThm)
qed (auto intro: prf_rel.intros)

lemma hd_set_types_twice[simp]: "hd_set_types (hd_set_types h Ts) Us = hd_set_types h Us"
  by (simp add: hd_set_types_def)

text \<open>The instances of a proof and of its normalization.\<close>

lemma prf_rel_inst:
  assumes "prf_rel R f p p'" "prf_all P Q p"
    and "\<And>t t' lev. R t t' \<Longrightarrow> P t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> ann_eq (Some (psubst \<rho>' \<theta>' lev t)) (Some (psubst \<rho> \<theta> lev t'))"
    and "\<And>T. Q T \<Longrightarrow> tsubst \<rho> (f T) = tsubst \<rho>' T"
    and "0 \<le> lev"
  shows "prf_aeq (prf_inst \<rho>' \<theta>' lev p) (prf_inst \<rho> \<theta> lev p')"
  using assms(1,2,5)
proof (induction arbitrary: lev rule: prf_rel.induct)
  case (Abst p p' a T)
  then have "map_option (tsubst \<rho>) (map_option f T) = map_option (tsubst \<rho>') T"
    using assms(4) by (cases T) auto
  with Abst show ?case by (auto intro: prf_aeq.Abst)
next
  case (AbsP t t' p p' a)
  have "ann_eq (map_option (psubst \<rho>' \<theta>' lev) t) (map_option (psubst \<rho> \<theta> lev) t')"
    using AbsP.hyps(1) AbsP.prems assms(3) by (cases rule: option.rel_cases) (auto simp: ann_eq_def)
  with AbsP show ?case by (auto intro: prf_aeq.AbsP)
next
  case (PAppt p p' t t')
  have "ann_eq (map_option (psubst \<rho>' \<theta>' lev) t) (map_option (psubst \<rho> \<theta> lev) t')"
    using PAppt.hyps(2) PAppt.prems assms(3) by (cases rule: option.rel_cases) (auto simp: ann_eq_def)
  with PAppt show ?case by (auto intro: prf_aeq.PAppt)
next
  case (PAppp p p' q q')
  then show ?case by (auto intro: prf_aeq.PAppp)
next
  case (PAxm a A Ts)
  then have "map_option (map (tsubst \<rho>')) Ts = map_option (map (tsubst \<rho>)) (map_option (map f) Ts)"
    using assms(4) by (cases Ts) auto
  then show ?case by (simp add: prf_aeq.refl)
next
  case (PClass T c)
  then show ?case using assms(4) by (simp add: prf_aeq.refl)
next
  case (Oracle a A Ts)
  then have "map_option (map (tsubst \<rho>')) Ts = map_option (map (tsubst \<rho>)) (map_option (map f) Ts)"
    using assms(4) by (cases Ts) auto
  then show ?case by (simp add: prf_aeq.refl)
next
  case (PThm h b)
  then have "map_option (map (tsubst \<rho>')) (hd_types h) = map_option (map (tsubst \<rho>)) (map_option (map f) (hd_types h))"
    using assms(4) by (cases "hd_types h") auto
  then show ?case by (simp add: prf_aeq.refl)
qed (simp_all add: prf_aeq.refl)

end

end
