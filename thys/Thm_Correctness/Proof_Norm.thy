section \<open>Normalizing proofs\<close>

theory Proof_Norm
  imports Proof_Flatten
begin

text \<open>
  \<^const>\<open>norm_proof\<close> normalizes the annotations of a proof with respect to an environment. For
  annotations without schematic variables whose type variables are consistent with the type
  environment, it raises no exception and prints no warning; the normalized annotations are
  \<open>\<beta>\<close>-reducts of the canonical type instances of the original ones.
\<close>

subsection \<open>Terms\<close>

definition tnormal :: "tyenv \<Rightarrow> pterm \<Rightarrow> bool" where
  "tnormal \<theta> t \<longleftrightarrow> (\<forall>U\<in>typs t. \<forall>(w, S)\<in>tvars U. vt_lookup \<theta> w = None)"

definition tconsT :: "tyenv \<Rightarrow> pterm \<Rightarrow> bool" where
  "tconsT \<theta> t \<longleftrightarrow> (\<forall>U\<in>typs t. tcons \<theta> U)"

lemma tconsT_tnormal: "tnormal \<theta> t \<Longrightarrow> tconsT \<theta> t"
  by (fastforce simp: tnormal_def tconsT_def tcons_def)

lemma typs_subst_bound: "typs (subst_bound u body) \<subseteq> typs body \<union> typs u"
  by (simp add: subst_bound_subst typs_subst)

lemma vars_subst_bound: "vars (subst_bound u body) \<subseteq> vars body \<union> vars u"
  by (simp add: subst_bound_subst vars_subst)

context prf_sig
begin

text \<open>
  A term whose variables are looked up without a type conflict (\<^const>\<open>vok\<close>) and whose types
  are consistent with the type environment, in an environment whose bindings are such terms:
\<close>

definition aok :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "aok env t \<longleftrightarrow> vok env (vars t) \<and> tconsT (tyenv env) t"

definition eok :: "env \<Rightarrow> bool" where
  "eok env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> aok env u \<and> tcons (tyenv env) U)"

text \<open>The results of normalization: the variables are unbound and the types normal.\<close>

definition nout :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "nout env t \<longleftrightarrow> aok env t \<and> tnormal (tyenv env) t \<and> (\<forall>v\<in>vars t. vt_lookup (tenv env) (fst v) = None)"

lemma vok_Un: "vok env X \<Longrightarrow> vok env Y \<Longrightarrow> vok env (X \<union> Y)"
  unfolding vok_def by blast

lemma aok_subst_bound: "aok env body \<Longrightarrow> aok env u \<Longrightarrow> aok env (subst_bound u body)"
proof -
  assume a: "aok env body" "aok env u"
  then have "vok env (vars body \<union> vars u)" by (intro vok_Un) (simp_all add: aok_def)
  then have "vok env (vars (subst_bound u body))" by (rule vok_mono) (rule vars_subst_bound)
  moreover have "tconsT (tyenv env) (subst_bound u body)"
    using a typs_subst_bound[of u body] by (auto simp: aok_def tconsT_def)
  ultimately show ?thesis by (simp add: aok_def)
qed

lemma eokD: "eok env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> aok env u \<and> tcons (tyenv env) U"
proof -
  assume e: "eok env" and lk: "vt_lookup (tenv env) x = Some (U, u)"
  from e have "\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> aok env u \<and> tcons (tyenv env) U"
    unfolding eok_def by (rule spec)
  with lk show ?thesis by blast
qed

lemma nout_unb: "nout env t \<Longrightarrow> unb env t"
  by (fastforce simp: nout_def unb_def tnormal_def ttvars_def)

lemma tcons_tnorm: "tacyc \<theta> \<Longrightarrow> tcons \<theta> (tnorm \<theta> T)"
  using tnorm_unbound[of \<theta>] by (fastforce simp: tcons_def)

lemma nout_Var:
  assumes "tacyc (tyenv env)" "vt_lookup (tenv env) x = None"
  shows "nout env (Var x (tnorm (tyenv env) T))"
  using assms tnorm_unbound[OF assms(1)] tcons_tnorm[OF assms(1)]
  by (fastforce simp: nout_def aok_def vok_def tconsT_def tnormal_def)

lemma nout_typ:
  assumes "tacyc (tyenv env)"
  shows "nout env (Const a (tnorm (tyenv env) T))" "nout env (Free a (tnorm (tyenv env) T))"
  using tnorm_unbound[OF assms] tcons_tnorm[OF assms]
  by (fastforce simp: nout_def aok_def vok_def tconsT_def tnormal_def)+

lemma lookup_aok:
  assumes ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)" and e: "eok env"
    and v: "(x, T) \<in> vars t" "aok env t"
  shows "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
proof (cases "vt_lookup (tenv env) x")
  case (Some b)
  obtain U u where b: "b = (U, u)" by force
  have "tcons (tyenv env) U" using eokD[OF e] Some b by blast
  moreover have "tcons (tyenv env) T" "tnorm (tyenv env) T = tnorm (tyenv env) U"
    using v Some b by (auto simp: aok_def vok_def)
  ultimately show ?thesis using Some b by (simp add: lookup_def unified_ok[OF ac tc])
qed (simp add: lookup_def)

lemma norm_term2_aok:
  assumes "norm_term2 env t = Some r"
  shows "tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow> eok env \<Longrightarrow> aok env t \<Longrightarrow>
    \<exists>t'. r = Ok t' \<and> nout env t'"
  using assms
proof (induction env t r rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  let ?\<theta> = "tyenv env"
  note h = "1.hyps" and ac = "1.prems"(1) and tc = "1.prems"(2) and ee = "1.prems"(3) and at = "1.prems"(4)
  have IH: "\<exists>t'. r' = Ok t' \<and> nout env t'" if "nt env u = Some r'" "aok env u" for u r'
    using "1.IH"[OF that(1) ac tc ee that(2)] .
  have nT: "norm_type_aux ?\<theta> T = return (tnorm ?\<theta> T)" if "tcons ?\<theta> T" for T
    by (rule norm_type_aux_ok[OF ac tc that])
  have redex: "\<exists>t'. r = Ok t' \<and> nout env t'"
    if hs: "nt env (subst_bound u body) = Some r" and a: "aok env body" "aok env u" for body u
    using IH[OF hs aok_subst_bound[OF a]] .
  show ?case
  proof (cases t)
    case (Const a T)
    with at have "tcons ?\<theta> T" by (simp add: aok_def tconsT_def)
    with h Const nT nout_typ[OF ac] show ?thesis by (auto simp: return_def bindM_def)
  next
    case (Free a T)
    with at have "tcons ?\<theta> T" by (simp add: aok_def tconsT_def)
    with h Free nT nout_typ[OF ac] show ?thesis by (auto simp: return_def bindM_def)
  next
    case (Var x T)
    have lk: "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
      by (rule lookup_aok[OF ac tc ee _ at]) (simp add: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      have "tcons ?\<theta> T" using at Var by (simp add: aok_def vok_def)
      with h Var lk None nT nout_Var[OF ac None] show ?thesis by (auto simp: return_def bindM_def)
    next
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have "nt env u = Some r" using h Var lk Some b by (simp add: return_def bindM_def)
      moreover have "aok env u" using eokD[OF ee] Some b by blast
      ultimately show ?thesis by (rule IH)
    qed
  next
    case (Bound i)
    with h show ?thesis by (auto simp: return_def nout_def aok_def vok_def tconsT_def tnormal_def)
  next
    case (Abs a T body)
    with at have cT: "tcons ?\<theta> T" and ab: "aok env body" by (auto simp: aok_def tconsT_def vok_def)
    from h Abs nT[OF cT] obtain rb where rb: "nt env body = Some rb"
      and r: "r = (case rb of Ok body' \<Rightarrow> Ok (Abs a (tnorm ?\<theta> T) body') | Err e \<Rightarrow> Err e)"
      by (auto simp: bindM_def return_def split: option.splits res.splits)
    from IH[OF rb ab] obtain body' where "rb = Ok body'" "nout env body'" by blast
    with r tnorm_unbound[OF ac] tcons_tnorm[OF ac] show ?thesis
      by (fastforce simp: nout_def aok_def vok_def tconsT_def tnormal_def)
  next
    case (App f u)
    have af: "aok env f" "aok env u" using at App by (auto simp: aok_def tconsT_def vok_def)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt env (subst_bound u body) = Some r" using h App f by simp
      moreover have "aok env body" using af(1) f by (auto simp: aok_def tconsT_def vok_def)
      ultimately show ?thesis using redex af(2) by blast
    next
      case False
      with h App obtain rf where hf: "nt env f = Some rf"
        and rest: "(case rf of Ok nf \<Rightarrow> (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) | Err e \<Rightarrow> Some (Err e)) = Some r"
        by (cases f) (auto simp: bindM_def split: option.splits)
      from IH[OF hf af(1)] obtain nf where nf: "rf = Ok nf" "nout env nf" by blast
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have "nt env (subst_bound u body) = Some r" using rest nf(1) nfb by simp
        moreover have "aok env body" using nf(2) nfb by (auto simp: nout_def aok_def tconsT_def vok_def)
        ultimately show ?thesis using redex af(2) by blast
      next
        case False
        with rest nf(1) obtain ru where hu: "nt env u = Some ru"
          and r: "r = (case ru of Ok nu \<Rightarrow> Ok (nf $ nu) | Err e \<Rightarrow> Err e)"
          by (cases nf) (auto simp: bindM_def return_def split: option.splits res.splits)
        from IH[OF hu af(2)] obtain nu where "ru = Ok nu" "nout env nu" by blast
        with r nf show ?thesis by (auto simp: nout_def aok_def tconsT_def vok_def tnormal_def)
      qed
    qed
  qed
qed

lemma norm_term1_aok:
  assumes "norm_term1 te t = Some r"
  shows "vt_is_empty (tyenv env) \<Longrightarrow> te = tenv env \<Longrightarrow> eok env \<Longrightarrow> aok env t \<Longrightarrow>
    \<exists>t'. r = Ok t' \<and> nout env t'"
  using assms
proof (induction te t r rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps" and em = "1.prems"(1) and te = "1.prems"(2) and ee = "1.prems"(3) and at = "1.prems"(4)
  have IH: "\<exists>t'. r' = Ok t' \<and> nout env t'" if "nt te u = Some r'" "aok env u" for u r'
    using "1.IH"[OF that(1) em te ee that(2)] .
  have nl: "vt_lookup (tyenv env) v = None" for v using em by (rule vt_is_empty_lookup)
  have tn: "tnorm (tyenv env) T = T" for T using em by (rule tnorm_empty)
  have redex: "\<exists>t'. r = Ok t' \<and> nout env t'"
    if hs: "nt te (subst_bound u body) = Some r" and a: "aok env body" "aok env u" for body u
    using IH[OF hs aok_subst_bound[OF a]] .
  show ?case
  proof (cases t)
    case (Var x T)
    show ?thesis
    proof (cases "vt_lookup (tenv env) x")
      case None
      with h Var te show ?thesis
        using at by (auto simp: lookup1_def return_def bindM_def nout_def aok_def vok_def tconsT_def tnormal_def nl)
    next
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have "T = U" using at Var Some b tn by (auto simp: aok_def vok_def)
      then have "nt te u = Some r" using h Var te Some b by (simp add: lookup1_def return_def bindM_def)
      moreover have "aok env u" using eokD[OF ee] Some b by blast
      ultimately show ?thesis by (rule IH)
    qed
  next
    case (Abs a T body)
    with at have ab: "aok env body" by (auto simp: aok_def tconsT_def vok_def)
    from h Abs obtain rb where rb: "nt te body = Some rb"
      and r: "r = (case rb of Ok body' \<Rightarrow> Ok (Abs a T body') | Err e \<Rightarrow> Err e)"
      by (auto simp: bindM_def return_def split: option.splits res.splits)
    from IH[OF rb ab] obtain body' where "rb = Ok body'" "nout env body'" by blast
    with r at Abs show ?thesis by (auto simp: nout_def aok_def vok_def tconsT_def tnormal_def nl)
  next
    case (App f u)
    have af: "aok env f" "aok env u" using at App by (auto simp: aok_def tconsT_def vok_def)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      have "nt te (subst_bound u body) = Some r" using h App f by simp
      moreover have "aok env body" using af(1) f by (auto simp: aok_def tconsT_def vok_def)
      ultimately show ?thesis using redex af(2) by blast
    next
      case False
      with h App obtain rf where hf: "nt te f = Some rf"
        and rest: "(case rf of Ok nf \<Rightarrow> (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) | Err e \<Rightarrow> Some (Err e)) = Some r"
        by (cases f) (auto simp: bindM_def split: option.splits)
      from IH[OF hf af(1)] obtain nf where nf: "rf = Ok nf" "nout env nf" by blast
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nfb: "nf = Abs b U0 body" by (cases nf) auto
        have "nt te (subst_bound u body) = Some r" using rest nf(1) nfb by simp
        moreover have "aok env body" using nf(2) nfb by (auto simp: nout_def aok_def tconsT_def vok_def)
        ultimately show ?thesis using redex af(2) by blast
      next
        case False
        with rest nf(1) obtain ru where hu: "nt te u = Some ru"
          and r: "r = (case ru of Ok nu \<Rightarrow> Ok (nf $ nu) | Err e \<Rightarrow> Err e)"
          by (cases nf) (auto simp: bindM_def return_def split: option.splits res.splits)
        from IH[OF hu af(2)] obtain nu where "ru = Ok nu" "nout env nu" by blast
        with r nf show ?thesis by (auto simp: nout_def aok_def tconsT_def vok_def tnormal_def)
      qed
    qed
  qed (use h at in \<open>auto simp: return_def nout_def aok_def vok_def tconsT_def tnormal_def nl\<close>)
qed

theorem norm_term_aok:
  assumes "norm_term env t = Some r" "tacyc (tyenv env)" "tcons_env (tyenv env)" "eok env" "aok env t"
  shows "\<exists>t'. r = Ok t' \<and> nout env t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case id
    then have "vt_is_empty (tyenv env)" "vt_is_empty (tenv env)" by (simp_all add: env_is_empty_def)
    with id assms(1,5) show ?thesis
      by (auto simp: norm_term_def nout_def tnormal_def vt_is_empty_lookup return_def)
  next
    case n1
    with assms(1) have "norm_term1 (tenv env) t = Some r" by (simp add: norm_term_def)
    from norm_term1_aok[OF this n1(2) HOL.refl assms(4,5)] show ?thesis .
  next
    case n2
    with assms(1) have "norm_term2 env t = Some r" by (simp add: norm_term_def)
    from norm_term2_aok[OF this assms(2-5)] show ?thesis .
  qed
qed

end


subsection \<open>Equivalence of instances\<close>

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

lemma ueq_beta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<approx> t"
proof (induction rule: rtranclp_induct)
  case (step y z)
  then have "sup beta eta (erase y) (erase z)" by (simp add: erase_beta)
  from equivclp_into_equivclp[OF step(3)] this show ?case by blast
qed simp

lemma vars_remove_types [simp]: "vars (remove_types t) = vars t"
  by (induction t) simp_all

lemma loose_bvar_remove_types [simp]: "loose_bvar (remove_types t) k = loose_bvar t k"
  by (induction t arbitrary: k) simp_all

lemma typs_remove_types: "typs (remove_types t) \<subseteq> typs t \<union> {dummyT}"
  by (induction t) auto

context prf_sig
begin

lemma remove_types_env_simps [simp]:
  "tyenv (remove_types_env env) = tyenv env" "maxidx (remove_types_env env) = maxidx env"
  "vt_lookup (tenv (remove_types_env env)) x = map_option (\<lambda>(T, t). (T, remove_types t)) (vt_lookup (tenv env) x)"
  by (simp_all add: remove_types_env_def)

lemma dep_remove_types_env [simp]: "dep (remove_types_env env) = dep env"
  by (auto simp: dep_def split: option.splits) force+

lemma acyc_remove_types_env [simp]: "acyc (remove_types_env env) = acyc env"
  by (simp add: acyc_def)

lemma closed_env_remove_types_env: "closed_env env \<Longrightarrow> closed_env (remove_types_env env)"
  by (auto simp: closed_env_def closed_def)

lemma evars_remove_types_env [simp]: "evars (remove_types_env env) = evars env"
  by (auto simp: evars_def bnds_def) (force, force)

lemma vok_remove_types_env [simp]: "vok (remove_types_env env) X = vok env X"
  by (auto simp: vok_def)

lemma erase_ap_remove_types: "erase (ap \<rho> \<sigma> (remove_types t)) = erase (ap \<rho> \<sigma> t)"
  by (induction t) simp_all

lemma eok_remove_types_env: "eok env \<Longrightarrow> eok (remove_types_env env)"
proof -
  assume e: "eok env"
  have "tconsT (tyenv env) (remove_types u)" if "tconsT (tyenv env) u" for u
    using that typs_remove_types[of u] by (auto simp: tconsT_def dummyT_def)
  with e show ?thesis by (fastforce simp: eok_def aok_def)
qed

text \<open>
  An untyped variant of \<open>ap_unf\<close>: a solution of an environment, up to the erased equivalence
  of annotations, gives the meaning of the unfolding of any term whose variables agree in
  their types with the bindings.
\<close>

lemma ap_unf_ueq:
  assumes ac: "acyc E"
    and sl: "\<And>x U u. vt_lookup (tenv E) x = Some (U, u) \<Longrightarrow> \<sigma> x (tsubst \<rho> U) \<approx> ap \<rho> \<sigma> u"
    and vc: "\<And>x T U u. (x, T) \<in> vars t \<union> evars E \<Longrightarrow> vt_lookup (tenv E) x = Some (U, u) \<Longrightarrow>
      tsubst \<rho> T = tsubst \<rho> U"
  shows "ap \<rho> \<sigma> (unf E t) \<approx> ap \<rho> \<sigma> t"
proof -
  have var: "ap \<rho> \<sigma> (unf E (Var x T)) \<approx> ap \<rho> \<sigma> (Var x T)" if "(x, T) \<in> vars t \<union> evars E" for x T
    using that
  proof (induction x arbitrary: T rule: dep_induct[OF ac])
    case (1 x)
    show ?case
    proof (cases "vt_lookup (tenv E) x")
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      note lk = Some[unfolded b]
      have vu: "vars u \<subseteq> evars E" using evarsI2[OF lk] by blast
      have "ap \<rho> \<sigma> (unf E s) \<approx> ap \<rho> \<sigma> s" if "vars s \<subseteq> vars u" for s
        using that
      proof (induction s)
        case (Var y T')
        have yu: "(y, T') \<in> vars u" using Var.prems by simp
        have "(y, x) \<in> dep E" using depI[OF lk yu] .
        with "1.IH"[of y T'] vu yu show ?case by blast
      next
        case (Abs a T0 b)
        have "ap \<rho> \<sigma> (unf E b) \<approx> ap \<rho> \<sigma> b" by (rule Abs.IH) (use Abs.prems in simp)
        then show ?case by (simp only: unf_simps ap_simps) (rule ueq_Abs)
      next
        case (App f g)
        have "ap \<rho> \<sigma> (unf E f) \<approx> ap \<rho> \<sigma> f" "ap \<rho> \<sigma> (unf E g) \<approx> ap \<rho> \<sigma> g"
          by (rule App.IH(1), use App.prems in simp) (rule App.IH(2), use App.prems in simp)
        then show ?case by (simp only: unf_simps ap_simps) (rule ueq_App)
      qed simp_all
      then have "ap \<rho> \<sigma> (unf E u) \<approx> ap \<rho> \<sigma> u" by blast
      moreover have "\<sigma> x (tsubst \<rho> U) \<approx> ap \<rho> \<sigma> u" by (rule sl[OF lk])
      moreover have "tsubst \<rho> T = tsubst \<rho> U" by (rule vc[OF "1.prems" lk])
      ultimately have "ap \<rho> \<sigma> (unf E u) \<approx> \<sigma> x (tsubst \<rho> T)"
        by (metis equivclp_sym equivclp_trans)
      moreover have "unf E (Var x T) = unf E u" using lk by (simp add: unf_Var[OF ac])
      moreover have "ap \<rho> \<sigma> (Var x T) = \<sigma> x (tsubst \<rho> T)" by simp
      ultimately show ?thesis by (simp only:)
    qed (simp add: unf_Var[OF ac])
  qed
  have "ap \<rho> \<sigma> (unf E s) \<approx> ap \<rho> \<sigma> s" if "vars s \<subseteq> vars t" for s
    using that
  proof (induction s)
    case (Var y T')
    then have "(y, T') \<in> vars t \<union> evars E" by simp
    from var[OF this] show ?case .
  next
    case (Abs a T0 b)
    have "ap \<rho> \<sigma> (unf E b) \<approx> ap \<rho> \<sigma> b" by (rule Abs.IH) (use Abs.prems in simp)
    then show ?case by (simp only: unf_simps ap_simps) (rule ueq_Abs)
  next
    case (App f g)
    have "ap \<rho> \<sigma> (unf E f) \<approx> ap \<rho> \<sigma> f" "ap \<rho> \<sigma> (unf E g) \<approx> ap \<rho> \<sigma> g"
          by (rule App.IH(1), use App.prems in simp) (rule App.IH(2), use App.prems in simp)
    then show ?case by (simp only: unf_simps ap_simps) (rule ueq_App)
  qed simp_all
  then show ?thesis by blast
qed

text \<open>
  A normalized annotation and the original one are equivalent at an instance and its
  extension through a solution of the environment:
\<close>

theorem norm_term_ann:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and ac: "acyc env" "closed_env env"
    and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)" and ee: "eok env" and at: "aok env t"
    and nt: "norm_term (remove_types_env env) t = Some r"
  shows "\<exists>t'. r = Ok t' \<and> nout env t' \<and> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
proof -
  let ?E = "remove_types_env env" and ?\<theta> = "tyenv env"
  note i = iextD[OF ie]
  have acE: "acyc ?E" "closed_env ?E" "tacyc (tyenv ?E)" using ac tac closed_env_remove_types_env by simp_all
  have atE: "aok ?E t" using at by (simp add: aok_def)
  from norm_term_aok[OF nt _ _ eok_remove_types_env[OF ee] atE] tac
  obtain t' where r: "r = Ok t'" and no: "nout ?E t'" by auto
  have nt': "nout env t'" using no by (auto simp: nout_def aok_def tconsT_def tnormal_def)
  have red: "env_apply ?E t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" by (rule norm_term_env_apply(1)[OF nt[unfolded r] acE])
  text \<open>The bindings of the type-erased environment are solved up to erasure.\<close>
  have sl: "\<sigma>' x (tsubst \<rho>' U) \<approx> ap \<rho>' \<sigma>' u" if "vt_lookup (tenv ?E) x = Some (U, u)" for x U u
  proof -
    from that have "\<exists>u0. vt_lookup (tenv env) x = Some (U, u0) \<and> u = remove_types u0"
      by (cases "vt_lookup (tenv env) x") auto
    then obtain u0 where lk: "vt_lookup (tenv env) x = Some (U, u0)" and u: "u = remove_types u0" by blast
    have "\<sigma>' x (tsubst \<rho>' U) \<approx> ap \<rho>' \<sigma>' u0" by (rule conv_ueq[OF solutionD(4)[OF i(3) lk]])
    then show ?thesis by (simp add: u erase_ap_remove_types)
  qed
  have vc: "tsubst \<rho>' T = tsubst \<rho>' U"
    if "(x, T) \<in> vars t \<union> evars ?E" "vt_lookup (tenv ?E) x = Some (U, u)" for x T U u
  proof -
    from that(2) have "\<exists>u0. vt_lookup (tenv env) x = Some (U, u0)"
      by (cases "vt_lookup (tenv env) x") auto
    then obtain u0 where lk: "vt_lookup (tenv env) x = Some (U, u0)" by blast
    have vT: "tcons ?\<theta> T \<and> (\<forall>U' u'. vt_lookup (tenv env) x = Some (U', u') \<longrightarrow> tnorm ?\<theta> T = tnorm ?\<theta> U')"
    proof (cases "(x, T) \<in> vars t")
      case True
      with at show ?thesis by (auto simp: aok_def vok_def)
    next
      case False
      with that(1) have "(x, T) \<in> evars env" by simp
      then obtain y V v where yl: "vt_lookup (tenv env) y = Some (V, v)" and xT: "(x, T) = (y, V) \<or> (x, T) \<in> vars v"
        by (auto simp: evars_def bnds_def)
      note ey = eokD[OF ee yl]
      from xT show ?thesis
      proof
        assume "(x, T) = (y, V)"
        then have "x = y" "T = V" by simp_all
        with ey yl show ?thesis by simp
      next
        assume "(x, T) \<in> vars v"
        with ey show ?thesis by (auto simp: aok_def vok_def)
      qed
    qed
    have cU: "tcons ?\<theta> U" using eokD[OF ee lk] by blast
    from vT lk have "tnorm ?\<theta> T = tnorm ?\<theta> U" by blast
    then show ?thesis using tsubst_tnorm[OF tac i(5)] vT cU by metis
  qed
  have "ap \<rho>' \<sigma>' (unf ?E t) \<approx> ap \<rho>' \<sigma>' t" by (rule ap_unf_ueq[OF acE(1) sl vc]) auto
  moreover have "ap \<rho>' \<sigma>' (env_apply ?E t) = ap \<rho>' \<sigma>' (unf ?E t)"
  proof -
    have "inst \<rho>' (inst (tnorm_inst ?\<theta>) (unf ?E t)) = inst \<rho>' (unf ?E t)"
      unfolding inst_inst
    proof (rule inst_cong)
      fix U assume U: "U \<in> typs (unf ?E t)"
      have "tcons ?\<theta> U"
      proof (cases "U \<in> typs t")
        case True
        with at show ?thesis by (simp add: aok_def tconsT_def)
      next
        case False
        with U typs_unf[OF acE(1), of t] obtain x V u where lk: "vt_lookup (tenv ?E) x = Some (V, u)" "U \<in> typs u"
          by blast
        from eokD[OF eok_remove_types_env[OF ee] lk(1)] lk(2) show ?thesis
          by (simp add: aok_def tconsT_def)
      qed
      then show "tsubst (\<lambda>v S. tsubst \<rho>' (tnorm_inst ?\<theta> v S)) U = tsubst \<rho>' U"
        using tsubst_tnorm[OF tac i(5)] by (simp flip: tsubst_tsubst)
    qed
    then show ?thesis by (simp add: env_apply_def ap_def)
  qed
  moreover have "ap \<rho>' \<sigma>' (env_apply ?E t) \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho>' \<sigma>' t'"
    by (rule beta_reds_ap[OF red gsubstD(1)[OF i(2)]])
  moreover have "ap \<rho>' \<sigma>' t' = ap \<rho> \<sigma> t'" by (rule iext_unb[OF ie nout_unb[OF nt']])
  ultimately have "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t"
    by (metis ueq_beta_reds ueq_sym ueq_trans)
  with r nt' show ?thesis by blast
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


text \<open>A computation that does not print warnings or raise exceptions:\<close>

definition retN :: "'a P \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "retN m Q \<longleftrightarrow> m = None \<or> (\<exists>x. m = returnP x \<and> Q x)"

lemma retN_returnP: "Q x \<Longrightarrow> retN (returnP x) Q"
  by (auto simp: retN_def)

lemma retN_bindP: "retN m Q \<Longrightarrow> (\<And>x. Q x \<Longrightarrow> retN (f x) R) \<Longrightarrow> retN (bindP m f) R"
  unfolding retN_def by (elim disjE exE conjE) simp_all

lemma retN_map_optionP:
  "(\<And>y. x = Some y \<Longrightarrow> retN (f y) (Q y)) \<Longrightarrow>
    retN (map_optionP f x) (\<lambda>z. case x of None \<Rightarrow> z = None | Some y \<Rightarrow> \<exists>z'. z = Some z' \<and> Q y z')"
  by (cases x) (auto simp: map_optionP_def retN_def)

context prf_sig
begin

definition prf_nok :: "env \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_nok env p \<longleftrightarrow> (\<forall>t\<in>prf_terms p. aok env t) \<and> (\<forall>T\<in>prf_typs p. tcons (tyenv env) T)"

lemma norm_term_P_aok:
  assumes ac: "acyc env" "closed_env env" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and ee: "eok env" and at: "aok env t"
  shows "retN (norm_term_P (remove_types_env env) t)
    (\<lambda>t'. nout env t' \<and> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>'. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t))"
proof (cases "norm_term (remove_types_env env) t")
  case None
  then show ?thesis by (simp add: norm_term_P_def retN_def liftMP_def)
next
  case (Some r)
  from norm_term_aok[OF Some _ _ eok_remove_types_env[OF ee]] tac at
  obtain t' where r: "r = Ok t'" "nout (remove_types_env env) t'" by (auto simp: aok_def)
  have "nout env t' \<and> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>'. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t)"
  proof (intro conjI allI impI)
    show "nout env t'" using r(2) by (auto simp: nout_def aok_def tconsT_def tnormal_def)
    fix \<rho> \<sigma> \<rho>' \<sigma>' assume ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'"
    from norm_term_ann[OF ie ac tac ee at Some] r(1) show "ap \<rho> \<sigma> t' \<approx> ap \<rho>' \<sigma>' t" by auto
  qed
  with Some r(1) show ?thesis by (simp add: norm_term_P_def liftMP_def retN_def returnP_def handleP_def)
qed

lemma norm_type_P_tcons:
  "tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tcons \<theta> T \<Longrightarrow> norm_type_P \<theta> T = returnP (tnorm \<theta> T)"
  by (simp add: norm_type_P_def norm_type_ok)

lemma norm_types_P_tcons:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "\<forall>T\<in>set Ts. tcons \<theta> T"
  shows "norm_types_P \<theta> Ts = returnP (map (tnorm \<theta>) Ts)"
proof (cases "vt_is_empty \<theta>")
  case True
  then show ?thesis by (simp add: norm_types_P_def tnorm_empty map_idI)
next
  case False
  have "mapM (norm_type_aux \<theta>) Ts = return (map (tnorm \<theta>) Ts)"
    using assms(3) norm_type_aux_ok[OF assms(1,2)] by (induction Ts) auto
  with False show ?thesis by (simp add: norm_types_P_def)
qed

text \<open>
  The normalized proof is, at every instance, equivalent to the original proof at the extension
  of the instance through a solution of the environment:
\<close>

definition nrel :: "env \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> bool" where
  "nrel env q q' \<longleftrightarrow> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>'. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> prf_aeq (prf_ap \<rho>' \<sigma>' q) (prf_ap \<rho> \<sigma> q'))"

lemma iext_tnorm:
  assumes ie: "iext env \<rho> \<sigma> \<rho>' \<sigma>'" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and T: "tcons (tyenv env) T"
  shows "tsubst \<rho> (tnorm (tyenv env) T) = tsubst \<rho>' T"
proof -
  have "tsubst \<rho>' (tnorm (tyenv env) T) = tsubst \<rho> (tnorm (tyenv env) T)"
    by (rule tsubst_cong) (use iextD(6)[OF ie] tnorm_unbound[OF tac(1)] in force)
  with tsubst_tnorm[OF tac iextD(5)[OF ie] T] show ?thesis by simp
qed

theorem norm_proof_aok:
  assumes ac: "acyc env" "closed_env env" and tac: "tacyc (tyenv env)" "tcons_env (tyenv env)"
    and ee: "eok env"
  shows "prf_nok env q \<Longrightarrow> retN (norm_proof (remove_types_env env) q) (nrel env q)"
proof (induction q)
  let ?E = "remove_types_env env" and ?\<theta> = "tyenv env"
  have tyP: "map_optionP (norm_type_P (tyenv ?E)) T = returnP (map_option (tnorm ?\<theta>) T)"
    if "\<forall>U\<in>set_option T. tcons ?\<theta> U" for T
    using that by (cases T) (simp_all add: map_optionP_def norm_type_P_tcons[OF tac])
  have tysP: "map_optionP (norm_types_P (tyenv ?E)) Ts = returnP (map_option (map (tnorm ?\<theta>)) Ts)"
    if "case Ts of None \<Rightarrow> True | Some Us \<Rightarrow> \<forall>U\<in>set Us. tcons ?\<theta> U" for Ts
    using that by (cases Ts) (simp_all add: map_optionP_def norm_types_P_tcons[OF tac])
  let ?Q = "\<lambda>u u'. nout env u' \<and> (\<forall>\<rho> \<sigma> \<rho>' \<sigma>'. iext env \<rho> \<sigma> \<rho>' \<sigma>' \<longrightarrow> ap \<rho> \<sigma> u' \<approx> ap \<rho>' \<sigma>' u)"
  have tmP: "retN (map_optionP (norm_term_P ?E) t)
      (\<lambda>t'. (case t of None \<Rightarrow> t' = None | Some u \<Rightarrow> \<exists>u'. t' = Some u' \<and> ?Q u u'))"
    if "\<forall>u\<in>set_option t. aok env u" for t
    by (rule retN_map_optionP) (use that norm_term_P_aok[OF ac tac ee] in auto)
  have aeq: "ann_eq (map_option (ap \<rho>' \<sigma>') t) (map_option (ap \<rho> \<sigma>) t')"
    if "case t of None \<Rightarrow> t' = None | Some u \<Rightarrow> \<exists>u'. t' = Some u' \<and> ?Q u u'"
      "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for t t' \<rho> \<sigma> \<rho>' \<sigma>'
  proof (cases t)
    case None
    with that(1) show ?thesis by (simp add: ann_eq_def)
  next
    case (Some a)
    with that(1) obtain u' where t': "t' = Some u'" and q: "?Q a u'" by auto
    from q that(2) have "ap \<rho> \<sigma> u' \<approx> ap \<rho>' \<sigma>' a" by blast
    then have "ap \<rho>' \<sigma>' a \<approx> ap \<rho> \<sigma> u'" by (rule equivclp_sym)
    then show ?thesis using Some t' unfolding ann_eq_def by simp
  qed
  have tyeq: "map_option (tsubst \<rho>) (map_option (tnorm ?\<theta>) T) = map_option (tsubst \<rho>') T"
    if "\<forall>U\<in>set_option T. tcons ?\<theta> U" "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for T \<rho> \<sigma> \<rho>' \<sigma>'
    using that iext_tnorm[OF _ tac] by (cases T) auto
  have tyseq: "map_option (map (tsubst \<rho>)) (map_option (map (tnorm ?\<theta>)) Ts) = map_option (map (tsubst \<rho>')) Ts"
    if "case Ts of None \<Rightarrow> True | Some Us \<Rightarrow> \<forall>U\<in>set Us. tcons ?\<theta> U" "iext env \<rho> \<sigma> \<rho>' \<sigma>'" for Ts \<rho> \<sigma> \<rho>' \<sigma>'
    using that iext_tnorm[OF _ tac] by (cases Ts) auto
  {
    case (Abst a T q)
    have nq: "prf_nok env q" and cT: "\<forall>U\<in>set_option T. tcons ?\<theta> U" using Abst.prems by (auto simp: prf_nok_def)
    show ?case unfolding norm_proof.simps tyP[OF cT] bindP_simps
    proof (rule retN_bindP[OF Abst.IH[OF nq]], rule retN_returnP)
      fix q' assume "nrel env q q'"
      then show "nrel env (Abst a T q) (Abst a (map_option (tnorm ?\<theta>) T) q')"
        using tyeq[OF cT] by (auto simp: nrel_def prf_ap_def intro: prf_aeq.Abst)
    qed
  next
    case (AbsP a t q)
    have nq: "prf_nok env q" and ct: "\<forall>u\<in>set_option t. aok env u"
      using AbsP.prems by (auto simp: prf_nok_def)
    show ?case unfolding norm_proof.simps
    proof (rule retN_bindP[OF tmP[OF ct]], rule retN_bindP[OF AbsP.IH[OF nq]], rule retN_returnP)
      fix t' q' assume "nrel env q q'" and "case t of None \<Rightarrow> t' = None | Some u \<Rightarrow> \<exists>u'. t' = Some u' \<and> ?Q u u'"
      then show "nrel env (AbsP a t q) (AbsP a t' q')"
        using aeq by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.AbsP)
    qed
  next
    case (PAppt q t)
    have nq: "prf_nok env q" and ct: "\<forall>u\<in>set_option t. aok env u"
      using PAppt.prems by (auto simp: prf_nok_def)
    show ?case unfolding norm_proof.simps
    proof (rule retN_bindP[OF PAppt.IH[OF nq]], rule retN_bindP[OF tmP[OF ct]], rule retN_returnP)
      fix t' q' assume "nrel env q q'" and "case t of None \<Rightarrow> t' = None | Some u \<Rightarrow> \<exists>u'. t' = Some u' \<and> ?Q u u'"
      then show "nrel env (PAppt q t) (PAppt q' t')"
        using aeq by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.PAppt)
    qed
  next
    case (PAppp q1 q2)
    have nq: "prf_nok env q1" "prf_nok env q2" using PAppp.prems by (auto simp: prf_nok_def)
    show ?case unfolding norm_proof.simps
    proof (rule retN_bindP[OF PAppp.IH(1)[OF nq(1)]], rule retN_bindP[OF PAppp.IH(2)[OF nq(2)]], rule retN_returnP)
      fix q1' q2' assume "nrel env q1 q1'" "nrel env q2 q2'"
      then show "nrel env (PAppp q1 q2) (PAppp q1' q2')"
        by (auto simp: nrel_def prf_ap_def intro!: prf_aeq.PAppp)
    qed
  next
    case (PAxm a A Ts)
    have cT: "case Ts of None \<Rightarrow> True | Some Us \<Rightarrow> \<forall>U\<in>set Us. tcons ?\<theta> U"
      using PAxm.prems by (auto simp: prf_nok_def split: option.splits)
    show ?case unfolding norm_proof.simps tysP[OF cT] bindP_simps
      by (rule retN_returnP) (use tyseq[OF cT] in \<open>auto simp: nrel_def prf_ap_def intro: prf_aeq.refl\<close>)
  next
    case (Oracle a A Ts)
    have cT: "case Ts of None \<Rightarrow> True | Some Us \<Rightarrow> \<forall>U\<in>set Us. tcons ?\<theta> U"
      using Oracle.prems by (auto simp: prf_nok_def split: option.splits)
    show ?case unfolding norm_proof.simps tysP[OF cT] bindP_simps
      by (rule retN_returnP) (use tyseq[OF cT] in \<open>auto simp: nrel_def prf_ap_def intro: prf_aeq.refl\<close>)
  next
    case (PThm hb)
    obtain h b where hb: "hb = (h, b)" by (cases hb)
    have cT: "case hd_types h of None \<Rightarrow> True | Some Us \<Rightarrow> \<forall>U\<in>set Us. tcons ?\<theta> U"
      using PThm.prems by (auto simp: prf_nok_def hb split: option.splits)
    show ?case unfolding hb norm_proof.simps tysP[OF cT] bindP_simps
      by (rule retN_returnP) (use tyseq[OF cT] in \<open>auto simp: nrel_def prf_ap_def intro: prf_aeq.refl\<close>)
  next
    case (PClass T c)
    have cT: "tcons ?\<theta> T" using PClass.prems by (simp add: prf_nok_def)
    show ?case unfolding norm_proof.simps remove_types_env_simps norm_type_P_tcons[OF tac cT] bindP_simps
      by (rule retN_returnP) (use cT iext_tnorm[OF _ tac cT] in \<open>auto simp: nrel_def prf_ap_def intro: prf_aeq.refl\<close>)
  }
qed (auto intro!: retN_returnP simp: nrel_def prf_ap_def intro: prf_aeq.refl)

end

end
