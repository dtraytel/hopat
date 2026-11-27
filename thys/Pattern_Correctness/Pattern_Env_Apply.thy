section \<open>Applying an Environment\<close>

text \<open>
  The most general solution of a type environment (\<open>tsol0\<close>), the application of an
  environment to a term (\<open>env_apply\<close>) as computed by \<open>norm_term\<close>, and the occurrence of a
  variable in a term modulo the environment (\<open>occt\<close>). The soundness of the rules uses them;
  the most general unifiers are in theory \<open>Pattern_Most_General\<close>.
\<close>

theory Pattern_Env_Apply
  imports Pattern_Invariant
begin

subsection \<open>Occurrences of unbound variables reachable through bindings\<close>

context pure_sig
begin

definition occt :: "env \<Rightarrow> indexname \<Rightarrow> pterm \<Rightarrow> bool" where
  "occt env F t \<longleftrightarrow> vt_lookup (tenv env) F = None \<and> (\<exists>y\<in>fst ` vars t. (F, y) \<in> (dep env)\<^sup>*)"

lemma occt_simps [simp]:
  "occt env F (s $ t) \<longleftrightarrow> occt env F s \<or> occt env F t" "occt env F (Abs a T t) \<longleftrightarrow> occt env F t"
  "occt env F (Bound i) \<longleftrightarrow> False" "occt env F (Const c T) \<longleftrightarrow> False" "occt env F (Free c T) \<longleftrightarrow> False"
  by (auto simp: occt_def)

lemma occt_Var_bound:
  assumes lk: "vt_lookup (tenv env) y = Some (U, u)"
  shows "occt env F (Var y T) \<longleftrightarrow> occt env F u"
proof
  assume "occt env F (Var y T)"
  then have F: "vt_lookup (tenv env) F = None" and Fy: "(F, y) \<in> (dep env)\<^sup>*" by (simp_all add: occt_def)
  from Fy show "occt env F u"
  proof (cases rule: rtranclE)
    case base
    with F lk show ?thesis by simp
  next
    case (step z)
    from step(2) obtain U' u' T' where "vt_lookup (tenv env) y = Some (U', u')" "(z, T') \<in> vars u'"
      by (rule depE)
    with lk have "(z, T') \<in> vars u" by simp
    then have "z \<in> fst ` vars u" by force
    with step(1) F show ?thesis unfolding occt_def by blast
  qed
next
  assume "occt env F u"
  then obtain z T' where F: "vt_lookup (tenv env) F = None" and z: "(z, T') \<in> vars u" "(F, z) \<in> (dep env)\<^sup>*"
    by (auto simp: occt_def)
  have "(z, y) \<in> dep env" by (rule depI[OF lk z(1)])
  with z(2) F show "occt env F (Var y T)" by (simp add: occt_def)
qed

lemma occt_Var_unbound: "vt_lookup (tenv env) y = None \<Longrightarrow> occt env F (Var y T) \<longleftrightarrow> F = y"
  by (auto simp: occt_def elim: rtranclE elim!: depE)

end

subsection \<open>The most general solution and the application of an environment\<close>

context pure_sig_gen
begin

text \<open>
  A sorted type environment has a well-sorted certified solution: it maps a bound variable of the
  sort of its binding to the normal form of the binding, and other variables to themselves.
\<close>

definition tsol0 :: "tyenv \<Rightarrow> tinst" where
  "tsol0 \<theta> v S = (case vt_lookup \<theta> v of
     Some (S', U) \<Rightarrow> if S = S' then tnorm \<theta> U else TVar v S
   | None \<Rightarrow> TVar v S)"

lemma tsubst_tsol0: "tacyc \<theta> \<Longrightarrow> tcons \<theta> T \<Longrightarrow> tsubst (tsol0 \<theta>) T = tnorm \<theta> T"
proof -
  assume ac: "tacyc \<theta>" and tc: "tcons \<theta> T"
  have "tsol0 \<theta> v S = tnorm \<theta> (TVar v S)" if "(v, S) \<in> tvars T" for v S
  proof (cases "vt_lookup \<theta> v")
    case (Some b)
    obtain S' U where b: "b = (S', U)" by force
    with Some tc that have "S' = S" unfolding tcons_def by blast
    with Some b show ?thesis by (simp add: tsol0_def tnorm_TVar[OF ac])
  qed (simp add: tsol0_def tnorm_TVar[OF ac])
  then show ?thesis unfolding tnorm_tsubst[of \<theta> T] by (rule tsubst_cong)
qed

lemma tsol0:
  assumes inv: "tinv ar n \<theta> A" and srt: "tsorted alg \<theta>" and sc: "scert alg \<theta>"
  shows "tsol \<theta> (tsol0 \<theta>)" "wsinst alg (tsol0 \<theta>)" "cert_inst (tsol0 \<theta>)"
proof -
  have ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" by (rule tinv_tacyc[OF inv], rule tinv_tcons_env[OF inv])
  show "tsol \<theta> (tsol0 \<theta>)"
    unfolding tsol_def using tsubst_tsol0[OF ac] tcons_envD[OF tc] by (simp add: tsol0_def)
  show "wsinst alg (tsol0 \<theta>)"
    unfolding wsinst_def
  proof (intro allI)
    fix v S
    have "bsorted alg \<theta> v" using srt by (cases v) (simp add: tsorted_def)
    then show "has_sort alg (tsol0 \<theta> v S) S"
      by (auto simp: tsol0_def bsorted_def simp del: has_sort.simps split: option.splits)
  qed
  have ci: "cert_inst (tnorm_inst \<theta>)"
    by (rule cert_inst_tnorm[OF ac]) (use inv tinv_wft sc in \<open>auto simp: scert_def\<close>)
  show "cert_inst (tsol0 \<theta>)"
    unfolding cert_inst_def
  proof (intro allI impI)
    fix v S assume S: "sort_ok alg S"
    have "tsol0 \<theta> v S = tnorm_inst \<theta> v S \<or> tsol0 \<theta> v S = TVar v S"
      by (auto simp: tsol0_def tnorm_TVar[OF ac] split: option.splits)
    then show "cert_typ alg ar (tsol0 \<theta> v S)"
      using ci[unfolded cert_inst_def, rule_format, OF S, of v] S by (auto simp: cert_typ_def)
  qed
qed

end

context pure_sig_gen
begin

text \<open>
  An acyclic environment stands for a substitution: its type environment for the instantiation
  \<^const>\<open>tnorm_inst\<close> of the type variables by the normal forms of their bindings, its term
  environment for the unfolding \<^const>\<open>unf\<close> of the bound variables. Applying the environment to
  a term is what \<open>Envir.norm_term\<close> computes, up to \<open>\<beta>\<close>-normalization (theorem
  \<open>norm_term_env_apply\<close>), and it is the most general solution of the environment
  (theorems \<open>env_apply_esol\<close> and \<open>ap_env_apply\<close> in theory \<open>Pattern_Most_General\<close>). The correctness
  proofs of unification work with arbitrary solutions \<open>(\<rho>, \<sigma>)\<close> of environments; their final
  results are restated with the application of the resulting environment.
\<close>

definition env_apply :: "env \<Rightarrow> pterm \<Rightarrow> pterm" where
  "env_apply env t = inst (tnorm_inst (tyenv env)) (unf env t)"

text \<open>Terms on which the environment acts as the identity:\<close>

definition env_normal :: "env \<Rightarrow> pterm \<Rightarrow> bool" where
  "env_normal env t \<longleftrightarrow> (\<forall>(x, T)\<in>vars t. vt_lookup (tenv env) x = None) \<and>
    (\<forall>U\<in>typs t. tnorm (tyenv env) U = U)"

lemma env_normal_simps [simp]:
  "env_normal env (Const c T) \<longleftrightarrow> tnorm (tyenv env) T = T"
  "env_normal env (Free a T) \<longleftrightarrow> tnorm (tyenv env) T = T"
  "env_normal env (Var x T) \<longleftrightarrow> vt_lookup (tenv env) x = None \<and> tnorm (tyenv env) T = T"
  "env_normal env (Bound i)"
  "env_normal env (Abs a T t) \<longleftrightarrow> tnorm (tyenv env) T = T \<and> env_normal env t"
  "env_normal env (s $ t) \<longleftrightarrow> env_normal env s \<and> env_normal env t"
  by (auto simp: env_normal_def)

lemma inst_TVar_id [simp]: "inst TVar t = t"
  by (induction t) simp_all

lemma unf_unbound: "(\<forall>(x, T)\<in>vars t. vt_lookup (tenv env) x = None) \<Longrightarrow> acyc env \<Longrightarrow> unf env t = t"
  by (induction t) (auto simp: unf_Var)

lemma inst_tnorm_inst_id: "(\<forall>U\<in>typs t. tnorm \<theta> U = U) \<Longrightarrow> inst (tnorm_inst \<theta>) t = t"
proof -
  assume "\<forall>U\<in>typs t. tnorm \<theta> U = U"
  then have "inst (tnorm_inst \<theta>) t = inst TVar t" by (intro inst_cong) simp
  then show ?thesis by simp
qed

lemma env_apply_normal: "env_normal env t \<Longrightarrow> acyc env \<Longrightarrow> env_apply env t = t"
  unfolding env_apply_def env_normal_def by (simp add: unf_unbound inst_tnorm_inst_id)

lemma env_apply_empty: "env_is_empty env \<Longrightarrow> env_apply env t = t"
proof -
  assume "env_is_empty env"
  then have em: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: env_is_empty_def)
  have "acyc env" using em(1) by (simp add: acyc_def dep_def vt_is_empty_lookup acyclic_def)
  moreover have "env_normal env t" using em by (simp add: env_normal_def vt_is_empty_lookup tnorm_empty)
  ultimately show ?thesis by (simp add: env_apply_normal)
qed

subsection \<open>Normalization\<close>

text \<open>The results of normalization are \<open>\<beta>\<close>-reducts of the unfolding, up to the types:\<close>

lemma norm_term1_unf:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow> unf env t \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and ac = "1.prems"(3) and cl = "1.prems"(4)
  have IH: "unf env u \<rightarrow>\<^sub>\<beta>\<^sup>* unf env u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te ac cl] .
  have redex: "unf env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'" if "ok (nt te (subst_bound u body)) t'" for b U0 body u
  proof -
    have "unf env (Abs b U0 body $ u) \<rightarrow>\<^sub>\<beta> unf env (body[u/0])"
      by (simp add: unf_subst[OF ac cl])
    with IH[OF that[unfolded subst_bound_subst]] show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
  qed
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with ok_lookup1[OF lr] te have "vt_lookup (tenv env) x = Some (T, u)" by simp
      with IH[of u t'] rest Some Var show ?thesis by (simp add: unf_Var[OF ac])
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      have fu: "unf env (f $ u) \<rightarrow>\<^sub>\<beta>\<^sup>* unf env (nf $ u)" using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded nf] redex[OF this]] App show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt te u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from rtrancl_beta_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed

lemma norm_term2_unf:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> acyc env \<Longrightarrow> closed_env env \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow>
    inst \<rho> (unf env t) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unf env t')"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2) and cl = "1.prems"(3) and tsol = "1.prems"(4)
  have IH: "inst \<rho> (unf env u) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unf env u')" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl ac cl tsol] .
  have nty: "tsubst \<rho> T' = tsubst \<rho> T" if "ok (norm_type_aux (tyenv env) T) T'" for T T'
    using norm_type_aux_sound[OF that refl tsol] .
  have redex: "inst \<rho> (unf env (Abs b U0 body $ u)) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unf env t')"
    if "ok (nt env (subst_bound u body)) t'" for b U0 body u
  proof -
    have "inst \<rho> (unf env (Abs b U0 body $ u)) \<rightarrow>\<^sub>\<beta> inst \<rho> (unf env (body[u/0]))"
      using inst_beta[of \<rho> b U0 "unf env body" "unf env u"] by (simp add: unf_subst[OF ac cl])
    with IH[OF that[unfolded subst_bound_subst]] show ?thesis by (simp add: converse_rtranclp_into_rtranclp)
  qed
  show ?case
  proof (cases t)
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nty[OF this(1)] Const show ?thesis by simp
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nty[OF this(1)] Free show ?thesis by simp
  next
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      from lr Some obtain U where lk: "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      from rest Some have "ok (nt env u) t'" by simp
      with IH[OF this] lk Var show ?thesis by (simp add: unf_Var[OF ac])
    next
      case None
      with ok_lookup_None lr have lk: "vt_lookup (tenv env) x = None" by blast
      from rest None obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nty[OF this(1)] lk Var show ?thesis by (simp add: unf_Var[OF ac])
    qed
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'"
      "t' = Abs a T' body'" by auto
    with nty[OF this(1)] IH[OF this(2)] Abs show ?thesis by (simp add: rtrancl_beta_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      have fu: "inst \<rho> (unf env (f $ u)) \<rightarrow>\<^sub>\<beta>\<^sup>* inst \<rho> (unf env (nf $ u))"
        using IH[OF hf] by (simp add: rtrancl_beta_AppL)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where nf: "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        from rtranclp_trans[OF fu[unfolded nf] redex[OF this]] App show ?thesis by simp
      next
        case False
        with rest obtain nu where hu: "ok (nt env u) nu" and t': "t' = nf $ nu" by (cases nf) auto
        from rtrancl_beta_App[OF IH[OF hf] IH[OF hu]] App t' show ?thesis by simp
      qed
    qed
  qed (use h in auto)
qed

lemma norm_type_aux_tnorm:
  assumes "norm_type_aux \<theta> T = Some r"
  shows "r = Ok T' \<Longrightarrow> tacyc \<theta> \<Longrightarrow> T' = tnorm \<theta> T"
  using assms
proof (induction \<theta> T r arbitrary: T' rule: norm_type_aux.raw_induct[rotated, consumes 1])
  case (1 nt \<theta> T r)
  note n = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2)
  show ?case
  proof (cases T)
    case (Type a Ts)
    with n obtain Ts' where l: "list_all2 (\<lambda>x y. ok (nt \<theta> x) y) Ts Ts'" and T': "T' = Type a Ts'"
      by (auto simp: ok_mapM)
    from l have "Ts' = map (tnorm \<theta>) Ts"
      by (induction rule: list_all2_induct) (use "1.IH" ac in auto)
    with Type T' show ?thesis by simp
  next
    case (TVar v S)
    with n obtain lr where lr: "ok (type_lookup \<theta> v S) lr"
      and rest: "ok (case lr of Some U \<Rightarrow> nt \<theta> U | None \<Rightarrow> return T) T'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some U)
      with lr have "vt_lookup \<theta> v = Some (S, U)"
        by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)
      moreover from rest Some have "ok (nt \<theta> U) T'" by simp
      with "1.IH" ac have "T' = tnorm \<theta> U" by blast
      ultimately show ?thesis using TVar by (simp add: tnorm_TVar[OF ac])
    next
      case None
      with lr have "vt_lookup \<theta> v = None"
        by (auto simp: type_lookup_def tvar_clash_def split: option.splits if_splits)
      moreover from rest None TVar have "T' = TVar v S" by simp
      ultimately show ?thesis using TVar by (simp add: tnorm_TVar[OF ac])
    qed
  qed (use n in auto)
qed

text \<open>The results of normalization are normal for the environment:\<close>

lemma norm_term1_normal:
  assumes "norm_term1 te t = Some r"
  shows "r = Ok t' \<Longrightarrow> te = tenv env \<Longrightarrow> vt_is_empty (tyenv env) \<Longrightarrow> env_normal env t'"
  using assms
proof (induction te t r arbitrary: t' rule: norm_term1.raw_induct[rotated, consumes 1])
  case (1 nt te t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and te = "1.prems"(2) and em = "1.prems"(3)
  have IH: "env_normal env u'" if "ok (nt te u) u'" for u u'
    using "1.IH"[OF that refl te em] .
  have ty: "tnorm (tyenv env) T = T" for T by (rule tnorm_empty[OF em])
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup1 te x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt te u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with ok_lookup1[OF lr] te have "vt_lookup (tenv env) x = None" by simp
      moreover from rest None Var have "t' = Var x T" by simp
      ultimately show ?thesis by (simp add: ty)
    qed (use rest IH in simp)
  next
    case (Abs a T body)
    with h obtain body' where "ok (nt te body) body'" "t' = Abs a T body'" by auto
    with IH[OF this(1)] show ?thesis by (simp add: ty)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt te (subst_bound u body)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt te f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt te (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt te u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt te (subst_bound u body)) t'" by simp
        then show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where "ok (nt te u) nu" "t' = nf $ nu" by (cases nf) auto
        with IH[OF hf] IH[OF this(1)] show ?thesis by simp
      qed
    qed
  qed (use h ty in auto)
qed

lemma norm_term2_normal:
  assumes "norm_term2 env t = Some r"
  shows "r = Ok t' \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> env_normal env t'"
  using assms
proof (induction env t r arbitrary: t' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)] and ac = "1.prems"(2)
  have IH: "env_normal env u'" if "ok (nt env u) u'" for u u'
    using "1.IH"[OF that refl ac] .
  have nty: "T' = tnorm (tyenv env) T" "tnorm (tyenv env) T' = T'" if "ok (norm_type_aux (tyenv env) T) T'" for T T'
    using norm_type_aux_tnorm[OF that refl ac] tnorm_idem[OF ac] by simp_all
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> do {T' \<leftarrow> norm_type_aux (tyenv env) T; return (Var x T')}) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case None
      with ok_lookup_None lr have lk: "vt_lookup (tenv env) x = None" by blast
      from rest None obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Var x T'" by auto
      with nty(2)[OF this(1)] lk show ?thesis by simp
    qed (use rest IH in simp)
  next
    case (Abs a T body)
    with h obtain T' body' where "ok (norm_type_aux (tyenv env) T) T'" "ok (nt env body) body'"
      "t' = Abs a T' body'" by auto
    with nty(2)[OF this(1)] IH[OF this(2)] show ?thesis by simp
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U body where f: "f = Abs b U body" by (cases f) auto
      with h App have "ok (nt env (subst_bound u body)) t'" by simp
      then show ?thesis by (rule IH)
    next
      case False
      with h App obtain nf where hf: "ok (nt env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> nt env (subst_bound u body)
          | _ \<Rightarrow> do {nu \<leftarrow> nt env u; return (nf $ nu)}) t'"
        by (cases f) auto
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain b U0 body where "nf = Abs b U0 body" by (cases nf) auto
        with rest have "ok (nt env (subst_bound u body)) t'" by simp
        then show ?thesis by (rule IH)
      next
        case nA: False
        with rest obtain nu where "ok (nt env u) nu" "t' = nf $ nu" by (cases nf) auto
        with IH[OF hf] IH[OF this(1)] show ?thesis by simp
      qed
    qed
  next
    case (Const a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Const a T'" by auto
    with nty(2)[OF this(1)] show ?thesis by simp
  next
    case (Free a T)
    with h obtain T' where "ok (norm_type_aux (tyenv env) T) T'" "t' = Free a T'" by auto
    with nty(2)[OF this(1)] show ?thesis by simp
  qed (use h in auto)
qed

text \<open>
  \<open>Envir.norm_term\<close> applies the environment and \<open>\<beta>\<close>-reduces; its results are normal for the
  environment.
\<close>

theorem norm_term_env_apply:
  assumes nt: "ok (norm_term env t) t'" and ac: "acyc env" "closed_env env" "tacyc (tyenv env)"
  shows "env_apply env t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "env_normal env t'"
proof -
  consider (id) "env_is_empty env \<and> \<not> could_beta_contract t"
    | (n1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "vt_is_empty (tyenv env)"
    | (n2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract t)" "\<not> vt_is_empty (tyenv env)"
    by blast
  then have "env_apply env t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> env_normal env t'"
  proof cases
    case id
    then have em: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: env_is_empty_def)
    from id nt have "t' = t" by (simp add: norm_term_def)
    moreover have "env_normal env t" using em by (simp add: env_normal_def vt_is_empty_lookup tnorm_empty)
    ultimately show ?thesis using id by (simp add: env_apply_empty)
  next
    case n1
    with nt have n: "norm_term1 (tenv env) t = Some (Ok t')" by (simp add: norm_term_def)
    have "unf env t \<rightarrow>\<^sub>\<beta>\<^sup>* unf env t'" by (rule norm_term1_unf[OF n refl refl ac(1,2)])
    moreover have nn: "env_normal env t'" by (rule norm_term1_normal[OF n refl refl n1(2)])
    moreover have "env_apply env s = unf env s" for s
      unfolding env_apply_def by (rule inst_tnorm_inst_id) (simp add: tnorm_empty[OF n1(2)])
    ultimately show ?thesis using env_apply_normal[OF nn ac(1)] by simp
  next
    case n2
    with nt have n: "norm_term2 env t = Some (Ok t')" by (simp add: norm_term_def)
    have "env_apply env t \<rightarrow>\<^sub>\<beta>\<^sup>* env_apply env t'"
      unfolding env_apply_def by (rule norm_term2_unf[OF n refl ac(1,2) tsol_tnorm[OF ac(3)]])
    moreover have nn: "env_normal env t'" by (rule norm_term2_normal[OF n refl ac(3)])
    ultimately show ?thesis using env_apply_normal[OF nn ac(1)] by simp
  qed
  then show "env_apply env t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "env_normal env t'" by blast+
qed

end

end
