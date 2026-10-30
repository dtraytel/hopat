section \<open>Polymorphic Typing\<close>

theory Poly_Typing
  imports Poly_Unif_Term
begin

context csig
begin

text \<open>
  Typing in an environment, and the invariant of environments: the invariant \<^const>\<open>env_inv\<close>
  of the type-free core, read modulo the type environment \<open>\<theta>\<close>, together with the invariant of
  type unification for \<open>\<theta>\<close>. Its ground instances satisfy \<^const>\<open>env_inv\<close>, and
  \<^const>\<open>unify\<close> preserves it.
\<close>


subsection \<open>Typing modulo a type environment\<close>

text \<open>Terms with their types normalized by a type environment:\<close>

fun tnormt :: "tyenv \<Rightarrow> pterm \<Rightarrow> pterm" where
  "tnormt \<theta> (Const a T) = Const a (tnorm \<theta> T)"
| "tnormt \<theta> (Free a T) = Free a (tnorm \<theta> T)"
| "tnormt \<theta> (Var x T) = Var x (tnorm \<theta> T)"
| "tnormt \<theta> (Bound i) = Bound i"
| "tnormt \<theta> (Abs a T t) = Abs a (tnorm \<theta> T) (tnormt \<theta> t)"
| "tnormt \<theta> (s $ t) = tnormt \<theta> s $ tnormt \<theta> t"

lemma tnormt_empty: "vt_is_empty \<theta> \<Longrightarrow> tnormt \<theta> t = t"
  by (induction t) (simp_all add: tnorm_empty)

lemma tnormt_textends: "tacyc \<theta>' \<Longrightarrow> textends \<theta> \<theta>' \<Longrightarrow> tnormt \<theta>' (tnormt \<theta> t) = tnormt \<theta>' t"
  by (induction t) (simp_all add: tnorm_textends)

lemma tys_tnormt: "tys (tnormt \<theta> t) = tnorm \<theta> ` tys t"
  by (induction t) auto

lemma vps_tnormt: "vps (tnormt \<theta> t) = (\<lambda>(x, T). (x, tnorm \<theta> T)) ` vps t"
  by (induction t) auto

lemma vars_tnormt[simp]: "vars (tnormt \<theta> t) = vars t"
  by (induction t) auto

lemma has_type_vars:
  "has_type V Ts t T \<Longrightarrow> (\<And>x. x \<in> vars t \<Longrightarrow> V' x = V x) \<Longrightarrow> has_type V' Ts t T"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

lemma has_type_tnormt:
  "has_type V Ts t T \<Longrightarrow> has_type (\<lambda>x. tnorm \<theta> (V x)) (map (tnorm \<theta>) Ts) (tnormt \<theta> t) (tnorm \<theta> T)"
  by (induction rule: has_type.induct) (auto intro: has_type.intros)

text \<open>
  Typing in an environment \<open>env\<close>: bound variables have the types of their bindings, the other
  variables the types given by \<open>W\<close>, and types are compared modulo the type environment, that
  is, after normalization by \<^const>\<open>tnorm\<close>.
\<close>

definition vtyp :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "vtyp env W x = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> U | None \<Rightarrow> W x)"

abbreviation tctx :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> indexname \<Rightarrow> ptyp" where
  "tctx env W \<equiv> \<lambda>x. tnorm (tyenv env) (vtyp env W x)"

definition typed :: "env \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "typed env W Ts t T \<longleftrightarrow>
    has_type (tctx env W) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) t) (tnorm (tyenv env) T)"

definition wt_env :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "wt_env W env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> typed env W [] u U)"

lemma typed_empty:
  "vt_is_empty (tyenv env) \<Longrightarrow> typed env W Ts t T \<longleftrightarrow> has_type (vtyp env W) Ts t T"
  by (simp add: typed_def tnormt_empty tnorm_empty map_idI)

text \<open>The internal form: the typing \<open>W\<close> is already normalized and covers the bound variables.\<close>

definition env_typed_mod :: "tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "env_typed_mod \<theta> W env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
    W x = tnorm \<theta> U \<and> has_type W [] (tnormt \<theta> u) (tnorm \<theta> U))"

lemma env_typed_modD:
  "env_typed_mod \<theta> W env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
    W x = tnorm \<theta> U \<and> has_type W [] (tnormt \<theta> u) (tnorm \<theta> U)"
  unfolding env_typed_mod_def by blast

lemma wt_env_mod: "wt_env W env \<Longrightarrow> env_typed_mod (tyenv env) (tctx env W) env"
  unfolding wt_env_def env_typed_mod_def typed_def by (auto simp: vtyp_def)

lemma tctx_normal:
  assumes "env_typed_mod (tyenv env) W env" "\<And>x. tnorm (tyenv env) (W x) = W x"
  shows "tctx env W = W"
proof
  fix x show "tnorm (tyenv env) (vtyp env W x) = W x"
    using assms env_typed_modD[OF assms(1), of x] by (cases "vt_lookup (tenv env) x") (auto simp: vtyp_def)
qed

lemma mod_wt_env:
  assumes "env_typed_mod (tyenv env) W env" "\<And>x. tnorm (tyenv env) (W x) = W x"
  shows "wt_env W env"
  using assms(1) unfolding wt_env_def typed_def tctx_normal[OF assms] by (auto dest: env_typed_modD)

text \<open>Well-formed terms and environments whose types need not be ground:\<close>

definition pwf_term :: "(name \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pterm \<Rightarrow> bool" where
  "pwf_term ar n t \<longleftrightarrow> proper t \<and> (\<forall>T\<in>tys t. wft ar T) \<and> no_loose_bound (tr t) n"

definition pwf_env :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> bool" where
  "pwf_env ar env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> pwf_term ar 0 u \<and> wft ar U)"

lemma pwf_envD: "pwf_env ar env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> pwf_term ar 0 u \<and> wft ar U"
  unfolding pwf_env_def by blast

text \<open>The type variables of an environment and of a problem:\<close>

definition etvars :: "env \<Rightarrow> (indexname \<times> psort) set" where
  "etvars env = (\<Union>T\<in>etys env. tvars T)"

definition ptvars :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> (indexname \<times> psort) set" where
  "ptvars env s t = (\<Union>T\<in>tys s \<union> tys t. tvars T) \<union> etvars env"

lemma finite_tys[simp]: "finite (tys t)"
  by (induction t) auto

lemma finite_etys: "finite (etys env)"
proof -
  have "etys env = (\<Union>x\<in>{x. vt_lookup (tenv env) x \<noteq> None}.
      insert (fst (the (vt_lookup (tenv env) x))) (tys (snd (the (vt_lookup (tenv env) x)))))"
    by (force simp: etys_def)
  then show ?thesis using finite_vt_lookup[of "tenv env"] by simp
qed

lemma finite_ptvars: "finite (ptvars env s t)"
  using finite_etys by (simp add: ptvars_def etvars_def)

lemma etvars_ptvars: "etvars env \<subseteq> ptvars env s t"
  by (simp add: ptvars_def)

text \<open>The invariant of polymorphic environments, the analogue of \<^const>\<open>env_inv\<close>:\<close>

definition penv_inv :: "algebra \<Rightarrow> (name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "penv_inv alg ar W env \<longleftrightarrow> tinv ar (maxidx env) (tyenv env) (etvars env) \<and> tsorted alg (tyenv env) \<and>
    nacyc env \<and> pwf_env ar env \<and> wt_env W env \<and> fresh_env env"

lemma penv_invD:
  assumes "penv_inv alg ar W env"
  shows "tinv ar (maxidx env) (tyenv env) (etvars env)" "tsorted alg (tyenv env)" "nacyc env"
    "pwf_env ar env" "env_typed_mod (tyenv env) (tctx env W) env" "fresh_env env"
  using assms wt_env_mod by (simp_all add: penv_inv_def)


subsection \<open>Type variables\<close>

lemma tinv_subset: "tinv ar n \<theta> A \<Longrightarrow> B \<subseteq> tvars_env \<theta> \<union> A \<Longrightarrow> tinv ar n \<theta> B"
  unfolding tinv_def scons_def by blast

lemma tyw_tvars:
  assumes "tvars T \<subseteq> A" "wft ar T"
  shows "tyw ar \<theta> A T"
proof -
  have "uvars \<theta> T \<subseteq> uvarsA \<theta> A"
  proof
    fix u assume "u \<in> uvars \<theta> T"
    then obtain w S where "(w, S) \<in> tvars T" "u \<in> uvars \<theta> (TVar w S)"
      by (subst (asm) uvars_def, subst (asm) tnorm_tsubst) (force simp: uvars_def tvars_tsubst)
    with assms(1) show "u \<in> uvarsA \<theta> A" by (auto simp: uvarsA_def)
  qed
  with assms show ?thesis by (auto simp: tyw_def)
qed

lemma tcons_tnorm: "tacyc \<theta> \<Longrightarrow> tcons \<theta> (tnorm \<theta> T)"
  unfolding tcons_def using tnorm_unbound by fastforce


subsection \<open>Ground instances\<close>

lemma typs_ok_inst: "\<forall>T\<in>tys t. wft ar T \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> typs_ok ar (inst \<rho> t)"
  by (induction t) (auto intro: ground_tsubst)

lemma wf_term_inst: "pwf_term ar n t \<Longrightarrow> \<forall>v S. ground ar (\<rho> v S) \<Longrightarrow> wf_term ar n (inst \<rho> t)"
  by (simp add: pwf_term_def wf_term_def typs_ok_inst)

lemma inst_tnormt:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>"
  shows "\<forall>T\<in>tys t. tcons \<theta> T \<Longrightarrow> inst \<rho> (tnormt \<theta> t) = inst \<rho> t"
  by (induction t) (simp_all add: tsubst_tnorm[OF assms])

lemma has_type_inst_mod:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>" "\<forall>U\<in>tys t. tcons \<theta> U" "tcons \<theta> T"
    and "has_type W [] (tnormt \<theta> t) (tnorm \<theta> T)"
  shows "has_type (\<lambda>x. tsubst \<rho> (W x)) [] (inst \<rho> t) (tsubst \<rho> T)"
  using has_type_inst[OF assms(6), of \<rho>] by (simp add: inst_tnormt[OF assms(1-4)] tsubst_tnorm[OF assms(1-3,5)])

text \<open>The ground instances of an environment satisfy the invariant of the core:\<close>

lemma penv_inv_inst:
  assumes inv: "penv_inv alg ar W env" and g: "gsol alg ar (tyenv env) \<rho>"
  shows "env_inv ar (\<lambda>x. tsubst \<rho> (tctx env W x)) (instE \<rho> env)"
proof -
  let ?\<theta> = "tyenv env" and ?W = "\<lambda>x. tsubst \<rho> (tctx env W x)"
  note i = penv_invD[OF inv]
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF i(1)] tinv_tcons_env[OF i(1)] by simp_all
  have sol: "tsol ?\<theta> \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)" using g by (simp_all add: gsol_def)
  have tc: "tcons ?\<theta> T" if "T \<in> etys env" for T
    using that by (intro tinv_tcons[OF i(1)]) (auto simp: etvars_def)
  have wfb: "proper u \<and> typs_ok ar u \<and> ground ar U \<and> no_loose_bound (tr u) 0"
    if "vt_lookup (tenv (instE \<rho> env)) x = Some (U, u)" for x U u
  proof -
    from that obtain U0 u0 where b: "vt_lookup (tenv env) x = Some (U0, u0)" and U: "U = tsubst \<rho> U0"
      and u: "u = inst \<rho> u0" by auto
    from pwf_envD[OF i(4) b] have "wf_term ar 0 u" "ground ar U"
      using wf_term_inst[OF _ gr] ground_tsubst[OF _ gr] by (auto simp: U u)
    then show ?thesis by (simp add: wf_term_def)
  qed
  have "wf_env ar (instE \<rho> env)" unfolding wf_env_def using wfb by auto
  moreover have ety: "env_typed ?W (instE \<rho> env)"
    unfolding env_typed_def
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv (instE \<rho> env)) x = Some (U, u)"
    then obtain U0 u0 where b: "vt_lookup (tenv env) x = Some (U0, u0)" and U: "U = tsubst \<rho> U0"
      and u: "u = inst \<rho> u0" by auto
    have tU: "tcons ?\<theta> U0" and tu: "\<forall>T\<in>tys u0. tcons ?\<theta> T" using tc etysI[OF b] by auto
    from env_typed_modD[OF i(5) b] show "?W x = U \<and> has_type ?W [] u U"
      using has_type_inst_mod[OF ac sol tu tU] tsubst_tnorm[OF ac sol tU] by (simp add: U u)
  qed
  moreover have "fresh_env (instE \<rho> env)"
    using i(6) unfolding fresh_env_def by auto
  moreover have "acyc (instE \<rho> env)" using acyc_instE[OF ety] i(3) by simp
  ultimately show ?thesis by (simp add: env_inv_def)
qed


subsection \<open>Reflecting the typing of a faithful instance\<close>

text \<open>
  If a type instantiation \<open>\<rho>\<close> is injective on a set \<open>\<T>\<close> of types that is closed under
  components, and does not map the type variables of \<open>\<T>\<close> to type constructors, then a type of
  \<open>\<T>\<close> whose instance is an instance of a type \<open>U\<close> without fixed type variables (such as a
  declared type of a constant) is itself an instance of \<open>U\<close>.
\<close>

lemma tsubst_reflect:
  fixes \<T> :: "ptyp set"
  assumes inj: "\<And>T U. T \<in> \<T> \<Longrightarrow> U \<in> \<T> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow> T = U"
    and sub: "\<And>a Ts. Type a Ts \<in> \<T> \<Longrightarrow> set Ts \<subseteq> \<T>"
    and nty: "\<And>v S a Ts. TVar v S \<in> \<T> \<Longrightarrow> \<rho> v S \<noteq> Type a Ts"
  shows "no_tfrees U \<Longrightarrow> T \<in> \<T> \<Longrightarrow> tsubst \<theta> U = tsubst \<rho> T \<Longrightarrow>
    tsubst (\<lambda>v S. SOME X. X \<in> \<T> \<and> tsubst \<rho> X = \<theta> v S) U = T"
proof (induction U arbitrary: T)
  case (Type a Us)
  show ?case
  proof (cases T)
    case (Type b Ts)
    with Type.prems have b: "b = a" and m: "map (tsubst \<theta>) Us = map (tsubst \<rho>) Ts" by simp_all
    from m have l: "length Us = length Ts" by (metis length_map)
    have Ts: "set Ts \<subseteq> \<T>" using sub Type.prems(2) \<open>T = Type b Ts\<close> by blast
    have "map (tsubst (\<lambda>v S. SOME X. X \<in> \<T> \<and> tsubst \<rho> X = \<theta> v S)) Us = Ts"
    proof (rule nth_equalityI)
      fix i assume "i < length (map (tsubst (\<lambda>v S. SOME X. X \<in> \<T> \<and> tsubst \<rho> X = \<theta> v S)) Us)"
      then have i: "i < length Us" by simp
      have "tsubst \<theta> (Us ! i) = tsubst \<rho> (Ts ! i)"
        using arg_cong[OF m, of "\<lambda>xs. xs ! i"] i l by simp
      with Type.IH[of "Us ! i" "Ts ! i"] Type.prems(1) i l Ts
      show "map (tsubst (\<lambda>v S. SOME X. X \<in> \<T> \<and> tsubst \<rho> X = \<theta> v S)) Us ! i = Ts ! i" by auto
    qed (simp add: l)
    then show ?thesis using \<open>T = Type b Ts\<close> b by simp
  next
    case (TVar v S)
    with Type.prems nty show ?thesis by (metis tsubst.simps(1,3))
  qed (use Type.prems in simp)
next
  case (TVar v S)
  then have "\<exists>X. X \<in> \<T> \<and> tsubst \<rho> X = \<theta> v S" by auto
  from someI_ex[OF this] TVar.prems inj show ?case by auto
qed simp

text \<open>
  If a type instantiation \<open>\<rho>\<close> is injective on a set \<open>\<T>\<close> of types that is closed under function
  types and components, and does not map the type variables of \<open>\<T>\<close> to type constructors, then
  a typing of an instance \<open>inst \<rho> t\<close> is the instance of a typing of \<open>t\<close> with types in \<open>\<T>\<close>.
\<close>

lemma has_type_reflect:
  fixes \<T> :: "ptyp set"
  assumes inj: "\<And>T U. T \<in> \<T> \<Longrightarrow> U \<in> \<T> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow> T = U"
    and sub: "\<And>a Ts. Type a Ts \<in> \<T> \<Longrightarrow> set Ts \<subseteq> \<T>"
    and arr: "\<And>T U. T \<in> \<T> \<Longrightarrow> U \<in> \<T> \<Longrightarrow> (T \<rightarrow>\<^sub>T U) \<in> \<T>"
    and nty: "\<And>v S a Ts. TVar v S \<in> \<T> \<Longrightarrow> \<rho> v S \<noteq> Type a Ts"
  shows "has_type V (map (tsubst \<rho>) Ts) (inst \<rho> t) U' \<Longrightarrow> tys t \<subseteq> \<T> \<Longrightarrow> set Ts \<subseteq> \<T> \<Longrightarrow>
    (\<And>x T. (x, T) \<in> vps t \<Longrightarrow> W x \<in> \<T> \<and> V x = tsubst \<rho> (W x)) \<Longrightarrow>
    \<exists>U\<in>\<T>. U' = tsubst \<rho> U \<and> has_type W Ts t U"
proof (induction t arbitrary: Ts U')
  case (Const a T)
  have nv: "\<exists>Ys. X = Type b Ys \<and> map (tsubst \<rho>) Ys = Xs \<and> set Ys \<subseteq> \<T>"
    if "tsubst \<rho> X = Type b Xs" "X \<in> \<T>" for X b Xs
    using that nty sub by (cases X) auto
  have nf: "\<exists>X1 X2. X = X1 \<rightarrow>\<^sub>T X2 \<and> tsubst \<rho> X1 = A \<and> tsubst \<rho> X2 = B \<and> X1 \<in> \<T> \<and> X2 \<in> \<T>"
    if "tsubst \<rho> X = A \<rightarrow>\<^sub>T B" "X \<in> \<T>" for X A B
    using nv[OF that] by (auto simp: map_eq_Cons_conv)
  have np: "X = Type STR ''prop'' []" if "tsubst \<rho> X = Type STR ''prop'' []" "X \<in> \<T>" for X
    using nv[OF that] by auto
  from Const.prems(1) have U': "U' = tsubst \<rho> T" and ok: "const_typ_ok a (tsubst \<rho> T)"
    by (auto elim: has_type_elims)
  have T: "T \<in> \<T>" using Const.prems(2) by simp
  have "const_typ_ok a T"
    unfolding const_typ_ok_def
  proof (intro conjI impI)
    assume "a = STR ''Pure.imp''"
    with ok have "tsubst \<rho> T = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (simp add: const_typ_ok_def)
    from nf[OF this T] obtain X1 X2 where X: "T = X1 \<rightarrow>\<^sub>T X2" "tsubst \<rho> X1 = Type STR ''prop'' []"
      "tsubst \<rho> X2 = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []" "X1 \<in> \<T>" "X2 \<in> \<T>" by blast
    from nf[OF X(3,5)] obtain Y1 Y2 where Y: "X2 = Y1 \<rightarrow>\<^sub>T Y2" "tsubst \<rho> Y1 = Type STR ''prop'' []"
      "tsubst \<rho> Y2 = Type STR ''prop'' []" "Y1 \<in> \<T>" "Y2 \<in> \<T>" by blast
    show "T = Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' [] \<rightarrow>\<^sub>T Type STR ''prop'' []"
      using X Y np by simp
  next
    assume "a = STR ''Pure.all''"
    with ok obtain U0 where "tsubst \<rho> T = (U0 \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
      by (auto simp: const_typ_ok_def)
    from nf[OF this T] obtain X1 X2 where X: "T = X1 \<rightarrow>\<^sub>T X2" "tsubst \<rho> X1 = U0 \<rightarrow>\<^sub>T Type STR ''prop'' []"
      "tsubst \<rho> X2 = Type STR ''prop'' []" "X1 \<in> \<T>" "X2 \<in> \<T>" by blast
    from nf[OF X(2,4)] obtain Y1 Y2 where Y: "X1 = Y1 \<rightarrow>\<^sub>T Y2" "tsubst \<rho> Y2 = Type STR ''prop'' []"
      "Y2 \<in> \<T>" by blast
    show "\<exists>U. T = (U \<rightarrow>\<^sub>T Type STR ''prop'' []) \<rightarrow>\<^sub>T Type STR ''prop'' []"
      using X Y np by auto
  next
    assume "a \<noteq> STR ''Pure.imp''" "a \<noteq> STR ''Pure.all''"
    with ok obtain U \<theta> where U: "ctab a = Some U" "no_tfrees U" "tsubst \<rho> T = tsubst \<theta> U"
      by (auto simp: const_typ_ok_def)
    from tsubst_reflect[OF inj sub nty U(2) T U(3)[symmetric]] U(1,2)
    show "\<exists>U \<rho>. ctab a = Some U \<and> no_tfrees U \<and> T = tsubst \<rho> U" by metis
  qed
  with U' T show ?case by (auto intro: has_type.Const)
next
  case (Free a T)
  then show ?case by (auto elim: has_type_elims intro: has_type.intros)
next
  case (Var x T)
  then have "W x = T" using inj by (auto elim: has_type_elims)
  with Var show ?case by (auto elim: has_type_elims intro: has_type.intros)
next
  case (Bound i)
  then show ?case by (auto simp: has_type_Bound_iff)
next
  case (Abs a T b)
  from Abs.prems(1) obtain U2' where U': "U' = tsubst \<rho> T \<rightarrow>\<^sub>T U2'"
    and b: "has_type V (map (tsubst \<rho>) (T # Ts)) (inst \<rho> b) U2'"
    by (auto elim: has_type_elims)
  from Abs.IH[OF b] Abs.prems(2-4) obtain U2 where "U2 \<in> \<T>" "U2' = tsubst \<rho> U2"
    "has_type W (T # Ts) b U2" by auto
  with Abs.prems(2) U' show ?case by (intro bexI[of _ "T \<rightarrow>\<^sub>T U2"]) (auto intro: has_type.intros arr)
next
  case (App f u)
  from App.prems(1) obtain A' where f: "has_type V (map (tsubst \<rho>) Ts) (inst \<rho> f) (A' \<rightarrow>\<^sub>T U')"
    and u: "has_type V (map (tsubst \<rho>) Ts) (inst \<rho> u) A'"
    by (auto elim: has_type_elims)
  have "\<exists>U\<in>\<T>. A' \<rightarrow>\<^sub>T U' = tsubst \<rho> U \<and> has_type W Ts f U"
    by (rule App.IH(1)[OF f]) (use App.prems(2-4) in auto)
  then obtain Uf where Uf: "Uf \<in> \<T>" "A' \<rightarrow>\<^sub>T U' = tsubst \<rho> Uf" "has_type W Ts f Uf" by blast
  have "\<exists>U\<in>\<T>. A' = tsubst \<rho> U \<and> has_type W Ts u U"
    by (rule App.IH(2)[OF u]) (use App.prems(2-4) in auto)
  then obtain Uu where Uu: "Uu \<in> \<T>" "A' = tsubst \<rho> Uu" "has_type W Ts u Uu" by blast
  obtain A B where AB: "Uf = A \<rightarrow>\<^sub>T B" "A' = tsubst \<rho> A" "U' = tsubst \<rho> B"
  proof (cases Uf)
    case (Type c Us)
    with Uf(2) obtain A B where "Us = [A, B]" by (cases Us rule: list.exhaust[case_product list.exhaust]) auto
    with Type Uf(2) show ?thesis by (intro that) auto
  next
    case (TVar v S)
    with Uf nty show ?thesis by (metis tsubst.simps(3))
  qed (use Uf(2) in simp)
  have AB\<T>: "A \<in> \<T>" "B \<in> \<T>" using sub[of "STR ''fun''" "[A, B]"] Uf(1) AB(1) by auto
  have "Uu = A" using inj[OF Uu(1) AB\<T>(1)] Uu(2) AB(2) by simp
  with Uf(3) Uu(3) AB(1,3) AB\<T>(2) show ?case by (auto intro: has_type.intros)
qed


subsection \<open>Preservation by unification\<close>

lemma vars_vps: "vars t = fst ` vps t"
  by (induction t) auto

end

context wf_csig
begin

lemma inst_ok_mod:
  assumes inv: "penv_inv alg ar W env" and A: "tinv ar (maxidx env) (tyenv env) (ptvars env s t)"
    and g: "gsol alg ar (tyenv env) \<rho>"
    and s: "pwf_term ar 0 s" "typed env W [] s T"
    and t: "pwf_term ar 0 t" "typed env W [] t T"
  shows "inst_ok ar (\<lambda>x. tsubst \<rho> (tctx env W x)) \<rho> [] s t env"
proof -
  have ac: "tacyc (tyenv env)" "tcons_env (tyenv env)" using tinv_tacyc[OF A] tinv_tcons_env[OF A] by simp_all
  have sol: "tsol (tyenv env) \<rho>" and gr: "\<forall>v S. ground ar (\<rho> v S)" using g by (simp_all add: gsol_def)
  have tc: "\<forall>U\<in>tys u. tcons (tyenv env) U" if "u = s \<or> u = t" for u
    using that by (auto intro!: tinv_tcons[OF A] simp: ptvars_def)
  have "has_type (\<lambda>x. tsubst \<rho> (tctx env W x)) [] (inst \<rho> u) (tsubst \<rho> (tnorm (tyenv env) T))"
    if "typed env W [] u T" "u = s \<or> u = t" for u
    using has_type_inst[OF that(1)[unfolded typed_def], of \<rho>] inst_tnormt[OF ac sol tc[OF that(2)]] by simp
  with s t env_invD[OF penv_inv_inst[OF inv g]] wf_term_inst[OF s(1) gr] wf_term_inst[OF t(1) gr]
  show ?thesis by (auto simp: inst_ok_def binders_ok_def env_inv_def)
qed

text \<open>
  \<^const>\<open>unify\<close> preserves the invariant, and the problem stays typed. The new typing \<open>W'\<close> is
  obtained from the typing of a faithful ground instance of the returned environment.
\<close>

lemma postok_penv_inv:
  assumes inv: "penv_inv alg ar W env" and A: "tinv ar (maxidx env) (tyenv env) (ptvars env s t)"
    and s: "pwf_term ar 0 s" "typed env W [] s T" "below (maxidx env) s"
    and t: "pwf_term ar 0 t" "typed env W [] t T" "below (maxidx env) t"
    and post: "postok alg ar (ptvars env s t) [] s t env env'" and nac: "nacyc env'"
  obtains W' where "penv_inv alg ar W' env'" "typed env' W' [] s T" "typed env' W' [] t T"
proof -
  let ?\<theta> = "tyenv env" and ?\<theta>' = "tyenv env'" and ?A = "ptvars env s t"
  note i = penv_invD[OF inv]
  note p = post[unfolded postok_def]
  define W0 where "W0 = tctx env W"
  have i5: "env_typed_mod (tyenv env) W0 env" using i(5) unfolding W0_def .
  have s2: "has_type W0 [] (tnormt (tyenv env) s) (tnorm (tyenv env) T)"
    and t2: "has_type W0 [] (tnormt (tyenv env) t) (tnorm (tyenv env) T)"
    using s(2) t(2) by (simp_all add: typed_def W0_def)
  have ext: "textends ?\<theta> ?\<theta>'" "extends env' env" "maxidx env \<le> maxidx env'" using p by blast+
  have inv': "tinv ar (maxidx env') ?\<theta>' ?A" and srt': "tsorted alg ?\<theta>'"
    and tw: "\<forall>T\<in>etys env'. tyw ar ?\<theta>' ?A T" using p by blast+
  have ac: "tacyc ?\<theta>" "tcons_env ?\<theta>" using tinv_tacyc[OF A] tinv_tcons_env[OF A] by simp_all
  have ac': "tacyc ?\<theta>'" "tcons_env ?\<theta>'" using tinv_tacyc[OF inv'] tinv_tcons_env[OF inv'] by simp_all
  define B where "B = tys s \<union> tys t \<union> etys env \<union> etys env'"
  have tc0: "tcons ?\<theta> U" if "U \<in> tys s \<union> tys t \<union> etys env" for U
    using that by (intro tinv_tcons[OF A]) (auto simp: ptvars_def etvars_def)
  have tc': "tcons ?\<theta>' U" if "U \<in> B" for U
  proof (rule tinv_tcons[OF inv'])
    show "tvars U \<subseteq> tvars_env ?\<theta>' \<union> ?A"
      using that tw by (auto simp: B_def ptvars_def etvars_def tyw_def)
  qed
  define Z where "Z = (\<Union>U\<in>B. tvars (tnorm ?\<theta>' U))"
  define N where "N = (\<Union>U\<in>B. tfnames (tnorm ?\<theta>' U))"
  define \<T> where "\<T> = {U. tnorm ?\<theta>' U = U \<and> tvars U \<subseteq> Z \<and> tfnames U \<subseteq> N}"
  have finB: "finite B" using finite_etys by (simp add: B_def)
  have finZ: "finite Z" and finN: "finite N" using finB by (simp_all add: Z_def N_def)
  have in\<T>: "tnorm ?\<theta>' U \<in> \<T>" if "U \<in> B" for U
    using that ac'(1) by (auto simp: \<T>_def Z_def N_def)
  obtain \<rho> where g': "gsol alg ar ?\<theta>' \<rho>" and tf: "tfree_on \<rho> ?\<theta>'"
    and fi: "\<And>T U. tcons ?\<theta>' T \<Longrightarrow> tcons ?\<theta>' U \<Longrightarrow> tvars (tnorm ?\<theta>' T) \<union> tvars (tnorm ?\<theta>' U) \<subseteq> Z \<Longrightarrow>
      tfnames (tnorm ?\<theta>' T) \<union> tfnames (tnorm ?\<theta>' U) \<subseteq> N \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U \<Longrightarrow>
      tnorm ?\<theta>' T = tnorm ?\<theta>' U"
    using faithful_exists[OF inv' srt' finZ finN] by blast
  have inj: "T = U" if "T \<in> \<T>" "U \<in> \<T>" "tsubst \<rho> T = tsubst \<rho> U" for T U
  proof -
    have "tcons ?\<theta>' T" "tcons ?\<theta>' U" using that(1,2) tcons_tnorm[OF ac'(1)] by (metis (mono_tags) \<T>_def mem_Collect_eq)+
    with fi[OF _ _ _ _ that(3)] that(1,2) show ?thesis by (auto simp: \<T>_def)
  qed
  have sub: "set Ts \<subseteq> \<T>" if "Type a Ts \<in> \<T>" for a Ts
  proof
    fix T assume T: "T \<in> set Ts"
    have "tnorm ?\<theta>' T = T" if "map (tnorm ?\<theta>') Us = Us" "T \<in> set Us" for Us
      using that by (induction Us) auto
    with \<open>Type a Ts \<in> \<T>\<close> T show "T \<in> \<T>" by (auto simp: \<T>_def)
  qed
  have arr: "(T \<rightarrow>\<^sub>T U) \<in> \<T>" if "T \<in> \<T>" "U \<in> \<T>" for T U
    using that by (auto simp: \<T>_def)
  have nty: "\<rho> v S \<noteq> Type a Ts" if "TVar v S \<in> \<T>" for v S a Ts
  proof -
    have "(v, S) \<in> tvars (tnorm ?\<theta>' (TVar v S))" using that by (simp add: \<T>_def)
    then have "vt_lookup ?\<theta>' v = None" by (rule tnorm_unbound[OF ac'(1)])
    with tf show ?thesis unfolding tfree_on_def by blast
  qed
  have g: "gsol alg ar ?\<theta> \<rho>" by (rule gsol_textends[OF ext(1) g'])
  have sol: "tsol ?\<theta> \<rho>" "tsol ?\<theta>' \<rho>" using g g' by (simp_all add: gsol_def)
  have io: "inst_ok ar (\<lambda>x. tsubst \<rho> (W0 x)) \<rho> [] s t env"
    using inst_ok_mod[OF inv A g s(1,2) t(1,2)] by (simp add: W0_def)
  from p g' io obtain W1
    where "ty_ext ar (\<lambda>x. tsubst \<rho> (W0 x)) (instE \<rho> env) W1 (instE \<rho> env')" by blast
  then have agV: "agreeV (maxidx env) (\<lambda>x. tsubst \<rho> (W0 x)) W1" and ety1: "env_typed W1 (instE \<rho> env')"
    and wf1: "wf_env ar (instE \<rho> env')" and fr1: "fresh_env (instE \<rho> env')"
    by (simp_all add: ty_ext_def)
  have ty1: "W1 x = tsubst \<rho> U \<and> has_type W1 [] (inst \<rho> u) (tsubst \<rho> U)"
    if "vt_lookup (tenv env') x = Some (U, u)" for x U u
    using env_typedD[OF ety1, of x] that by simp
  define X0 where "X0 = vars s \<union> vars t \<union> fst ` bvps env \<union> {x. vt_lookup (tenv env) x \<noteq> None}"
  have X0: "snd x \<le> maxidx env \<and> (\<exists>U\<in>tys s \<union> tys t \<union> etys env. W0 x = tnorm ?\<theta> U)" if "x \<in> X0" for x
  proof -
    have vp: "snd x \<le> maxidx env \<and> W0 x = tnorm ?\<theta> T"
      if "has_type W0 [] (tnormt ?\<theta> u) U" "(x, T) \<in> vps u" "below (maxidx env) u" for u U T
    proof -
      have "(x, tnorm ?\<theta> T) \<in> vps (tnormt ?\<theta> u)" using that(2) by (force simp: vps_tnormt)
      then have "W0 x = tnorm ?\<theta> T" by (rule has_type_vps[OF that(1)])
      moreover have "x \<in> vars u" using that(2) by (force simp: vars_vps)
      ultimately show ?thesis using that(3) by (simp add: below_def)
    qed
    from that consider "x \<in> vars s" | "x \<in> vars t" | "x \<in> fst ` bvps env"
      | U u where "vt_lookup (tenv env) x = Some (U, u)" by (auto simp: X0_def)
    then show ?thesis
    proof cases
      case 1
      then obtain T where "(x, T) \<in> vps s" by (auto simp: vars_vps)
      with vp[OF s2 _ s(3)] vps_tys[of "(x, T)" s] show ?thesis by auto
    next
      case 2
      then obtain T where "(x, T) \<in> vps t" by (auto simp: vars_vps)
      with vp[OF t2 _ t(3)] vps_tys[of "(x, T)" t] show ?thesis by auto
    next
      case 3
      then obtain T y U u where b: "vt_lookup (tenv env) y = Some (U, u)" and p: "(x, T) \<in> vps u"
        by (auto simp: bvps_def)
      have h: "has_type W0 [] (tnormt ?\<theta> u) (tnorm ?\<theta> U)" using env_typed_modD[OF i5 b] by blast
      have bl: "below (maxidx env) u" using fresh_envD[OF i(6) b] by blast
      have "T \<in> etys env" using vps_tys[OF p] etysI[OF b] by auto
      with vp[OF h p bl] show ?thesis by blast
    next
      case 4
      then show ?thesis using env_typed_modD[OF i5 4] fresh_envD[OF i(6) 4] etysI[OF 4] by blast
    qed
  qed
  define W' where "W' x = (if x \<in> X0 then tnorm ?\<theta>' (W0 x) else case vt_lookup (tenv env') x of
    Some (U, u) \<Rightarrow> tnorm ?\<theta>' U | None \<Rightarrow> tnorm ?\<theta>' (SOME T. (x, T) \<in> bvps env'))" for x
  have key: "W' x \<in> \<T> \<and> W1 x = tsubst \<rho> (W' x)"
    if "x \<in> X0 \<or> vt_lookup (tenv env') x \<noteq> None \<or> x \<in> fst ` bvps env'" for x
  proof (cases "x \<in> X0")
    case True
    with X0 obtain U where U: "U \<in> tys s \<union> tys t \<union> etys env" "W0 x = tnorm ?\<theta> U"
      and ix: "snd x \<le> maxidx env" by blast
    have UB: "U \<in> B" using U(1) by (auto simp: B_def)
    have W'x: "W' x = tnorm ?\<theta>' U" using True U(2) by (simp add: W'_def tnorm_textends[OF ac'(1) ext(1)])
    have "W1 x = tsubst \<rho> (W0 x)" using agV ix unfolding agreeV_def by blast
    also have "\<dots> = tsubst \<rho> U" using U(2) tsubst_tnorm[OF ac sol(1) tc0[OF U(1)]] by simp
    also have "\<dots> = tsubst \<rho> (tnorm ?\<theta>' U)" using tsubst_tnorm[OF ac' sol(2) tc'[OF UB]] by simp
    finally show ?thesis using in\<T>[OF UB] W'x by simp
  next
    case False
    show ?thesis
    proof (cases "vt_lookup (tenv env') x")
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have UB: "U \<in> B" using etysI[of env' x U u] Some b by (auto simp: B_def)
      have "W' x = tnorm ?\<theta>' U" using False Some b by (simp add: W'_def)
      moreover have "W1 x = tsubst \<rho> U" using ty1[of x U u] Some b by simp
      ultimately show ?thesis using in\<T>[OF UB] tsubst_tnorm[OF ac' sol(2) tc'[OF UB]] by simp
    next
      case None
      let ?T = "SOME T. (x, T) \<in> bvps env'"
      from that False None have "\<exists>T. (x, T) \<in> bvps env'" by force
      then have "(x, ?T) \<in> bvps env'" by (rule someI_ex)
      then obtain y U u where b: "vt_lookup (tenv env') y = Some (U, u)" and p: "(x, ?T) \<in> vps u"
        by (auto simp: bvps_def)
      have TB: "?T \<in> B" using vps_tys[OF p] etysI[OF b] by (auto simp: B_def)
      have "W1 x = tsubst \<rho> ?T" using typed_inst_vps[OF conjunct2[OF ty1[OF b]] p] by simp
      moreover have "W' x = tnorm ?\<theta>' ?T" using False None by (simp add: W'_def)
      ultimately show ?thesis using in\<T>[OF TB] tsubst_tnorm[OF ac' sol(2) tc'[OF TB]] by simp
    qed
  qed
  have tm: "env_typed_mod ?\<theta>' W' env'"
    unfolding env_typed_mod_def
  proof (intro allI impI)
    fix x U u assume b: "vt_lookup (tenv env') x = Some (U, u)"
    have UB: "U \<in> B" and uB: "tys u \<subseteq> B" using etysI[OF b] by (auto simp: B_def)
    have kx: "W' x \<in> \<T>" "W1 x = tsubst \<rho> (W' x)" using key b by blast+
    note k = ty1[OF b]
    have eqU: "tsubst \<rho> (tnorm ?\<theta>' U) = tsubst \<rho> U" by (rule tsubst_tnorm[OF ac' sol(2) tc'[OF UB]])
    have Wx: "W' x = tnorm ?\<theta>' U" by (rule inj[OF kx(1) in\<T>[OF UB]]) (use kx(2) k eqU in simp)
    have "inst \<rho> (tnormt ?\<theta>' u) = inst \<rho> u"
      by (rule inst_tnormt[OF ac' sol(2)]) (use tc' uB in blast)
    then have hu: "has_type W1 (map (tsubst \<rho>) []) (inst \<rho> (tnormt ?\<theta>' u)) (tsubst \<rho> U)"
      using k by simp
    have "\<exists>U2\<in>\<T>. tsubst \<rho> U = tsubst \<rho> U2 \<and> has_type W' [] (tnormt ?\<theta>' u) U2"
    proof (rule has_type_reflect[where \<rho> = \<rho> and \<T> = \<T> and W = W', OF inj sub arr nty hu])
      show "tys (tnormt ?\<theta>' u) \<subseteq> \<T>" using uB in\<T> by (auto simp: tys_tnormt)
      fix y T assume "(y, T) \<in> vps (tnormt ?\<theta>' u)"
      then have "y \<in> fst ` bvps env'" using bvpsI[OF b] by (force simp: vps_tnormt)
      then show "W' y \<in> \<T> \<and> W1 y = tsubst \<rho> (W' y)" using key by blast
    qed simp_all
    then obtain U2 where "U2 \<in> \<T>" "tsubst \<rho> U = tsubst \<rho> U2" "has_type W' [] (tnormt ?\<theta>' u) U2" by blast
    moreover have "U2 = tnorm ?\<theta>' U" by (rule inj[OF calculation(1) in\<T>[OF UB]]) (use calculation(2) eqU in simp)
    ultimately show "W' x = tnorm ?\<theta>' U \<and> has_type W' [] (tnormt ?\<theta>' u) (tnorm ?\<theta>' U)" using Wx by simp
  qed
  have ti: "tinv ar (maxidx env') ?\<theta>' (etvars env')"
    by (rule tinv_subset[OF inv']) (use tw in \<open>auto simp: etvars_def tyw_def\<close>)
  have bi: "vt_lookup (tenv (instE \<rho> env')) x = Some (tsubst \<rho> U, inst \<rho> u)"
    if "vt_lookup (tenv env') x = Some (U, u)" for x U u
    using that by simp
  moreover have "pwf_env ar env'"
    unfolding pwf_env_def
  proof (intro allI impI)
    fix x U u assume b: "vt_lookup (tenv env') x = Some (U, u)"
    have "proper (inst \<rho> u) \<and> no_loose_bound (tr (inst \<rho> u)) 0"
      using wf1 bi[OF b] unfolding wf_env_def by blast
    moreover have "\<forall>T\<in>insert U (tys u). wft ar T" using tw etysI[OF b] by (auto simp: tyw_def)
    ultimately show "pwf_term ar 0 u \<and> wft ar U" by (simp add: pwf_term_def)
  qed
  moreover have "fresh_env env'"
    unfolding fresh_env_def using fresh_envD[OF fr1 bi] by simp
  moreover have nW': "tnorm ?\<theta>' (W' x) = W' x" for x
    by (simp add: W'_def tnorm_idem[OF ac'(1)] split: option.splits)
  ultimately have pinv: "penv_inv alg ar W' env'"
    using ti srt' nac mod_wt_env[OF tm nW'] by (simp add: penv_inv_def)
  have ht: "typed env' W' [] u T"
    if "has_type W0 [] (tnormt ?\<theta> u) (tnorm ?\<theta> T)" "vars u \<subseteq> X0" for u
    unfolding typed_def tctx_normal[OF tm nW']
  proof (rule has_type_vars)
    show "has_type (\<lambda>x. tnorm ?\<theta>' (W0 x)) (map (tnorm ?\<theta>') []) (tnormt ?\<theta>' u) (tnorm ?\<theta>' T)"
      using has_type_tnormt[OF that(1), of ?\<theta>']
      by (simp add: tnormt_textends[OF ac'(1) ext(1)] tnorm_textends[OF ac'(1) ext(1)])
  qed (use that(2) in \<open>auto simp: W'_def\<close>)
  show thesis by (rule that[OF pinv ht[OF s2] ht[OF t2]]) (auto simp: X0_def)
qed

end

end
