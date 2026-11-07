section \<open>Acyclic Environments\<close>

theory Pattern_Acyclic
  imports Pattern_Vars
begin

text \<open>
  \<^const>\<open>head_norm\<close>, \<^const>\<open>occurs\<close> and \<^const>\<open>unif\<close> diverge on cyclic environments. As
  \<^const>\<open>lookup\<close>, the dependencies between variables are by name: \<open>(y, x) \<in> dep env\<close> if \<open>y\<close>
  occurs in the binding of \<open>x\<close>. On acyclic environments, \<open>unf env t\<close> applies the bindings
  exhaustively.
\<close>

context pure_sig
begin

subsection \<open>Dependencies\<close>

definition dep :: "env \<Rightarrow> (indexname \<times> indexname) set" where
  "dep env = {(y, x). \<exists>U u. vt_lookup (tenv env) x = Some (U, u) \<and> y \<in> fst ` vars u}"

definition acyc :: "env \<Rightarrow> bool" where
  "acyc env \<longleftrightarrow> acyclic (dep env)"

lemma depI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> (y, T) \<in> vars u \<Longrightarrow> (y, x) \<in> dep env"
  unfolding dep_def by force

lemma depE:
  assumes "(y, x) \<in> dep env"
  obtains U u T where "vt_lookup (tenv env) x = Some (U, u)" "(y, T) \<in> vars u"
  using assms unfolding dep_def by force

lemma finite_vars [simp]: "finite (vars t)"
  by (induction t) auto

lemma finite_dep: "finite (dep env)"
proof -
  let ?D = "{x. vt_lookup (tenv env) x \<noteq> None}"
  have "dep env \<subseteq> (\<Union>x\<in>?D. (\<lambda>y. (y, x)) ` fst ` vars (snd (the (vt_lookup (tenv env) x))))"
    by (force simp: dep_def image_iff)
  moreover have "finite (\<Union>x\<in>?D. (\<lambda>y. (y, x)) ` fst ` vars (snd (the (vt_lookup (tenv env) x))))"
    using finite_vt_lookup[of "tenv env"] by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma wf_dep: "acyc env \<Longrightarrow> wf (dep env)"
  by (simp add: acyc_def finite_acyclic_wf finite_dep)

lemma dep_bound: "(y, x) \<in> (dep env)\<^sup>+ \<Longrightarrow> vt_lookup (tenv env) x \<noteq> None"
  by (induction rule: trancl_induct) (auto elim: depE)


subsection \<open>Unfolding\<close>

definition uval_step :: "env \<Rightarrow> (indexname \<Rightarrow> pterm option) \<Rightarrow> indexname \<Rightarrow> pterm option" where
  "uval_step env f x = (case vt_lookup (tenv env) x of
     Some (U, u) \<Rightarrow> Some (vsubst (\<lambda>y T. case f y of Some v \<Rightarrow> v | None \<Rightarrow> Var y T) u)
   | None \<Rightarrow> None)"

definition uval :: "env \<Rightarrow> indexname \<Rightarrow> pterm option" where
  "uval env = wfrec (dep env) (uval_step env)"

definition unf :: "env \<Rightarrow> pterm \<Rightarrow> pterm" where
  "unf env = vsubst (\<lambda>x T. case uval env x of Some v \<Rightarrow> v | None \<Rightarrow> Var x T)"

lemma adm_uval_step: "adm_wf (dep env) (uval_step env)"
  unfolding adm_wf_def
proof (intro allI impI)
  fix f g :: "indexname \<Rightarrow> pterm option" and x
  assume eq: "\<forall>y. (y, x) \<in> dep env \<longrightarrow> f y = g y"
  show "uval_step env f x = uval_step env g x"
  proof (cases "vt_lookup (tenv env) x")
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    have "vsubst (\<lambda>y T. case f y of Some v \<Rightarrow> v | None \<Rightarrow> Var y T) u =
        vsubst (\<lambda>y T. case g y of Some v \<Rightarrow> v | None \<Rightarrow> Var y T) u"
    proof (rule vsubst_cong)
      fix y T' assume "(y, T') \<in> vars u"
      then have "f y = g y" using eq depI[OF Some[unfolded b]] by blast
      then show "(case f y of Some v \<Rightarrow> v | None \<Rightarrow> Var y T') = (case g y of Some v \<Rightarrow> v | None \<Rightarrow> Var y T')"
        by simp
    qed
    with Some b show ?thesis by (simp add: uval_step_def)
  qed (simp add: uval_step_def)
qed

lemma vars_vsubst: "vars (vsubst \<sigma> t) = (\<Union>(x, T)\<in>vars t. vars (\<sigma> x T))"
  by (induction t) auto

lemma vars_unf: "vars (unf env t) = (\<Union>(y, T)\<in>vars t. vars (unf env (Var y T)))"
  by (simp add: unf_def vars_vsubst)

lemma unf_simps [simp]:
  "unf env (Abs a T t) = Abs a T (unf env t)"
  "unf env (s $ t) = unf env s $ unf env t"
  "unf env (Const c T) = Const c T"
  "unf env (Free y T) = Free y T"
  "unf env (Bound i) = Bound i"
  by (simp_all add: unf_def)

lemma unf_apps: "unf env (h \<degree>\<degree> ts) = unf env h \<degree>\<degree> map (unf env) ts"
  by (induction ts arbitrary: h) simp_all

context
  fixes env assumes ac: "acyc env"
begin

lemma uval_eq: "uval env x = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> Some (unf env u) | None \<Rightarrow> None)"
  unfolding uval_def
  by (subst wfrec_fixpoint[OF wf_dep[OF ac] adm_uval_step])
    (simp add: uval_step_def unf_def uval_def split: option.splits)

lemma unf_Var:
  "unf env (Var x T) = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> unf env u | None \<Rightarrow> Var x T)"
  by (simp add: unf_def uval_eq[unfolded unf_def] split: option.splits)

lemma dep_induct: "(\<And>x. (\<And>y. (y, x) \<in> dep env \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P x"
  by (rule wf_induct_rule[OF wf_dep[OF ac]]) blast

text \<open>The variables of an unfolding are the unbound variables reachable from the term:\<close>

lemma vars_unf_Var:
  "fst ` vars (unf env (Var x T)) = {y. vt_lookup (tenv env) y = None \<and> (y, x) \<in> (dep env)\<^sup>*}"
proof (induction x arbitrary: T rule: dep_induct)
  case (1 x)
  show ?case
  proof (cases "vt_lookup (tenv env) x")
    case None
    have "y = x" if "(y, x) \<in> (dep env)\<^sup>*" for y
      using that by (rule rtranclE) (use None in \<open>auto elim: depE\<close>)
    with None show ?thesis by (auto simp: unf_Var)
  next
    case (Some b)
    obtain U u where b: "b = (U, u)" by force
    have IH: "fst ` vars (unf env (Var y T')) = {z. vt_lookup (tenv env) z = None \<and> (z, y) \<in> (dep env)\<^sup>*}"
      if "(y, T') \<in> vars u" for y T'
      using "1.IH"[OF depI[OF Some[unfolded b] that]] .
    have "fst ` vars (unf env (Var x T)) = (\<Union>(y, T')\<in>vars u. fst ` vars (unf env (Var y T')))"
      using Some b by (simp add: unf_Var vars_unf[of env u] image_UN split_def)
    also have "\<dots> = {z. vt_lookup (tenv env) z = None \<and> (z, x) \<in> (dep env)\<^sup>*}"
    proof (intro equalityI subsetI)
      fix z assume "z \<in> (\<Union>(y, T')\<in>vars u. fst ` vars (unf env (Var y T')))"
      then obtain y T' where yu: "(y, T') \<in> vars u" and "z \<in> fst ` vars (unf env (Var y T'))"
        by blast
      with IH[OF yu] have z: "vt_lookup (tenv env) z = None" "(z, y) \<in> (dep env)\<^sup>*" by auto
      have "(y, x) \<in> dep env" by (rule depI[OF Some[unfolded b] yu])
      with z show "z \<in> {z. vt_lookup (tenv env) z = None \<and> (z, x) \<in> (dep env)\<^sup>*}" by simp
    next
      fix z assume z: "z \<in> {z. vt_lookup (tenv env) z = None \<and> (z, x) \<in> (dep env)\<^sup>*}"
      then have "z \<noteq> x" using Some by auto
      with z obtain y where zy: "(z, y) \<in> (dep env)\<^sup>*" and "(y, x) \<in> dep env"
        by (auto elim: rtranclE)
      from this(2) obtain T' where yu: "(y, T') \<in> vars u"
        using Some b by (auto elim: depE)
      have "z \<in> fst ` vars (unf env (Var y T'))" using IH[OF yu] z zy by blast
      with yu show "z \<in> (\<Union>(y, T')\<in>vars u. fst ` vars (unf env (Var y T')))" by blast
    qed
    finally show ?thesis .
  qed
qed

text \<open>The variables of an unfolding are the unbound variables reachable from the term:\<close>

lemma vars_unf_name:
  "fst ` vars (unf env t) = {y. vt_lookup (tenv env) y = None \<and> (\<exists>x\<in>fst ` vars t. (y, x) \<in> (dep env)\<^sup>*)}"
proof -
  have "fst ` vars (unf env t) = (\<Union>(x, T)\<in>vars t. fst ` vars (unf env (Var x T)))"
    by (simp add: vars_unf[of env t] image_UN split_def)
  also have "\<dots> = (\<Union>(x, T)\<in>vars t. {y. vt_lookup (tenv env) y = None \<and> (y, x) \<in> (dep env)\<^sup>*})"
    by (simp add: vars_unf_Var split_def)
  also have "\<dots> = {y. vt_lookup (tenv env) y = None \<and> (\<exists>x\<in>fst ` vars t. (y, x) \<in> (dep env)\<^sup>*)}"
    by (auto simp: image_iff) (metis fst_conv)
  finally show ?thesis .
qed

end


subsection \<open>Ranks\<close>

text \<open>The rank of a variable is the number of variables its binding depends on, transitively.\<close>

definition rk :: "env \<Rightarrow> indexname \<Rightarrow> nat" where
  "rk env x = card {y. (y, x) \<in> (dep env)\<^sup>+}"

lemma rk_less: "acyc env \<Longrightarrow> (y, x) \<in> dep env \<Longrightarrow> rk env y < rk env x"
proof -
  assume ac: "acyc env" and yx: "(y, x) \<in> dep env"
  have fin: "finite {z. (z, x) \<in> (dep env)\<^sup>+}"
    by (rule finite_subset[of _ "fst ` (dep env)\<^sup>+"]) (force, simp add: finite_dep)
  have "{z. (z, y) \<in> (dep env)\<^sup>+} \<subset> {z. (z, x) \<in> (dep env)\<^sup>+}"
  proof
    show "{z. (z, y) \<in> (dep env)\<^sup>+} \<subseteq> {z. (z, x) \<in> (dep env)\<^sup>+}" using yx by auto
    have "(y, y) \<notin> (dep env)\<^sup>+" using ac unfolding acyc_def acyclic_def by blast
    moreover have "(y, x) \<in> (dep env)\<^sup>+" using yx by blast
    ultimately show "{z. (z, y) \<in> (dep env)\<^sup>+} \<noteq> {z. (z, x) \<in> (dep env)\<^sup>+}" by blast
  qed
  then show ?thesis unfolding rk_def by (rule psubset_card_mono[OF fin])
qed

subsection \<open>Lookup and the occurs check\<close>

text \<open>
  The variables of a problem are consistent with the environment if their types have consistent
  sorts and agree with the types of their bindings, modulo the type environment. Then
  \<^const>\<open>lookup\<close> does not raise exceptions.
\<close>

definition vok :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vok env X \<longleftrightarrow> (\<forall>(x, T)\<in>X. tcons (tyenv env) T \<and>
    (\<forall>U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> tnorm (tyenv env) T = tnorm (tyenv env) U))"

lemma vok_mono: "vok env X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> vok env Y"
  unfolding vok_def by blast

lemma vokD:
  assumes "vok env X" "(x, T) \<in> X"
  shows "tcons (tyenv env) T"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tnorm (tyenv env) T = tnorm (tyenv env) U"
  using assms unfolding vok_def by blast+

lemma lookup_ok:
  assumes ac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
    and v: "vok env ({(x, T)} \<union> evars env)"
  shows "lookup env x T = return (map_option snd (vt_lookup (tenv env) x))"
proof (cases "vt_lookup (tenv env) x")
  case (Some b)
  obtain U u where b: "b = (U, u)" by force
  have "(x, U) \<in> evars env" using Some b by (simp add: evarsI)
  then have "tcons (tyenv env) U" using vokD(1)[OF v] by blast
  moreover have "tcons (tyenv env) T" "tnorm (tyenv env) T = tnorm (tyenv env) U"
    using vokD[OF v, of x T] Some b by auto
  ultimately show ?thesis using Some b by (simp add: lookup_def unified_ok[OF ac tc])
qed (simp add: lookup_def)

lemma vok_binding:
  "vok env (X \<union> evars env) \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> vok env (vars u \<union> evars env)"
  using evarsI2[of env x U u] by (auto intro: vok_mono)

lemma occurs_ok:
  assumes ac: "acyc env" and tac: "tacyc (tyenv env)" and tc: "tcons_env (tyenv env)"
  shows "vok env (vars t \<union> evars env) \<Longrightarrow> occurs F t env = return (F \<in> fst ` vars (unf env t))"
proof (induction t rule: wf_induct_rule[OF wf_inv_image[OF wf_lex_prod[OF wf_less_than wf_less_than],
    of "\<lambda>t. (size (unf env t), case t of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0)"]])
  case (1 t)
  note IH = "1.IH"[simplified, rule_format]
  show ?case
  proof (cases t)
    case (Var G T)
    have lk: "lookup env G T = return (map_option snd (vt_lookup (tenv env) G))"
      by (rule lookup_ok[OF tac tc vok_mono[OF "1.prems"]]) (auto simp: Var)
    show ?thesis
    proof (cases "vt_lookup (tenv env) G")
      case None
      then show ?thesis using lk Var by (subst occurs.simps) (simp add: unf_Var[OF ac])
    next
      case (Some b)
      obtain U u where b: "b = (U, u)" by force
      have u: "unf env (Var G T) = unf env u" using Some b by (simp add: unf_Var[OF ac])
      have "rank": "(case u of Var x T \<Rightarrow> Suc (rk env x) | _ \<Rightarrow> 0) < Suc (rk env G)"
      proof (cases u)
        case (Var y U')
        have "(y, G) \<in> dep env" using depI[OF Some[unfolded b], of y U'] Var by simp
        then show ?thesis using rk_less[OF ac] Var by simp
      qed simp_all
      have "occurs F u env = return (F \<in> fst ` vars (unf env u))"
        by (rule IH) (use u "rank" Var vok_binding[OF "1.prems" Some[unfolded b]] in simp_all)
      then show ?thesis using lk Var Some b u by (subst occurs.simps) simp
    qed
  next
    case (App t1 t2)
    have "occurs F t1 env = return (F \<in> fst ` vars (unf env t1))"
      by (rule IH) (use "1.prems" App in \<open>auto intro: vok_mono\<close>)
    moreover have "occurs F t2 env = return (F \<in> fst ` vars (unf env t2))"
      by (rule IH) (use "1.prems" App in \<open>auto intro: vok_mono\<close>)
    ultimately show ?thesis using App by (subst occurs.simps) (auto simp: image_Un)
  next
    case (Abs a T u)
    have "occurs F u env = return (F \<in> fst ` vars (unf env u))"
      by (rule IH) (use "1.prems" Abs in \<open>auto intro: vok_mono\<close>)
    then show ?thesis using Abs by (subst occurs.simps) simp
  qed (subst occurs.simps, simp)+
qed


subsection \<open>New bindings\<close>

lemma rtrancl_Un_into: "(F, y) \<in> (r \<union> Y \<times> {F})\<^sup>* \<Longrightarrow> (F, y) \<in> r\<^sup>*"
  by (induction rule: rtrancl_induct) auto

lemma trancl_Un_into:
  "(a, b) \<in> (r \<union> Y \<times> {F})\<^sup>+ \<Longrightarrow> (a, b) \<in> r\<^sup>+ \<or> (\<exists>y\<in>Y. (a, y) \<in> (r \<union> Y \<times> {F})\<^sup>* \<and> (F, b) \<in> (r \<union> Y \<times> {F})\<^sup>*)"
proof (induction rule: trancl_induct)
  case (base c)
  then show ?case by auto
next
  case (step c d)
  from step.IH show ?case
  proof
    assume ac: "(a, c) \<in> r\<^sup>+"
    show ?thesis
    proof (cases "(c, d) \<in> r")
      case True
      with ac show ?thesis by (blast intro: trancl_into_trancl)
    next
      case False
      with step.hyps(2) have "c \<in> Y" "d = F" by auto
      moreover have "(a, c) \<in> (r \<union> Y \<times> {F})\<^sup>*"
        using trancl_mono[OF ac, of "r \<union> Y \<times> {F}"] by (auto intro: trancl_into_rtrancl)
      ultimately show ?thesis by auto
    qed
  next
    assume "\<exists>y\<in>Y. (a, y) \<in> (r \<union> Y \<times> {F})\<^sup>* \<and> (F, c) \<in> (r \<union> Y \<times> {F})\<^sup>*"
    with step.hyps(2) show ?thesis by (meson rtrancl.rtrancl_into_rtrancl)
  qed
qed

lemma acyclic_Un_target:
  assumes "acyclic r" "\<forall>y\<in>Y. (F, y) \<notin> r\<^sup>*"
  shows "acyclic (r \<union> Y \<times> {F})"
  unfolding acyclic_def
proof (intro allI notI)
  fix a assume "(a, a) \<in> (r \<union> Y \<times> {F})\<^sup>+"
  from trancl_Un_into[OF this] show False
  proof
    assume "(a, a) \<in> r\<^sup>+"
    with assms(1) show False by (simp add: acyclic_def)
  next
    assume "\<exists>y\<in>Y. (a, y) \<in> (r \<union> Y \<times> {F})\<^sup>* \<and> (F, a) \<in> (r \<union> Y \<times> {F})\<^sup>*"
    then obtain y where "y \<in> Y" "(F, y) \<in> (r \<union> Y \<times> {F})\<^sup>*" by (meson rtrancl_trans)
    with assms(2) rtrancl_Un_into[of F y r Y] show False by simp
  qed
qed

lemma dep_update:
  "ok (update (F, T) u env) env' \<Longrightarrow> dep env' = dep env \<union> fst ` vars u \<times> {F}"
  using ok_update(1,2)[of F T u env env'] unfolding dep_def by auto

text \<open>A new binding keeps the environment acyclic if its variable is not reachable from it.\<close>

lemma acyc_update:
  assumes "ok (update (F, T) u env) env'" "acyc env" "\<And>y U. (y, U) \<in> vars u \<Longrightarrow> (F, y) \<notin> (dep env)\<^sup>*"
  shows "acyc env'"
  unfolding acyc_def dep_update[OF assms(1)]
  by (rule acyclic_Un_target) (use assms(2,3) in \<open>auto simp: acyc_def\<close>)

lemma acyc_genvar: "genvar a env T = (env', G) \<Longrightarrow> acyc env' \<longleftrightarrow> acyc env"
  by (simp add: acyc_def dep_def genvar_simps)

end

end
