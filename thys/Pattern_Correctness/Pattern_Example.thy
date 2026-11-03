section \<open>Examples\<close>

theory Pattern_Example
  imports Pattern_Unify_Correctness
begin

text \<open>
  We apply the results of theory \<^theory>\<open>Pattern_Correctness.Pattern_Unify_Correctness\<close> to five
  problems in the empty environment, for an arbitrary well-formed algebra and a signature that
  declares every constant (other than those of Pure's logic) with the most general type. The
  base types are the free type variables \<open>i\<close> and \<open>o\<close> of the empty sort. The examples show that
  the hypotheses \<^const>\<open>pure_sig.uinv\<close> of the results are satisfiable and that the results give
  the expected outcomes.
  \<^item> \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close> is a unifiable pattern problem, so \<^const>\<open>unify\<close> returns an
    environment (of patterns);
  \<^item> \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>, where \<open>P\<close> is used at the types \<open>'a \<Rightarrow> o\<close> and \<open>i \<Rightarrow> o\<close> for a schematic type
    variable \<open>'a\<close>: \<^const>\<open>unify\<close> returns an environment, and every certified solution of it
    instantiates \<open>'a\<close> to \<open>i\<close>;
  \<^item> \<open>?Z =?= g ?Z\<close> is a pattern problem that is not unifiable (occurs check), so \<^const>\<open>unify\<close>
    fails with \<open>Unif\<close>;
  \<^item> \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>, where \<open>'b\<close> has sort \<open>{cls}\<close> for a declared class \<open>cls\<close>: as \<open>i\<close> does not have sort
    \<open>{cls}\<close>, the problem is not unifiable, so \<^const>\<open>unify\<close> fails with \<open>Unif\<close>;
  \<^item> \<open>?F a =?= b\<close> is not a pattern problem; \<^const>\<open>unify\<close> gives up with \<open>Pattern\<close>, although the
    problem is unifiable. The results cannot force this outcome, so we evaluate \<^const>\<open>unify\<close>.
\<close>

locale ex_sig = pure_sig +
  assumes ctab_any: "ctab c = Some (TVar (STR ''a'', 0) [])"
begin

abbreviation \<iota> :: ptyp where "\<iota> \<equiv> TFree STR ''i'' []"
abbreviation \<kappa> :: ptyp where "\<kappa> \<equiv> TFree STR ''o'' []"

subsection \<open>The signature and the empty environment\<close>

text \<open>The constants of the problems are not those of Pure's logic; they have every type.\<close>

lemma const_typ_ok_other [simp]:
  "c \<noteq> STR ''Pure.imp'' \<Longrightarrow> c \<noteq> STR ''Pure.all'' \<Longrightarrow> const_typ_ok ctab c T"
  by (auto simp: const_typ_ok_def ctab_any intro!: exI[of _ "\<lambda>_ _. T"])

lemma cert_typ_simps [simp]:
  "cert_typ alg ar (T \<rightarrow>\<^sub>T U) \<longleftrightarrow> cert_typ alg ar T \<and> cert_typ alg ar U"
  "cert_typ alg ar (TFree a [])"
  by (auto simp: cert_typ_def tarity_def sort_ok_def)

definition env0 :: env where "env0 = Envir 0 vt_empty vt_empty"

lemma vt_is_empty_vt_empty [simp]: "vt_is_empty vt_empty"
  by transfer simp

lemma env0_simps [simp]:
  "maxidx env0 = 0" "tenv env0 = vt_empty" "tyenv env0 = vt_empty"
  "bnds env0 = {}" "evars env0 = {}" "tvars_env vt_empty = {}"
  by (simp_all add: env0_def bnds_def evars_def tvars_env_def)

lemma env_ppat_env0: "env_ppat env0"
  by (simp add: env_ppat_def)

text \<open>The hypotheses of the results for problems in the empty environment:\<close>

lemma uinv_env0:
  assumes A: "finite A" "scons A" "\<forall>p\<in>A. snd (fst p) \<le> 0" "tcert alg A"
    and X: "\<And>\<rho>. vcons \<rho> (vars s \<union> vars t)" "below 0 (vars s \<union> vars t)"
    and tv: "ttvars s \<union> ttvars t \<subseteq> A" and cl: "closed s" "closed t"
    and ty: "\<And>\<rho>. cert_inst \<rho> \<Longrightarrow> \<exists>e T. e \<turnstile> inst \<rho> s : T \<and> e \<turnstile> inst \<rho> t : T"
  shows "uinv A env0 s t"
proof -
  have "tvinv A env0" using A by (simp add: tvinv_def tinv_def tacyc_empty)
  moreover have "acyc env0" by (simp add: acyc_def dep_def acyclic_def)
  moreover have "winv env0 (vars s \<union> vars t)" using X by (simp add: winv_def wt_env_def vinv_def)
  ultimately show ?thesis using A tv cl ty
    by (simp add: uinv_def scert_def tsorted_empty)
qed

text \<open>Solutions of problems in the empty environment:\<close>

lemma unifiable_env0I:
  assumes "wsinst alg \<rho>" "wt_subst \<sigma>" "vcons \<rho> (vars s \<union> vars t)" "below 0 (vars s \<union> vars t)"
    "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T" "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  shows "unifiable env0 s t"
  unfolding unifiable_def
  using assms by (intro exI[of _ \<rho>] exI[of _ \<sigma>] exI[of _ e] exI[of _ T])
    (simp add: solution_def tsol_def wt_env_def vinv_def)

lemma unifiable_env0D:
  assumes "unifiable env0 s t"
  obtains \<rho> \<sigma> e T where "wsinst alg \<rho>" "wt_subst \<sigma>" "e \<turnstile> inst \<rho> s : T" "e \<turnstile> inst \<rho> t : T"
    "ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  using assms unfolding unifiable_def solution_def by blast

text \<open>
  The type instantiation that maps every type variable to \<open>i\<close> is well-sorted, and substitutions
  that map one variable to a closed term of its type and the others to constants are
  well-typed.
\<close>

definition \<rho>\<^sub>i :: tinst where "\<rho>\<^sub>i = (\<lambda>v S. TFree STR ''i'' S)"

lemma wsinst_\<rho>\<^sub>i: "wsinst alg \<rho>\<^sub>i"
  by (simp add: wsinst_def \<rho>\<^sub>i_def) (blast intro: class_le_refl)

definition sbind :: "indexname \<Rightarrow> ptyp \<Rightarrow> pterm \<Rightarrow> vsubst" where
  "sbind x U u = (\<lambda>y V. if y = x \<and> V = U then u else Const STR ''d'' V)"

lemma wt_subst_sbind:
  assumes "closed u" "\<And>e. e \<turnstile> u : U"
  shows "wt_subst (sbind x U u)"
  unfolding wt_subst_def closed_subst_def
proof (intro conjI allI impI)
  fix y V
  show "closed (sbind x U u y V)" using assms(1) by (simp add: sbind_def closed_def)
  assume "cert_typ alg ar V"
  then show "\<exists>e. e \<turnstile> sbind x U u y V : V" using assms(2) by (auto simp: sbind_def)
qed

subsection \<open>Success: \<open>\<lambda>x. ?F x =?= \<lambda>x. f x x\<close>\<close>

definition f :: pterm where "f = Const STR ''f'' (\<iota> \<rightarrow>\<^sub>T \<iota> \<rightarrow>\<^sub>T \<iota>)"
definition F :: indexname where "F = (STR ''F'', 0)"

definition s\<^sub>1 :: pterm where "s\<^sub>1 = Abs STR ''x'' \<iota> (Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ Bound 0)"
definition t\<^sub>1 :: pterm where "t\<^sub>1 = Abs STR ''x'' \<iota> (f $ Bound 0 $ Bound 0)"

lemma uinv\<^sub>1: "uinv {} env0 s\<^sub>1 t\<^sub>1"
proof (rule uinv_env0)
  fix \<rho> :: tinst
  show "vcons \<rho> (vars s\<^sub>1 \<union> vars t\<^sub>1)" by (simp add: vcons_def s\<^sub>1_def t\<^sub>1_def f_def)
  show "\<exists>e T. e \<turnstile> inst \<rho> s\<^sub>1 : T \<and> e \<turnstile> inst \<rho> t\<^sub>1 : T"
    by (intro exI[of _ "\<lambda>_. \<iota>"] exI[of _ "\<iota> \<rightarrow>\<^sub>T \<iota>"] conjI) (auto simp: s\<^sub>1_def t\<^sub>1_def f_def)
qed (auto simp: below_def ttvars_def closed_def s\<^sub>1_def t\<^sub>1_def f_def F_def scons_def)

lemma patterns\<^sub>1: "ppat s\<^sub>1" "ppat t\<^sub>1"
proof -
  show "ppat s\<^sub>1"
    using ppat_flex[of "[0]" F "\<iota> \<rightarrow>\<^sub>T \<iota>"] by (auto simp: s\<^sub>1_def app_def intro: ppat_Abs)
  have "ppat (f \<degree>\<degree> [Bound 0, Bound 0])" by (rule ppat_rigid) (auto simp: f_def intro: ppat_atom)
  then show "ppat t\<^sub>1" by (auto simp: t\<^sub>1_def intro: ppat_Abs)
qed

text \<open>The substitution \<open>?F := \<lambda>y. f y y\<close> unifies the terms.\<close>

lemma unifiable\<^sub>1: "unifiable env0 s\<^sub>1 t\<^sub>1"
proof -
  let ?u = "Abs STR ''y'' \<iota> (f $ Bound 0 $ Bound 0)"
  let ?\<sigma> = "sbind F (\<iota> \<rightarrow>\<^sub>T \<iota>) ?u"
  have \<sigma>: "wt_subst ?\<sigma>" by (rule wt_subst_sbind) (auto simp: closed_def f_def)
  have "ap \<rho>\<^sub>i ?\<sigma> s\<^sub>1 \<rightarrow>\<^sub>\<beta> ap \<rho>\<^sub>i ?\<sigma> t\<^sub>1"
  proof -
    have "Abs STR ''x'' \<iota> (?u $ Bound 0) \<rightarrow>\<^sub>\<beta> Abs STR ''x'' \<iota> ((f $ Bound 0 $ Bound 0)[Bound 0/0])"
      by (intro beta.abs beta.beta)
    then show ?thesis by (simp add: ap_def s\<^sub>1_def t\<^sub>1_def sbind_def \<rho>\<^sub>i_def f_def)
  qed
  moreover have "wt (ap \<rho>\<^sub>i ?\<sigma> s\<^sub>1)"
    unfolding wt_def
    by (intro exI[of _ "\<lambda>_. \<iota>"] exI[of _ "\<iota> \<rightarrow>\<^sub>T \<iota>"]) (force simp: ap_def s\<^sub>1_def sbind_def \<rho>\<^sub>i_def f_def)
  ultimately have cv: "ap \<rho>\<^sub>i ?\<sigma> s\<^sub>1 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>\<^sub>i ?\<sigma> t\<^sub>1" by (blast intro: beta_eta_conv)
  show ?thesis
    by (rule unifiable_env0I[where e = "\<lambda>_. \<iota>" and T = "\<iota> \<rightarrow>\<^sub>T \<iota>", OF wsinst_\<rho>\<^sub>i \<sigma> _ _ _ _ cv])
      (force simp: vcons_def below_def s\<^sub>1_def t\<^sub>1_def f_def F_def \<rho>\<^sub>i_def)+
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>, by @{thm [source] decides}; it binds
  patterns only, by @{thm [source] unify_ppat}.
\<close>

theorem example_Ok\<^sub>1:
  obtains env' where "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" "env_ppat env'"
proof -
  from decides(1)[OF uinv\<^sub>1 patterns\<^sub>1 env_ppat_env0] unifiable\<^sub>1 obtain env'
    where un: "unify alg s\<^sub>1 t\<^sub>1 env0 = Some (Ok env')" by blast
  have "env_ppat env'"
    using unify_ppat(2)[OF un patterns\<^sub>1 env_ppat_env0] uinvD(9,10)[OF uinv\<^sub>1]
    by (simp add: closed_env_def env_nonneg_def s\<^sub>1_def t\<^sub>1_def f_def)
  with un show thesis by (rule that)
qed

subsection \<open>Success with types: \<open>P\<^sub>'\<^sub>a ?X =?= P\<^sub>i c\<close>\<close>

abbreviation \<alpha> :: ptyp where "\<alpha> \<equiv> TVar (STR ''a'', 0) []"

definition c :: pterm where "c = Const STR ''c'' \<iota>"
definition X :: indexname where "X = (STR ''X'', 0)"

definition s\<^sub>2 :: pterm where "s\<^sub>2 = Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>) $ Var X \<alpha>"
definition t\<^sub>2 :: pterm where "t\<^sub>2 = Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

lemma typing\<^sub>2:
  assumes "cert_typ alg ar (\<rho> (STR ''a'', 0) [])"
  shows "e \<turnstile> inst \<rho> s\<^sub>2 : \<kappa>" "e \<turnstile> inst \<rho> t\<^sub>2 : \<kappa>"
  using assms by (force simp: s\<^sub>2_def t\<^sub>2_def c_def)+

lemma uinv\<^sub>2: "uinv {((STR ''a'', 0), [])} env0 s\<^sub>2 t\<^sub>2"
proof (rule uinv_env0)
  fix \<rho> :: tinst
  show "vcons \<rho> (vars s\<^sub>2 \<union> vars t\<^sub>2)" by (simp add: vcons_def s\<^sub>2_def t\<^sub>2_def c_def)
  assume "cert_inst \<rho>"
  then have "cert_typ alg ar (\<rho> (STR ''a'', 0) [])" by (simp add: cert_inst_def sort_ok_def)
  with typing\<^sub>2 show "\<exists>e T. e \<turnstile> inst \<rho> s\<^sub>2 : T \<and> e \<turnstile> inst \<rho> t\<^sub>2 : T" by blast
qed (auto simp: below_def ttvars_def closed_def s\<^sub>2_def t\<^sub>2_def c_def X_def scons_def sort_ok_def)

lemma patterns\<^sub>2: "ppat s\<^sub>2" "ppat t\<^sub>2"
proof -
  have "ppat (Var X \<alpha>)" using ppat_flex[of "[]" X \<alpha>] by (simp add: app_def)
  then have "ppat (Const STR ''P'' (\<alpha> \<rightarrow>\<^sub>T \<kappa>) \<degree>\<degree> [Var X \<alpha>])" by (intro ppat_rigid) auto
  then show "ppat s\<^sub>2" by (simp add: s\<^sub>2_def)
  have "ppat (Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) \<degree>\<degree> [c])" by (intro ppat_rigid) (auto simp: c_def intro: ppat_atom)
  then show "ppat t\<^sub>2" by (simp add: t\<^sub>2_def)
qed

text \<open>The instance \<open>'a := i\<close> with \<open>?X := c\<close> is a unifier.\<close>

lemma unifiable\<^sub>2: "unifiable env0 s\<^sub>2 t\<^sub>2"
proof -
  let ?\<sigma> = "sbind X \<iota> c"
  have \<sigma>: "wt_subst ?\<sigma>" by (rule wt_subst_sbind) (auto simp: closed_def c_def)
  have cv: "ap \<rho>\<^sub>i ?\<sigma> s\<^sub>2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>\<^sub>i ?\<sigma> t\<^sub>2"
    by (simp add: ap_def s\<^sub>2_def t\<^sub>2_def sbind_def \<rho>\<^sub>i_def c_def)
  show ?thesis
    by (rule unifiable_env0I[where e = "\<lambda>_. \<iota>" and T = \<kappa>, OF wsinst_\<rho>\<^sub>i \<sigma> _ _ typing\<^sub>2 cv])
      (auto simp: vcons_def below_def s\<^sub>2_def t\<^sub>2_def c_def X_def \<rho>\<^sub>i_def)
qed

text \<open>
  Hence \<^const>\<open>unify\<close> returns an environment \<open>env'\<close>; by soundness
  (@{thm [source] unify_sound}), every certified solution of \<open>env'\<close> unifies the heads, so it
  instantiates \<open>'a\<close> to \<open>i\<close>.
\<close>

theorem example_Ok\<^sub>2:
  obtains env' where "unify alg s\<^sub>2 t\<^sub>2 env0 = Some (Ok env')"
    and "\<And>\<rho> \<sigma>. solution \<rho> \<sigma> env' \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> \<rho> (STR ''a'', 0) [] = \<iota>"
proof -
  from decides(1)[OF uinv\<^sub>2 patterns\<^sub>2 env_ppat_env0] unifiable\<^sub>2 obtain env'
    where un: "unify alg s\<^sub>2 t\<^sub>2 env0 = Some (Ok env')" by blast
  show thesis
  proof (rule that[OF un])
    fix \<rho> \<sigma> assume sol: "solution \<rho> \<sigma> env'" and ci: "cert_inst \<rho>"
    then have a: "cert_typ alg ar (\<rho> (STR ''a'', 0) [])" by (simp add: cert_inst_def sort_ok_def)
    have "wt_env \<rho> env0" "vinv \<rho> env0 (vars s\<^sub>2 \<union> vars t\<^sub>2)"
      by (auto simp: wt_env_def vinv_def vcons_def below_def s\<^sub>2_def t\<^sub>2_def c_def X_def)
    from unify_sound(2)[OF un sol this(1) typing\<^sub>2[where \<rho> = \<rho>, OF a] this(2)] uinvD(9,10)[OF uinv\<^sub>2]
    have cv: "ap \<rho> \<sigma> s\<^sub>2 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t\<^sub>2" by blast
    have "wt (ap \<rho> \<sigma> s\<^sub>2)"
      using typing_vsubst[OF typing\<^sub>2(1)[where \<rho> = \<rho> and e = "\<lambda>_. \<iota>", OF a] solutionD(3)[OF sol]]
      by (auto simp: wt_def ap_def)
    with cv have "Const STR ''P'' (\<rho> (STR ''a'', 0) [] \<rightarrow>\<^sub>T \<kappa>) = Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)"
      using conv_atom_apps_inv(1)[of "Const STR ''P'' (\<rho> (STR ''a'', 0) [] \<rightarrow>\<^sub>T \<kappa>)"
          "Const STR ''P'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)" "[\<sigma> X (\<rho> (STR ''a'', 0) [])]" "[c]"]
      by (simp add: ap_def s\<^sub>2_def t\<^sub>2_def c_def)
    then show "\<rho> (STR ''a'', 0) [] = \<iota>" by simp
  qed
qed

subsection \<open>Failure by the occurs check: \<open>?Z =?= g ?Z\<close>\<close>

definition g :: pterm where "g = Const STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>)"
definition Z :: indexname where "Z = (STR ''Z'', 0)"

definition s\<^sub>3 :: pterm where "s\<^sub>3 = Var Z \<iota>"
definition t\<^sub>3 :: pterm where "t\<^sub>3 = g $ Var Z \<iota>"

lemma uinv\<^sub>3: "uinv {} env0 s\<^sub>3 t\<^sub>3"
proof (rule uinv_env0)
  fix \<rho> :: tinst
  show "vcons \<rho> (vars s\<^sub>3 \<union> vars t\<^sub>3)" by (simp add: vcons_def s\<^sub>3_def t\<^sub>3_def g_def)
  show "\<exists>e T. e \<turnstile> inst \<rho> s\<^sub>3 : T \<and> e \<turnstile> inst \<rho> t\<^sub>3 : T"
    by (intro exI[of _ "\<lambda>_. \<iota>"] exI[of _ \<iota>] conjI) (force simp: s\<^sub>3_def t\<^sub>3_def g_def)+
qed (auto simp: below_def ttvars_def closed_def s\<^sub>3_def t\<^sub>3_def g_def Z_def scons_def)

lemma patterns\<^sub>3: "ppat s\<^sub>3" "ppat t\<^sub>3"
proof -
  show "ppat s\<^sub>3" using ppat_flex[of "[]" Z \<iota>] by (simp add: s\<^sub>3_def app_def)
  then have "ppat (g \<degree>\<degree> [Var Z \<iota>])" by (intro ppat_rigid) (auto simp: s\<^sub>3_def g_def)
  then show "ppat t\<^sub>3" by (simp add: t\<^sub>3_def)
qed

text \<open>
  A solution would satisfy \<open>\<sigma> ?Z \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> g (\<sigma> ?Z)\<close>. As \<open>\<sigma> ?Z\<close> is well-typed, it has a normal
  form \<open>w\<close>; then \<open>g w\<close> is normal too, and both normal forms would be \<open>\<alpha>\<close>-equivalent.
\<close>

lemma normal_Const_App: "normal w \<Longrightarrow> normal (Const a T $ w)"
  by (auto simp: normal_def)

lemma not_conv_Const_App:
  assumes "e \<turnstile> w : U"
  shows "\<not> w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Const a T $ w"
proof
  assume cv: "w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Const a T $ w"
  obtain n where n: "w \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* n" "normal n" using normal_form_ex[OF assms] by blast
  have wt: "wt w" using assms by (auto simp: wt_def)
  then have wt': "wt (Const a T $ w)" using wt_conv[OF cv] by blast
  have "n \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> w" by (rule conv_sym[OF beta_eta_conv[OF n(1) wt]])
  also note cv
  also have "Const a T $ w \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Const a T $ n"
    by (rule beta_eta_conv[OF rtrancl_beta_eta_AppR[OF n(1)] wt'])
  finally have cn: "n \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Const a T $ n" .
  have "wt n" using wt_conv[OF beta_eta_conv[OF n(1) wt]] wt by blast
  from church_rosser[OF this cn] obtain u v where
    uv: "n \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" "Const a T $ n \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* v" "aconv_term u v" by blast
  have "u = n" "v = Const a T $ n"
    using normal_reds[OF uv(1) n(2)] normal_reds[OF uv(2) normal_Const_App[OF n(2)]] by simp_all
  with uv(3) have "unname n = Const a T $ unname n" by (simp add: aconv_term_unname)
  then have "size (unname n) = size (Const a T $ unname n)" by (rule arg_cong)
  then show False by simp
qed

lemma not_unifiable\<^sub>3: "\<not> unifiable env0 s\<^sub>3 t\<^sub>3"
proof
  assume "unifiable env0 s\<^sub>3 t\<^sub>3"
  then obtain \<rho> \<sigma> where \<sigma>: "wt_subst \<sigma>" and cv: "ap \<rho> \<sigma> s\<^sub>3 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t\<^sub>3"
    by (rule unifiable_env0D)
  have "(\<lambda>_. \<iota>) \<turnstile> \<sigma> Z \<iota> : \<iota>" by (rule wt_subst_typing[OF \<sigma>]) simp
  moreover have "\<sigma> Z \<iota> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Const STR ''g'' (\<iota> \<rightarrow>\<^sub>T \<iota>) $ \<sigma> Z \<iota>"
    using cv by (simp add: ap_def s\<^sub>3_def t\<^sub>3_def g_def)
  ultimately show False using not_conv_Const_App by blast
qed

text \<open>Hence \<^const>\<open>unify\<close> fails with \<open>Unif\<close>, by @{thm [source] decides}.\<close>

theorem example_Unif\<^sub>3: "\<exists>u. unify alg s\<^sub>3 t\<^sub>3 env0 = Some (Err (Unif u))"
  using decides(2)[OF uinv\<^sub>3 patterns\<^sub>3 env_ppat_env0] not_unifiable\<^sub>3 by blast

subsection \<open>Failure by sorts: \<open>Q\<^sub>'\<^sub>b ?Y =?= Q\<^sub>i c\<close>\<close>

definition \<beta> :: "pclass \<Rightarrow> ptyp" where "\<beta> cls = TVar (STR ''b'', 0) [cls]"

definition Y :: indexname where "Y = (STR ''Y'', 0)"

definition s\<^sub>4 :: "pclass \<Rightarrow> pterm" where "s\<^sub>4 cls = Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>) $ Var Y (\<beta> cls)"
definition t\<^sub>4 :: pterm where "t\<^sub>4 = Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) $ c"

lemma typing\<^sub>4:
  assumes "cert_typ alg ar (\<rho> (STR ''b'', 0) [cls])"
  shows "e \<turnstile> inst \<rho> (s\<^sub>4 cls) : \<kappa>" "e \<turnstile> inst \<rho> t\<^sub>4 : \<kappa>"
  using assms by (force simp: s\<^sub>4_def t\<^sub>4_def c_def \<beta>_def)+

text \<open>The class \<open>cls\<close> must be declared for the problem to be well-formed.\<close>

lemma uinv\<^sub>4:
  assumes "cls \<in> classes alg"
  shows "uinv {((STR ''b'', 0), [cls])} env0 (s\<^sub>4 cls) t\<^sub>4"
proof (rule uinv_env0)
  fix \<rho> :: tinst
  show "vcons \<rho> (vars (s\<^sub>4 cls) \<union> vars t\<^sub>4)" by (simp add: vcons_def s\<^sub>4_def t\<^sub>4_def c_def)
  assume "cert_inst \<rho>"
  then have "cert_typ alg ar (\<rho> (STR ''b'', 0) [cls])" using assms by (simp add: cert_inst_def sort_ok_def)
  with typing\<^sub>4 show "\<exists>e T. e \<turnstile> inst \<rho> (s\<^sub>4 cls) : T \<and> e \<turnstile> inst \<rho> t\<^sub>4 : T" by blast
qed (use assms in \<open>auto simp: below_def ttvars_def closed_def s\<^sub>4_def t\<^sub>4_def c_def \<beta>_def Y_def
  scons_def sort_ok_def\<close>)

lemma patterns\<^sub>4: "ppat (s\<^sub>4 cls)" "ppat t\<^sub>4"
proof -
  have "ppat (Var Y (\<beta> cls))" using ppat_flex[of "[]" Y "\<beta> cls"] by (simp add: app_def)
  then have "ppat (Const STR ''Q'' (\<beta> cls \<rightarrow>\<^sub>T \<kappa>) \<degree>\<degree> [Var Y (\<beta> cls)])" by (intro ppat_rigid) auto
  then show "ppat (s\<^sub>4 cls)" by (simp add: s\<^sub>4_def)
  have "ppat (Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>) \<degree>\<degree> [c])" by (intro ppat_rigid) (auto simp: c_def intro: ppat_atom)
  then show "ppat t\<^sub>4" by (simp add: t\<^sub>4_def)
qed

text \<open>
  A unifier would identify the instances of the heads, so the instance of \<open>'b\<close> would be \<open>i\<close>,
  which does not have sort \<open>{cls}\<close>.
\<close>

lemma not_unifiable\<^sub>4: "\<not> unifiable env0 (s\<^sub>4 cls) t\<^sub>4"
proof
  assume "unifiable env0 (s\<^sub>4 cls) t\<^sub>4"
  then obtain \<rho> \<sigma> e T where \<rho>: "wsinst alg \<rho>" and \<sigma>: "wt_subst \<sigma>" and ty: "e \<turnstile> inst \<rho> (s\<^sub>4 cls) : T"
    and cv: "ap \<rho> \<sigma> (s\<^sub>4 cls) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t\<^sub>4"
    by (rule unifiable_env0D)
  let ?b = "\<rho> (STR ''b'', 0) [cls]"
  have "wt (ap \<rho> \<sigma> (s\<^sub>4 cls))" using typing_vsubst[OF ty \<sigma>] by (auto simp: wt_def ap_def)
  with cv have "Const STR ''Q'' (?b \<rightarrow>\<^sub>T \<kappa>) = Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)"
    using conv_atom_apps_inv(1)[of "Const STR ''Q'' (?b \<rightarrow>\<^sub>T \<kappa>)" "Const STR ''Q'' (\<iota> \<rightarrow>\<^sub>T \<kappa>)"
        "[\<sigma> Y ?b]" "[c]"]
    by (simp add: ap_def s\<^sub>4_def t\<^sub>4_def c_def \<beta>_def)
  then have "?b = \<iota>" by simp
  moreover have "has_sort alg ?b [cls]" using \<rho> by (simp add: wsinst_def del: has_sort.simps)
  ultimately show False by simp
qed

theorem example_Unif\<^sub>4:
  assumes "cls \<in> classes alg"
  shows "\<exists>u. unify alg (s\<^sub>4 cls) t\<^sub>4 env0 = Some (Err (Unif u))"
  using decides(2)[OF uinv\<^sub>4[OF assms] patterns\<^sub>4 env_ppat_env0] not_unifiable\<^sub>4 by blast

subsection \<open>Giving up: \<open>?F a =?= b\<close>\<close>

definition a :: pterm where "a = Const STR ''a'' \<iota>"
definition b :: pterm where "b = Const STR ''b'' \<iota>"

definition s\<^sub>5 :: pterm where "s\<^sub>5 = Var F (\<iota> \<rightarrow>\<^sub>T \<iota>) $ a"
definition t\<^sub>5 :: pterm where "t\<^sub>5 = b"

lemma uinv\<^sub>5: "uinv {} env0 s\<^sub>5 t\<^sub>5"
proof (rule uinv_env0)
  fix \<rho> :: tinst
  show "vcons \<rho> (vars s\<^sub>5 \<union> vars t\<^sub>5)" by (simp add: vcons_def s\<^sub>5_def t\<^sub>5_def a_def b_def)
  show "\<exists>e T. e \<turnstile> inst \<rho> s\<^sub>5 : T \<and> e \<turnstile> inst \<rho> t\<^sub>5 : T"
    by (intro exI[of _ "\<lambda>_. \<iota>"] exI[of _ \<iota>] conjI) (force simp: s\<^sub>5_def t\<^sub>5_def a_def b_def)+
qed (auto simp: below_def ttvars_def closed_def s\<^sub>5_def t\<^sub>5_def a_def b_def F_def scons_def)

text \<open>\<^const>\<open>unify\<close> gives up because the argument \<open>a\<close> of \<open>?F\<close> is not a bound variable.\<close>

lemma head_norm_env0:
  "head_norm env0 (Const n T) = return (Const n T)"
  "head_norm env0 (Var x T) = return (Var x T)"
  "head_norm env0 (Var x T $ u) = return (Var x T $ u)"
proof -
  show "head_norm env0 (Const n T) = return (Const n T)" by (subst head_norm.simps) simp
  show v: "head_norm env0 (Var x T) = return (Var x T)"
    by (subst head_norm.simps) (simp add: lookup_def)
  show "head_norm env0 (Var x T $ u) = return (Var x T $ u)"
    by (subst head_norm.simps) (simp add: v bindM_def return_def)
qed

theorem example_Pattern: "unify alg s\<^sub>5 t\<^sub>5 env0 = Some (Err Pattern)"
  unfolding unify_def s\<^sub>5_def t\<^sub>5_def a_def b_def
  by (subst unif.simps) (simp add: head_norm_env0 ints_of'_def strip_comb_def bindM_def return_def
    raise_def)

text \<open>
  This is consistent with @{thm [source] Pattern_not_pattern}: \<open>s\<^sub>5\<close> is not a pattern.
  Yet the problem is unifiable, by \<open>?F := \<lambda>x. b\<close>: giving up is not failure.
\<close>

lemma not_pattern\<^sub>5: "\<not> ppat s\<^sub>5"
  using Pattern_not_pattern[OF uinv\<^sub>5 example_Pattern] env_ppat_env0 ppat_atom[of t\<^sub>5]
  by (simp add: t\<^sub>5_def b_def)

lemma unifiable\<^sub>5: "unifiable env0 s\<^sub>5 t\<^sub>5"
proof -
  let ?\<sigma> = "sbind F (\<iota> \<rightarrow>\<^sub>T \<iota>) (Abs STR ''x'' \<iota> b)"
  have \<sigma>: "wt_subst ?\<sigma>" by (rule wt_subst_sbind) (auto simp: closed_def b_def)
  have "ap \<rho>\<^sub>i ?\<sigma> s\<^sub>5 \<rightarrow>\<^sub>\<beta> ap \<rho>\<^sub>i ?\<sigma> t\<^sub>5"
  proof -
    have "Abs STR ''x'' \<iota> b $ a \<rightarrow>\<^sub>\<beta> b[a/0]" by (rule beta.beta)
    then show ?thesis by (simp add: ap_def s\<^sub>5_def t\<^sub>5_def sbind_def \<rho>\<^sub>i_def a_def b_def)
  qed
  moreover have "wt (ap \<rho>\<^sub>i ?\<sigma> s\<^sub>5)"
    unfolding wt_def
    by (intro exI[of _ "\<lambda>_. \<iota>"] exI[of _ \<iota>]) (force simp: ap_def s\<^sub>5_def sbind_def \<rho>\<^sub>i_def a_def b_def)
  ultimately have cv: "ap \<rho>\<^sub>i ?\<sigma> s\<^sub>5 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>\<^sub>i ?\<sigma> t\<^sub>5" by (blast intro: beta_eta_conv)
  show ?thesis
    by (rule unifiable_env0I[where e = "\<lambda>_. \<iota>" and T = \<iota>, OF wsinst_\<rho>\<^sub>i \<sigma> _ _ _ _ cv])
      (force simp: vcons_def below_def s\<^sub>5_def t\<^sub>5_def a_def b_def F_def \<rho>\<^sub>i_def)+
qed

end

end
