section \<open>Semantics of Environments\<close>

theory Pattern_Semantics
  imports Pattern_Signature "Pure_Pattern.Pure_Pattern" "Pure_Lambda.Pure_Inversion"
begin

text \<open>
  A solution of an environment is a pair of a type instantiation \<open>\<rho>\<close> and a substitution \<open>\<sigma>\<close> of
  the schematic variables. \<open>\<rho>\<close> respects sorts and solves the type environment; \<open>\<sigma>\<close> maps
  variables of certified types to closed terms of their types. A schematic variable \<open>Var x T\<close> denotes
  \<open>\<sigma> x (\<rho> T)\<close>: as \<open>Envir.lookup\<close> compares types modulo the type environment, a variable is
  identified by its name and its instantiated type. The bindings of the environment hold
  modulo \<open>\<alpha>\<beta>\<eta>\<close>-equivalence.
\<close>

context pure_sig
begin

definition ap :: "tinst \<Rightarrow> vsubst \<Rightarrow> pterm \<Rightarrow> pterm" where
  "ap \<rho> \<sigma> t = vsubst \<sigma> (inst \<rho> t)"

definition solution :: "tinst \<Rightarrow> vsubst \<Rightarrow> env \<Rightarrow> bool" where
  "solution \<rho> \<sigma> env \<longleftrightarrow> wsinst alg \<rho> \<and> tsol (tyenv env) \<rho> \<and> wt_subst \<sigma> \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> \<sigma> x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u)"

text \<open>Solutions exist: the identity solves an empty environment.\<close>

lemma solutionD:
  assumes "solution \<rho> \<sigma> env"
  shows "wsinst alg \<rho>" "tsol (tyenv env) \<rho>" "wt_subst \<sigma>"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> \<sigma> x (tsubst \<rho> U) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  using assms unfolding solution_def by blast+


subsection \<open>Extensions of environments\<close>

text \<open>Unification only adds bindings, to the type and the term environment, and new variables.\<close>

definition extends :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "extends env env' \<longleftrightarrow> textends (tyenv env) (tyenv env') \<and>
    (\<forall>x b. vt_lookup (tenv env) x = Some b \<longrightarrow> vt_lookup (tenv env') x = Some b) \<and>
    maxidx env \<le> maxidx env'"

lemma extends_refl [simp]: "extends env env"
  by (simp add: extends_def textends_def)

lemma extends_trans: "extends env env' \<Longrightarrow> extends env' env'' \<Longrightarrow> extends env env''"
  unfolding extends_def textends_def by (meson order_trans)

lemma solution_extends: "solution \<rho> \<sigma> env' \<Longrightarrow> extends env env' \<Longrightarrow> solution \<rho> \<sigma> env"
  unfolding solution_def extends_def by (meson tsol_textends)

lemma extends_tsol: "tsol (tyenv env') \<rho> \<Longrightarrow> extends env env' \<Longrightarrow> tsol (tyenv env) \<rho>"
  unfolding extends_def by (meson tsol_textends)


subsection \<open>Typing modulo the type environment\<close>

text \<open>
  A term is well-typed in an environment if it is well-typed after normalizing its types by the
  type environment \<open>\<theta>\<close>; then its instances under the solutions of \<open>\<theta>\<close> are well-typed.
\<close>

abbreviation tnorm_inst :: "tyenv \<Rightarrow> tinst" where
  "tnorm_inst \<theta> \<equiv> \<lambda>v S. tnorm \<theta> (TVar v S)"

definition typed :: "env \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "typed env e t T \<longleftrightarrow>
    (\<lambda>i. tnorm (tyenv env) (e i)) \<turnstile> inst (tnorm_inst (tyenv env)) t : tnorm (tyenv env) T"

lemma tsubst_tnorm_inst:
  "tacyc \<theta> \<Longrightarrow> tcons_env \<theta> \<Longrightarrow> tsol \<theta> \<rho> \<Longrightarrow> tcons \<theta> U \<Longrightarrow>
    tsubst (\<lambda>v S. tsubst \<rho> (tnorm \<theta> (TVar v S))) U = tsubst \<rho> U"
proof -
  assume a: "tacyc \<theta>" "tcons_env \<theta>" "tsol \<theta> \<rho>" "tcons \<theta> U"
  have "tsubst (\<lambda>v S. tsubst \<rho> (tnorm \<theta> (TVar v S))) U = tsubst \<rho> (tsubst (tnorm_inst \<theta>) U)"
    by (simp only: tsubst_tsubst)
  also have "\<dots> = tsubst \<rho> (tnorm \<theta> U)" by (rule arg_cong[of _ _ "tsubst \<rho>"], rule tnorm_tsubst[symmetric])
  also have "\<dots> = tsubst \<rho> U" using tsubst_tnorm[OF a(1-3) a(4)] .
  finally show ?thesis .
qed


subsection \<open>Equations\<close>

text \<open>
  Flex-flex pairs are equations. \<open>eqv E e s t\<close>: the terms \<open>s\<close> and \<open>t\<close>, well-typed with the
  same type in the environment \<open>e\<close> of their loose bound variables, are equal by
  \<open>\<alpha>\<beta>\<eta>\<close>-conversion, congruence and the equations \<open>E\<close>; the schematic variables are not
  instantiated. Every substitution that solves the equations solves \<open>s = t\<close>
  (\<open>eqv_vsubst\<close>), and so does every interpretation in a model.
\<close>

inductive eqv :: "(pterm \<times> pterm) set \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" for E where
  eqv_ax: "(s, t) \<in> E \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> eqv E e s t"
| eqv_conv: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> e \<turnstile> s : T \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> eqv E e s t"
| eqv_sym: "eqv E e s t \<Longrightarrow> eqv E e t s"
| eqv_trans: "eqv E e s t \<Longrightarrow> eqv E e t u \<Longrightarrow> eqv E e s u"
| eqv_app: "eqv E e s s' \<Longrightarrow> eqv E e t t' \<Longrightarrow> e \<turnstile> s $ t : U \<Longrightarrow> e \<turnstile> s' $ t' : U \<Longrightarrow>
    eqv E e (s $ t) (s' $ t')"
| eqv_abs: "eqv E (e\<langle>0:T\<rangle>) s t \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> eqv E e (Abs a T s) (Abs b T t)"

lemma eqv_typing: "eqv E e s t \<Longrightarrow> \<exists>T. e \<turnstile> s : T \<and> e \<turnstile> t : T"
proof (induction rule: eqv.induct)
  case (eqv_trans e s t u)
  then show ?case by (metis typing_unique)
next
  case (eqv_app e s s' t t' U)
  then show ?case by blast
next
  case (eqv_abs e T s t a b)
  then show ?case by blast
qed blast+

lemma eqv_refl: "e \<turnstile> t : T \<Longrightarrow> eqv E e t t"
  by (rule eqv_conv) auto

lemma eqv_mono: "eqv E e s t \<Longrightarrow> E \<subseteq> E' \<Longrightarrow> eqv E' e s t"
  by (induction rule: eqv.induct) (auto intro: eqv.intros)

lemma eqv_vsubst:
  assumes "eqv E e s t" and \<sigma>: "wt_subst \<sigma>" and E: "\<And>l r. (l, r) \<in> E \<Longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r"
  shows "vsubst \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> t"
  using assms(1)
proof (induction rule: eqv.induct)
  case (eqv_conv s t e T)
  from conv_vsubst[OF eqv_conv.hyps(1) \<sigma>] show ?case .
next
  case (eqv_sym e s t)
  from conv_sym[OF eqv_sym.IH] show ?case .
next
  case (eqv_trans e s t u)
  from conv_trans[OF eqv_trans.IH] show ?case .
next
  case (eqv_app e s s' t t' U)
  have "wt (vsubst \<sigma> (s $ t))" "wt (vsubst \<sigma> (s' $ t'))"
    unfolding wt_def using typing_vsubst[OF eqv_app.hyps(3) \<sigma>] typing_vsubst[OF eqv_app.hyps(4) \<sigma>] by blast+
  with eqv_app.IH show ?case by (simp add: conv_App)
next
  case (eqv_abs e T s t a b)
  from eqv_typing[OF eqv_abs.hyps(1)] obtain U where "e\<langle>0:T\<rangle> \<turnstile> s : U" "e\<langle>0:T\<rangle> \<turnstile> t : U" by blast
  then have "e \<turnstile> Abs a T s : T \<rightarrow>\<^sub>T U" "e \<turnstile> Abs b T t : T \<rightarrow>\<^sub>T U" using eqv_abs.hyps(2) by auto
  then have "wt (vsubst \<sigma> (Abs a T s))" "wt (vsubst \<sigma> (Abs b T t))"
    unfolding wt_def using typing_vsubst[OF _ \<sigma>] by blast+
  with eqv_abs.IH show ?case by (simp add: conv_Abs)
qed (rule E)

lemma eqv_apps_head:
  "eqv E e f g \<Longrightarrow> e \<turnstile> f \<degree>\<degree> ts : T \<Longrightarrow> e \<turnstile> g \<degree>\<degree> ts : T \<Longrightarrow> eqv E e (f \<degree>\<degree> ts) (g \<degree>\<degree> ts)"
proof (induction ts arbitrary: f g)
  case (Cons t ts)
  from Cons.prems(2) obtain Us where f: "e \<turnstile> f : Us \<Rrightarrow> T" and "e \<tturnstile> t # ts : Us" by (elim list_app_typeE)
  then obtain U Us' where Us: "Us = U # Us'" and t: "e \<turnstile> t : U" by (cases Us) auto
  from eqv_typing[OF Cons.prems(1)] f have "e \<turnstile> g : Us \<Rrightarrow> T" by (metis typing_unique)
  with f t Us have "e \<turnstile> f $ t : Us' \<Rrightarrow> T" "e \<turnstile> g $ t : Us' \<Rrightarrow> T" by auto
  then have "eqv E e (f $ t) (g $ t)" using Cons.prems(1) t by (intro eqv_app[OF _ eqv_refl])
  with Cons.IH Cons.prems(2,3) show ?case by simp
qed simp

lemma eqv_apps:
  "list_all2 (eqv E e) ts us \<Longrightarrow> eqv E e f g \<Longrightarrow> e \<turnstile> f \<degree>\<degree> ts : T \<Longrightarrow> eqv E e (f \<degree>\<degree> ts) (g \<degree>\<degree> us)"
proof (induction arbitrary: f g rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons t ts u us)
  from Cons.prems(2) obtain Vs where f: "e \<turnstile> f : Vs \<Rrightarrow> T" and "e \<tturnstile> t # ts : Vs" by (elim list_app_typeE)
  then obtain V Vs' where Vs: "Vs = V # Vs'" and t: "e \<turnstile> t : V" and ts: "e \<tturnstile> ts : Vs'" by (cases Vs) auto
  from eqv_typing[OF Cons.prems(1)] f have g: "e \<turnstile> g : Vs \<Rrightarrow> T" by (metis typing_unique)
  from eqv_typing[OF Cons.hyps(1)] t have u: "e \<turnstile> u : V" by (metis typing_unique)
  have "eqv E e (f $ t) (g $ u)"
    using Cons.prems(1) Cons.hyps(1) f g t u Vs by (intro eqv_app) auto
  moreover have "e \<turnstile> (f $ t) \<degree>\<degree> ts : T" using f t ts Vs by (auto intro: list_app_typeI)
  ultimately show ?case using Cons.IH by simp
qed

text \<open>The bindings of an environment as equations, at a type instantiation \<open>\<rho>\<close>:\<close>

definition binds :: "tinst \<Rightarrow> env \<Rightarrow> (pterm \<times> pterm) set" where
  "binds \<rho> env = {(Var x (tsubst \<rho> U), inst \<rho> u) | x U u. vt_lookup (tenv env) x = Some (U, u)}"

lemma binds_extends: "extends env env' \<Longrightarrow> binds \<rho> env \<subseteq> binds \<rho> env'"
  unfolding binds_def extends_def by blast

lemma solution_binds: "solution \<rho> \<sigma> env \<Longrightarrow> (l, r) \<in> binds \<rho> env \<Longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r"
  unfolding binds_def by (auto dest: solutionD(4) simp: ap_def)

lemma eqv_ap:
  "eqv (binds \<rho> env \<union> E) e (inst \<rho> s) (inst \<rho> t) \<Longrightarrow> solution \<rho> \<sigma> env \<Longrightarrow>
    (\<And>l r. (l, r) \<in> E \<Longrightarrow> vsubst \<sigma> l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> vsubst \<sigma> r) \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  unfolding ap_def by (erule eqv_vsubst) (auto dest: solutionD(3) solution_binds)

end

end
