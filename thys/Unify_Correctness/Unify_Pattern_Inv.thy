section \<open>The Typed Invariant of Pattern Unification\<close>

theory Unify_Pattern_Inv
  imports Unify_Flexflex_Typed
begin

text \<open>
  Pattern unification keeps the type-level invariant of theory \<open>Unify_Typed_Inv\<close>: the type
  environment stays well-formed, the type variables of the bindings stay known, and the type
  environment grows as \<^const>\<open>pure_sig_gen.tgrow\<close> says. Types are unified at abstractions and
  at constants and free variables; these types must be certified, which is a syntactic
  invariant here (\<open>ctyps\<close>: the types at abstractions, constants and free variables of the
  terms and of the bindings), so that no typing is needed. The proof is by induction on the
  computation, as for soundness (@{thm [source] pure_sig_gen.unif_gsound}), and needs no
  termination.
\<close>

subsection \<open>The types at abstractions, constants and free variables\<close>

primrec ctyps :: "pterm \<Rightarrow> ptyp set" where
  "ctyps (Const c T) = {T}"
| "ctyps (Free x T) = {T}"
| "ctyps (Var x T) = {}"
| "ctyps (Bound i) = {}"
| "ctyps (Abs a T t) = insert T (ctyps t)"
| "ctyps (s $ t) = ctyps s \<union> ctyps t"

lemma ctyps_typs: "ctyps t \<subseteq> typs t"
  by (induction t) auto

lemma ctyps_apps: "ctyps (s \<degree>\<degree> ts) = ctyps s \<union> \<Union> (ctyps ` set ts)"
  by (induction ts arbitrary: s) auto

lemma ctyps_incr_bv [simp]: "ctyps (incr_bv n k t) = ctyps t"
  by (induction t arbitrary: k) auto

lemma ctyps_subst: "ctyps (t[s/k]) \<subseteq> ctyps t \<union> ctyps s"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "lift s 0" "k + 1"] by auto
next
  case (App t1 t2)
  have "ctyps (t1[s/k]) \<subseteq> ctyps t1 \<union> ctyps s" "ctyps (t2[s/k]) \<subseteq> ctyps t2 \<union> ctyps s"
    by (rule App.IH(1), rule App.IH(2))
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma ctyps_abs_list: "ctyps (abs_list bs t) = snd ` set bs \<union> ctyps t"
  by (induction bs) force+

definition ectyps :: "env \<Rightarrow> ptyp set" where
  "ectyps env = (\<Union>(x, U, u)\<in>bnds env. ctyps u)"

lemma ectypsI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ctyps u \<subseteq> ectyps env"
  unfolding ectyps_def bnds_def by blast

lemma ectyps_tenv: "tenv env1 = tenv env \<Longrightarrow> ectyps env1 = ectyps env"
  by (simp add: ectyps_def bnds_def)

context pure_sig_gen
begin

lemma ctyps_incr [simp]: "ctyps (incr t) = ctyps t"
  by (simp add: incr_def incr_aux_lift)

lemma pi_ttvars_incr [simp]: "ttvars (incr t) = ttvars t"
  by (simp add: ttvars_def incr_def incr_aux_lift)

lemma ctyps_app [simp]: "ctyps (app s is) = ctyps s"
  by (simp add: app_apps ctyps_apps)

lemma ectyps_update: "ok (update (F, T) b env) env' \<Longrightarrow> ectyps env' = ctyps b \<union> ectyps env"
  by (auto simp: ectyps_def bnds_update)

lemma head_norm_ctyps:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> ctyps t' \<subseteq> ctyps t \<union> ectyps env"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "ctyps u' \<subseteq> ctyps u \<union> ectyps env" if "ok (hn env u) u'" for u u'
    using "1.IH"[OF that refl] .
  show ?case
  proof (cases t)
    case (Var x T)
    with h obtain lr where lr: "ok (lookup env x T) lr"
      and rest: "ok (case lr of Some u \<Rightarrow> hn env u | None \<Rightarrow> return t) t'"
      by auto
    show ?thesis
    proof (cases lr)
      case (Some u)
      with lr obtain U where "vt_lookup (tenv env) x = Some (U, u)" by (auto elim: ok_lookup_Some)
      with IH[of u t'] rest Some show ?thesis by (auto dest: ectypsI)
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h IH show ?thesis by fastforce
  next
    case (App f u)
    have redex: "ctyps t' \<subseteq> ctyps (Abs b U0 body $ u) \<union> ectyps env"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
      using IH[OF that] ctyps_subst[of body u 0] by (auto simp: subst_bound_subst)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain b U0 body where f: "f = Abs b U0 body" by (cases f) auto
      with h App redex show ?thesis by simp
    next
      case False
      with h App obtain nf where hf: "ok (hn env f) nf"
        and rest: "ok (case nf of Abs _ _ body \<Rightarrow> hn env (subst_bound u body) | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF hf] have nf: "ctyps nf \<subseteq> ctyps f \<union> ectyps env" .
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this, of b U0] nf App Abs show ?thesis by auto
      qed (use rest nf App in auto)
    qed
  qed (use h in auto)
qed


subsection \<open>The invariant\<close>

text \<open>
  The invariant of an environment: its type environment is well-formed, the type variables of
  its bindings are known, and the types at the abstractions, constants and free variables of its
  bindings are certified.
\<close>

definition pinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "pinv A K env \<longleftrightarrow> einv A K (tyonly env) \<and> etvars env \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>T\<in>ectyps env. cert_typ alg ar T)"

text \<open>A term under binders: its type variables are known and its types are certified.\<close>

definition tkn :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "tkn A env bs t \<longleftrightarrow> ttvars t \<union> btvars bs \<subseteq> tvars_env (tyenv env) \<union> A \<and>
    (\<forall>T\<in>ctyps t \<union> snd ` set bs. cert_typ alg ar T)"

lemma pinvD:
  assumes "pinv A K env"
  shows "einv A K (tyonly env)" "etvars env \<subseteq> tvars_env (tyenv env) \<union> A" "T \<in> ectyps env \<Longrightarrow> cert_typ alg ar T"
  using assms unfolding pinv_def by blast+

lemma tknD:
  assumes "tkn A env bs t"
  shows "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    "T \<in> ctyps t \<Longrightarrow> cert_typ alg ar T" "(a, T) \<in> set bs \<Longrightarrow> cert_typ alg ar T"
  using assms unfolding tkn_def by force+

lemma tkn_grow: "tkn A env bs t \<Longrightarrow> tgrow A env env' \<Longrightarrow> tkn A env' bs t"
  unfolding tkn_def using tgrowD(1)[of A env env'] by blast

lemma tkn_tyenv: "tkn A env bs t \<Longrightarrow> tyenv env' = tyenv env \<Longrightarrow> tkn A env' bs t"
  unfolding tkn_def by simp

lemma tkn_apps: "tkn A env bs (h \<degree>\<degree> ts) \<longleftrightarrow> tkn A env bs h \<and> (\<forall>t\<in>set ts. tkn A env bs t)"
  unfolding tkn_def by (auto simp: ttvars_apps ctyps_apps)

lemma tkn_Abs: "tkn A env bs (Abs a T t) \<longleftrightarrow> tkn A env ((a, T) # bs) t"
  unfolding tkn_def by (auto simp: btvars_def)

lemma tkn_head_norm:
  assumes "ok (head_norm env s) s'" "pinv A K env" "tkn A env bs s"
  shows "tkn A env bs s'"
proof -
  have "ttvars s' \<subseteq> tvars_env (tyenv env) \<union> A"
    using head_norm_ttvars[OF assms(1) refl] pinvD(2)[OF assms(2)] tknD(1)[OF assms(3)] by blast
  moreover have "cert_typ alg ar T" if "T \<in> ctyps s'" for T
    using head_norm_ctyps[OF assms(1) refl] that pinvD(3)[OF assms(2)] tknD(3)[OF assms(3)] by blast
  ultimately show ?thesis using assms(3) unfolding tkn_def by blast
qed

text \<open>Type unification on known certified types:\<close>

lemma pinv_unify_types:
  assumes ut: "ok (unify_types alg T U env) env1" and fK: "finite K" and pi: "pinv A K env"
    and T: "tvars T \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar T"
    and U: "tvars U \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar U"
  shows "pinv A K env1" "tgrow A env env1" "tenv env1 = tenv env"
proof -
  have cu: "okW (cunify_types alg T U env) env1" using ut by (simp add: cunify_types_ok)
  note c = tyinv_cunify_c[OF cu fK pinvD(1)[OF pi] T U]
  show "tgrow A env env1" by (rule c(6))
  show "tenv env1 = tenv env" by (rule c(2))
  show "pinv A K env1"
    unfolding pinv_def using c(1,3) pinvD(2,3)[OF pi] etvars_tenv[OF c(2)] ectyps_tenv[OF c(2)] by auto
qed

text \<open>A new binding whose type variables are known and whose types are certified:\<close>

lemma pinv_update:
  assumes upd: "ok (update (F, Fty) u env1) env'" and pi: "pinv A K env"
    and te: "tenv env1 = tenv env" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1"
    and k: "tvars Fty \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" and c: "\<forall>T\<in>ctyps u. cert_typ alg ar T"
  shows "pinv A K env'" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
proof -
  note u = ok_update[OF upd]
  show te': "tyenv env' = tyenv env" using u(3) te(2) by simp
  show mx: "maxidx env \<le> maxidx env'" using u(4) te(3) by simp
  have "einv A K (tyonly env')" by (rule einv_tyonly_maxidx[OF pinvD(1)[OF pi] te' mx])
  moreover have "etvars env' \<subseteq> tvars_env (tyenv env') \<union> A"
    using etvars_update[OF upd] etvars_tenv[OF te(1)] pinvD(2)[OF pi] k te' by auto
  moreover have "\<forall>T\<in>ectyps env'. cert_typ alg ar T"
    using ectyps_update[OF upd] ectyps_tenv[OF te(1)] pinvD(3)[OF pi] c by auto
  ultimately show "pinv A K env'" by (simp add: pinv_def)
qed

lemma type_of_G_known:
  assumes "ok (type_of_G env T n is) G" "pinv A K env" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars G \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  have "type_of_G (tyonly env) T n is = type_of_G env T n is" by (simp add: type_of_G_def)
  with assms(1) have "ok (type_of_G (tyonly env) T n is) G" by simp
  from type_of_G_tvars[OF this einvD(1)[OF pinvD(1)[OF assms(2)]]] assms(3) show ?thesis by simp
qed

lemma tkn_mkabs:
  assumes mk: "ok (mkabs bs is t) u" and k: "ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
    "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A" and c: "\<forall>T\<in>ctyps t \<union> snd ` set bs. cert_typ alg ar T"
  shows "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>T\<in>ctyps u. cert_typ alg ar T"
proof -
  from mk have ir: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    and u: "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t" by (simp_all add: ok_mkabs)
  show "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" using btvars_nths[OF ir] k by (auto simp: u ttvars_abs_list)
  have mem: "bs ! nat_of_integer i \<in> set bs" if "i \<in> set is" for i
    using ir that by (simp add: nat_of_integer_less_ilength)
  show "\<forall>T\<in>ctyps u. cert_typ alg ar T"
  proof
    fix T assume "T \<in> ctyps u"
    then consider "T \<in> ctyps t" | i where "i \<in> set is" "T = snd (bs ! nat_of_integer i)"
      by (auto simp: u ctyps_abs_list)
    then show "cert_typ alg ar T"
    proof cases
      case 1
      with c show ?thesis by blast
    next
      case (2 i)
      from mem[OF 2(1)] have "T \<in> snd ` set bs" unfolding 2(2) by (rule imageI)
      with c show ?thesis by blast
    qed
  qed
qed


subsection \<open>Steps\<close>

definition step_tk :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "step_tk env bs s t env' \<longleftrightarrow> (\<forall>A K. finite K \<longrightarrow> pinv A K env \<longrightarrow> tkn A env bs s \<longrightarrow> tkn A env bs t \<longrightarrow>
    pinv A K env' \<and> tgrow A env env')"

lemma step_tkI:
  "(\<And>A K. finite K \<Longrightarrow> pinv A K env \<Longrightarrow> tkn A env bs s \<Longrightarrow> tkn A env bs t \<Longrightarrow> pinv A K env' \<and> tgrow A env env') \<Longrightarrow>
    step_tk env bs s t env'"
  unfolding step_tk_def by blast

lemma step_tkD:
  "step_tk env bs s t env' \<Longrightarrow> finite K \<Longrightarrow> pinv A K env \<Longrightarrow> tkn A env bs s \<Longrightarrow> tkn A env bs t \<Longrightarrow>
    pinv A K env' \<and> tgrow A env env'"
  unfolding step_tk_def by blast

lemma step_tk_sym: "step_tk env bs s t env' \<Longrightarrow> step_tk env bs t s env'"
  unfolding step_tk_def by blast

lemma step_tk_head_norm:
  assumes hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'" and st: "step_tk env bs s' t' env'"
  shows "step_tk env bs s t env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs s" and kt: "tkn A env bs t"
  show "pinv A K env' \<and> tgrow A env env'"
    by (rule step_tkD[OF st fK pi tkn_head_norm[OF hs pi ks] tkn_head_norm[OF ht pi kt]])
qed

lemma step_tk_Abs:
  assumes ut: "ok (unify_types alg Ts Tt env) env1" and st: "step_tk env1 ((c, Ts) # bs) ts tt env'"
  shows "step_tk env bs (Abs ns Ts ts) (Abs nt Tt tt) env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (Abs ns Ts ts)"
    and kt: "tkn A env bs (Abs nt Tt tt)"
  have kTs: "tvars Ts \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar Ts"
    using tknD(1,3)[OF ks] by auto
  have kTt: "tvars Tt \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar Tt"
    using tknD(1,3)[OF kt] by auto
  note u = pinv_unify_types[OF ut fK pi kTs kTt]
  have ks1: "tkn A env1 ((c, Ts) # bs) ts" using tkn_grow[OF ks u(2)] by (simp add: tkn_def btvars_def)
  have kt1: "tkn A env1 ((c, Ts) # bs) tt"
    using tkn_grow[OF kt u(2)] tkn_grow[OF ks u(2)] by (simp add: tkn_def btvars_def)
  from step_tkD[OF st fK u(1) ks1 kt1] tgrow_trans[OF u(2)] show "pinv A K env' \<and> tgrow A env env'" by blast
qed

lemma step_tk_eta:
  assumes st: "step_tk env ((a, Ts) # bs) ts (incr t' $ Bound 0) env'"
  shows "step_tk env bs (Abs a Ts ts) t' env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (Abs a Ts ts)"
    and kt: "tkn A env bs t'"
  have ks1: "tkn A env ((a, Ts) # bs) ts" using ks by (simp add: tkn_Abs)
  have kt1: "tkn A env ((a, Ts) # bs) (incr t' $ Bound 0)" using ks kt by (simp add: tkn_def btvars_def)
  from step_tkD[OF st fK pi ks1 kt1] show "pinv A K env' \<and> tgrow A env env'" .
qed

definition steps_tk :: "env \<Rightarrow> binders \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> env \<Rightarrow> bool" where
  "steps_tk env bs ps env' \<longleftrightarrow> (\<forall>A K. finite K \<longrightarrow> pinv A K env \<longrightarrow>
    (\<forall>(s, t)\<in>set ps. tkn A env bs s \<and> tkn A env bs t) \<longrightarrow> pinv A K env' \<and> tgrow A env env')"

lemma steps_tkD:
  "steps_tk env bs ps env' \<Longrightarrow> finite K \<Longrightarrow> pinv A K env \<Longrightarrow>
    \<forall>(s, t)\<in>set ps. tkn A env bs s \<and> tkn A env bs t \<Longrightarrow> pinv A K env' \<and> tgrow A env env'"
  unfolding steps_tk_def by blast

lemma foldM_steps_tk:
  assumes "ok (foldM (\<lambda>(s, t) env. f s t env) ps env) env'"
    and "\<And>s t env env'. (s, t) \<in> set ps \<Longrightarrow> ok (f s t env) env' \<Longrightarrow> step_tk env bs s t env'"
  shows "steps_tk env bs ps env'"
  using assms
proof (induction ps arbitrary: env)
  case Nil
  then show ?case by (simp add: steps_tk_def)
next
  case (Cons p ps)
  obtain s t where p: "p = (s, t)" by (cases p)
  with Cons.prems(1) obtain env1 where f: "ok (f s t env) env1"
    and rest: "ok (foldM (\<lambda>(s, t) env. f s t env) ps env1) env'"
    by auto
  have s1: "step_tk env bs s t env1" using Cons.prems(2)[OF _ f] p by simp
  have s2: "steps_tk env1 bs ps env'" using Cons.IH[OF rest] Cons.prems(2) by simp
  show ?case unfolding steps_tk_def
  proof (intro allI impI)
    fix A K assume fK: "finite K" and pi: "pinv A K env"
      and k: "\<forall>(s, t)\<in>set (p # ps). tkn A env bs s \<and> tkn A env bs t"
    from k p have k0: "tkn A env bs s" "tkn A env bs t" by auto
    from step_tkD[OF s1 fK pi k0] have r1: "pinv A K env1" "tgrow A env env1" by blast+
    have k1: "\<forall>(s, t)\<in>set ps. tkn A env1 bs s \<and> tkn A env1 bs t" using k tkn_grow[OF _ r1(2)] by auto
    from steps_tkD[OF s2 fK r1(1) k1] tgrow_trans[OF r1(2)]
    show "pinv A K env' \<and> tgrow A env env'" by blast
  qed
qed

lemma step_tk_rigid:
  assumes ut: "ok (unify_types alg Ta Tb env) env1" and c: "c = Const a \<or> c = Free a"
    and len: "length ss = length ts" and st: "steps_tk env1 bs (zip ss ts) env'"
  shows "step_tk env bs (c Ta \<degree>\<degree> ss) (c Tb \<degree>\<degree> ts) env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (c Ta \<degree>\<degree> ss)"
    and kt: "tkn A env bs (c Tb \<degree>\<degree> ts)"
  have kTa: "tvars Ta \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar Ta"
    using ks c by (auto simp: tkn_def ttvars_apps ctyps_apps)
  have kTb: "tvars Tb \<subseteq> tvars_env (tyenv env) \<union> A" "cert_typ alg ar Tb"
    using kt c by (auto simp: tkn_def ttvars_apps ctyps_apps)
  note u = pinv_unify_types[OF ut fK pi kTa kTb]
  have k1: "\<forall>(s, t)\<in>set (zip ss ts). tkn A env1 bs s \<and> tkn A env1 bs t"
    using ks kt tkn_grow[OF _ u(2)] by (auto simp: tkn_apps dest: set_zip_leftD set_zip_rightD)
  from steps_tkD[OF st fK u(1) k1] tgrow_trans[OF u(2)]
  show "pinv A K env' \<and> tgrow A env env'" by blast
qed

lemma step_tk_rigid_same:
  assumes len: "length ss = length ts" and st: "steps_tk env bs (zip ss ts) env'"
  shows "step_tk env bs (h \<degree>\<degree> ss) (h' \<degree>\<degree> ts) env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (h \<degree>\<degree> ss)"
    and kt: "tkn A env bs (h' \<degree>\<degree> ts)"
  have k1: "\<forall>(s, t)\<in>set (zip ss ts). tkn A env bs s \<and> tkn A env bs t"
    using ks kt by (auto simp: tkn_apps dest: set_zip_leftD set_zip_rightD)
  from steps_tkD[OF st fK pi k1] show "pinv A K env' \<and> tgrow A env env'" .
qed

lemma step_tk_flex:
  assumes st: "step_tk env bs (app (Var F Fty) is) t env'"
  shows "step_tk env bs (Var F Fty \<degree>\<degree> ss) t env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (Var F Fty \<degree>\<degree> ss)"
    and kt: "tkn A env bs t"
  have "tkn A env bs (app (Var F Fty) is)" using ks by (auto simp: tkn_def ttvars_apps)
  from step_tkD[OF st fK pi this kt] show "pinv A K env' \<and> tgrow A env env'" .
qed


subsection \<open>Flexible cases\<close>

lemma tkn_flexD:
  assumes "tkn A env bs (app (Var F Fty) is)"
  shows "tvars Fty \<subseteq> tvars_env (tyenv env) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env) \<union> A"
    "\<forall>T\<in>snd ` set bs. cert_typ alg ar T"
  using assms by (auto simp: tkn_def)

lemma flexflex1_tk:
  assumes ff: "ok (flexflex1 env bs F Fty is js) env'"
  shows "step_tk env bs (app (Var F Fty) is) (app (Var F Gty) js) env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (app (Var F Fty) is)"
  note kF = tkn_flexD[OF ks]
  show "pinv A K env' \<and> tgrow A env env'"
  proof (cases "is = js")
    case True
    with ff have "env' = env" by (simp add: flexflex1_def)
    with pi show ?thesis by simp
  next
    case False
    with ff obtain ks where hnf: "ok (mk_new_hnf env bs is F Fty ks) env'" by (auto simp: flexflex1_def)
    from hnf obtain Gty' where tg: "ok (type_of_G env Fty (ilength is) ks) Gty'"
      and rest: "ok (let (env1, G) = genvar (fst F) env Gty' in
        mk_hnf bs is G ks \<bind> (\<lambda>t. update (F, Fty) t env1)) env'"
      by (auto simp: mk_new_hnf_def)
    obtain env1 G where G: "genvar (fst F) env Gty' = (env1, G)" by force
    with rest obtain u where u: "ok (mkabs bs is (app G ks)) u" and upd: "ok (update (F, Fty) u env1) env'"
      by (auto simp: mk_hnf_def)
    note gs = genvar_simps[OF G]
    have kG: "tvars Gty' \<subseteq> tvars_env (tyenv env) \<union> A" by (rule type_of_G_known[OF tg pi kF(1)])
    have m: "ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" "\<forall>T\<in>ctyps u. cert_typ alg ar T"
      by (rule tkn_mkabs[OF u _ kF(2)], use kG kF(3) in \<open>simp_all add: gs(4)\<close>)+
    have "maxidx env \<le> maxidx env1" using gs(3) by simp
    from pinv_update[OF upd pi gs(1,2) this _ m(2)] kF(1) m(1)
    have r: "pinv A K env'" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'" by auto
    with tgrow_tyenv[OF r(2,3)] show ?thesis by simp
  qed
qed

lemma ff_tk:
  assumes ff: "ok (ff env bs F Fty is G Gty js) env'"
  shows "step_tk env bs (app (Var F Fty) is) (app (Var G Gty) js) env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (app (Var F Fty) is)"
    and kt: "tkn A env bs (app (Var G Gty) js)"
  note kF = tkn_flexD[OF ks] and kG = tkn_flexD[OF kt]
  let ?KN = "tvars_env (tyenv env) \<union> A"
  show "pinv A K env' \<and> tgrow A env env'"
  proof (cases "subset js is")
    case True
    with ff obtain ks u where u: "ok (mkabs bs is (app (Var G Gty) ks)) u"
      and upd: "ok (update (F, Fty) u env) env'"
      by (auto simp: ff_def)
    have m: "ttvars u \<subseteq> ?KN" "\<forall>T\<in>ctyps u. cert_typ alg ar T"
      by (rule tkn_mkabs[OF u _ kF(2)], use kG(1) kF(3) in simp_all)+
    from pinv_update[OF upd pi refl refl order_refl _ m(2)] kF(1) m(1)
    have r: "pinv A K env'" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'" by auto
    with tgrow_tyenv[OF r(2,3)] show ?thesis by simp
  next
    case False
    let ?ks = "inter js is"
    from False ff obtain ksF Hty where tg: "ok (type_of_G env Fty (ilength is) ksF) Hty"
      and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs bs js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs bs is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain ksG ksF' tG tF env2 where tG: "ok (mkabs bs js (app H ksG)) tG"
      and tF: "ok (mkabs bs is (app H ksF')) tF"
      and upd1: "ok (update (F, Fty) tF env1) env2" and upd2: "ok (update (G, Gty) tG env2) env'"
      by auto
    note gs = genvar_simps[OF H]
    have kH: "tvars Hty \<subseteq> ?KN" by (rule type_of_G_known[OF tg pi kF(1)])
    have mF: "ttvars tF \<subseteq> ?KN" "\<forall>T\<in>ctyps tF. cert_typ alg ar T"
      by (rule tkn_mkabs[OF tF _ kF(2)], use kH kF(3) in \<open>simp_all add: gs(4)\<close>)+
    have mG: "ttvars tG \<subseteq> ?KN" "\<forall>T\<in>ctyps tG. cert_typ alg ar T"
      by (rule tkn_mkabs[OF tG _ kF(2)], use kH kF(3) in \<open>simp_all add: gs(4)\<close>)+
    have "maxidx env \<le> maxidx env1" using gs(3) by simp
    from pinv_update[OF upd1 pi gs(1,2) this _ mF(2)] kF(1) mF(1)
    have r1: "pinv A K env2" "tyenv env2 = tyenv env" "maxidx env \<le> maxidx env2" by auto
    from pinv_update[OF upd2 r1(1) refl refl order_refl _ mG(2)] kG(1) mG(1) r1(2)
    have r2: "pinv A K env'" "tyenv env' = tyenv env2" "maxidx env2 \<le> maxidx env'" by auto
    have "tgrow A env env'" by (rule tgrow_tyenv) (use r1 r2 in simp_all)
    with r2(1) show ?thesis by simp
  qed
qed

lemma flexflex2_tk:
  assumes "ok (flexflex2 env bs F Fty is G Gty js) env'"
  shows "step_tk env bs (app (Var F Fty) is) (app (Var G Gty) js) env'"
  using assms by (cases "indexname_less G F") (auto simp: flexflex2_def intro: ff_tk step_tk_sym)


subsection \<open>Projection\<close>

definition pr_tk :: "env \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> env \<Rightarrow> bool" where
  "pr_tk env bs s u env' \<longleftrightarrow> (\<forall>A K. finite K \<longrightarrow> pinv A K env \<longrightarrow> tkn A env bs s \<longrightarrow>
    pinv A K env' \<and> tyenv env' = tyenv env \<and> maxidx env \<le> maxidx env' \<and> tkn A env' bs u)"

lemma mapAccM_pr_tk:
  assumes "ok (mapAccM f ts env) (us, env')"
    and "\<And>s env u env'. s \<in> set ts \<Longrightarrow> ok (f s env) (u, env') \<Longrightarrow> pr_tk env bs s u env'"
    and "finite K" "pinv A K env" "\<forall>s\<in>set ts. tkn A env bs s"
  shows "pinv A K env' \<and> tyenv env' = tyenv env \<and> maxidx env \<le> maxidx env' \<and> (\<forall>u\<in>set us. tkn A env' bs u)"
  using assms
proof (induction ts arbitrary: env us)
  case Nil
  then show ?case by simp
next
  case (Cons s ts)
  from Cons.prems(1) obtain u env1 us' where f: "ok (f s env) (u, env1)"
    and r: "ok (mapAccM f ts env1) (us', env')" and us: "us = u # us'"
    by (auto split: prod.splits)
  have "pr_tk env bs s u env1" using Cons.prems(2)[of s env u env1] f by simp
  then have p: "pinv A K env1" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1" "tkn A env1 bs u"
    using Cons.prems(3,4,5) unfolding pr_tk_def by auto
  have k1: "\<forall>s\<in>set ts. tkn A env1 bs s" using Cons.prems(5) tkn_tyenv[OF _ p(2)] by simp
  have hyp: "\<And>s' env u env'. s' \<in> set ts \<Longrightarrow> ok (f s' env) (u, env') \<Longrightarrow> pr_tk env bs s' u env'"
    by (rule Cons.prems(2)) simp_all
  note q = Cons.IH[OF r hyp Cons.prems(3) p(1) k1]
  have "tkn A env' bs u" by (rule tkn_tyenv[OF p(4)]) (use q in simp)
  with q p show ?case by (simp add: us)
qed

lemma pr_typed:
  assumes "pr xs s env d bs = Some r"
  shows "r = Ok (u, env') \<Longrightarrow> pr_tk env bs s u env'"
  using assms
proof (induction xs s env d bs r arbitrary: u env' rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d bs r)
  have IH: "pr_tk env1 bs1 s1 u1 env2" if "ok (prr xs1 s1 env1 d1 bs1) (u1, env2)" for xs1 s1 env1 d1 bs1 u1 env2
    using "1.IH"[OF that refl] .
  have "ok (head_norm env s \<bind> (\<lambda>s'. pr_step prr xs s' env d bs)) (u, env')"
    using "1.hyps" "1.prems"(1) unfolding pr_step_def by simp
  then obtain s' where hs: "ok (head_norm env s) s'" and st: "ok (pr_step prr xs s' env d bs) (u, env')"
    by auto
  show ?case unfolding pr_tk_def
  proof (intro allI impI)
    fix A K assume fK: "finite K" and pi: "pinv A K env" and ks0: "tkn A env bs s"
    let ?KN = "tvars_env (tyenv env) \<union> A"
    have ks: "tkn A env bs s'" by (rule tkn_head_norm[OF hs pi ks0])
    show "pinv A K env' \<and> tyenv env' = tyenv env \<and> maxidx env \<le> maxidx env' \<and> tkn A env' bs u"
    proof (cases "is_Abs s'")
      case True
      then obtain a T t where s': "s' = Abs a T t" by (cases s') auto
      from st obtain t' where r: "ok (prr xs t env (d + 1) ((a, T) # bs)) (t', env')"
        and u: "u = Abs a T t'"
        by (auto simp: pr_step_def s')
      have "tkn A env ((a, T) # bs) t" using ks by (simp add: s' tkn_Abs)
      with IH[OF r] fK pi have "pinv A K env'" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'"
        "tkn A env' ((a, T) # bs) t'"
        unfolding pr_tk_def by blast+
      then show ?thesis by (simp add: u tkn_Abs)
    next
      case nA: False
      obtain h ts where sc: "strip_comb s' = (h, ts)" by force
      have s'eq: "s' = h \<degree>\<degree> ts" by (rule strip_comb_apps[OF sc])
      show ?thesis
      proof (cases "is_Var h")
        case True
        then obtain F Fty where hF: "h = Var F Fty" by (cases h) auto
        from st nA sc hF obtain js js' Hty where
          tg: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty" and
          rest: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow> mk_hnf bs js H (mk_proj_list js') \<bind>
             (\<lambda>t. update (F, Fty) t env1 \<bind> (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (u, env')"
          by (auto simp: pr_step_def Let_def)
        obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
        with rest obtain t where t: "ok (mkabs bs js (app H (mk_proj_list js'))) t"
          and upd: "ok (update (F, Fty) t env1) env'" and u: "u = app H (List.map_filter id js')"
          by (auto simp: mk_hnf_def)
        note gs = genvar_simps[OF G]
        have kF: "tvars Fty \<subseteq> ?KN" "btvars bs \<subseteq> ?KN" "\<forall>T\<in>snd ` set bs. cert_typ alg ar T"
          using ks by (auto simp: tkn_def s'eq hF ttvars_apps)
        have kH: "tvars Hty \<subseteq> ?KN" by (rule type_of_G_known[OF tg pi kF(1)])
        have m: "ttvars t \<subseteq> ?KN" "\<forall>T\<in>ctyps t. cert_typ alg ar T"
          by (rule tkn_mkabs[OF t _ kF(2)], use kH kF(3) in \<open>simp_all add: gs(4)\<close>)+
        have "maxidx env \<le> maxidx env1" using gs(3) by simp
        from pinv_update[OF upd pi gs(1,2) this _ m(2)] kF(1) m(1)
        have r: "pinv A K env'" "tyenv env' = tyenv env" "maxidx env \<le> maxidx env'" by auto
        moreover have "tkn A env' bs u" using kH kF r(2) by (simp add: tkn_def u gs(4))
        ultimately show ?thesis by simp
      next
        case nV: False
        show ?thesis
        proof (cases "is_Abs h")
          case True
          with st nA sc nV show ?thesis by (simp add: pr_step_def)
        next
          case nAh: False
          let ?h = "case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h"
          from st nA sc nV nAh obtain h' ts' where hh: "ok ?h h'"
            and m: "ok (mapAccM (\<lambda>s env. prr xs s env d bs) ts env) (ts', env')"
            and u: "u = list_comb h' ts'"
            by (auto simp: pr_step_def)
          have kh: "tkn A env bs h" and kts: "\<forall>t\<in>set ts. tkn A env bs t" using ks by (simp_all add: s'eq tkn_apps)
          have kh': "tkn A env bs h'"
          proof (cases h)
            case (Bound i)
            with hh obtain j where "h' = Bound j" by auto
            with kh show ?thesis by (simp add: tkn_def)
          qed (use hh kh in auto)
          have hyp: "\<And>s1 env1 u1 env2. s1 \<in> set ts \<Longrightarrow> ok (prr xs s1 env1 d bs) (u1, env2) \<Longrightarrow>
              pr_tk env1 bs s1 u1 env2"
            by (rule IH)
          note m' = mapAccM_pr_tk[OF m hyp fK pi kts]
          have "tkn A env' bs h'" by (rule tkn_tyenv[OF kh']) (use m' in simp)
          with m' show ?thesis by (simp add: u list_comb_apps tkn_apps)
        qed
      qed
    qed
  qed
qed

lemma proj_tk:
  assumes "ok (proj t env bs is) (u, env')"
  shows "pr_tk env bs t u env'"
proof (cases "downto0 is (ilength bs - 1)")
  case True
  with assms have "u = t" "env' = env" by (simp_all add: proj_def)
  then show ?thesis unfolding pr_tk_def by auto
next
  case False
  with assms have "ok (pr is t env 0 bs) (u, env')" by (simp add: proj_def)
  from pr_typed[OF this refl] show ?thesis .
qed

lemma flexrigid_tk:
  assumes fr: "ok (flexrigid env bs F Fty is t) env'"
  shows "step_tk env bs (app (Var F Fty) is) t env'"
proof (rule step_tkI)
  fix A K assume fK: "finite K" and pi: "pinv A K env" and ks: "tkn A env bs (app (Var F Fty) is)"
    and kt: "tkn A env bs t"
  note kF = tkn_flexD[OF ks]
  have nh: False if "ok (case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env bs F is t)) | _ \<Rightarrow> raise e) y" for e y
    using that by (cases e) auto
  have pj: "ok (do {(u, env1) \<leftarrow> proj t env bs is; u' \<leftarrow> mkabs bs is u; update (F, Fty) u' env1}) env'"
    using fr by (auto simp: flexrigid_def ok_handle split: if_splits dest: nh)
  then obtain u env1 u' where pj': "ok (proj t env bs is) (u, env1)" and mk: "ok (mkabs bs is u) u'"
    and upd: "ok (update (F, Fty) u' env1) env'"
    by (auto split: prod.splits)
  from proj_tk[OF pj'] fK pi kt
  have p: "pinv A K env1" "tyenv env1 = tyenv env" "maxidx env \<le> maxidx env1" "tkn A env1 bs u"
    unfolding pr_tk_def by blast+
  have ku: "ttvars u \<subseteq> tvars_env (tyenv env1) \<union> A" "btvars bs \<subseteq> tvars_env (tyenv env1) \<union> A"
    "\<forall>T\<in>ctyps u \<union> snd ` set bs. cert_typ alg ar T"
    using p(4) by (auto simp: tkn_def)
  note m = tkn_mkabs[OF mk ku]
  from pinv_update[OF upd p(1) refl refl order_refl _ m(2)] kF(1) m(1) p(2)
  have r: "pinv A K env'" "tyenv env' = tyenv env1" "maxidx env1 \<le> maxidx env'" by auto
  have "tgrow A env env'" by (rule tgrow_tyenv) (use p r in simp_all)
  with r(1) show "pinv A K env' \<and> tgrow A env env'" by simp
qed


subsection \<open>Unification\<close>

theorem unif_typed:
  assumes "unif alg' bs s t env = Some r"
  shows "r = Ok env' \<Longrightarrow> alg' = alg \<Longrightarrow> step_tk env bs s t env'"
  using assms
proof (induction alg' bs s t env r arbitrary: env' rule: unif.raw_induct[rotated, consumes 1])
  case (1 uni alg' bs s t env r)
  note al = "1.prems"(2)
  have IH: "step_tk env1 bs1 s1 t1 env2" if "ok (uni alg bs1 s1 t1 env1) env2" for bs1 s1 t1 env1 env2
    using "1.IH"[OF that[folded al] refl al] .
  have "ok (head_norm env s \<bind> (\<lambda>s'. head_norm env t \<bind> (\<lambda>t'. unif_step uni alg' bs s' t' env))) env'"
    using "1.hyps" "1.prems"(1) unfolding unif_step_def by simp
  then obtain s' t' where hs: "ok (head_norm env s) s'" and ht: "ok (head_norm env t) t'"
    and body: "ok (unif_step uni alg bs s' t' env) env'"
    unfolding al by auto
  have "step_tk env bs s' t' env'"
  proof (cases "is_Abs s'")
    case sAbs: True
    then obtain ns Ts ts where s': "s' = Abs ns Ts ts" by (cases s') auto
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
      with body s' obtain env1 where ut: "ok (unify_types alg Ts Tt env) env1"
        and r: "ok (uni alg ((if ns = STR '''' then nt else ns, Ts) # bs) ts tt env1) env'"
        by (auto simp: unif_step_def Let_def)
      show ?thesis unfolding s' t' by (rule step_tk_Abs[OF ut IH[OF r]])
    next
      case False
      with body s' have r: "ok (uni alg ((ns, Ts) # bs) ts (incr t' $ Bound 0) env) env'"
        by (simp add: unif_step_def)
      show ?thesis unfolding s' by (rule step_tk_eta[OF IH[OF r]])
    qed
  next
    case nsAbs: False
    show ?thesis
    proof (cases "is_Abs t'")
      case True
      then obtain nt Tt tt where t': "t' = Abs nt Tt tt" by (cases t') auto
      with body nsAbs have r: "ok (uni alg ((nt, Tt) # bs) (incr s' $ Bound 0) tt env) env'"
        by (simp add: unif_step_def)
      show ?thesis unfolding t' by (rule step_tk_sym[OF step_tk_eta[OF step_tk_sym[OF IH[OF r]]]])
    next
      case ntAbs: False
      obtain hs ss where shs: "strip_comb s' = (hs, ss)" by force
      obtain ht ts where sht: "strip_comb t' = (ht, ts)" by force
      have s': "s' = hs \<degree>\<degree> ss" and t': "t' = ht \<degree>\<degree> ts"
        by (rule strip_comb_apps[OF shs], rule strip_comb_apps[OF sht])
      have body': "ok (if is_Var hs \<and> is_Var ht then
            (case (hs, ht) of
              (Var F Fty, Var G Gty) \<Rightarrow> do {
                is \<leftarrow> ints_of' env ss;
                js \<leftarrow> ints_of' env ts;
                if F = G then flexflex1 env bs F Fty is js
                else flexflex2 env bs F Fty is G Gty js}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var hs then
            (case hs of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ss; flexrigid env bs F Fty is t'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Var ht then
            (case ht of
              Var F Fty \<Rightarrow> do {is \<leftarrow> ints_of' env ts; flexrigid env bs F Fty is s'}
            | _ \<Rightarrow> raise (Failure (STR ''unif'')))
          else if is_Abs hs \<or> is_Abs ht then raise Pattern
          else
            (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht)) env'"
        using body nsAbs ntAbs shs sht by (simp add: unif_step_def)
      show ?thesis
      proof (cases "is_Var hs")
        case sVar: True
        then obtain F Fty where hs: "hs = Var F Fty" by (cases hs) auto
        show ?thesis
        proof (cases "is_Var ht")
          case True
          then obtain G Gty where ht: "ht = Var G Gty" by (cases ht) auto
          from body' hs ht obtain "is" js where
            r: "ok (if F = G then flexflex1 env bs F Fty is js else flexflex2 env bs F Fty is G Gty js) env'"
            by auto
          have "step_tk env bs (app (Var F Fty) is) (app (Var G Gty) js) env'"
          proof (cases "F = G")
            case True
            with r flexflex1_tk[of env bs F Fty "is" js env' Gty] show ?thesis by simp
          next
            case False
            with r flexflex2_tk show ?thesis by simp
          qed
          from step_tk_flex[OF step_tk_sym[OF step_tk_flex[OF step_tk_sym[OF this]]]]
          show ?thesis by (simp add: s' t' hs ht)
        next
          case False
          from body' hs False obtain "is" where r: "ok (flexrigid env bs F Fty is t') env'"
            by auto
          from step_tk_flex[OF flexrigid_tk[OF r]] show ?thesis by (simp add: s' hs)
        qed
      next
        case nsVar: False
        show ?thesis
        proof (cases "is_Var ht")
          case True
          then obtain F Fty where ht: "ht = Var F Fty" by (cases ht) auto
          from body' nsVar ht obtain "is" where r: "ok (flexrigid env bs F Fty is s') env'"
            by auto
          from step_tk_sym[OF step_tk_flex[OF flexrigid_tk[OF r]]] show ?thesis by (simp add: t' ht)
        next
          case ntVar: False
          have nAbs: "\<not> is_Abs hs" "\<not> is_Abs ht" using body' nsVar ntVar by (auto split: if_splits)
          have body'': "ok (case (hs, ht) of
              (Const a Ta, Const b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Free a Ta, Free b Tb) \<Rightarrow>
                if a \<noteq> b then raise (Unif (Clash a b)) else do {
                  env' \<leftarrow> unify_types alg Ta Tb env;
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env'}
            | (Bound i, Bound j) \<Rightarrow>
                if i \<noteq> j then raise (Unif (Clash_BB bs i j)) else do {
                  ps \<leftarrow> zip_eq ss ts;
                  foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env}
            | _ \<Rightarrow> rigid_clash bs hs ht) env'"
            using body' nsVar ntVar nAbs by simp
          have nApp: "\<not> (\<exists>f u. hs = f $ u)" "\<not> (\<exists>f u. ht = f $ u)"
            using strip_comb_head[OF shs] strip_comb_head[OF sht] by simp_all
          have rigid: "step_tk env bs (hs \<degree>\<degree> ss) (ht \<degree>\<degree> ts) env'"
          proof (cases hs)
            case hsC: (Const a Ta)
            show ?thesis
            proof (cases ht)
              case (Const b Tb)
              from body'' hsC Const obtain env1 ps where ab: "a = b"
                and ut: "ok (unify_types alg Ta Tb env) env1" and ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env1) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              have "steps_tk env1 bs (zip ss ts) env'" using foldM_steps_tk[OF f[unfolded psz]] IH by blast
              from step_tk_rigid[OF ut disjI1[OF refl] len this] show ?thesis by (simp add: hsC Const ab)
            qed (use body'' hsC not_ok_rigid_clash in auto)
          next
            case hsF: (Free a Ta)
            show ?thesis
            proof (cases ht)
              case (Free b Tb)
              from body'' hsF Free obtain env1 ps where ab: "a = b"
                and ut: "ok (unify_types alg Ta Tb env) env1" and ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env1) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              have "steps_tk env1 bs (zip ss ts) env'" using foldM_steps_tk[OF f[unfolded psz]] IH by blast
              from step_tk_rigid[OF ut disjI2[OF refl] len this] show ?thesis by (simp add: hsF Free ab)
            qed (use body'' hsF not_ok_rigid_clash in auto)
          next
            case hsB: (Bound i)
            show ?thesis
            proof (cases ht)
              case (Bound j)
              from body'' hsB Bound obtain ps where ps: "ok (zip_eq ss ts) ps"
                and f: "ok (foldM (\<lambda>(s, t) env. uni alg bs s t env) ps env) env'"
                by (auto split: if_splits)
              from ps have len: "length ss = length ts" and psz: "ps = zip ss ts" by (simp_all add: ok_zip_eq)
              have "steps_tk env bs (zip ss ts) env'" using foldM_steps_tk[OF f[unfolded psz]] IH by blast
              from step_tk_rigid_same[OF len this] show ?thesis .
            qed (use body'' hsB not_ok_rigid_clash in auto)
          qed (use nsVar nAbs nApp in auto)
          then show ?thesis by (simp add: s' t')
        qed
      qed
    qed
  qed
  then show ?case by (rule step_tk_head_norm[OF hs ht])
qed

text \<open>The pattern case of \<^const>\<open>unifiers\<close>: a list of pairs, one after the other.\<close>

theorem foldM_unify_typed:
  assumes f: "ok (foldM (\<lambda>(t, u) env. unify alg t u env) tus env) env'" and fK: "finite K"
    and pi: "pinv A K env" and k: "\<forall>(t, u)\<in>set tus. tkn A env [] t \<and> tkn A env [] u"
  shows "pinv A K env' \<and> tgrow A env env'"
proof -
  have "steps_tk env [] tus env'"
  proof (rule foldM_steps_tk[OF f])
    fix s t env1 env2 assume "ok (unify alg s t env1) env2"
    then have "unif alg [] s t env1 = Some (Ok env2)" by (simp add: unify_def)
    from unif_typed[OF this refl refl] show "step_tk env1 [] s t env2" .
  qed
  from steps_tkD[OF this fK pi k] show ?thesis .
qed

end

end
