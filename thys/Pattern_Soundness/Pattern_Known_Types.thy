section \<open>Known Type Variables\<close>

text \<open>
  The type variables of binders, variables and environments, and the invariant that the type
  variables of the bindings are known (\<open>tvinv\<close>), with the facts on them for head
  normalization, new variables and the terms that pattern unification builds. The soundness
  of the unifiers uses them; completeness is in the theories \<open>Pattern_Complete_\<dots>\<close>.
\<close>

theory Pattern_Known_Types
  imports Pattern_Renaming
begin

subsection \<open>Variables and types of terms\<close>

lemma vars_typs: "(x, T) \<in> vars t \<Longrightarrow> T \<in> typs t"
  by (induction t) auto

lemma vars_inst: "vars (inst \<rho> t) = (\<lambda>(x, T). (x, tsubst \<rho> T)) ` vars t"
  by (induction t) auto

subsection \<open>The invariant of known type variables\<close>

context pure_sig_gen
begin

lemma typing_typs: "e \<turnstile> t : T \<Longrightarrow> U \<in> typs t \<Longrightarrow> cert_typ alg ar U"
  by (induction rule: typing.induct) auto

lemma typs_inst: "typs (inst \<rho> t) = tsubst \<rho> ` typs t"
  by (induction t) auto

text \<open>
  The invariant of the type environment (\<^const>\<open>tinv\<close>), for a set \<open>A\<close> of type variables of the
  problem, which also contains the type variables of the bindings.
\<close>

definition tvinv :: "(indexname \<times> psort) set \<Rightarrow> env \<Rightarrow> bool" where
  "tvinv A env \<longleftrightarrow> tinv ar (maxidx env) (tyenv env) A \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
      tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A)"

lemma tvinvD:
  assumes "tvinv A env"
  shows "tinv ar (maxidx env) (tyenv env) A"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A"
  using assms unfolding tvinv_def by blast+

end

subsection \<open>Type variables of variables and binders\<close>

context pure_sig_gen
begin

text \<open>The type variables of a set of variables and of binders:\<close>

definition vtvars :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> psort) set" where
  "vtvars X = (\<Union>(x, T)\<in>X. tvars T)"

definition btvars :: "binders \<Rightarrow> (indexname \<times> psort) set" where
  "btvars bs = (\<Union>(x, T)\<in>set bs. tvars T)"

lemma evarsE:
  assumes "(x, T) \<in> evars env"
  obtains y U u where "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
  using assms unfolding evars_def bnds_def by blast

lemma tvinv_evars:
  assumes "tvinv A env" "(x, T) \<in> evars env"
  shows "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  from assms(2) obtain y U u where b: "vt_lookup (tenv env) y = Some (U, u)" "(x, T) = (y, U) \<or> (x, T) \<in> vars u"
    by (rule evarsE)
  have "tvars U \<union> ttvars u \<subseteq> tvars_env (tyenv env) \<union> A" by (rule tvinvD(2)[OF assms(1) b(1)])
  with b(2) show ?thesis by (auto simp: ttvars_def dest: vars_typs)
qed

subsection \<open>Head normalization\<close>

definition etvars :: "env \<Rightarrow> (indexname \<times> psort) set" where
  "etvars env = (\<Union>(x, U, u)\<in>bnds env. tvars U \<union> ttvars u)"

lemma etvarsI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> ttvars u \<subseteq> etvars env"
  unfolding etvars_def bnds_def by blast

lemma tvinv_etvars: "tvinv A env \<Longrightarrow> etvars env \<subseteq> tvars_env (tyenv env) \<union> A"
  unfolding etvars_def bnds_def using tvinvD(2) by blast

lemma ttvars_subst: "ttvars (t[s/k]) \<subseteq> ttvars t \<union> ttvars s"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "lift s 0" "k + 1"] by (auto simp: ttvars_def)
next
  case (App t1 t2)
  have "ttvars (t1[s/k]) \<subseteq> ttvars t1 \<union> ttvars s" "ttvars (t2[s/k]) \<subseteq> ttvars t2 \<union> ttvars s"
    by (rule App.IH(1), rule App.IH(2))
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma head_norm_ttvars:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> ttvars t' \<subseteq> ttvars t \<union> etvars env"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "ttvars u' \<subseteq> ttvars u \<union> etvars env" if "ok (hn env u) u'" for u u'
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
      with IH[of u t'] rest Some show ?thesis by (auto dest: etvarsI)
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h IH show ?thesis by fastforce
  next
    case (App f u)
    have redex: "ttvars t' \<subseteq> ttvars (Abs b U0 body $ u) \<union> etvars env"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
      using IH[OF that] ttvars_subst[of body u 0] by (auto simp: subst_bound_subst)
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
      from IH[OF hf] have nf: "ttvars nf \<subseteq> ttvars f \<union> etvars env" .
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this] nf App Abs show ?thesis by auto
      qed (use rest nf App in auto)
    qed
  qed (use h in auto)
qed

lemma vtvars_Un [simp]: "vtvars (X \<union> Y) = vtvars X \<union> vtvars Y"
  by (auto simp: vtvars_def)

lemma vtvars_vars: "vtvars (vars t) \<subseteq> ttvars t"
  by (auto simp: vtvars_def ttvars_def dest: vars_typs)

lemma vtvars_evars: "tvinv A env \<Longrightarrow> vtvars (evars env) \<subseteq> tvars_env (tyenv env) \<union> A"
  using tvinv_evars unfolding vtvars_def by blast

end

subsection \<open>The type invariant for new bindings\<close>

context pure_sig_gen
begin

lemma tvinv_genvar: "genvar a env T = (env', G) \<Longrightarrow> tvinv A env \<Longrightarrow> tvinv A env'"
  unfolding tvinv_def using tinv_mono by (auto simp: genvar_simps)

lemma tvinv_update:
  assumes "ok (update (F, T) t env) env'" "tvinv A env" "tvars T \<union> ttvars t \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvinv A env'"
  using assms ok_update[OF assms(1)] unfolding tvinv_def by (auto split: if_splits)

lemma tvars_funs: "tvars (Ts \<Rrightarrow> T) = (\<Union>U\<in>set Ts. tvars U) \<union> tvars T"
  by (induction Ts) auto

lemma type_of_G_tvars:
  assumes "ok (type_of_G env T n is) G" "tvinv A env" "tvars T \<subseteq> tvars_env (tyenv env) \<union> A"
  shows "tvars G \<subseteq> tvars_env (tyenv env) \<union> A"
proof -
  let ?\<theta> = "tyenv env"
  have inv: "tinv ar (maxidx env) ?\<theta> A" by (rule tvinvD(1)[OF assms(2)])
  have nt: "norm_type ?\<theta> T = return (tnorm ?\<theta> T)"
    by (rule norm_type_ok[OF tinv_tacyc[OF inv] tinv_tcons_env[OF inv] tinv_tcons[OF inv assms(3)]])
  from assms(1) nt obtain Ts U Us where st: "ok (split_type (tnorm ?\<theta> T) n []) (Ts, U)"
    and us: "ok (mapM (nth Ts) is) Us" and G: "G = foldr (\<rightarrow>\<^sub>T) Us U"
    by (auto simp: type_of_G_def split: prod.splits)
  from ok_split_type[OF st] obtain Vs where Vs: "tnorm ?\<theta> T = foldr (\<rightarrow>\<^sub>T) Vs U" "Ts = rev Vs"
    by auto
  have tvn: "tvars (tnorm ?\<theta> T) \<subseteq> tvars_env ?\<theta> \<union> A"
    using tvars_tnorm[OF tinv_tacyc[OF inv], of T] assms(3) by blast
  have nth_set: "x \<in> set Ts" if "ok (nth Ts i) x" for i x
    using that nat_of_integer_less_ilength[of i Ts] by (auto simp: ok_nth)
  have "list_all2 (\<lambda>i x. ok (nth Ts i) x) is Us" using us by (simp add: ok_mapM)
  then have "set Us \<subseteq> set Ts" by (induction rule: list_all2_induct) (auto dest: nth_set)
  then show ?thesis using tvn Vs G by (auto simp: tvars_funs)
qed

subsection \<open>Type variables of abstractions and applications\<close>

lemma ttvars_abs_list: "ttvars (abs_list bs t) = btvars bs \<union> ttvars t"
  by (induction bs) (auto simp: btvars_def)

lemma btvars_nths:
  assumes "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
  shows "btvars (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> btvars bs"
proof -
  have "set (map (\<lambda>i. bs ! nat_of_integer i) is) \<subseteq> set bs"
    using assms by (auto intro!: nth_mem simp: nat_of_integer_less_ilength)
  then show ?thesis unfolding btvars_def by blast
qed

lemma ttvars_app [simp]: "ttvars (app s is) = ttvars s"
  by (simp add: app_apps ttvars_apps)

end

subsection \<open>Domain and range of a function type\<close>

fun dom_type :: "ptyp \<Rightarrow> ptyp" where
  "dom_type (Type a [T, U]) = (if a = STR ''fun'' then T else Type a [T, U])"
| "dom_type T = T"

fun rng_type :: "ptyp \<Rightarrow> ptyp" where
  "rng_type (Type a [T, U]) = (if a = STR ''fun'' then U else Type a [T, U])"
| "rng_type T = T"

subsection \<open>Typing of lists by their elements\<close>

context pure_sig_gen
begin

lemma typings_nthI: "length ts = length Ts \<Longrightarrow> (\<And>i. i < length ts \<Longrightarrow> e \<turnstile> ts ! i : Ts ! i) \<Longrightarrow> e \<tturnstile> ts : Ts"
proof (induction ts arbitrary: Ts)
  case (Cons t ts)
  then obtain U Us where "Ts = U # Us" by (cases Ts) auto
  with Cons show ?case by (fastforce simp: nth_Cons')
qed simp

end

end
