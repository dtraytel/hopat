section \<open>Variables of Problems\<close>

theory Pattern_Vars
  imports Pattern_Terms
begin

text \<open>
  A variable is identified by its name and its type, but \<open>Envir\<close> and the flex-flex cases of
  pattern unification compare names only. Like Isabelle, soundness assumes that all occurrences
  of a name have the same type (in the solution). New variables keep this invariant: their
  indices exceed \<^const>\<open>maxidx\<close>.
\<close>

fun vars :: "pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vars (Var x T) = {(x, T)}"
| "vars (Abs a T t) = vars t"
| "vars (s $ t) = vars s \<union> vars t"
| "vars _ = {}"

definition bnds :: "env \<Rightarrow> (indexname \<times> ptyp \<times> pterm) set" where
  "bnds env = {(x, U, u). vt_lookup (tenv env) x = Some (U, u)}"

definition evars :: "env \<Rightarrow> (indexname \<times> ptyp) set" where
  "evars env = (\<Union>(x, U, u)\<in>bnds env. insert (x, U) (vars u))"

definition vcons :: "tinst \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vcons \<rho> X \<longleftrightarrow> (\<forall>x T U. (x, T) \<in> X \<longrightarrow> (x, U) \<in> X \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U)"

definition below :: "integer \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "below n X \<longleftrightarrow> (\<forall>p\<in>X. snd (fst p) \<le> n)"

definition vinv :: "tinst \<Rightarrow> env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vinv \<rho> env X \<longleftrightarrow> vcons \<rho> (X \<union> evars env) \<and> below (maxidx env) (X \<union> evars env)"

lemma vcons_mono: "vcons \<rho> X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> vcons \<rho> Y"
  unfolding vcons_def by blast

lemma below_mono: "below n X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> n \<le> m \<Longrightarrow> below m Y"
  unfolding below_def by force

lemma vinv_mono: "vinv \<rho> env X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> vinv \<rho> env Y"
proof -
  assume "vinv \<rho> env X" "Y \<subseteq> X"
  moreover from \<open>Y \<subseteq> X\<close> have "Y \<union> evars env \<subseteq> X \<union> evars env" by blast
  ultimately show ?thesis
    unfolding vinv_def using vcons_mono below_mono[OF _ _ order_refl] by blast
qed

lemma vconsD: "vcons \<rho> X \<Longrightarrow> (x, T) \<in> X \<Longrightarrow> (x, U) \<in> X \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
  unfolding vcons_def by blast

lemma belowD: "below n X \<Longrightarrow> (x, T) \<in> X \<Longrightarrow> snd x \<le> n"
  unfolding below_def by force

lemma evarsI: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> (x, U) \<in> evars env"
  and evarsI2: "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> vars u \<subseteq> evars env"
  unfolding evars_def bnds_def by blast+


subsection \<open>Variables of terms\<close>

lemma vars_apps: "vars (s \<degree>\<degree> ts) = vars s \<union> \<Union> (vars ` set ts)"
  by (induction ts arbitrary: s) auto

lemma vars_incr_bv [simp]: "vars (incr_bv n k t) = vars t"
  by (induction n k t rule: incr_bv.induct) auto

lemma vars_subst: "vars (t[s/k]) \<subseteq> vars t \<union> vars s"
proof (induction t arbitrary: s k)
  case (Abs a T t)
  then show ?case using Abs.IH[of "lift s 0" "k + 1"] by simp
next
  case (App t1 t2)
  have "vars (t1[s/k]) \<subseteq> vars t1 \<union> vars s" "vars (t2[s/k]) \<subseteq> vars t2 \<union> vars s"
    by (rule App.IH(1), rule App.IH(2))
  then show ?case by auto
qed (auto simp: subst_Bound)

lemma vars_rename [simp]: "vars (rename f d t) = vars t"
  by (induction f d t rule: rename.induct) auto

lemma vars_abs_list [simp]: "vars (abs_list bs t) = vars t"
proof (induction bs)
  case (Cons b bs)
  then show ?case by (cases b) simp
qed simp

lemma vars_incr_aux [simp]: "vars (incr_aux d t) = vars t"
  by (induction d t rule: incr_aux.induct) auto

context pure_sig
begin

lemma head_norm_vars:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> vars t' \<subseteq> vars t \<union> evars env"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  note h = "1.hyps"[unfolded "1.prems"(1)]
  have IH: "vars u' \<subseteq> vars u \<union> evars env" if "ok (hn env u) u'" for u u'
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
      with IH[of u t'] rest Some show ?thesis by (auto dest: evarsI2)
    qed (use rest in simp)
  next
    case (Abs a T body)
    with h IH show ?thesis by fastforce
  next
    case (App f u)
    have redex: "vars t' \<subseteq> vars (Abs b U0 body $ u) \<union> evars env"
      if "ok (hn env (subst_bound u body)) t'" for b U0 body
      using IH[OF that] vars_subst[of body u 0] by (auto simp: subst_bound_subst)
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
      from IH[OF hf] have nf: "vars nf \<subseteq> vars f \<union> evars env" .
      show ?thesis
      proof (cases nf)
        case (Abs b U0 body)
        with rest have "ok (hn env (subst_bound u body)) t'" by simp
        from redex[OF this] nf App Abs show ?thesis by auto
      qed (use rest nf App in auto)
    qed
  qed (use h in auto)
qed


subsection \<open>Updating environments\<close>

lemma ok_update:
  assumes "ok (update (F, T) t env) env'"
  shows "vt_lookup (tenv env) F = None" "tenv env' = vt_update (F, (T, t)) (tenv env)"
    "tyenv env' = tyenv env" "maxidx env' = maxidx env"
  using assms by (cases env; auto simp: update_def ok_update_new)+

lemma extends_update: "ok (update (F, T) t env) env' \<Longrightarrow> extends env env'"
  using ok_update[of F T t env env'] by (auto simp: extends_def)

lemma bnds_update: "ok (update (F, T) t env) env' \<Longrightarrow> bnds env' = insert (F, T, t) (bnds env)"
  using ok_update[of F T t env env'] unfolding bnds_def by (auto split: if_splits)

lemma evars_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> evars env' = insert (F, T) (vars t \<union> evars env)"
  unfolding evars_def bnds_update by auto

lemma solution_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> solution \<rho> \<sigma> env' \<Longrightarrow> \<sigma> F (tsubst \<rho> T) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  using ok_update(2)[of F T t env env'] solutionD(4)[of \<rho> \<sigma> env' F T t] by simp

lemma wt_env_update:
  "ok (update (F, T) t env) env' \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> (\<And>e. e \<turnstile> inst \<rho> t : tsubst \<rho> T) \<Longrightarrow>
    wt_env \<rho> env'"
  using ok_update(2)[of F T t env env'] unfolding wt_env_def by auto

lemma genvar_simps:
  assumes "genvar a env T = (env', G)"
  shows "tenv env' = tenv env" "tyenv env' = tyenv env" "maxidx env' = maxidx env + 1"
    "G = Var (a, maxidx env + 1) T"
  using assms by (auto simp: genvar_def split: env.splits)

lemma extends_genvar: "genvar a env T = (env', G) \<Longrightarrow> extends env env'"
  by (simp add: extends_def genvar_simps)

lemma solution_genvar: "genvar a env T = (env', G) \<Longrightarrow> solution \<rho> \<sigma> env' \<longleftrightarrow> solution \<rho> \<sigma> env"
  by (simp add: solution_def genvar_simps)

lemma wt_env_genvar: "genvar a env T = (env', G) \<Longrightarrow> wt_env \<rho> env' \<longleftrightarrow> wt_env \<rho> env"
  by (simp add: wt_env_def genvar_simps)

lemma evars_genvar: "genvar a env T = (env', G) \<Longrightarrow> evars env' = evars env"
  by (simp add: evars_def bnds_def genvar_simps)

text \<open>A new variable keeps the problem consistent:\<close>

lemma vinv_genvar:
  assumes "genvar a env T = (env', G)" "vinv \<rho> env X"
  shows "vinv \<rho> env' (vars G \<union> X)"
proof -
  note g = genvar_simps[OF assms(1)] and ev = evars_genvar[OF assms(1)]
  have b: "below (maxidx env) (X \<union> evars env)" and c: "vcons \<rho> (X \<union> evars env)"
    using assms(2) by (simp_all add: vinv_def)
  have le: "maxidx env \<le> maxidx env'" using g by (simp add: integer_arith)
  have "below (maxidx env') (vars G \<union> X \<union> evars env')"
    using below_mono[OF b _ le] g ev by (auto simp: below_def)
  moreover have "vcons \<rho> (vars G \<union> X \<union> evars env')"
    unfolding vcons_def
  proof (intro allI impI)
    fix x U V assume U: "(x, U) \<in> vars G \<union> X \<union> evars env'" and V: "(x, V) \<in> vars G \<union> X \<union> evars env'"
    have new: "W = T \<and> x = (a, maxidx env + 1)" if "(x, W) \<in> vars G" for W
      using that g by simp
    have old: "snd x \<le> maxidx env" if "(x, W) \<in> X \<union> evars env" for W
      using belowD[OF b that] .
    have "(x, W) \<in> vars G \<or> (x, W) \<in> X \<union> evars env" if "(x, W) \<in> vars G \<union> X \<union> evars env'" for W
      using that ev by blast
    note UV = this[OF U] this[OF V]
    have clash: False if "(x, W) \<in> vars G" "(x, W') \<in> X \<union> evars env" for W W'
      using new[OF that(1)] old[OF that(2)] by (simp add: integer_arith)
    show "tsubst \<rho> U = tsubst \<rho> V"
      using UV
    proof (elim disjE)
      assume "(x, U) \<in> vars G" "(x, V) \<in> vars G"
      then show ?thesis using new by metis
    next
      assume "(x, U) \<in> X \<union> evars env" "(x, V) \<in> X \<union> evars env"
      with vconsD[OF c] show ?thesis .
    qed (use clash in blast)+
  qed
  ultimately show ?thesis by (simp add: vinv_def)
qed

end

end
