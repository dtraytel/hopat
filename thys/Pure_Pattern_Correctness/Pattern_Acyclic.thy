section \<open>Dependencies between the Variables of an Environment\<close>

theory Pattern_Acyclic
  imports Pattern_Patterns
begin

text \<open>
  The functions \<^const>\<open>head_norm\<close>, \<^const>\<open>occurs\<close>, \<^const>\<open>pr\<close> and \<^const>\<open>unif\<close> are partial:
  they diverge on cyclic environments. This theory introduces the dependency relation between the
  variables of an environment, acyclic environments, and how binding steps change them.
\<close>

subsection \<open>Variables and their dependencies\<close>

text \<open>
  Variables are identified with their type, as in \<^const>\<open>lookup\<close>: a variable occurring with a
  type different from the one of its binding is stuck (\<^const>\<open>lookup\<close> raises an exception).
  \<open>lk env x T\<close> is the binding of \<open>x\<close> at type \<open>T\<close>.
\<close>

context csig
begin

definition lk :: "env \<Rightarrow> indexname \<Rightarrow> ptyp \<Rightarrow> pterm option" where
  "lk env x T = (case vt_lookup (tenv env) x of Some (U, u) \<Rightarrow> if U = T then Some u else None | None \<Rightarrow> None)"

lemma lkD: "lk env x T = Some u \<Longrightarrow> vt_lookup (tenv env) x = Some (T, u)"
  by (auto simp: lk_def split: option.splits if_splits)

fun vps :: "pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps (Var x T) = {(x, T)}"
| "vps (Abs _ _ t) = vps t"
| "vps (s $ t) = vps s \<union> vps t"
| "vps _ = {}"

lemma finite_vps[simp]: "finite (vps t)"
  by (induction t) auto

lemma vps_incr_bv: "vps (incr_bv inc lev t) = vps t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma vps_incr_aux: "vps (incr_aux d t) = vps t"
  by (induction d t rule: incr_aux.induct) auto

lemma vps_incr[simp]: "vps (incr t) = vps t"
  by (simp add: incr_def vps_incr_aux)

lemma vps_subst_bound_aux: "vps (subst_bound_aux arg lev t) \<subseteq> vps arg \<union> vps t"
  by (induction arg lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_def vps_incr_bv)

lemma vps_subst_bound: "vps (subst_bound arg t) \<subseteq> vps arg \<union> vps t"
  using vps_subst_bound_aux[of arg 0 t] by (simp add: subst_bound_def)

lemma vps_list_comb: "vps (list_comb h ts) = vps h \<union> \<Union> (vps ` set ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma vps_app[simp]: "vps (app h is) = vps h"
  by (induction "is" arbitrary: h) (simp_all add: app_def)

lemma vps_vars: "y \<in> vps t \<Longrightarrow> fst y \<in> vars t"
  by (induction t) auto

lemma vps_mkabs: "ok (mkabs binders is t) u \<Longrightarrow> vps u = vps t"
  by (induction "is" arbitrary: u) (auto split: prod.splits)

lemma below_vps: "below m t \<Longrightarrow> y \<in> vps t \<Longrightarrow> snd (fst y) \<le> m"
  using vps_vars by (auto simp: below_def)

definition dep :: "env \<Rightarrow> ((indexname \<times> ptyp) \<times> (indexname \<times> ptyp)) set" where
  "dep env = {(y, xT). \<exists>u. lk env (fst xT) (snd xT) = Some u \<and> y \<in> vps u}"

lemma dep_iff: "(y, (x, T)) \<in> dep env \<longleftrightarrow> (\<exists>u. lk env x T = Some u \<and> y \<in> vps u)"
  by (simp add: dep_def)

definition reach :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "reach env X = {y. \<exists>x\<in>X. (y, x) \<in> (dep env)\<^sup>*}"

lemma reach_incl: "X \<subseteq> reach env X"
  by (auto simp: reach_def)

lemma reach_mono: "X \<subseteq> reach env Y \<Longrightarrow> reach env X \<subseteq> reach env Y"
  by (auto simp: reach_def intro: rtrancl_trans)

lemma reach_subset: "X \<subseteq> Y \<Longrightarrow> reach env X \<subseteq> reach env Y"
  by (auto simp: reach_def)

lemma reach_Un: "reach env (X \<union> Y) = reach env X \<union> reach env Y"
  by (auto simp: reach_def)

lemma reach_lk: "lk env x T = Some u \<Longrightarrow> reach env (vps u) \<subseteq> reach env {(x, T)}"
proof
  fix y assume "y \<in> reach env (vps u)" and lu: "lk env x T = Some u"
  then obtain z where "z \<in> vps u" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  moreover from \<open>z \<in> vps u\<close> lu have "(z, (x, T)) \<in> dep env" by (auto simp: dep_iff)
  ultimately show "y \<in> reach env {(x, T)}" by (auto simp: reach_def intro: rtrancl_into_rtrancl)
qed


subsection \<open>Acyclic environments\<close>

definition acyc :: "env \<Rightarrow> bool" where
  "acyc env \<longleftrightarrow> acyclic (dep env)"

lemma finite_dep: "finite (dep env)"
proof -
  let ?D = "{x. vt_lookup (tenv env) x \<noteq> None}"
  have "dep env \<subseteq> (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))"
  proof
    fix p assume "p \<in> dep env"
    then obtain y x T u where p: "p = (y, (x, T))" "lk env x T = Some u" "y \<in> vps u"
      by (auto simp: dep_def)
    from lkD[OF p(2)] p show "p \<in> (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))" by (intro UN_I[of x]) auto
  qed
  moreover have "finite (\<Union>x\<in>?D. (\<lambda>y. (y, (x, fst (the (vt_lookup (tenv env) x))))) `
      vps (snd (the (vt_lookup (tenv env) x))))"
    using finite_vt_lookup[of "tenv env"] by simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma wf_dep: "acyc env \<Longrightarrow> wf (dep env)"
  by (simp add: acyc_def finite_acyclic_wf finite_dep)

lemma reach_lk_trancl:
  assumes "lk env x T = Some u" "y \<in> reach env (vps u)"
  shows "(y, (x, T)) \<in> (dep env)\<^sup>+"
proof -
  from assms(2) obtain z where "z \<in> vps u" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  moreover from \<open>z \<in> vps u\<close> assms(1) have "(z, (x, T)) \<in> dep env" by (auto simp: dep_iff)
  ultimately show ?thesis by (blast intro: rtrancl_into_trancl1)
qed

text \<open>
  The invariant of unification problems: an acyclic, well-formed environment, typed by \<open>W\<close>,
  whose variables and bindings are not newer than \<^const>\<open>maxidx\<close>.
\<close>

definition env_inv :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "env_inv ar W env \<longleftrightarrow> acyc env \<and> wf_env ar env \<and> env_typed W env \<and> fresh_env env"

lemma env_invD:
  assumes "env_inv ar W env"
  shows "acyc env" "wf_env ar env" "env_typed W env" "fresh_env env"
  using assms by (simp_all add: env_inv_def)


subsection \<open>Extending environments\<close>

lemma extends_lk:
  assumes "extends env' env" "lk env x T = Some u"
  shows "lk env' x T = Some u"
proof -
  have "vt_lookup (tenv env') x = Some (T, u)" using assms(1) lkD[OF assms(2)] unfolding extends_def by blast
  then show ?thesis by (simp add: lk_def)
qed

lemma dep_extends: "extends env' env \<Longrightarrow> dep env \<subseteq> dep env'"
  by (auto simp: dep_def dest: extends_lk)

lemma reach_extends: "extends env' env \<Longrightarrow> reach env X \<subseteq> reach env' X"
  unfolding reach_def using rtrancl_mono[OF dep_extends] by blast


lemma lk_tenv: "tenv env' = tenv env \<Longrightarrow> lk env' = lk env"
  by (simp add: lk_def fun_eq_iff)


lemma dep_tenv: assumes "tenv env' = tenv env" shows "dep env' = dep env"
  unfolding dep_def lk_tenv[OF assms] by (rule refl)


lemma reach_tenv: assumes "tenv env' = tenv env" shows "reach env' = reach env"
  unfolding reach_def dep_tenv[OF assms] by (rule refl)


subsection \<open>Unbound reachable variables\<close>

definition unb :: "env \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> (indexname \<times> ptyp) set" where
  "unb env X = {y \<in> reach env X. lk env (fst y) (snd y) = None}"

lemma unb_subset: "X \<subseteq> Y \<Longrightarrow> unb env X \<subseteq> unb env Y"
  unfolding unb_def using reach_subset[of X Y env] by blast

lemma unb_reach_mono: "A \<subseteq> reach env B \<Longrightarrow> unb env A \<subseteq> unb env B"
  using reach_mono[of A env B] by (auto simp: unb_def)

lemma reach_pred: "(y, z) \<in> dep env \<Longrightarrow> z \<in> reach env X \<Longrightarrow> y \<in> reach env X"
  by (auto simp: reach_def intro: converse_rtrancl_into_rtrancl)

lemma reach_Domain: "reach env X \<subseteq> X \<union> Domain (dep env)"
proof
  fix y assume "y \<in> reach env X"
  then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  from x(2) have "y = x \<or> (\<exists>z. (y, z) \<in> dep env)" by (cases rule: converse_rtranclE) auto
  with x(1) show "y \<in> X \<union> Domain (dep env)" by auto
qed

lemma finite_reach:
  assumes "finite X"
  shows "finite (reach env X)"
proof -
  have "finite (X \<union> Domain (dep env))" using assms finite_dep by (simp add: finite_Domain)
  with reach_Domain[of env X] show ?thesis by (rule finite_subset)
qed

lemma finite_unb: "finite X \<Longrightarrow> finite (unb env X)"
  using finite_reach[of X env] by (auto simp: unb_def)

lemma reach_unbound: "lk env x T = None \<Longrightarrow> reach env {(x, T)} = {(x, T)}"
proof -
  assume u: "lk env x T = None"
  have "y = (x, T)" if "(y, (x, T)) \<in> (dep env)\<^sup>*" for y
    using that by (cases rule: rtranclE) (auto simp: dep_def u)
  then show ?thesis by (auto simp: reach_def)
qed

lemma lk_update:
  "tenv env' = vt_update (F, (T, u)) (tenv env) \<Longrightarrow>
    lk env' x X = (if x = F then (if X = T then Some u else None) else lk env x X)"
  by (simp add: lk_def)

lemma dep_update:
  assumes "tenv env' = vt_update (F, (T, u)) (tenv env)" "vt_lookup (tenv env) F = None"
  shows "dep env' = dep env \<union> (\<lambda>y. (y, (F, T))) ` vps u"
proof -
  have "lk env F X = None" for X using assms(2) by (simp add: lk_def)
  then show ?thesis using lk_update[OF assms(1)] by (auto simp: dep_def)
qed

lemma dep_update_path:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
    and p: "(a, b) \<in> (dep env')\<^sup>*"
  shows "(a, b) \<in> (dep env)\<^sup>* \<or> (a \<in> reach env V \<and> (c, b) \<in> (dep env)\<^sup>*)"
  using p
proof (induction rule: rtrancl_induct)
  case (step b d')
  from step.hyps(2) d consider "(b, d') \<in> dep env" | "d' = c" "b \<in> V" by auto
  then show ?case
  proof cases
    case 1
    with step.IH show ?thesis by (auto intro: rtrancl_into_rtrancl)
  next
    case 2
    from step.IH 2 have "a \<in> reach env V" by (auto simp: reach_def)
    with 2 show ?thesis by simp
  qed
qed simp

lemma reach_update:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
  shows "reach env' X = reach env X \<union> (if c \<in> reach env X then reach env V else {})"
proof
  show "reach env' X \<subseteq> reach env X \<union> (if c \<in> reach env X then reach env V else {})"
  proof
    fix y assume "y \<in> reach env' X"
    then obtain x where x: "x \<in> X" "(y, x) \<in> (dep env')\<^sup>*" by (auto simp: reach_def)
    from dep_update_path[OF d c x(2)] x(1)
    show "y \<in> reach env X \<union> (if c \<in> reach env X then reach env V else {})"
      by (auto simp: reach_def)
  qed
next
  have sub: "dep env \<subseteq> dep env'" using d by auto
  then have "reach env X \<subseteq> reach env' X" unfolding reach_def using rtrancl_mono by blast
  moreover have "reach env V \<subseteq> reach env' X" if "c \<in> reach env X"
  proof
    fix y assume "y \<in> reach env V"
    then obtain z where z: "z \<in> V" "(y, z) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
    from that obtain x where x: "x \<in> X" "(c, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
    have "(y, z) \<in> (dep env')\<^sup>*" "(c, x) \<in> (dep env')\<^sup>*" using z(2) x(2) rtrancl_mono[OF sub] by auto
    moreover have "(z, c) \<in> dep env'" using d z(1) by auto
    ultimately have "(y, x) \<in> (dep env')\<^sup>*" by (meson rtrancl_into_rtrancl rtrancl_trans)
    with x(1) show "y \<in> reach env' X" by (auto simp: reach_def)
  qed
  ultimately show "reach env X \<union> (if c \<in> reach env X then reach env V else {}) \<subseteq> reach env' X"
    by auto
qed

lemma acyclic_update:
  assumes d: "dep env' = dep env \<union> (\<lambda>y. (y, c)) ` V" and c: "c \<notin> reach env V"
    and ac: "acyclic (dep env)"
  shows "acyclic (dep env')"
  unfolding acyclic_def
proof
  fix x
  show "(x, x) \<notin> (dep env')\<^sup>+"
  proof
    assume "(x, x) \<in> (dep env')\<^sup>+"
    then obtain z where xz: "(x, z) \<in> dep env'" and zx: "(z, x) \<in> (dep env')\<^sup>*"
      by (auto dest: tranclD)
    from xz d consider "(x, z) \<in> dep env" | "z = c" "x \<in> V" by auto
    then show False
    proof cases
      case 1
      from dep_update_path[OF d c zx] show False
      proof
        assume "(z, x) \<in> (dep env)\<^sup>*"
        with 1 have "(x, x) \<in> (dep env)\<^sup>+" by (rule rtrancl_into_trancl2)
        with ac show False unfolding acyclic_def by blast
      next
        assume "z \<in> reach env V \<and> (c, x) \<in> (dep env)\<^sup>*"
        then have "x \<in> reach env V" "(c, x) \<in> (dep env)\<^sup>*" using reach_pred[OF 1] by auto
        then have "c \<in> reach env V" by (auto simp: reach_def intro: rtrancl_trans)
        with c show False by simp
      qed
    next
      case 2
      from dep_update_path[OF d c zx[unfolded 2(1)]] 2(2) have "c \<in> reach env V"
        by (auto simp: reach_def)
      with c show False by simp
    qed
  qed
qed

lemma unb_update:
  assumes "tenv env' = vt_update (F, (T, u)) (tenv env)" "vt_lookup (tenv env) F = None"
    and c: "(F, T) \<notin> reach env (vps u)"
  shows "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
proof -
  note r = reach_update[OF dep_update[OF assms(1,2)] c]
  have l: "lk env' (fst y) (snd y) = None \<longleftrightarrow> y \<noteq> (F, T) \<and> lk env (fst y) (snd y) = None" for y
    using lk_update[OF assms(1)] assms(2) by (cases y) (auto simp: lk_def)
  have "(F, T) \<notin> unb env (vps u)" using c by (auto simp: unb_def)
  then show ?thesis unfolding unb_def r l by auto
qed

lemma unb_tenv: assumes "tenv env' = tenv env" shows "unb env' = unb env"
  unfolding unb_def reach_tenv[OF assms] lk_tenv[OF assms] by (rule refl)

text \<open>
  A step that binds the variables in \<open>D\<close> and introduces the fewer new variables in \<open>N\<close>
  decreases the number of unbound variables.
\<close>

lemma card_unb_less:
  assumes "finite A" "unb' \<subseteq> (A - D) \<union> N" "D \<subseteq> A" "card N < card D" "finite N"
  shows "card unb' < card A"
proof -
  have "card unb' \<le> card ((A - D) \<union> N)" using assms by (intro card_mono) auto
  also have "\<dots> \<le> card (A - D) + card N" by (rule card_Un_le)
  also have "card (A - D) = card A - card D" using assms(1,3) by (simp add: card_Diff_subset finite_subset)
  also have "card D \<le> card A" using assms(1,3) by (rule card_mono)
  then have "card A - card D + card N < card A" using assms(4) by linarith
  finally show ?thesis .
qed


subsection \<open>Fresh variables and binding steps\<close>

definition fr :: "env \<Rightarrow> (indexname \<times> ptyp) set" where
  "fr env = {y. maxidx env < snd (fst y)}"

lemma fr_mono: "maxidx env \<le> maxidx env' \<Longrightarrow> fr env' \<subseteq> fr env"
  by (auto simp: fr_def)

lemma reach_old:
  assumes "fresh_env env" "\<forall>y\<in>X. snd (fst y) \<le> maxidx env" "y \<in> reach env X"
  shows "snd (fst y) \<le> maxidx env"
proof -
  from assms(3) obtain x where x: "x \<in> X" "(y, x) \<in> (dep env)\<^sup>*" by (auto simp: reach_def)
  from x(2) show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    with x(1) assms(2) show ?case by simp
  next
    case (step y z)
    then obtain u where "lk env (fst z) (snd z) = Some u" "y \<in> vps u" by (auto simp: dep_def)
    with fresh_envD[OF assms(1) lkD] vps_vars[of y u] show ?case by (auto simp: below_def)
  qed
qed

lemma lk_fresh: "fresh_env env \<Longrightarrow> maxidx env < snd x \<Longrightarrow> lk env x T = None"
  using fresh_envD[of env x] by (cases "vt_lookup (tenv env) x") (auto simp: lk_def)



lemma bind_step:
  assumes ac: "acyc env" and fr: "fresh_env env"
    and upd: "ok (update (F, T) u env) env'" and nc: "(F, T) \<notin> reach env (vps u)"
    and Fm: "snd F \<le> maxidx env" and bu: "below (maxidx env) u"
  shows "acyc env'" "fresh_env env'" "extends env' env" "maxidx env' = maxidx env"
    "vt_lookup (tenv env) F = None"
    "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
    "reach env' X = reach env X \<union> (if (F, T) \<in> reach env X then reach env (vps u) else {})"
    "lk env' F T = Some u"
proof -
  note up = ok_update[OF upd]
  have d: "dep env' = dep env \<union> (\<lambda>y. (y, (F, T))) ` vps u" by (rule dep_update[OF up(2,1)])
  show "acyc env'" using acyclic_update[OF d nc] ac by (simp add: acyc_def)
  show "fresh_env env'"
    unfolding fresh_env_def
  proof (intro allI impI)
    fix x U' u' assume "vt_lookup (tenv env') x = Some (U', u')"
    then consider "x = F" "u' = u" | "vt_lookup (tenv env) x = Some (U', u')"
      using up(2) by (auto split: if_splits)
    then show "snd x \<le> maxidx env' \<and> below (maxidx env') u'"
      using fresh_envD[OF fr] Fm bu up(4) by cases auto
  qed
  show "extends env' env" by (rule ok_update_extends[OF upd])
  show "maxidx env' = maxidx env" by (rule up(4))
  show "vt_lookup (tenv env) F = None" by (rule up(1))
  show "unb env' X = (unb env X - {(F, T)}) \<union> (if (F, T) \<in> reach env X then unb env (vps u) else {})"
    by (rule unb_update[OF up(2,1) nc])
  show "reach env' X = reach env X \<union> (if (F, T) \<in> reach env X then reach env (vps u) else {})"
    by (rule reach_update[OF d nc])
  show "lk env' F T = Some u" using ok_update_lookup[OF upd] by (simp add: lk_def)
qed

lemma int_succ_not_le: "\<not> (m + 1 \<le> (m :: integer))"
  by (simp add: less_eq_integer.rep_eq)

lemma int_le_succ: "x \<le> m \<Longrightarrow> x \<le> (m :: integer) + 1"
  by (simp add: less_eq_integer.rep_eq)

lemma fresh_env_genvar:
  assumes "genvar a env T = (env', H)" "fresh_env env"
  shows "fresh_env env'"
  unfolding fresh_env_def
proof (intro allI impI)
  note g = genvar_simps[OF assms(1)]
  fix x U u assume "vt_lookup (tenv env') x = Some (U, u)"
  with fresh_envD[OF assms(2)] g(1) have "snd x \<le> maxidx env" "below (maxidx env) u" by auto
  then show "snd x \<le> maxidx env' \<and> below (maxidx env') u"
    using g(3) int_le_succ by (auto intro: below_mono)
qed

end

end
