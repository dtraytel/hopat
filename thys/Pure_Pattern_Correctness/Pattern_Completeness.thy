section \<open>Completeness of Unification\<close>

theory Pattern_Completeness
  imports Pattern_Rigid
begin

text \<open>
  Completeness: if two well-typed terms have a unifier that solves the environment, then
  \<^const>\<open>unif\<close> does not fail with exception \<open>Unif\<close>, and if it returns an environment, the unifier
  extends to a solution of that environment (on the new variables). With soundness, this means
  that the computed environment is a most general unifier.
\<close>

subsection \<open>Solutions\<close>

text \<open>
  A solution of an environment is a closed, well-typed substitution that fixes constants and
  free variables and satisfies all bindings. The variable typing \<open>V\<close> types the schematic
  variables of the problem, \<open>\<tau>'\<close> the free variables in the range of the substitution.
\<close>

definition solution :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> bool" where
  "solution V \<tau>' \<sigma> env \<longleftrightarrow>
    closed_on UNIV \<sigma> \<and> typed_on (range code) (tau V) \<tau>' \<sigma> \<and> rigid_subst \<sigma> \<and> sat \<sigma> env"

lemma solutionD:
  assumes "solution V \<tau>' \<sigma> env"
  shows "closed_on UNIV \<sigma>" "typed_on (range code) (tau V) \<tau>' \<sigma>" "rigid_subst \<sigma>" "sat \<sigma> env"
  using assms by (simp_all add: solution_def)


subsection \<open>Variables\<close>

fun vars :: "pterm \<Rightarrow> indexname set" where
  "vars (Var x T) = {x}"
| "vars (Abs _ _ t) = vars t"
| "vars (s $ t) = vars s \<union> vars t"
| "vars _ = {}"

definition below :: "integer \<Rightarrow> pterm \<Rightarrow> bool" where
  "below m t \<longleftrightarrow> (\<forall>x\<in>vars t. snd x \<le> m)"

lemma below_mono: "below m t \<Longrightarrow> m \<le> m' \<Longrightarrow> below m' t"
  by (auto simp: below_def)

text \<open>All variables of an environment are at most its \<^const>\<open>maxidx\<close>.\<close>

definition fresh_env :: "env \<Rightarrow> bool" where
  "fresh_env env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<le> maxidx env \<and> below (maxidx env) u)"

lemma fresh_envD:
  "fresh_env env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> snd x \<le> maxidx env \<and> below (maxidx env) u"
  by (cases x) (simp add: fresh_env_def)

text \<open>Substitutions and variable typings that differ only on new variables.\<close>

definition agree :: "integer \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> bool" where
  "agree m \<sigma> \<sigma>' \<longleftrightarrow> (\<forall>n. \<sigma>' n \<noteq> \<sigma> n \<longrightarrow> (\<exists>x. n = code (AVar x) \<and> m < snd x))"

definition agreeV :: "integer \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> bool" where
  "agreeV m V V' \<longleftrightarrow> (\<forall>x. snd x \<le> m \<longrightarrow> V' x = V x)"

lemma agree_refl[simp]: "agree m \<sigma> \<sigma>" and agreeV_refl[simp]: "agreeV m V V"
  by (simp_all add: agree_def agreeV_def)

lemma agree_trans: "agree m \<sigma> \<sigma>' \<Longrightarrow> agree m' \<sigma>' \<sigma>'' \<Longrightarrow> m \<le> m' \<Longrightarrow> agree m \<sigma> \<sigma>''"
  unfolding agree_def by (metis order_le_less_trans)

lemma agreeV_trans: "agreeV m V V' \<Longrightarrow> agreeV m' V' V'' \<Longrightarrow> m \<le> m' \<Longrightarrow> agreeV m V V''"
  by (auto simp: agreeV_def)

lemma agree_Var: "agree m \<sigma> \<sigma>' \<Longrightarrow> snd x \<le> m \<Longrightarrow> \<sigma>' (code (AVar x)) = \<sigma> (code (AVar x))"
  unfolding agree_def by (metis atom.inject(3) code_inj not_less)

lemma agreeV_D: "agreeV m V V' \<Longrightarrow> snd x \<le> m \<Longrightarrow> V' x = V x"
  by (cases x) (simp add: agreeV_def)

lemma agree_rigid: "agree m \<sigma> \<sigma>' \<Longrightarrow> rigid_code n \<Longrightarrow> \<sigma>' n = \<sigma> n"
  by (auto simp: agree_def rigid_code_def)

lemma FV_tr: "n \<in> FV (tr t) \<Longrightarrow> rigid_code n \<or> (\<exists>x\<in>vars t. n = code (AVar x))"
  by (induction t) auto

lemma mk_subst_agree:
  "below m t \<Longrightarrow> agree m \<sigma> \<sigma>' \<Longrightarrow> mk_subst \<sigma>' (tr t) = mk_subst \<sigma> (tr t)"
  by (rule mk_subst_cong) (auto dest!: FV_tr simp: below_def agree_rigid agree_Var)

lemma sat_agree:
  assumes "sat \<sigma> env" "fresh_env env" "agree (maxidx env) \<sigma> \<sigma>'"
  shows "sat \<sigma>' env"
  unfolding sat_def
proof (intro allI impI)
  fix x U u assume lk: "vt_lookup (tenv env) x = Some (U, u)"
  note f = fresh_envD[OF assms(2) lk]
  have "\<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)" by (rule satD[OF assms(1) lk])
  then show "\<sigma>' (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr u)"
    using f agree_Var[OF assms(3)] mk_subst_agree[OF _ assms(3)] by simp
qed

lemma has_type_agreeV:
  "has_type V Ts t T \<Longrightarrow> below m t \<Longrightarrow> agreeV m V V' \<Longrightarrow> has_type V' Ts t T"
  by (induction rule: has_type.induct) (auto intro: has_type.intros simp: below_def agreeV_def)

lemma env_typed_agreeV:
  assumes "env_typed V env" "fresh_env env" "agreeV (maxidx env) V V'"
  shows "env_typed V' env"
  unfolding env_typed_def
proof (intro allI impI)
  fix x U u assume lk: "vt_lookup (tenv env) x = Some (U, u)"
  from env_typedD[OF assms(1) lk] fresh_envD[OF assms(2) lk] agreeV_D[OF assms(3)]
  show "V' x = U \<and> has_type V' [] u U" using has_type_agreeV assms(3) by blast
qed



subsection \<open>Types of applications, abstractions and new variables\<close>

lemma trty_foldr: "trty (foldr fun_type Us T) = map trty Us \<Rrightarrow> trty T"
  by (induction Us) auto

lemma has_type_App_Bound_iff:
  "has_type V Ts (h $ Bound i) U \<longleftrightarrow>
    0 \<le> i \<and> nat_of_integer i < length Ts \<and> has_type V Ts h ((Ts ! nat_of_integer i) \<rightarrow>\<^sub>T U)"
proof
  assume "has_type V Ts (h $ Bound i) U"
  then obtain T' where "has_type V Ts h (T' \<rightarrow>\<^sub>T U)" "has_type V Ts (Bound i) T'"
    by (rule has_type_elims(6))
  then show "0 \<le> i \<and> nat_of_integer i < length Ts \<and> has_type V Ts h ((Ts ! nat_of_integer i) \<rightarrow>\<^sub>T U)"
    by (simp add: has_type_Bound_iff)
next
  assume "0 \<le> i \<and> nat_of_integer i < length Ts \<and> has_type V Ts h ((Ts ! nat_of_integer i) \<rightarrow>\<^sub>T U)"
  then show "has_type V Ts (h $ Bound i) U"
    by (auto intro: has_type.App simp: has_type_Bound_iff)
qed

lemma has_type_app:
  "has_type V Ts (app h is) T \<longleftrightarrow>
    (\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length Ts) \<and>
    has_type V Ts h (foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is) T)"
proof (induction "is" arbitrary: h)
  case Nil
  then show ?case by (simp add: app_def)
next
  case (Cons i "is")
  have "app h (i # is) = app (h $ Bound i) is" by (simp add: app_def)
  then show ?case by (simp only: Cons has_type_App_Bound_iff) auto
qed

lemma has_type_mkabs:
  "ok (mkabs binders is b) u \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders \<Longrightarrow>
    has_type V (rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) @ Ts) b U \<Longrightarrow>
    has_type V Ts u (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) U)"
proof (induction "is" arbitrary: u Ts)
  case (Cons i "is")
  from Cons.prems(1) obtain u' where u': "ok (mkabs binders is b) u'"
    and u: "u = pterm.Abs (fst (binders ! nat_of_integer i)) (snd (binders ! nat_of_integer i)) u'"
    using Cons.prems(2) by (auto simp: ok_nth split: prod.splits)
  have "has_type V (snd (binders ! nat_of_integer i) # Ts) u'
    (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) U)"
    using Cons.IH[OF u'] Cons.prems(2,3) by simp
  then show ?case by (simp add: u has_type.Abs)
qed simp

lemma split_type_foldr:
  "split_type (foldr fun_type Us U) (integer_of_nat (length Us)) Acc = return (rev Us @ Acc, U)"
proof (induction Us arbitrary: Acc)
  case Nil
  then show ?case by (subst split_type.simps) (simp add: integer_eq_iff)
next
  case (Cons U1 Us)
  have "integer_of_nat (length (U1 # Us)) - 1 = integer_of_nat (length Us)"
    by (simp add: integer_eq_iff)
  moreover have "integer_of_nat (length (U1 # Us)) \<noteq> 0" by (simp add: integer_eq_iff)
  ultimately show ?case
    by (subst split_type.simps) (simp add: Cons.IH)
qed

lemma type_of_G_foldr:
  assumes "vt_is_empty (tyenv env)" "ok (type_of_G env (foldr fun_type Us U) (integer_of_nat (length Us)) ks) G"
  shows "G = foldr fun_type (map (\<lambda>k. rev Us ! nat_of_integer k) ks) U"
    "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us"
proof -
  from assms obtain Gs where Gs: "list_all2 (\<lambda>k G. ok (nth (rev Us) k) G) ks Gs"
    and G: "G = foldr fun_type Gs U"
    by (auto simp: type_of_G_def norm_type_def split_type_foldr ok_mapM)
  from Gs have "Gs = map (\<lambda>k. rev Us ! nat_of_integer k) ks"
    "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us"
    by (induction ks Gs rule: list_all2_induct) (auto simp: ok_nth)
  with G show "G = foldr fun_type (map (\<lambda>k. rev Us ! nat_of_integer k) ks) U"
    "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us"
    by simp_all
qed

lemma ok_mk_ff_list_aux_complete:
  "ok (mk_ff_list_aux is js k) ks \<Longrightarrow> p < length is \<Longrightarrow> is ! p = js ! p \<Longrightarrow>
    k - integer_of_nat p \<in> set ks"
proof (induction "is" js k arbitrary: ks p rule: mk_ff_list_aux.induct)
  case (2 i "is" j js k)
  show ?case
  proof (cases p)
    case 0
    with "2.prems" show ?thesis by (auto simp: integer_eq_iff)
  next
    case (Suc p')
    obtain ks' where ks': "ok (mk_ff_list_aux is js (k - 1)) ks'" "set ks' \<subseteq> set ks"
    proof (cases "i = j")
      case True
      with "2.prems"(1) obtain ks' where "ok (mk_ff_list_aux is js (k - 1)) ks'" "ks = k # ks'" by auto
      then show ?thesis using that by auto
    next
      case False
      with "2.prems"(1) show ?thesis using that by auto
    qed
    from "2.IH"[OF _ ks'(1)] "2.IH"(2)[OF _ ks'(1)] "2.prems" Suc
    have "k - 1 - integer_of_nat p' \<in> set ks'" by (cases "i = j") auto
    moreover have "k - 1 - integer_of_nat p' = k - integer_of_nat p"
      by (simp add: Suc integer_eq_iff)
    ultimately show ?thesis using ks'(2) by auto
  qed
qed auto


subsection \<open>Extending solutions\<close>

definition ext_sol :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" where
  "ext_sol V \<tau>' \<sigma> env env' \<longleftrightarrow> (\<exists>V' \<sigma>'. agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and>
    solution V' \<tau>' \<sigma>' env' \<and> env_typed V' env' \<and> fresh_env env' \<and> maxidx env \<le> maxidx env')"

lemma ext_sol_refl: "solution V \<tau>' \<sigma> env \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow> ext_sol V \<tau>' \<sigma> env env"
  unfolding ext_sol_def by (intro exI[of _ V] exI[of _ \<sigma>]) simp

definition no_unif :: "'a M \<Rightarrow> bool" where
  "no_unif m \<longleftrightarrow> (\<forall>e. m \<noteq> Some (Err (Unif e)))"

lemma no_unif_simps[simp]:
  "no_unif (return x)" "no_unif None" "no_unif (raise e) \<longleftrightarrow> (\<forall>t. e \<noteq> Unif t)"
  by (auto simp: no_unif_def return_def raise_def)

lemma no_unif_bindM: "no_unif m \<Longrightarrow> (\<And>x. ok m x \<Longrightarrow> no_unif (f x)) \<Longrightarrow> no_unif (bindM m f)"
  by (auto simp: no_unif_def bindM_def split: option.splits res.splits)

lemma no_unif_mapM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_unif (f x)) \<Longrightarrow> no_unif (mapM f xs)"
  by (induction xs) (auto intro!: no_unif_bindM)

lemma no_unif_nth: "no_unif (nth xs i)"
  by (induction xs i rule: nth.induct) auto

lemma no_unif_mkabs: "no_unif (mkabs binders is t)"
  by (induction "is") (auto intro!: no_unif_bindM no_unif_nth split: prod.splits)

lemma no_unif_update: "no_unif (update xT t env)"
  by (auto simp: update_def update_new_def split: env.splits intro!: no_unif_bindM)

lemma no_unif_split_type: "no_unif (split_type T n Ts)"
  by (induction T n Ts rule: split_type.induct) (subst split_type.simps; auto split: ptyp.splits list.splits)

lemma no_unif_type_of_G: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (type_of_G env T n is)"
  by (auto simp: type_of_G_def norm_type_def intro!: no_unif_bindM no_unif_split_type no_unif_mapM
    no_unif_nth split: prod.splits)

lemma no_unif_mk_ff_list_aux: "no_unif (mk_ff_list_aux is js k)"
  by (induction "is" js k rule: mk_ff_list_aux.induct) (auto intro!: no_unif_bindM)

lemma no_unif_mk_new_hnf: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (mk_new_hnf env binders is F T js)"
  by (auto simp: mk_new_hnf_def mk_hnf_def intro!: no_unif_bindM no_unif_type_of_G no_unif_mkabs
    no_unif_update split: prod.splits)

lemma size_foldr_fun_type: "size T \<le> size (foldr fun_type Us T)"
  by (induction Us) auto

lemma foldr_fun_type_neq: "foldr fun_type (U # Us) T \<noteq> T"
proof
  assume "foldr fun_type (U # Us) T = T"
  then have "size (U \<rightarrow>\<^sub>T foldr fun_type Us T) = size T" by simp
  with size_foldr_fun_type[of T Us] show False by simp
qed

lemma foldr_fun_type_inj: "foldr fun_type Us T = foldr fun_type Us' T \<Longrightarrow> Us = Us'"
proof (induction Us arbitrary: Us')
  case Nil
  show ?case
  proof (cases Us')
    case (Cons U Us)
    with Nil have "foldr fun_type (U # Us) T = T" by simp
    with foldr_fun_type_neq show ?thesis by blast
  qed simp
next
  case (Cons U Us)
  note prems = Cons.prems and IH = Cons.IH
  show ?case
  proof (cases Us')
    case Nil
    with prems have "foldr fun_type (U # Us) T = T" by simp
    with foldr_fun_type_neq show ?thesis by blast
  next
    case (Cons U' Us'')
    with prems IH show ?thesis by auto
  qed
qed

lemma has_type_app_Var:
  assumes "has_type V Ts (app (pterm.Var F Fty) is) T"
  shows "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length Ts" "V F = Fty"
    "Fty = foldr fun_type (map (\<lambda>i. Ts ! nat_of_integer i) is) T"
  using assms by (auto simp: has_type_app elim: has_type_elims(3))

lemma distinct_nats: "distinct is \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<Longrightarrow> distinct (nats is)"
  by (auto simp: distinct_map intro: inj_on_nat_of_integer)

lemma tau_upd: "tau (V(G := T)) (code a) = (if a = AVar G then trty T else tau V (code a))"
  by (cases a) (auto simp: tau_def)

text \<open>Extending a solution by a value for a new variable.\<close>

lemma solution_new_var:
  assumes sol: "solution V \<tau>' \<sigma> env" and fr: "fresh_env env" and ety: "env_typed V env"
    and G: "genvar a env Gty = (env1, G)"
    and w: "no_loose_bound w 0" "\<And>e. (e, \<tau>') \<turnstile> w : trty Gty"
  defines "\<sigma>' \<equiv> \<sigma>(code (AVar (a, maxidx env + 1)) := w)" and "V' \<equiv> V((a, maxidx env + 1) := Gty)"
  shows "solution V' \<tau>' \<sigma>' env1" "agree (maxidx env) \<sigma> \<sigma>'" "agreeV (maxidx env) V V'"
    "env_typed V' env1" "fresh_env env1" "maxidx env1 = maxidx env + 1"
    "G = pterm.Var (a, maxidx env + 1) Gty" "\<sigma>' (code (AVar (a, maxidx env + 1))) = w"
    "V' (a, maxidx env + 1) = Gty"
proof -
  note G' = genvar_simps[OF G]
  note \<sigma> = solutionD[OF sol]
  show ag: "agree (maxidx env) \<sigma> \<sigma>'" by (auto simp: agree_def \<sigma>'_def)
  show agV: "agreeV (maxidx env) V V'" by (auto simp: agreeV_def V'_def)
  have "closed_on UNIV \<sigma>'" using \<sigma>(1) w(1) by (auto simp: closed_on_def \<sigma>'_def)
  moreover have "typed_on (range code) (tau V') \<tau>' \<sigma>'"
    using \<sigma>(2) w(2) by (auto simp: typed_on_def \<sigma>'_def V'_def tau_upd)
  moreover have "rigid_subst \<sigma>'"
    using \<sigma>(3) by (auto simp: rigid_subst_def \<sigma>'_def)
  moreover have "sat \<sigma>' env1"
    using sat_agree[OF \<sigma>(4) fr ag] by (simp add: sat_def G')
  ultimately show "solution V' \<tau>' \<sigma>' env1" by (simp add: solution_def)
  show "env_typed V' env1" using env_typed_agreeV[OF ety fr agV] by (simp add: env_typed_def G')
  show "fresh_env env1"
    unfolding fresh_env_def G'(1,3)
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
    from fresh_envD[OF fr this] show "snd x \<le> maxidx env + 1 \<and> below (maxidx env + 1) u"
      by (auto intro: below_mono)
  qed
  show "maxidx env1 = maxidx env + 1" "G = pterm.Var (a, maxidx env + 1) Gty" by (simp_all add: G')
  show "\<sigma>' (code (AVar (a, maxidx env + 1))) = w" "V' (a, maxidx env + 1) = Gty"
    by (simp_all add: \<sigma>'_def V'_def)
qed

text \<open>Adding a binding that the solution satisfies.\<close>

lemma solution_update:
  assumes sol: "solution V \<tau>' \<sigma> env" and fr: "fresh_env env" and ety: "env_typed V env"
    and upd: "ok (update (F, T) t env) env'"
    and eqv: "\<sigma> (code (AVar F)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
    and ty: "V F = T" "has_type V [] t T" and Fm: "snd F \<le> maxidx env" and tm: "below (maxidx env) t"
  shows "solution V \<tau>' \<sigma> env'" "env_typed V env'" "fresh_env env'" "maxidx env' = maxidx env"
proof -
  note u = ok_update[OF upd]
  note \<sigma> = solutionD[OF sol]
  have "sat \<sigma> env'"
    unfolding sat_def u(2)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "\<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u')"
      using satD[OF \<sigma>(4)] eqv by (auto split: if_splits)
  qed
  then show "solution V \<tau>' \<sigma> env'" using \<sigma> by (simp add: solution_def)
  show "env_typed V env'"
    unfolding env_typed_def u(2)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "V x = U \<and> has_type V [] u' U"
      using env_typedD[OF ety] ty by (auto split: if_splits)
  qed
  show "fresh_env env'"
    unfolding fresh_env_def u(2) u(4)
  proof (intro allI impI)
    fix x U u' assume "vt_lookup (vt_update (F, T, t) (tenv env)) x = Some (U, u')"
    then show "snd x \<le> maxidx env \<and> below (maxidx env) u'"
      using fresh_envD[OF fr] Fm tm by (auto split: if_splits)
  qed
  show "maxidx env' = maxidx env" by (rule u(4))
qed

lemma vars_app: "vars (app h is) = vars h"
  by (induction "is" arbitrary: h) (simp_all add: app_def)

lemma vars_mkabs: "ok (mkabs binders is t) u \<Longrightarrow> vars u = vars t"
  by (induction "is" arbitrary: u) (auto split: prod.splits)

lemma rev_nth_less: "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - Suc n)"
  by (simp add: rev_nth)

lemma flexflex1_complete:
  assumes ff: "flexflex1 env binders F Fty is js = Some r"
    and wf: "wf_env ar env" and ety: "env_typed V env" and fr: "fresh_env env"
    and Fm: "snd F \<le> maxidx env"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) (app (pterm.Var F Fty) js) T"
    and dist: "distinct is" "distinct js"
    and sol: "solution V \<tau>' \<sigma> env"
    and uni: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var F Fty) js))"
  shows "no_unif (Some r)" "r = Ok env' \<Longrightarrow> ext_sol V \<tau>' \<sigma> env env'"
proof -
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys] and tj = has_type_app_Var[OF tyt]
  define Us where "Us = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
  have Us_eq: "map (\<lambda>i. ?Bs ! nat_of_integer i) is = Us" using ti(1) by (auto simp: Us_def)
  have Fty: "Fty = foldr fun_type Us T" using ti(3) by (simp add: Us_eq)
  have "map (\<lambda>i. ?Bs ! nat_of_integer i) js = Us"
    using foldr_fun_type_inj ti(3) tj(3) Us_eq by metis
  then have len: "length js = length is" by (metis length_map Us_def)
  have lenUs: "length Us = length is" by (simp add: Us_def)
  have "no_unif (flexflex1 env binders F Fty is js)"
    unfolding flexflex1_def mk_ff_list_def using wf_envD(1)[OF wf]
    by (auto intro!: no_unif_bindM no_unif_mk_new_hnf no_unif_mk_ff_list_aux)
  then show "no_unif (Some r)" using ff by simp
  assume r: "r = Ok env'"
  show "ext_sol V \<tau>' \<sigma> env env'"
  proof (cases "is = js")
    case True
    with ff r have "env' = env" by (simp add: flexflex1_def)
    with sol ety fr show ?thesis by (simp add: ext_sol_refl)
  next
    case False
    with ff r obtain ks where ks: "ok (mk_ff_list is js) ks"
      and hnf: "ok (mk_new_hnf env binders is F Fty ks) env'"
      by (auto simp: flexflex1_def)
    from hnf obtain Gty env1 G t where Gty: "ok (type_of_G env Fty (ilength is) ks) Gty"
      and G: "genvar (fst F) env Gty = (env1, G)" and t: "ok (mkabs binders is (app G ks)) t"
      and env': "ok (update (F, Fty) t env1) env'"
      by (rule ok_mk_new_hnf)
    let ?G = "(fst F, maxidx env + 1)"
    have Gty': "Gty = foldr fun_type (map (\<lambda>k. rev Us ! nat_of_integer k) ks) T"
      "\<forall>k\<in>set ks. 0 \<le> k \<and> nat_of_integer k < length Us"
      using type_of_G_foldr[OF wf_envD(1)[OF wf], of Us T ks Gty] Gty Fty lenUs
      by (simp_all add: ilength_eq)
    note \<sigma> = solutionD[OF sol]
    let ?u = "\<sigma> (code (AVar F))"
    have cu: "no_loose_bound ?u 0" using closed_onD[OF \<sigma>(1)] by simp
    have tyu: "(e, \<tau>') \<turnstile> ?u : map trty Us \<Rrightarrow> trty T" for e
      using typed_onD[OF \<sigma>(2) rangeI[of code "AVar F"], of e] ti(2) Fty by (simp add: trty_foldr)
    have nis: "distinct (nats is)" "distinct (nats js)"
      using dist ti(1) tj(1) by (auto intro: distinct_nats)
    have eq: "?u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?u \<degree>\<degree> map BVar (nats js)"
      using uni by (simp add: unifies_def tr_app' comp_def)
    define Z where "Z = {nats is ! p | p. p < length (nats is) \<and> nats is ! p = nats js ! p}"
    have dep: "dep_on Z (?u \<degree>\<degree> map BVar (nats is))"
      using ff1_dep[OF cu tyu _ _ nis eq] lenUs len by (simp add: Z_def)
    have cover: "k \<in> set (nats ks)"
      if k: "k < length (nats is)" "nats is ! (length (nats is) - Suc k) \<in> Z" for k
    proof -
      let ?p = "length is - Suc k"
      from k obtain p where p: "p < length is" "nats is ! ?p = nats is ! p" "nats is ! p = nats js ! p"
        by (auto simp: Z_def)
      have "?p = p" using nth_eq_iff_index_eq[OF nis(1), of ?p p] p(1,2) k(1) by simp
      then have "is ! ?p = js ! ?p"
        using p(1,3) ti(1) tj(1) len by (simp add: nat_of_integer_eq_iff)
      from ok_mk_ff_list_aux_complete[OF ks[unfolded mk_ff_list_def] _ this] k(1)
      have "ilength is - 1 - integer_of_nat ?p \<in> set ks" by simp
      moreover have "nat_of_integer (ilength is - 1 - integer_of_nat ?p) = k"
        using k(1) by (simp add: ilength_eq integer_reps)
      ultimately show ?thesis by force
    qed
    obtain w where w: "no_loose_bound w 0"
      "(e0, \<tau>') \<turnstile> w : map (env_ext e0 (map trty Us)) (nats ks) \<Rrightarrow> trty T"
      "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats is)) (w \<degree>\<degree> map BVar (nats ks))"
      using restrict_flex[OF cu tyu[of e0] _ nis(1) dep cover] lenUs by auto
    have meq: "map (trty \<circ> (\<lambda>k. rev Us ! nat_of_integer k)) ks =
      map (env_ext e0 (map trty Us) \<circ> nat_of_integer) ks"
      using Gty'(2) by (auto simp: env_ext_less rev_nth intro!: map_cong)
    have trGty: "trty Gty = map (env_ext e0 (map trty Us)) (nats ks) \<Rrightarrow> trty T"
      by (simp only: Gty'(1) trty_foldr map_map meq)
    have tyw: "(e, \<tau>') \<turnstile> w : trty Gty" for e
      using typing_closed[OF w(2) w(1)] trGty by simp
    note nv = solution_new_var[OF sol fr ety G w(1) tyw]
    define \<sigma>' where "\<sigma>' = \<sigma>(code (AVar ?G) := w)"
    define V' where "V' = V(?G := Gty)"
    have F_ne: "F \<noteq> ?G" using Fm by (cases F) auto
    have tt: "tr t = Abs_m (length is) (dB.Var (code (AVar ?G)) \<degree>\<degree> map BVar (nats ks))"
      using ok_mkabs[OF t] nv(7) by (simp add: tr_app')
    have eqv: "\<sigma>' (code (AVar F)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr t)"
      using w(3) F_ne by (simp add: tt \<sigma>'_def comp_def)
    have tyt: "has_type V' [] t Fty"
    proof -
      have "has_type V' (rev Us) (app G ks) T"
        unfolding has_type_app using Gty' nv(7,9)[folded V'_def] lenUs
        by (auto intro: has_type.Var simp: \<sigma>'_def V'_def)
      then have "has_type V' (rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) @ []) (app G ks) T"
        by (simp add: Us_def)
      from has_type_mkabs[OF t _ this] ti(1) show ?thesis by (simp add: Fty Us_def)
    qed
    have VF: "V' F = Fty" using ti(2) F_ne by (simp add: V'_def)
    have below_t: "below (maxidx env1) t" using vars_mkabs[OF t] by (simp add: below_def vars_app nv(6,7))
    have Fm1: "snd F \<le> maxidx env1" using Fm nv(6) by simp
    note up = solution_update[OF nv(1)[folded \<sigma>'_def V'_def] nv(5) nv(4)[folded V'_def] env' eqv VF tyt Fm1 below_t]
    show ?thesis
      unfolding ext_sol_def
      using up nv(2,3)[folded \<sigma>'_def V'_def] nv(6) by (intro exI[of _ V'] exI[of _ \<sigma>']) auto
  qed
qed

end
