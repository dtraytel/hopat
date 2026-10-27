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

lemma below_simps[simp]:
  "below m (s $ t) \<longleftrightarrow> below m s \<and> below m t" "below m (Abs a T t) \<longleftrightarrow> below m t"
  "below m (Var x T) \<longleftrightarrow> snd x \<le> m" "below m (Const c T)" "below m (Free f T)" "below m (Bound i)"
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

lemma has_type_mkabs0:
  "ok (mkabs binders is b) u \<Longrightarrow> \<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders \<Longrightarrow>
    has_type V (rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) is)) b U \<Longrightarrow>
    has_type V [] u (foldr fun_type (map (\<lambda>i. snd (binders ! nat_of_integer i)) is) U)"
  using has_type_mkabs[of binders "is" b u V "[]" U] by simp

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

lemma no_unif_Ok[simp]: "no_unif (Some (Ok x))"
  by (simp add: no_unif_def)

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

text \<open>Instances of typed terms are typed.\<close>

lemma FV_tr_range: "FV (tr t) \<subseteq> range code"
  using FV_tr by (fastforce simp: rigid_code_def)

lemma has_type_subst:
  "has_type V Ts t T \<Longrightarrow> typed_on (range code) (tau V) \<tau>' \<sigma> \<Longrightarrow>
    (bnd_env Ts, \<tau>') \<turnstile> mk_subst \<sigma> (tr t) : trty T"
  by (rule typing_mk_subst[OF has_type_tr typed_on_mono[OF _ FV_tr_range]])

lemma idx_eq_return: "Unification.idx is j = Some n \<Longrightarrow> idx is j = return (integer_of_nat n)"
  by (induction "is") (auto simp: ilength_eq split: if_splits)

lemma no_unif_mapM_idx: "set ks \<subseteq> set xs \<Longrightarrow> no_unif (mapM (idx xs) ks)"
proof (rule no_unif_mapM)
  fix k assume "set ks \<subseteq> set xs" "k \<in> set ks"
  then obtain n where "Unification.idx xs k = Some n" using idx_None_iff[of xs k] by auto
  then show "no_unif (idx xs k)" by (simp add: idx_eq_return)
qed

lemma ok_mapM_idx_nats:
  assumes "ok (mapM (idx xs) ks) ks'" "\<forall>i\<in>set xs. 0 \<le> i" "\<forall>k\<in>set ks. 0 \<le> k"
  shows "nats ks' = map (\<lambda>k. the (Unification.idx (nats xs) k)) (nats ks)" "set ks \<subseteq> set xs"
proof -
  have *: "nat_of_integer k' = the (Unification.idx (nats xs) (nat_of_integer k)) \<and> k \<in> set xs"
    if "ok (idx xs k) k'" "0 \<le> k" for k k'
  proof -
    from that(1) obtain n where n: "Unification.idx xs k = Some n" "k' = integer_of_nat n"
      by (auto simp: ok_idx)
    have "k \<in> set xs" using n(1) idx_None_iff[of xs k] by auto
    moreover have "inj_on nat_of_integer (insert k (set xs))"
      using assms(2) that(2) calculation by (intro inj_on_nat_of_integer) auto
    ultimately show ?thesis using idx_map_inj_on[of nat_of_integer k xs] n by simp
  qed
  from assms(1) have "list_all2 (\<lambda>k k'. ok (idx xs k) k') ks ks'" by (simp add: ok_mapM)
  then show "nats ks' = map (\<lambda>k. the (Unification.idx (nats xs) k)) (nats ks)" "set ks \<subseteq> set xs"
    using assms(3) * by (induction ks ks' rule: list_all2_induct) auto
qed

text \<open>Two flexible terms that are equivalent only depend on their common arguments.\<close>

lemma flex_flex_dep:
  assumes "no_loose_bound u 0" "no_loose_bound w 0"
    "u \<degree>\<degree> map BVar xs \<equiv>\<^sub>\<beta>\<^sub>\<eta> w \<degree>\<degree> map BVar ys"
  shows "dep_on (set xs \<inter> set ys) (u \<degree>\<degree> map BVar xs)"
proof -
  from closure_confluent[OF assms(3)] obtain c where
    c: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar xs) c" "\<beta>\<eta>cl (w \<degree>\<degree> map BVar ys) c" by blast
  have "loose_BVars c \<subseteq> set xs" "loose_BVars c \<subseteq> set ys"
    using loose_BVars_\<beta>\<eta>cl[OF c(1)] loose_BVars_\<beta>\<eta>cl[OF c(2)]
      no_loose_bound_loose_BVars[OF assms(1)] no_loose_bound_loose_BVars[OF assms(2)] by auto
  then show ?thesis by (intro dep_onI[OF \<beta>\<eta>cl_into_equiv[OF c(1)]]) auto
qed

lemma typ_idx:
  assumes "ok (mapM (idx xs) ks) ks'" "set ks \<subseteq> set xs"
  shows "map (\<lambda>k. rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) xs) ! nat_of_integer k) ks' =
    map (\<lambda>j. snd (binders ! nat_of_integer j)) ks"
proof -
  have "list_all2 (\<lambda>k k'. ok (idx xs k) k') ks ks'" using assms(1) by (simp add: ok_mapM)
  then show ?thesis using assms(2)
  proof (induction ks ks' rule: list_all2_induct)
    case (Cons k ks k' ks')
    from Cons.hyps(1) obtain n where n: "Unification.idx xs k = Some n" "k' = integer_of_nat n"
      by (auto simp: ok_idx)
    from idx_SomeD[OF n(1)] have nl: "n < length xs" "xs ! (length xs - Suc n) = k" by auto
    then have "length xs - Suc n < length xs" by simp
    with nl have "rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) xs) ! n = snd (binders ! nat_of_integer k)"
      by (simp add: rev_nth)
    with Cons n show ?case by simp
  qed simp
qed

lemma ff_complete:
  assumes ff: "ff env binders F Fty is G Gty js = Some r"
    and wf: "wf_env ar env" and ety: "env_typed V env" and fr: "fresh_env env"
    and Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env" and FG: "F \<noteq> G"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) (app (pterm.Var G Gty) js) T"
    and dist: "distinct is" "distinct js"
    and sol: "solution V \<tau>' \<sigma> env"
    and uni: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var G Gty) js))"
  shows "no_unif (Some r)" "r = Ok env' \<Longrightarrow> ext_sol V \<tau>' \<sigma> env env'"
proof -
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys] and tj = has_type_app_Var[OF tyt]
  define UsF where "UsF = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
  define UsG where "UsG = map (\<lambda>i. snd (binders ! nat_of_integer i)) js"
  have Fty: "Fty = foldr fun_type UsF T" using ti(1,3) by (auto simp: UsF_def intro!: arg_cong2[of _ _ _ _ "foldr fun_type"])
  have Gty: "Gty = foldr fun_type UsG T" using tj(1,3) by (auto simp: UsG_def intro!: arg_cong2[of _ _ _ _ "foldr fun_type"])
  have nonneg: "\<forall>i\<in>set is. 0 \<le> i" "\<forall>j\<in>set js. 0 \<le> j" using ti(1) tj(1) by auto
  let ?ks = "inter js is"
  have ks_sub: "set ?ks \<subseteq> set is" "set ?ks \<subseteq> set js" by (auto simp: inter_def)
  have "no_unif (ff env binders F Fty is G Gty js)"
    unfolding ff_def Let_def using wf_envD(1)[OF wf] ks_sub
    by (auto simp: subset_def list_all_iff intro!: no_unif_bindM no_unif_mapM_idx
      no_unif_mkabs no_unif_update no_unif_type_of_G split: prod.splits)
  then show "no_unif (Some r)" using ff by simp
  assume r: "r = Ok env'"
  note \<sigma> = solutionD[OF sol]
  let ?u = "\<sigma> (code (AVar F))" and ?v = "\<sigma> (code (AVar G))"
  have cu: "no_loose_bound ?u 0" and cv: "no_loose_bound ?v 0" using closed_onD[OF \<sigma>(1)] by simp_all
  have tyF: "(bnd_env ?Bs, \<tau>') \<turnstile> ?u \<degree>\<degree> map BVar (nats is) : trty T"
    using has_type_subst[OF tys \<sigma>(2)] by (simp add: tr_app' comp_def)
  have tyG: "(bnd_env ?Bs, \<tau>') \<turnstile> ?v \<degree>\<degree> map BVar (nats js) : trty T"
    using has_type_subst[OF tyt \<sigma>(2)] by (simp add: tr_app' comp_def)
  have nis: "distinct (nats is)" "distinct (nats js)" using dist nonneg by (auto intro: distinct_nats)
  have eq: "?u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?v \<degree>\<degree> map BVar (nats js)"
    using uni by (simp add: unifies_def tr_app' comp_def)
  show "ext_sol V \<tau>' \<sigma> env env'"
  proof (cases "subset js is")
    case True
    with ff r obtain ks t where ks: "ok (mapM (idx is) js) ks"
      and t: "ok (mkabs binders is (app (pterm.Var G Gty) ks)) t"
      and env': "ok (update (F, Fty) t env) env'"
      by (auto simp: ff_def)
    note kn = ok_mapM_idx_nats[OF ks nonneg]
    note kb = ok_mapM_idx[OF ks nonneg]
    have sub: "set (nats js) \<subseteq> set (nats is)" using kn(2) by auto
    have equ: "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats is))
        (?v \<degree>\<degree> map BVar (map (\<lambda>y. the (Unification.idx (nats is) y)) (nats js)))"
      by (rule flex_bind_equiv[OF cu tyF nis(1) cv tyG eq sub])
    have tt: "tr t = Abs_m (length is) (dB.Var (code (AVar G)) \<degree>\<degree> map BVar (nats ks))"
      using ok_mkabs[OF t] by (simp add: tr_app')
    have eqv: "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)" using equ kn(1) by (simp add: tt comp_def)
    have tyt': "has_type V [] t Fty"
    proof -
      have "has_type V (rev UsF) (app (pterm.Var G Gty) ks) T"
        unfolding has_type_app using kb(1) tj(2) typ_idx[where binders=binders, OF ks kn(2)]
        by (auto simp: UsF_def Gty UsG_def intro: has_type.Var)
      from has_type_mkabs0[OF t _ this[unfolded UsF_def]] ti(1)
      show ?thesis by (simp add: Fty UsF_def)
    qed
    have below_t: "below (maxidx env) t"
      using vars_mkabs[OF t] Gm by (simp add: below_def vars_app)
    note up = solution_update[OF sol fr ety env' eqv ti(2) tyt' Fm below_t]
    show ?thesis unfolding ext_sol_def
      using up by (intro exI[of _ V] exI[of _ \<sigma>]) auto
  next
    case False
    from False ff r obtain ks' Hty where
      ks': "ok (mapM (idx is) ?ks) ks'" and Hty: "ok (type_of_G env Fty (ilength is) ks') Hty"
      and rest: "ok (case genvar (fst G) env Hty of (env1, H) \<Rightarrow>
        (mapM (idx js) ?ks \<bind> (\<lambda>ks'. mkabs binders js (app H ks'))) \<bind> (\<lambda>tG.
        (mapM (idx is) ?ks \<bind> (\<lambda>ks'. mkabs binders is (app H ks'))) \<bind> (\<lambda>tF.
        update (F, Fty) tF env1 \<bind> (\<lambda>env2. update (G, Gty) tG env2)))) env'"
      by (auto simp: ff_def Let_def)
    obtain env1 H where H: "genvar (fst G) env Hty = (env1, H)" by force
    with rest obtain ksG tG ksF tF env2 where
      ksG: "ok (mapM (idx js) ?ks) ksG" and tG: "ok (mkabs binders js (app H ksG)) tG"
      and ksF: "ok (mapM (idx is) ?ks) ksF" and tF: "ok (mkabs binders is (app H ksF)) tF"
      and env2: "ok (update (F, Fty) tF env1) env2" and env': "ok (update (G, Gty) tG env2) env'"
      by auto
    have "ksF = ks'" using ksF ks' by simp
    have ks_nonneg: "\<forall>k\<in>set ?ks. 0 \<le> k" using nonneg(1) ks_sub(1) by auto
    note knF = ok_mapM_idx_nats[OF ksF nonneg(1) ks_nonneg] and kbF = ok_mapM_idx[OF ksF nonneg(1) ks_nonneg]
    note knG = ok_mapM_idx_nats[OF ksG nonneg(2) ks_nonneg] and kbG = ok_mapM_idx[OF ksG nonneg(2) ks_nonneg]
    have lenUsF: "length UsF = length is" by (simp add: UsF_def)
    have Hty': "Hty = foldr fun_type (map (\<lambda>k. rev UsF ! nat_of_integer k) ksF) T"
      "\<forall>k\<in>set ksF. 0 \<le> k \<and> nat_of_integer k < length UsF"
      using type_of_G_foldr[OF wf_envD(1)[OF wf], of UsF T ksF Hty] Hty \<open>ksF = ks'\<close> Fty lenUsF
      by (simp_all add: ilength_eq)
    have tyu: "(e, \<tau>') \<turnstile> ?u : map trty UsF \<Rrightarrow> trty T" for e
      using typed_onD[OF \<sigma>(2) rangeI[of code "AVar F"], of e] ti(2) Fty by (simp add: trty_foldr)
    have dep: "dep_on (set (nats is) \<inter> set (nats js)) (?u \<degree>\<degree> map BVar (nats is))"
      by (rule flex_flex_dep[OF cu cv eq])
    have cover: "k \<in> set (nats ksF)"
      if k: "k < length (nats is)" "nats is ! (length (nats is) - Suc k) \<in> set (nats is) \<inter> set (nats js)" for k
    proof -
      let ?p = "length is - Suc k"
      have "is ! ?p \<in> set js"
        using k nonneg inj_on_nat_of_integer[of "insert (is ! ?p) (set js)"]
        by (auto simp: inj_on_def)
      then have "is ! ?p \<in> set ?ks" using k(1) by (auto simp: inter_def)
      moreover have "Unification.idx (nats is) (nats is ! ?p) = Some k"
        using idx_distinct[OF nis(1), of ?p] k(1) by simp
      ultimately show ?thesis using knF(1) k(1) by force
    qed
    obtain w where w: "no_loose_bound w 0"
      "(bnd_env ?Bs, \<tau>') \<turnstile> w : map (env_ext (bnd_env ?Bs) (map trty UsF)) (nats ksF) \<Rrightarrow> trty T"
      "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats is)) (w \<degree>\<degree> map BVar (nats ksF))"
      using restrict_flex[OF cu tyu[of "bnd_env ?Bs"] _ nis(1) dep cover] lenUsF by auto
    have meq: "map (trty \<circ> (\<lambda>k. rev UsF ! nat_of_integer k)) ksF =
      map (env_ext (bnd_env ?Bs) (map trty UsF) \<circ> nat_of_integer) ksF"
      using Hty'(2) by (auto simp: env_ext_less rev_nth intro!: map_cong)
    have trHty: "trty Hty = map (env_ext (bnd_env ?Bs) (map trty UsF)) (nats ksF) \<Rrightarrow> trty T"
      by (simp only: Hty'(1) trty_foldr map_map meq)
    have tyw: "(e, \<tau>') \<turnstile> w : trty Hty" for e
      using typing_closed[OF w(2) w(1)] trHty by simp
    note nv = solution_new_var[OF sol fr ety H w(1) tyw]
    let ?H = "(fst G, maxidx env + 1)"
    define \<sigma>' where "\<sigma>' = \<sigma>(code (AVar ?H) := w)"
    define V' where "V' = V(?H := Hty)"
    have F_ne: "F \<noteq> ?H" using Fm by (cases F) auto
    have G_ne: "G \<noteq> ?H" using Gm by (cases G) auto
    \<comment> \<open>the binding of \<open>F\<close>\<close>
    have ttF: "tr tF = Abs_m (length is) (dB.Var (code (AVar ?H)) \<degree>\<degree> map BVar (nats ksF))"
      using ok_mkabs[OF tF] nv(7) by (simp add: tr_app')
    have eqvF: "\<sigma>' (code (AVar F)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr tF)"
      using w(3) F_ne by (simp add: ttF \<sigma>'_def comp_def)
    have typF: "map (\<lambda>k. rev UsF ! nat_of_integer k) ksF = map (\<lambda>j. snd (binders ! nat_of_integer j)) ?ks"
      using typ_idx[where binders=binders, OF ksF ks_sub(1)] by (simp add: UsF_def)
    have tyF': "has_type V' [] tF Fty"
    proof -
      have "has_type V' (rev UsF) (app H ksF) T"
        unfolding has_type_app using kbF(1) nv(7,9)[folded V'_def] Hty' lenUsF
        by (auto intro: has_type.Var)
      from has_type_mkabs0[OF tF _ this[unfolded UsF_def]] ti(1)
      show ?thesis by (simp add: Fty UsF_def)
    qed
    have VF: "V' F = Fty" using ti(2) F_ne by (simp add: V'_def)
    have below_tF: "below (maxidx env1) tF" using vars_mkabs[OF tF] by (simp add: below_def vars_app nv(6,7))
    have Fm1: "snd F \<le> maxidx env1" using Fm nv(6) by simp
    note up1 = solution_update[OF nv(1)[folded \<sigma>'_def V'_def] nv(5) nv(4)[folded V'_def] env2 eqvF VF tyF' Fm1 below_tF]
    \<comment> \<open>the binding of \<open>G\<close>\<close>
    have ren_ks: "map (ren (nats is)) (nats ksF) = nats ?ks"
    proof -
      have "ren (nats is) (the (Unification.idx (nats is) k)) = k" if "k \<in> set (nats ?ks)" for k
        using that ks_sub(1) by (intro ren_idx) auto
      then show ?thesis using knF(1) by (auto intro!: map_idI simp: comp_def)
    qed
    have tyks: "(bnd_env ?Bs, \<tau>') \<turnstile> w \<degree>\<degree> map BVar (nats ?ks) : trty T"
    proof -
      have "(bnd_env ?Bs, \<tau>') \<turnstile> map_BVars (ren (nats is)) (w \<degree>\<degree> map BVar (nats ksF)) : trty T"
      proof (rule typing_map_BVars)
        show "(env_ext (bnd_env ?Bs) (map trty UsF), \<tau>') \<turnstile> w \<degree>\<degree> map BVar (nats ksF) : trty T"
          unfolding list_app_typing_iff typings_map_BVar using typing_closed[OF w(2) w(1)] by blast
        fix v assume "v \<in> loose_BVars (w \<degree>\<degree> map BVar (nats ksF))"
        then obtain k where k: "k \<in> set ksF" "v = nat_of_integer k"
          using no_loose_bound_loose_BVars[OF w(1)] by auto
        then have "v < length is" using Hty'(2) lenUsF by auto
        then show "bnd_env ?Bs (ren (nats is) v) = env_ext (bnd_env ?Bs) (map trty UsF) v"
          using ti(1) by (simp add: ren_def env_ext_less bnd_env_def UsF_def rev_nth)
      qed
      then show ?thesis unfolding map_BVars_closed_app[OF w(1)] ren_ks .
    qed
    have eqG: "?v \<degree>\<degree> map BVar (nats js) \<equiv>\<^sub>\<beta>\<^sub>\<eta> w \<degree>\<degree> map BVar (nats ?ks)"
    proof -
      have "?v \<degree>\<degree> map BVar (nats js) \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?u \<degree>\<degree> map BVar (nats is)" by (rule equiv_sym[OF eq])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats is)) (w \<degree>\<degree> map BVar (nats ksF)) \<degree>\<degree> map BVar (nats is)"
        using w(3) by (intro equiv_list_app) (auto simp: list_all2_refl)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (w \<degree>\<degree> map BVar (nats ksF))"
        by (rule Abs_m_apps_equiv)
      also have "\<dots> = w \<degree>\<degree> map BVar (nats ?ks)"
        unfolding map_BVars_closed_app[OF w(1)] ren_ks by (rule refl)
      finally show ?thesis .
    qed
    have subG: "set (nats ?ks) \<subseteq> set (nats js)" using ks_sub(2) by auto
    have equG: "?v \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats js))
        (w \<degree>\<degree> map BVar (map (\<lambda>y. the (Unification.idx (nats js) y)) (nats ?ks)))"
      by (rule flex_bind_equiv[OF cv tyG nis(2) w(1) tyks eqG subG])
    have ttG: "tr tG = Abs_m (length js) (dB.Var (code (AVar ?H)) \<degree>\<degree> map BVar (nats ksG))"
      using ok_mkabs[OF tG] nv(7) by (simp add: tr_app')
    have eqvG: "\<sigma>' (code (AVar G)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr tG)"
      using equG G_ne knG(1) by (simp add: ttG \<sigma>'_def comp_def)
    have tyG': "has_type V' [] tG Gty"
    proof -
      have "map (\<lambda>k. rev UsG ! nat_of_integer k) ksG = map (\<lambda>k. rev UsF ! nat_of_integer k) ksF"
        using typ_idx[where binders=binders, OF ksG ks_sub(2)] typ_idx[where binders=binders, OF ksF ks_sub(1)] by (simp add: UsF_def UsG_def)
      then have "has_type V' (rev UsG) (app H ksG) T"
        unfolding has_type_app using kbG(1) nv(7,9)[folded V'_def] Hty'(1)
        by (auto intro: has_type.Var simp: UsG_def)
      from has_type_mkabs0[OF tG _ this[unfolded UsG_def]] tj(1)
      show ?thesis by (simp add: Gty UsG_def)
    qed
    have VG: "V' G = Gty" using tj(2) G_ne by (simp add: V'_def)
    have below_tG: "below (maxidx env2) tG"
      using vars_mkabs[OF tG] up1(4) by (simp add: below_def vars_app nv(6,7))
    have Gm2: "snd G \<le> maxidx env2" using Gm nv(6) up1(4) by simp
    note up2 = solution_update[OF up1(1) up1(3) up1(2) env' eqvG VG tyG' Gm2 below_tG]
    show ?thesis
      unfolding ext_sol_def
      using up2 up1(4) nv(2,3,6)[folded \<sigma>'_def V'_def] by (intro exI[of _ V'] exI[of _ \<sigma>']) auto
  qed
qed


lemma unifies_sym: "unifies \<sigma> s t \<Longrightarrow> unifies \<sigma> t s"
  by (simp add: unifies_def equiv_sym)

lemma flexflex2_complete:
  assumes ff: "flexflex2 env binders F Fty is G Gty js = Some r"
    and wf: "wf_env ar env" and ety: "env_typed V env" and fr: "fresh_env env"
    and Fm: "snd F \<le> maxidx env" and Gm: "snd G \<le> maxidx env" and FG: "F \<noteq> G"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) (app (pterm.Var G Gty) js) T"
    and dist: "distinct is" "distinct js"
    and sol: "solution V \<tau>' \<sigma> env"
    and uni: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr (app (pterm.Var G Gty) js))"
  shows "no_unif (Some r)" "r = Ok env' \<Longrightarrow> ext_sol V \<tau>' \<sigma> env env'"
proof (atomize (full), cases "indexname_less G F")
  case True
  then show "no_unif (Some r) \<and> (r = Ok env' \<longrightarrow> ext_sol V \<tau>' \<sigma> env env')"
    using ff_complete[OF _ wf ety fr Fm Gm FG tys tyt dist sol uni] ff
    by (simp add: flexflex2_def)
next
  case False
  then show "no_unif (Some r) \<and> (r = Ok env' \<longrightarrow> ext_sol V \<tau>' \<sigma> env env')"
    using ff_complete[OF _ wf ety fr Gm Fm FG[symmetric] tyt tys dist(2,1) sol unifies_sym[OF uni]] ff
    by (simp add: flexflex2_def)
qed


subsection \<open>Auxiliary facts for projections\<close>

lemma no_unif_someI: "(\<And>r. m = Some r \<Longrightarrow> no_unif (Some r)) \<Longrightarrow> no_unif m"
  by (cases m) (auto simp: no_unif_def)

lemma bindM_SomeE:
  assumes "bindM m f = Some r"
  obtains e where "m = Some (Err e)" "r = Err e" | x where "m = Some (Ok x)" "f x = Some r"
  using assms by (auto simp: bindM_def split: option.splits res.splits)

lemma no_unif_lookup: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (lookup env xi T)"
  by (auto simp: lookup_def unified_def var_clash_def split: option.splits intro!: no_unif_bindM)

lemma no_unif_head_norm: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (head_norm env t)"
proof (rule no_unif_someI)
  fix r assume "head_norm env t = Some r" "vt_is_empty (tyenv env)"
  then show "no_unif (Some r)"
  proof (induction env t r rule: head_norm.raw_induct[rotated, consumes 1])
    case (1 hn env t r)
    have IH: "no_unif (hn env u)" for u by (rule no_unif_someI) (rule "1.IH"[OF _ "1.prems"])
    have "no_unif (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t)"
      using "1.prems" by (auto intro!: no_unif_bindM no_unif_lookup IH split: pterm.splits option.splits)
    then show ?case using "1.hyps" by simp
  qed
qed

lemma vars_incr_bv: "vars (incr_bv inc lev t) = vars t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma vars_subst_bound_aux: "vars (subst_bound_aux arg lev t) \<subseteq> vars arg \<union> vars t"
  by (induction arg lev t rule: subst_bound_aux.induct) (auto simp: incr_boundvars_def vars_incr_bv)

lemma below_subst_bound: "below m arg \<Longrightarrow> below m t \<Longrightarrow> below m (subst_bound arg t)"
  using vars_subst_bound_aux[of arg 0 t] by (auto simp: below_def subst_bound_def)

lemma below_head_norm:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wf_env ar env \<Longrightarrow> fresh_env env \<Longrightarrow> below (maxidx env) t \<Longrightarrow> below (maxidx env) t'"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and fr: "fresh_env env" and bt: "below (maxidx env) t" and t': "ok (case t of
      pterm.Var xi T \<Rightarrow> lookup env xi T \<bind> (\<lambda>r. case r of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u)
    | pterm.Abs a T body \<Rightarrow> hn env body \<bind> (\<lambda>body'. return (pterm.Abs a T body'))
    | f $ u \<Rightarrow>
        (case f of
          pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
        | _ \<Rightarrow> hn env f \<bind> (\<lambda>nf. case nf of
            pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)))
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  note IH = "1.IH"[OF _ refl wf fr]
  show ?case
  proof (cases t)
    case (Var xi U)
    with t' obtain r' where lk: "ok (lookup env xi U) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (U, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest bt show ?thesis by auto
    next
      case 2
      with rest have "hn env u = Some (Ok t')" by simp
      from IH[OF this] fresh_envD[OF fr 2(2)] show ?thesis by simp
    qed
  next
    case (Abs a U body)
    with t' obtain b' where "hn env body = Some (Ok b')" "t' = pterm.Abs a U b'" by auto
    with IH bt Abs show ?thesis by (auto simp: below_def)
  next
    case (App f u)
    have bfu: "below (maxidx env) f" "below (maxidx env) u" using bt App by (auto simp: below_def)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a U body where f: "f = pterm.Abs a U body" by (cases f) auto
      with t' App have hb: "hn env (subst_bound u body) = Some (Ok t')" by simp
      have "below (maxidx env) body" using bfu(1) f by (simp add: below_def)
      from IH[OF hb below_subst_bound[OF bfu(2) this]] show ?thesis .
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      have bn: "below (maxidx env) nf" using IH[OF nf bfu(1)] .
      show ?thesis
      proof (cases nf)
        case (Abs a U body)
        with rest have hb: "hn env (subst_bound u body) = Some (Ok t')" by simp
        have "below (maxidx env) body" using bn Abs by (simp add: below_def)
        from IH[OF hb below_subst_bound[OF bfu(2) this]] show ?thesis .
      qed (use rest bn bfu in auto)
    qed
  qed (use t' bt in auto)
qed


lemma has_type_list_comb:
  "has_type V Ts (list_comb h ts) T \<longleftrightarrow>
    (\<exists>Us. has_type V Ts h (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) ts Us)"
proof (induction ts arbitrary: h)
  case Nil
  then show ?case by (simp add: list_comb_def)
next
  case (Cons t ts)
  have "has_type V Ts (list_comb h (t # ts)) T \<longleftrightarrow> has_type V Ts (list_comb (h $ t) ts) T"
    by (simp add: list_comb_def)
  also have "\<dots> \<longleftrightarrow> (\<exists>Us. has_type V Ts (h $ t) (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) ts Us)"
    by (rule Cons.IH)
  also have "\<dots> \<longleftrightarrow> (\<exists>Us. has_type V Ts h (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) (t # ts) Us)"
  proof
    assume "\<exists>Us. has_type V Ts (h $ t) (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) ts Us"
    then obtain Us U where "has_type V Ts h (U \<rightarrow>\<^sub>T foldr fun_type Us T)" "has_type V Ts t U"
      "list_all2 (has_type V Ts) ts Us"
      by (auto elim: has_type_elims(6))
    then show "\<exists>Us. has_type V Ts h (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) (t # ts) Us"
      by (intro exI[of _ "U # Us"]) auto
  next
    assume "\<exists>Us. has_type V Ts h (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) (t # ts) Us"
    then obtain Us U where "has_type V Ts h (U \<rightarrow>\<^sub>T foldr fun_type Us T)" "has_type V Ts t U"
      "list_all2 (has_type V Ts) ts Us"
      by (auto simp: list_all2_Cons1)
    then show "\<exists>Us. has_type V Ts (h $ t) (foldr fun_type Us T) \<and> list_all2 (has_type V Ts) ts Us"
      by (auto intro: has_type.App)
  qed
  finally show ?case .
qed

lemma has_type_ints_of':
  assumes "ok (ints_of' env ts) js" "wf_env ar env" "env_typed V env" "has_type V Ts (list_comb h ts) T"
  shows "has_type V Ts (app h js) T"
proof -
  from assms(1) obtain ts' where hn: "list_all2 (\<lambda>t t'. ok (head_norm env t) t') ts ts'"
    and ints: "ok (ints_of ts') js"
    by (auto simp: ints_of'_def ok_mapM)
  from ints have ts': "ts' = map Bound js" by (simp add: ok_ints_of)
  from assms(4) obtain Us where h: "has_type V Ts h (foldr fun_type Us T)"
    and tys: "list_all2 (has_type V Ts) ts Us"
    by (auto simp: has_type_list_comb)
  have "list_all2 (has_type V Ts) ts' Us"
    using hn tys
  proof (induction ts ts' arbitrary: Us rule: list_all2_induct)
    case (Cons t ts t' ts')
    then show ?case by (auto simp: list_all2_Cons1 intro: head_norm_typed[OF _ refl assms(2,3)])
  qed simp
  then show ?thesis
    using h by (auto simp: app_list_comb has_type_list_comb ts')
qed

lemma no_unif_ints_of: "no_unif (ints_of ts)"
  by (induction ts rule: ints_of.induct) (auto intro!: no_unif_bindM)

lemma no_unif_ints_of': "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (ints_of' env ts)"
  unfolding ints_of'_def by (auto intro!: no_unif_bindM no_unif_mapM no_unif_head_norm no_unif_ints_of)

lemma no_unif_handle: "no_unif m \<or> (\<forall>e. no_unif (h e)) \<Longrightarrow> (\<And>e. no_unif (h e)) \<Longrightarrow> no_unif (handle m h)"
  by (auto simp: handle_def no_unif_def split: option.splits res.splits)

lemma no_unif_try_trans: "no_unif (try_trans xs d i)"
  unfolding try_trans_def by (rule no_unif_handle) auto


subsection \<open>Contexts of projections\<close>

text \<open>
  \<^const>\<open>pr\<close> at depth \<open>d\<close> maps the bound variables of a term in context \<open>Bs\<close> to the context
  \<open>pctx Bs d xs\<close>; the variables that may occur are \<open>pZ d xs\<close>.
\<close>

definition pctx :: "ptyp list \<Rightarrow> nat \<Rightarrow> integer list \<Rightarrow> ptyp list" where
  "pctx Bs d xs = take d Bs @ rev (map (\<lambda>x. Bs ! (d + nat_of_integer x)) xs)"

definition pZ :: "nat \<Rightarrow> integer list \<Rightarrow> nat set" where
  "pZ d xs = {v. v < d \<or> (d \<le> v \<and> v - d \<in> set (nats xs))}"

lemma pctx_Suc: "pctx (T # Bs) (Suc d) xs = T # pctx Bs d xs"
  by (simp add: pctx_def)

lemma pZ_Suc: "insert 0 (Suc ` pZ d xs) = pZ (Suc d) xs"
proof (rule set_eqI)
  fix v show "v \<in> insert 0 (Suc ` pZ d xs) \<longleftrightarrow> v \<in> pZ (Suc d) xs"
    by (cases v) (auto simp: pZ_def)
qed

lemma length_pctx: "d \<le> length Bs \<Longrightarrow> length (pctx Bs d xs) = d + length xs"
  by (simp add: pctx_def)

lemma pctx_nth:
  assumes "d \<le> length Bs" "l < d + length xs"
  shows "pctx Bs d xs ! l = Bs ! bren (nats xs) d l"
proof (cases "l < d")
  case True
  with assms show ?thesis by (simp add: pctx_def nth_append bren_def)
next
  case False
  then have "l - d < length xs" using assms(2) by simp
  with False assms(1) show ?thesis
    by (simp add: pctx_def nth_append bren_def ren_def rev_nth add.commute)
qed

lemma pZ_idx:
  assumes "0 \<le> d" "0 \<le> i" "\<not> i < d" "\<forall>x\<in>set xs. 0 \<le> x"
    "nat_of_integer i \<in> pZ (nat_of_integer d) xs"
  obtains n where "Unification.idx xs (i - d) = Some n"
proof -
  have "nat_of_integer d \<le> nat_of_integer i" using assms(3) by (simp add: integer_reps nat_mono)
  with assms(5) assms(3) have "nat_of_integer i - nat_of_integer d \<in> set (nats xs)"
    by (auto simp: pZ_def integer_reps nat_mono)
  then obtain x where x: "x \<in> set xs" "nat_of_integer x = nat_of_integer i - nat_of_integer d" by auto
  have "0 \<le> x" using assms(4) x(1) by blast
  with x(2) assms(1-3) have "x = i - d"
    unfolding integer_reps minus_integer.rep_eq zero_integer.rep_eq by (simp add: nat_diff_distrib)
  with x(1) show ?thesis using idx_None_iff[of xs "i - d"] that by auto
qed

lemma ok_try_trans_Some:
  assumes "ok (try_trans xs d i) r" "0 \<le> d" "0 \<le> i" "\<forall>x\<in>set xs. 0 \<le> x"
    "nat_of_integer i \<in> pZ (nat_of_integer d) xs"
  shows "r \<noteq> None"
proof (cases "i < d")
  case True
  with assms(1) show ?thesis by (auto simp: try_trans_def)
next
  case False
  obtain n where "Unification.idx xs (i - d) = Some n" by (rule pZ_idx[OF assms(2,3) False assms(4,5)])
  with assms(1) False show ?thesis by (auto simp: try_trans_def idx_eq_return)
qed

lemma no_unif_trans:
  assumes "0 \<le> d" "0 \<le> i" "\<forall>x\<in>set xs. 0 \<le> x" "nat_of_integer i \<in> pZ (nat_of_integer d) xs"
  shows "no_unif (trans xs d i)"
proof (cases "i < d")
  case True
  then show ?thesis by (simp add: trans_def)
next
  case False
  obtain n where "Unification.idx xs (i - d) = Some n" by (rule pZ_idx[OF assms(1,2) False assms(3,4)])
  with False show ?thesis by (simp add: trans_def idx_eq_return)
qed

lemma integer_of_nat_0[simp]: "integer_of_nat 0 = 0"
  by (simp add: integer_eq_iff)

lemma set_mk_proj_list_aux:
  "set (mk_proj_list_aux os j) = {j - integer_of_nat p | p. p < length os \<and> os ! p \<noteq> None}"
proof (induction os arbitrary: j)
  case (Cons opt os)
  have "{j - integer_of_nat p | p. p < length (opt # os) \<and> (opt # os) ! p \<noteq> None} =
    (if opt \<noteq> None then {j} else {}) \<union> {j - 1 - integer_of_nat p | p. p < length os \<and> os ! p \<noteq> None}"
    (is "?L = ?R")
  proof
    show "?L \<subseteq> ?R"
    proof
      fix k assume "k \<in> ?L"
      then obtain p where p: "k = j - integer_of_nat p" "p < Suc (length os)" "(opt # os) ! p \<noteq> None"
        by auto
      then show "k \<in> ?R"
        by (cases p) (auto simp: integer_of_nat_Suc)
    qed
    show "?R \<subseteq> ?L"
    proof
      fix k assume "k \<in> ?R"
      then consider "k = j" "opt \<noteq> None"
        | p where "k = j - 1 - integer_of_nat p" "p < length os" "os ! p \<noteq> None"
        by (auto split: if_splits)
      then show "k \<in> ?L"
      proof cases
        case 1
        then have "k = j - integer_of_nat 0 \<and> 0 < length (opt # os) \<and> (opt # os) ! 0 \<noteq> None" by simp
        then show ?thesis by blast
      next
        case 2
        then show ?thesis by (auto simp: integer_of_nat_Suc intro!: exI[of _ "Suc p"])
      qed
    qed
  qed
  then show ?case using Cons.IH by auto
qed simp

lemma in_nats_mk_proj_list:
  assumes "k < length os" "os ! (length os - Suc k) \<noteq> None"
  shows "k \<in> set (nats (mk_proj_list os))"
proof -
  let ?p = "length os - Suc k"
  have "ilength os - 1 - integer_of_nat ?p \<in> set (mk_proj_list os)"
    using assms by (auto simp: mk_proj_list_def set_mk_proj_list_aux)
  moreover have "nat_of_integer (ilength os - 1 - integer_of_nat ?p) = k"
    using assms(1) by (simp add: ilength_eq integer_reps)
  ultimately show ?thesis by force
qed

lemma mk_proj_list_aux_rev:
  "length zs = length os \<Longrightarrow>
    map (\<lambda>k. rev (pre @ zs) ! nat_of_integer k) (mk_proj_list_aux os (integer_of_nat (length zs) - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
proof (induction os arbitrary: pre zs)
  case (Cons opt os)
  then obtain z zs' where zs: "zs = z # zs'" "length zs' = length os" by (cases zs) auto
  let ?j = "integer_of_nat (length os)"
  have j: "integer_of_nat (length zs) - 1 = ?j"
    by (simp add: zs integer_eq_iff)
  have eq: "mk_proj_list_aux (opt # os) (integer_of_nat (length zs) - 1) =
    (if opt \<noteq> None then ?j # mk_proj_list_aux os (?j - 1) else mk_proj_list_aux os (?j - 1))"
    by (simp only: j mk_proj_list_aux.simps)
  have r: "rev (pre @ zs) ! nat_of_integer ?j = z"
    by (simp add: zs nth_append)
  from Cons.IH[of zs' "pre @ [z]"] zs(2)
  have ih: "map (\<lambda>k. rev (pre @ zs) ! nat_of_integer k) (mk_proj_list_aux os (?j - 1)) =
      map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs' os))"
    by (simp add: zs)
  show ?case
    unfolding eq using ih r by (auto simp: zs)
qed simp

lemma mk_proj_list_rev:
  "length zs = length os \<Longrightarrow>
    map (\<lambda>k. rev zs ! nat_of_integer k) (mk_proj_list os) = map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip zs os))"
  using mk_proj_list_aux_rev[of zs os "[]"] by (simp add: mk_proj_list_def ilength_eq)

end
