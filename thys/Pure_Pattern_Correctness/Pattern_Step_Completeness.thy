section \<open>Completeness of Unification\<close>

theory Pattern_Step_Completeness
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

context csig
begin

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

lemma no_unif_Err[simp]: "no_unif (Some (Err e)) \<longleftrightarrow> (\<forall>t. e \<noteq> Unif t)"
  by (auto simp: no_unif_def)

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

subsection \<open>Extensions of solutions\<close>

definition sol_ext :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> bool" where
  "sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env' \<longleftrightarrow> agreeV (maxidx env) V V' \<and> agree (maxidx env) \<sigma> \<sigma>' \<and>
    solution V' \<tau>' \<sigma>' env' \<and> env_typed V' env' \<and> fresh_env env' \<and> wf_env ar env' \<and> maxidx env \<le> maxidx env'"

lemma sol_ext_refl:
  "solution V \<tau>' \<sigma> env \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow> wf_env ar env \<Longrightarrow>
    sol_ext ar V \<tau>' \<sigma> env V \<sigma> env"
  by (simp add: sol_ext_def)

lemma sol_ext_trans:
  "sol_ext ar V \<tau>' \<sigma> e V1 \<sigma>1 e1 \<Longrightarrow> sol_ext ar V1 \<tau>' \<sigma>1 e1 V2 \<sigma>2 e2 \<Longrightarrow> sol_ext ar V \<tau>' \<sigma> e V2 \<sigma>2 e2"
  unfolding sol_ext_def by (meson agreeV_trans agree_trans order_trans)

lemma mapAccM_complete:
  assumes "mapAccM f xs e = Some r" "P g e"
    and "\<And>x g e r. x \<in> set xs \<Longrightarrow> P g e \<Longrightarrow> f x e = Some r \<Longrightarrow>
      no_unif (Some r) \<and> (\<forall>y e1. r = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x y g1 e1))"
    and mono: "\<And>x y g1 e1 g2 e2. Q x y g1 e1 \<Longrightarrow> R g2 e2 g1 e1 \<Longrightarrow> Q x y g2 e2"
    and trans: "\<And>g1 e1 g2 e2 g3 e3. R g2 e2 g1 e1 \<Longrightarrow> R g3 e3 g2 e2 \<Longrightarrow> R g3 e3 g1 e1"
    and refl: "\<And>g e. R g e g e"
  shows "no_unif (Some r) \<and> (\<forall>ys e'. r = Ok (ys, e') \<longrightarrow>
    (\<exists>g'. P g' e' \<and> R g' e' g e \<and> list_all2 (\<lambda>x y. Q x y g' e') xs ys))"
  using assms(1-3)
proof (induction xs arbitrary: g e r)
  case Nil
  then show ?case using refl by (auto simp: return_def)
next
  case (Cons x xs)
  have step: "no_unif (Some r) \<and> (\<forall>y e1. r = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x' y g1 e1))"
    if "x' \<in> set xs" "P g e" "f x' e = Some r" for x' g e r
    using Cons.prems(3)[OF _ that(2,3)] that(1) by simp
  from Cons.prems(1) have "f x e \<bind> (\<lambda>(y, s1). mapAccM f xs s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))) = Some r"
    by simp
  then show ?case
  proof (rule bindM_SomeE)
    fix ex assume "f x e = Some (Err ex)" "r = Err ex"
    with Cons.prems(3)[of x g e "Err ex"] Cons.prems(2) show ?thesis by simp
  next
    fix ye1 assume fx: "f x e = Some (Ok ye1)"
      and rest: "(\<lambda>(y, s1). mapAccM f xs s1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2))) ye1 = Some r"
    obtain y e1 where ye1: "ye1 = (y, e1)" by force
    from Cons.prems(3)[of x g e, OF _ Cons.prems(2) fx] ye1 obtain g1 where
      g1: "P g1 e1" "R g1 e1 g e" "Q x y g1 e1" by auto
    from rest ye1 have "mapAccM f xs e1 \<bind> (\<lambda>(ys, s2). return (y # ys, s2)) = Some r" by simp
    then show ?thesis
    proof (rule bindM_SomeE)
      fix ex assume m: "mapAccM f xs e1 = Some (Err ex)" and r: "r = Err ex"
      obtain r' where r': "mapAccM f xs e1 = Some r'" "r' = Err ex" using m by simp
      have "no_unif (Some r') \<and> (\<forall>ys e'. r' = Ok (ys, e') \<longrightarrow>
          (\<exists>g'. P g' e' \<and> R g' e' g1 e1 \<and> list_all2 (\<lambda>x y. Q x y g' e') xs ys))"
        by (rule Cons.IH[OF r'(1) g1(1)], rule step, assumption+)
      then have "\<forall>t. ex \<noteq> Unif t" by (simp add: r'(2))
      with r show ?thesis by simp
    next
      fix yse2 assume m: "mapAccM f xs e1 = Some (Ok yse2)"
        and r: "(\<lambda>(ys, s2). return (y # ys, s2)) yse2 = Some r"
      obtain ys e2 where yse2: "yse2 = (ys, e2)" by force
      have "no_unif (Some (Ok (ys, e2))) \<and> (\<forall>ys' e'. Ok (ys, e2) = Ok (ys', e') \<longrightarrow>
          (\<exists>g'. P g' e' \<and> R g' e' g1 e1 \<and> list_all2 (\<lambda>x y. Q x y g' e') xs ys'))"
        by (rule Cons.IH[OF m[unfolded yse2] g1(1)], rule step, assumption+)
      then have "\<exists>g2. P g2 e2 \<and> R g2 e2 g1 e1 \<and> list_all2 (\<lambda>x y. Q x y g2 e2) xs ys"
        by simp
      then obtain g2 where
        g2: "P g2 e2" "R g2 e2 g1 e1" "list_all2 (\<lambda>x y. Q x y g2 e2) xs ys" by blast
      from r yse2 have "r = Ok (y # ys, e2)" by (simp add: return_def)
      with g2 g1 show ?thesis by (auto intro: mono trans)
    qed
  qed
qed

lemma has_type_unique: "has_type V Ts t T \<Longrightarrow> has_type V Ts t U \<Longrightarrow> T = U"
proof (induction arbitrary: U rule: has_type.induct)
  case (Abs V T Ts t U' x)
  from Abs.prems obtain W where "U = T \<rightarrow>\<^sub>T W" "has_type V (T # Ts) t W"
    by (rule has_type_elims(5)) blast
  with Abs.IH show ?case by simp
next
  case (App V Ts s T U' t)
  from App.prems obtain T' where "has_type V Ts s (T' \<rightarrow>\<^sub>T U)" "has_type V Ts t T'"
    by (rule has_type_elims(6))
  from App.IH(1)[OF this(1)] show ?case by simp
qed (simp_all add: has_type_Bound_iff, (erule has_type_elims, simp)+)

lemma below_list_comb: "below m (list_comb h ts) \<longleftrightarrow> below m h \<and> (\<forall>t\<in>set ts. below m t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma below_app: "below m (app h is) \<longleftrightarrow> below m h"
  by (induction "is" arbitrary: h) (auto simp: app_def)

subsection \<open>Completeness of projections\<close>

lemma pr_complete:
  assumes "pr xs s env d binders = Some r"
  shows "wf_env ar env \<Longrightarrow> binders_ok ar binders \<Longrightarrow> env_typed V env \<Longrightarrow> fresh_env env \<Longrightarrow>
    proper s \<Longrightarrow> typs_ok ar s \<Longrightarrow> has_type V (map snd binders) s T \<Longrightarrow> below (maxidx env) s \<Longrightarrow>
    0 \<le> d \<Longrightarrow> nat_of_integer d \<le> length binders \<Longrightarrow>
    \<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders \<Longrightarrow>
    solution V \<tau>' \<sigma> env \<Longrightarrow> dep_on (pZ (nat_of_integer d) xs) (mk_subst \<sigma> (tr s)) \<Longrightarrow>
    no_unif (Some r) \<and> (\<forall>s' env'. r = Ok (s', env') \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env' \<and>
      below (maxidx env') s' \<and> has_type V' (pctx (map snd binders) (nat_of_integer d) xs) s' T))"
  using assms
proof (induction xs s env d binders r arbitrary: V \<sigma> T rule: pr.raw_induct[rotated, consumes 1])
  case (1 prr xs s env d binders r)
  have wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and ps: "proper s" "typs_ok ar s" and ty: "has_type V (map snd binders) s T"
    and bs: "below (maxidx env) s" and d0: "0 \<le> d" and dl: "nat_of_integer d \<le> length binders"
    and xsb: "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer d + nat_of_integer x < length binders"
    and sol: "solution V \<tau>' \<sigma> env" and dep: "dep_on (pZ (nat_of_integer d) xs) (mk_subst \<sigma> (tr s))"
    using "1.prems" by simp_all
  let ?Bs = "map snd binders" and ?Z = "pZ (nat_of_integer d) xs"
  let ?Ts = "pctx (map snd binders) (nat_of_integer d) xs"
  note \<sigma> = solutionD[OF sol]
  have xs0: "\<forall>x\<in>set xs. 0 \<le> x" using xsb by simp
  from "1.hyps" have "head_norm env s \<bind> (\<lambda>s0. (if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')}))) = Some r"
    by (simp only:)
  then show ?case
  proof (rule bindM_SomeE)
    fix e assume "head_norm env s = Some (Err e)" "r = Err e"
    with no_unif_head_norm[OF wf_envD(1)[OF wf], of s] show ?thesis by simp
  next
    fix s0 assume hn: "head_norm env s = Some (Ok s0)" and rest: "(if is_Abs s0 then
        (case s0 of
          pterm.Abs a T t \<Rightarrow> do {(t', env') \<leftarrow> prr xs t env (d + 1) ((a, T) # binders);
            return (pterm.Abs a T t', env')}
        | _ \<Rightarrow> raise (Failure (STR ''pr'')))
      else
        (let (h, ts) = strip_comb s0 in
          if is_Var h then
            (case h of
              pterm.Var F Fty \<Rightarrow> do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')}
            | _ \<Rightarrow> raise (Failure (STR ''pr'')))
          else if is_Abs h then raise Pattern
          else do {
            h' \<leftarrow> (case h of Bound i \<Rightarrow> do {j \<leftarrow> trans xs d i; return (Bound j)} | _ \<Rightarrow> return h);
            (ts', env') \<leftarrow> mapAccM (\<lambda>s env. prr xs s env d binders) ts env;
            return (list_comb h' ts', env')})) = Some r"
    from head_norm_sound[OF hn refl wf ps]
    have s0: "proper s0" "typs_ok ar s0" "env \<Turnstile> s \<approx> s0" by auto
    have ty0: "has_type V ?Bs s0 T" by (rule head_norm_typed[OF hn refl wf ety ty])
    have bs0: "below (maxidx env) s0" by (rule below_head_norm[OF hn refl wf fr bs])
    have dep0: "dep_on ?Z (mk_subst \<sigma> (tr s0))"
      using dep_on_equiv[OF equiv_sym[OF env_equivD[OF s0(3) \<sigma>(1,4)]] dep] .
    show ?thesis
    proof (cases "is_Abs s0")
      case True
      then obtain a U t where s0a: "s0 = pterm.Abs a U t" by (cases s0) auto
      from rest True s0a have prt: "prr xs t env (d + 1) ((a, U) # binders) \<bind>
          (\<lambda>(t', env'). return (pterm.Abs a U t', env')) = Some r"
        by simp
      from ty0 s0a obtain W where T: "T = U \<rightarrow>\<^sub>T W" and tyt: "has_type V (U # ?Bs) t W"
        by (auto elim: has_type_elims)
      have bt: "below (maxidx env) t" using bs0 s0a by simp
      have pt: "proper t" "typs_ok ar t" and gU: "ground ar U" using s0 s0a by simp_all
      have bok': "binders_ok ar ((a, U) # binders)" using bok gU by (simp add: binders_ok_def)
      have nd: "nat_of_integer (d + 1) = Suc (nat_of_integer d)" using d0 by (simp add: nat_of_integer_add)
      have "mk_subst \<sigma> (tr s0) = dB.Abs (mk_subst \<sigma> (tr t))" by (simp add: s0a)
      with dep0 have dept: "dep_on (pZ (nat_of_integer (d + 1)) xs) (mk_subst \<sigma> (tr t))"
        using Abs_dep_on[of ?Z] by (simp add: nd pZ_Suc)
      have d1: "0 \<le> d + 1" "nat_of_integer (d + 1) \<le> length ((a, U) # binders)"
        "\<forall>x\<in>set xs. 0 \<le> x \<and> nat_of_integer (d + 1) + nat_of_integer x < length ((a, U) # binders)"
        using d0 dl xsb by (simp_all add: nd)
      have tyt1: "has_type V (map snd ((a, U) # binders)) t W" using tyt by simp
      note IH = "1.IH"[OF _ wf bok' ety fr pt tyt1 bt d1 sol dept]
      from prt show ?thesis
      proof (rule bindM_SomeE)
        fix e assume "prr xs t env (d + 1) ((a, U) # binders) = Some (Err e)" "r = Err e"
        with IH show ?thesis by simp
      next
        fix te assume pr1: "prr xs t env (d + 1) ((a, U) # binders) = Some (Ok te)"
          and r: "(\<lambda>(t', env'). return (pterm.Abs a U t', env')) te = Some r"
        obtain t' env' where te: "te = (t', env')" by force
        from IH[OF pr1[unfolded te]] obtain V' \<sigma>' where ext: "sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
          and bt': "below (maxidx env') t'"
          and tyt': "has_type V' (pctx (map snd ((a, U) # binders)) (nat_of_integer (d + 1)) xs) t' W"
          by auto
        from r te have "r = Ok (pterm.Abs a U t', env')" by (simp add: return_def)
        moreover have "has_type V' ?Ts (pterm.Abs a U t') T"
          using tyt' by (simp add: nd pctx_Suc T has_type.Abs)
        ultimately show ?thesis using ext bt' by auto
      qed
    next
      case False
      obtain h ts where hts: "strip_comb s0 = (h, ts)" by force
      note s0_eq = strip_comb_list_comb[OF hts]
      show ?thesis
      proof (cases "is_Var h")
        case True
        then obtain F Fty where h: "h = pterm.Var F Fty" by (cases h) auto
        from rest False hts h have rv: "do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')} = Some r"
          by simp
        have pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
          using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
        have gFty: "ground ar Fty" using s0 s0_eq h by (simp add: typs_ok_list_comb)
        have Fm: "snd F \<le> maxidx env" using bs0 s0_eq h by (simp add: below_list_comb)
        have "no_unif (do {
                js \<leftarrow> ints_of' env ts;
                js' \<leftarrow> mapM (try_trans xs d) js;
                let ks = mk_proj_list js';
                let ls = List.map_filter id js';
                Hty \<leftarrow> type_of_G env Fty (ilength js) ks;
                let (env', H) = genvar (fst F) env Hty;
                t \<leftarrow> mk_hnf binders js H ks;
                env'' \<leftarrow> update (F, Fty) t env';
                return (app H ls, env'')})"
          using wf_envD(1)[OF wf]
          by (auto simp: Let_def mk_hnf_def intro!: no_unif_bindM no_unif_ints_of' no_unif_mapM
            no_unif_try_trans no_unif_type_of_G no_unif_mkabs no_unif_update split: prod.splits)
        then have nu: "no_unif (Some r)" using rv by simp
        show ?thesis
        proof (intro conjI allI impI nu)
          fix s' env' assume r: "r = Ok (s', env')"
          from rv r obtain js js' Hty where js: "ok (ints_of' env ts) js"
            and js': "ok (mapM (try_trans xs d) js) js'"
            and Hty: "ok (type_of_G env Fty (ilength js) (mk_proj_list js')) Hty"
            and rest2: "ok (case genvar (fst F) env Hty of (env1, H) \<Rightarrow>
              mk_hnf binders js H (mk_proj_list js') \<bind> (\<lambda>t. update (F, Fty) t env1 \<bind>
                (\<lambda>env''. return (app H (List.map_filter id js'), env'')))) (s', env')"
            by (auto simp: Let_def)
          obtain env1 H where G: "genvar (fst F) env Hty = (env1, H)" by force
          with rest2 obtain t where t: "ok (mkabs binders js (app H (mk_proj_list js'))) t"
            and env': "ok (update (F, Fty) t env1) env'" and s': "s' = app H (List.map_filter id js')"
            by (auto simp: mk_hnf_def return_def)
          let ?ks = "mk_proj_list js'" and ?ls = "List.map_filter id js'"
          let ?H = "(fst F, maxidx env + 1)"
          note ints = ints_of'_sound[OF js wf pts]
          have tyapp: "has_type V ?Bs (app (pterm.Var F Fty) js) T"
            using has_type_ints_of'[OF js wf ety] ty0 s0_eq h by simp
          note tj = has_type_app_Var[OF tyapp]
          define UsJ where "UsJ = map (\<lambda>i. ?Bs ! nat_of_integer i) js"
          have lenUsJ: "length UsJ = length js" by (simp add: UsJ_def)
          have UsJ_alt: "UsJ = map (\<lambda>i. snd (binders ! nat_of_integer i)) js"
            unfolding UsJ_def by (rule map_cong[OF refl]) (use tj(1) in auto)
          have FtyJ: "Fty = foldr fun_type UsJ T" using tj(3) by (simp add: UsJ_def)
          have js'2: "list_all2 (\<lambda>j opt. ok (try_trans xs d j) opt) js js'" using js' by (simp add: ok_mapM)
          then have len': "length js' = length js" by (simp add: list_all2_lengthD)
          have tt: "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and> 0 \<le> l \<and>
              nat_of_integer l < nat_of_integer d + length xs \<and>
              bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer j)) js js'"
          proof -
            have "js' ! p = None \<or> (\<exists>l. js' ! p = Some l \<and> 0 \<le> l \<and>
              nat_of_integer l < nat_of_integer d + length xs \<and>
              bren (nats xs) (nat_of_integer d) (nat_of_integer l) = nat_of_integer (js ! p))"
              if p: "p < length js" for p
            proof -
              from js'2 p have "ok (try_trans xs d (js ! p)) (js' ! p)" by (simp add: list_all2_conv_all_nth)
              from ok_try_trans[OF this d0 _ xs0] ints(2) p show ?thesis by auto
            qed
            with len' show ?thesis by (simp add: list_all2_conv_all_nth)
          qed
          note \<sigma>F = solutionD[OF sol]
          let ?u = "\<sigma> (code (AVar F))"
          have cu: "no_loose_bound ?u 0" using closed_onD[OF \<sigma>(1)] by simp
          have tyu: "(e, \<tau>') \<turnstile> ?u : map trty UsJ \<Rrightarrow> trty T" for e
            using typed_onD[OF \<sigma>(2) rangeI[of code "AVar F"], of e] tj(2) FtyJ by (simp add: trty_foldr)
          have njs: "distinct (nats js)" using ints(1,2) by (rule distinct_nats)
          have "env \<Turnstile> list_comb h ts \<approx> app h js" by (rule ints_of'_equiv[OF js wf pts])
          then have e1: "mk_subst \<sigma> (tr s0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (app (pterm.Var F Fty) js))"
            using env_equivD[OF _ \<sigma>(1,4)] s0_eq h by simp
          have "mk_subst \<sigma> (tr (app (pterm.Var F Fty) js)) = ?u \<degree>\<degree> map BVar (nats js)"
            by (simp add: tr_app' comp_def)
          with e1 have e2: "mk_subst \<sigma> (tr s0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> ?u \<degree>\<degree> map BVar (nats js)" by simp
          have dep: "dep_on ?Z (?u \<degree>\<degree> map BVar (nats js))"
            using dep_on_equiv[OF equiv_sym[OF e2] dep0] .
          have cover: "k \<in> set (nats ?ks)"
            if k: "k < length (nats js)" "nats js ! (length (nats js) - Suc k) \<in> ?Z" for k
          proof (rule in_nats_mk_proj_list)
            let ?p = "length js - Suc k"
            show "k < length js'" using k(1) len' by simp
            have p: "?p < length js" using k(1) by simp
            from js'2 p have "ok (try_trans xs d (js ! ?p)) (js' ! ?p)" by (simp add: list_all2_conv_all_nth)
            moreover have "0 \<le> js ! ?p" using ints(2) p by simp
            moreover have "nat_of_integer (js ! ?p) \<in> ?Z" using k(2) p by simp
            ultimately show "js' ! (length js' - Suc k) \<noteq> None"
              using ok_try_trans_Some[OF _ d0 _ xs0] len' by simp
          qed
          obtain w where w: "no_loose_bound w 0"
            "(bnd_env ?Bs, \<tau>') \<turnstile> w : map (env_ext (bnd_env ?Bs) (map trty UsJ)) (nats ?ks) \<Rrightarrow> trty T"
            "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats js)) (w \<degree>\<degree> map BVar (nats ?ks))"
            using restrict_flex[OF cu tyu[of "bnd_env ?Bs"] _ njs dep cover] lenUsJ by auto
          have Hty': "Hty = foldr fun_type (map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks) T"
            "\<forall>k\<in>set ?ks. 0 \<le> k \<and> nat_of_integer k < length UsJ"
            using type_of_G_foldr[OF wf_envD(1)[OF wf], of UsJ T ?ks Hty] Hty FtyJ lenUsJ
            by (simp_all add: ilength_eq)
          have meq: "map (trty \<circ> (\<lambda>k. rev UsJ ! nat_of_integer k)) ?ks =
            map (env_ext (bnd_env ?Bs) (map trty UsJ) \<circ> nat_of_integer) ?ks"
            using Hty'(2) by (auto simp: env_ext_less rev_nth intro!: map_cong)
          have trHty: "trty Hty = map (env_ext (bnd_env ?Bs) (map trty UsJ)) (nats ?ks) \<Rrightarrow> trty T"
            by (simp only: Hty'(1) trty_foldr map_map meq)
          have tyw: "(e, \<tau>') \<turnstile> w : trty Hty" for e
            using typing_closed[OF w(2) w(1)] trHty by simp
          note nv = solution_new_var[OF sol fr ety G w(1) tyw]
          define \<sigma>' where "\<sigma>' = \<sigma>(code (AVar ?H) := w)"
          define V' where "V' = V(?H := Hty)"
          have F_ne: "F \<noteq> ?H" using Fm by (cases F) auto
          have ttr: "tr t = Abs_m (length js) (dB.Var (code (AVar ?H)) \<degree>\<degree> map BVar (nats ?ks))"
            using ok_mkabs[OF t] nv(7) by (simp add: tr_app')
          have eqv: "\<sigma>' (code (AVar F)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>' (tr t)"
            using w(3) F_ne by (simp add: ttr \<sigma>'_def comp_def)
          have tyt: "has_type V' [] t Fty"
          proof -
            have "has_type V' (rev UsJ) (app H ?ks) T"
              unfolding has_type_app using Hty' nv(7,9)[folded V'_def] lenUsJ
              by (auto intro: has_type.Var)
            then have "has_type V' (rev (map (\<lambda>i. snd (binders ! nat_of_integer i)) js)) (app H ?ks) T"
              by (simp add: UsJ_alt)
            from has_type_mkabs0[OF t _ this] tj(1) show ?thesis by (simp add: FtyJ UsJ_alt)
          qed
          have VF: "V' F = Fty" using tj(2) F_ne by (simp add: V'_def)
          have below_t: "below (maxidx env1) t" using vars_mkabs[OF t] by (simp add: below_def vars_app nv(6,7))
          have Fm1: "snd F \<le> maxidx env1" using Fm nv(6) by simp
          note up = solution_update[OF nv(1)[folded \<sigma>'_def V'_def] nv(5) nv(4)[folded V'_def] env' eqv VF tyt
            Fm1 below_t]
          have ks_b: "\<forall>k\<in>set ?ks. 0 \<le> k \<and> nat_of_integer k < length js"
            using mk_proj_list_ren(2)[of "nats js" js'] len' by simp
          have Hg: "ground ar Hty" by (rule type_of_G_ground[OF Hty wf_envD(1)[OF wf] gFty])
          have wf1: "wf_env ar env1" by (rule genvar_wf_env[OF G wf])
          have wf': "wf_env ar env'"
            by (rule binding_sound(2)[OF t[unfolded nv(7)] env' wf1 gFty Hg bok ks_b])
          have ext: "sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
            using up nv(2,3,6)[folded \<sigma>'_def V'_def] wf' by (simp add: sol_ext_def)
          have ls_b: "\<forall>l\<in>set ?ls. 0 \<le> l \<and> nat_of_integer l < nat_of_integer d + length xs"
            using tt by (fastforce simp: set_map_filter_id list_all2_conv_all_nth in_set_conv_nth)
          have lenTs: "length ?Ts = nat_of_integer d + length xs" using dl by (simp add: length_pctx)
          have "map (\<lambda>l. ?Ts ! nat_of_integer l) ?ls =
              map fst (filter (\<lambda>(z, opt). opt \<noteq> None) (zip (map (\<lambda>j. ?Bs ! nat_of_integer j) js) js'))"
          proof (rule map_filter_bren)
            show "list_all2 (\<lambda>j opt. opt = None \<or> (\<exists>l. opt = Some l \<and>
                ?Ts ! nat_of_integer l = ?Bs ! nat_of_integer j)) js js'"
              using tt by (rule list_all2_mono) (use dl in \<open>auto simp: pctx_nth\<close>)
          qed
          also have "\<dots> = map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks"
            using mk_proj_list_rev[of UsJ js'] lenUsJ len' by (simp add: UsJ_def)
          finally have tyls: "map (\<lambda>l. ?Ts ! nat_of_integer l) ?ls = map (\<lambda>k. rev UsJ ! nat_of_integer k) ?ks" .
          have "has_type V' ?Ts s' T"
            unfolding s' has_type_app using ls_b lenTs nv(7,9)[folded V'_def] Hty'(1) tyls
            by (auto intro: has_type.Var)
          moreover have "below (maxidx env') s'" using up(4) nv(6,7) by (simp add: s' below_app)
          ultimately show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env' \<and> below (maxidx env') s' \<and>
              has_type V' ?Ts s' T"
            using ext by blast
        qed
      next
        case notVar: False
        show ?thesis
        proof (cases "is_Abs h")
          case True
          with rest False hts notVar have "r = Err Pattern" by (simp add: raise_def)
          then show ?thesis by simp
        next
          case notAbs: False
          have nApp: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF hts])
          define hm where "hm = (case h of Bound i \<Rightarrow> trans xs d i \<bind> (\<lambda>j. return (Bound j)) | _ \<Rightarrow> return h)"
          from rest False hts notVar notAbs have rr: "hm \<bind> (\<lambda>h'.
              mapAccM (\<lambda>s env. prr xs s env d binders) ts env \<bind>
              (\<lambda>(ts', env'). return (list_comb h' ts', env'))) = Some r"
            by (simp add: hm_def)
          from ty0 s0_eq obtain Us where tyh: "has_type V ?Bs h (foldr fun_type Us T)"
            and tyts: "list_all2 (has_type V ?Bs) ts Us"
            by (auto simp: has_type_list_comb)
          have pts: "\<forall>t\<in>set ts. proper t \<and> typs_ok ar t"
            using s0 s0_eq by (auto simp: proper_list_comb typs_ok_list_comb)
          have bts: "\<forall>t\<in>set ts. below (maxidx env) t" using bs0 s0_eq by (simp add: below_list_comb)
          have atom: "is_atom (mk_subst \<sigma> (tr h))"
            using nApp notVar notAbs by (cases h) (auto simp: rigid_substD[OF \<sigma>(3)])
          have "mk_subst \<sigma> (tr s0) = mk_subst \<sigma> (tr h) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts"
            by (simp add: s0_eq tr_list_comb comp_def)
          with dep0 have "dep_on ?Z (mk_subst \<sigma> (tr h) \<degree>\<degree> map (\<lambda>t. mk_subst \<sigma> (tr t)) ts)" by simp
          note ad = atom_apps_dep_on[OF atom this]
          have dep_ts: "dep_on ?Z (mk_subst \<sigma> (tr t))" if "t \<in> set ts" for t using ad(2) that by auto
          have lenTs: "length ?Ts = nat_of_integer d + length xs" using dl by (simp add: length_pctx)
          have hd: "no_unif hm" "\<And>h'. ok hm h' \<Longrightarrow> (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
          proof -
            have "no_unif hm \<and> (\<forall>h'. ok hm h' \<longrightarrow>
              (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T)))"
            proof (cases h)
              case (Bound i)
              from tyh Bound have i: "0 \<le> i" "nat_of_integer i < length ?Bs"
                "foldr fun_type Us T = ?Bs ! nat_of_integer i"
                by (simp_all add: has_type_Bound_iff)
              have iZ: "nat_of_integer i \<in> ?Z" using ad(1) Bound by simp
              have "no_unif hm" unfolding hm_def Bound
                by (auto intro!: no_unif_bindM no_unif_trans[OF d0 i(1) xs0 iZ])
              moreover have "(\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
                if "ok hm h'" for h'
              proof -
                from that obtain j where j: "ok (trans xs d i) j" "h' = Bound j"
                  by (auto simp: hm_def Bound)
                note tj = ok_trans[OF j(1) d0 i(1) xs0]
                have "?Ts ! nat_of_integer j = ?Bs ! nat_of_integer i"
                  using pctx_nth[OF _ conjunct1[OF conjunct2[OF tj]]] dl tj by simp
                then show ?thesis using tj i(3) lenTs by (auto simp: j(2) has_type_Bound_iff)
              qed
              ultimately show ?thesis by blast
            next
              case (Const c U)
              with tyh show ?thesis by (auto simp: hm_def elim: has_type_elims intro: has_type.Const)
            next
              case (Free c U)
              with tyh show ?thesis by (auto simp: hm_def elim: has_type_elims intro: has_type.Free)
            qed (use notVar notAbs nApp in auto)
            then show "no_unif hm" "\<And>h'. ok hm h' \<Longrightarrow> (\<forall>m. below m h') \<and> (\<forall>V0. has_type V0 ?Ts h' (foldr fun_type Us T))"
              by blast+
          qed
          define P where "P = (\<lambda>(g :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e. sol_ext ar V \<tau>' \<sigma> env (fst g) (snd g) e)"
          define R where "R = (\<lambda>(g2 :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e2 (g1 :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e1.
            agreeV (maxidx e1) (fst g1) (fst g2) \<and> maxidx e1 \<le> maxidx e2)"
          define Q where "Q = (\<lambda>x y (g :: (indexname \<Rightarrow> ptyp) \<times> (nat \<Rightarrow> dB)) e.
            below (maxidx e) y \<and> (\<forall>U. has_type V ?Bs x U \<longrightarrow> has_type (fst g) ?Ts y U))"
          have mc: "no_unif (Some rm) \<and> (\<forall>ys e'. rm = Ok (ys, e') \<longrightarrow>
            (\<exists>g'. P g' e' \<and> R g' e' (V, \<sigma>) env \<and> list_all2 (\<lambda>x y. Q x y g' e') ts ys))"
            if m: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some rm" for rm
          proof (rule mapAccM_complete[OF m, of P "(V, \<sigma>)" R Q])
            show "P (V, \<sigma>) env" using sol ety fr wf by (simp add: P_def sol_ext_refl)
          next
            fix x g e r1
            assume x: "x \<in> set ts" and Pg: "P g e" and pr1: "prr xs x e d binders = Some r1"
            obtain V1 \<sigma>1 where g: "g = (V1, \<sigma>1)" by force
            from Pg have ext1: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 e" by (simp add: P_def g)
            note e1 = ext1[unfolded sol_ext_def]
            from tyts x obtain U where tyx: "has_type V ?Bs x U"
              by (metis in_set_conv_nth list_all2_conv_all_nth)
            have bx: "below (maxidx env) x" using bts x by blast
            have tyx1: "has_type V1 ?Bs x U" using has_type_agreeV[OF tyx bx] e1 by blast
            have bx1: "below (maxidx e) x" using below_mono[OF bx] e1 by blast
            have "mk_subst \<sigma>1 (tr x) = mk_subst \<sigma> (tr x)" using mk_subst_agree[OF bx] e1 by blast
            then have depx: "dep_on ?Z (mk_subst \<sigma>1 (tr x))" using dep_ts[OF x] by simp
            have IHx: "no_unif (Some r1) \<and> (\<forall>s' env'. r1 = Ok (s', env') \<longrightarrow> (\<exists>V' \<sigma>'.
                sol_ext ar V1 \<tau>' \<sigma>1 e V' \<sigma>' env' \<and> below (maxidx env') s' \<and> has_type V' ?Ts s' U))"
              using "1.IH"[OF pr1 _ bok _ _ _ _ tyx1 bx1 d0 dl xsb _ depx] e1 pts x by blast
            show "no_unif (Some r1) \<and> (\<forall>y e1. r1 = Ok (y, e1) \<longrightarrow> (\<exists>g1. P g1 e1 \<and> R g1 e1 g e \<and> Q x y g1 e1))"
            proof (intro conjI allI impI)
              show "no_unif (Some r1)" using IHx by blast
              fix y e2 assume "r1 = Ok (y, e2)"
              with IHx obtain V2 \<sigma>2 where ext2: "sol_ext ar V1 \<tau>' \<sigma>1 e V2 \<sigma>2 e2"
                and by2: "below (maxidx e2) y" and ty2: "has_type V2 ?Ts y U"
                by blast
              have "P (V2, \<sigma>2) e2" using sol_ext_trans[OF ext1 ext2] by (simp add: P_def)
              moreover have "R (V2, \<sigma>2) e2 g e" using ext2 by (simp add: R_def g sol_ext_def)
              moreover have "Q x y (V2, \<sigma>2) e2"
                using by2 ty2 has_type_unique[OF tyx] by (auto simp: Q_def)
              ultimately show "\<exists>g1. P g1 e2 \<and> R g1 e2 g e \<and> Q x y g1 e2" by blast
            qed
          next
            fix x y g1 e1 g2 e2 assume "Q x y g1 e1" "R g2 e2 g1 e1"
            then show "Q x y g2 e2"
              by (auto simp: Q_def R_def intro: below_mono has_type_agreeV)
          next
            fix g1 e1 g2 e2 g3 e3 assume "R g2 e2 g1 e1" "R g3 e3 g2 e2"
            then show "R g3 e3 g1 e1" by (auto simp: R_def intro: agreeV_trans)
          next
            fix g e show "R g e g e" by (simp add: R_def)
          qed
          from rr show ?thesis
          proof (rule bindM_SomeE)
            fix e assume "hm = Some (Err e)" "r = Err e"
            with hd(1) show ?thesis by simp
          next
            fix h' assume h': "hm = Some (Ok h')" and rr2: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env \<bind>
              (\<lambda>(ts', env'). return (list_comb h' ts', env')) = Some r"
            note hd' = hd(2)[OF h']
            from rr2 show ?thesis
            proof (rule bindM_SomeE)
              fix e assume "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some (Err e)" "r = Err e"
              with mc show ?thesis by fastforce
            next
              fix tse assume m: "mapAccM (\<lambda>s env. prr xs s env d binders) ts env = Some (Ok tse)"
                and r: "(\<lambda>(ts', env'). return (list_comb h' ts', env')) tse = Some r"
              obtain ts' env' where tse: "tse = (ts', env')" by force
              from r tse have r': "r = Ok (list_comb h' ts', env')" by (simp add: return_def)
              from mc[OF m[unfolded tse]] obtain g' where Pg: "P g' env'"
                and Qs: "list_all2 (\<lambda>x y. Q x y g' env') ts ts'"
                by blast
              have "below (maxidx env') (list_comb h' ts')"
                using hd' Qs by (auto simp: below_list_comb Q_def list_all2_conv_all_nth in_set_conv_nth)
              moreover have "has_type (fst g') ?Ts (list_comb h' ts') T"
              proof -
                have "list_all2 (has_type (fst g') ?Ts) ts' Us"
                  using Qs tyts by (auto simp: Q_def list_all2_conv_all_nth)
                then show ?thesis using hd' by (auto simp: has_type_list_comb)
              qed
              ultimately show ?thesis using Pg r' by (auto simp: P_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma pZ_0: "pZ 0 xs = set (nats xs)"
  by (auto simp: pZ_def)

lemma map_nth_downs: "map ((!) Bs) (downs (length Bs)) = rev Bs"
  by (rule nth_equalityI) (auto simp: downs_nth rev_nth)

lemma proj_complete:
  assumes "proj t env binders is = Some r" "wf_env ar env" "binders_ok ar binders" "env_typed V env"
    "fresh_env env" "proper t" "typs_ok ar t" "has_type V (map snd binders) t T" "below (maxidx env) t"
    "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" "solution V \<tau>' \<sigma> env"
    "dep_on (set (nats is)) (mk_subst \<sigma> (tr t))"
  shows "no_unif (Some r) \<and> (\<forall>u env'. r = Ok (u, env') \<longrightarrow> (\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env' \<and>
    below (maxidx env') u \<and> has_type V' (rev (map (\<lambda>i. map snd binders ! nat_of_integer i) is)) u T))"
proof (cases "downto0 is (ilength binders - 1)")
  case True
  then have r: "r = Ok (t, env)" using assms(1) by (simp add: proj_def return_def)
  from downto0_nats[OF True] have "nats is = downs (length binders)" by simp
  then have "map (\<lambda>i. map snd binders ! nat_of_integer i) is = map ((!) (map snd binders)) (downs (length binders))"
    by (metis (no_types, lifting) list.map_comp comp_apply map_eq_conv)
  then have "rev (map (\<lambda>i. map snd binders ! nat_of_integer i) is) = map snd binders"
    using map_nth_downs[of "map snd binders"] by simp
  with r assms(2,4,5,8,9,11) show ?thesis by (auto intro: sol_ext_refl)
next
  case False
  with assms(1) have "pr is t env 0 binders = Some r" by (simp add: proj_def)
  from pr_complete[OF this assms(2-9) _ _ _ assms(11)] assms(10,12)
  show ?thesis by (simp add: pctx_def pZ_0)
qed

text \<open>A flex term equivalent to an injective renaming of another term.\<close>

lemma flex_ren_equiv:
  assumes closed: "no_loose_bound u 0" and tyu: "(E, \<tau>') \<turnstile> u : Ts \<Rrightarrow> U" and len: "length zs = length Ts"
    and zs: "distinct zs" and tyb: "(E', \<tau>'') \<turnstile> b : U'" and lb: "loose_BVars b \<subseteq> {..<length zs}"
    and eq: "u \<degree>\<degree> map BVar zs \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren zs) b"
  shows "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length zs) b"
proof -
  let ?m = "length zs" and ?g = "\<lambda>i. zs ! (length zs - Suc i)"
  obtain r where r: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar (downs ?m)) r" "normal r" "(env_ext E Ts, \<tau>') \<turnstile> r : U"
    "loose_BVars r \<subseteq> {..<?m}"
    using typed_nf_args[OF closed tyu len[symmetric]] .
  have nr: "\<beta>\<eta>cl (u \<degree>\<degree> map BVar zs) (map_BVars ?g r)"
    using nf_rename_args[OF closed r(1,2) refl zs] by simp
  have gr: "map_BVars ?g r = map_BVars (ren zs) r"
    using r(4) by (intro map_BVars_cong) (auto simp: ren_def)
  have "map_BVars (ren zs) r \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren zs) b"
    using equiv_sym[OF \<beta>\<eta>cl_into_equiv[OF nr]] eq unfolding gr by (rule equiv_trans)
  moreover have "inj_on (ren zs) (loose_BVars r \<union> loose_BVars b)"
  proof (rule inj_on_subset)
    show "inj_on (ren zs) {..<?m}" using zs by (auto simp: inj_on_def ren_def nth_eq_iff_index_eq)
    show "loose_BVars r \<union> loose_BVars b \<subseteq> {..<?m}" using r(4) lb by auto
  qed
  ultimately have rb: "r \<equiv>\<^sub>\<beta>\<^sub>\<eta> b" by (rule map_BVars_equiv_reflect[OF _ _ r(3) tyb])
  have "u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m (u \<degree>\<degree> map BVar (downs ?m))"
    using eta_expand_equiv[OF closed] by (rule equiv_sym)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m r" using r(1) by (intro equiv_Abs_m \<beta>\<eta>cl_into_equiv)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m ?m b" using rb by (rule equiv_Abs_m)
  finally show ?thesis .
qed

subsection \<open>Flex-rigid problems\<close>

lemma no_unif_occurs: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (occurs F t env)"
proof (rule no_unif_someI)
  fix r assume "occurs F t env = Some r" "vt_is_empty (tyenv env)"
  then show "no_unif (Some r)"
  proof (induction F t env r rule: occurs.raw_induct[rotated, consumes 1])
    case (1 occ F t env r)
    have IH: "no_unif (occ F u env)" for u by (rule no_unif_someI) (rule "1.IH"[OF _ "1.prems"])
    have "no_unif (case t of
      pterm.Var G T \<Rightarrow> lookup env G T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> occ F u env | None \<Rightarrow> return (F = G))
    | t1 $ t2 \<Rightarrow> occ F t1 env \<bind> (\<lambda>b. if b then return True else occ F t2 env)
    | pterm.Abs _ _ u \<Rightarrow> occ F u env
    | _ \<Rightarrow> return False)"
      using "1.prems" by (auto intro!: no_unif_bindM no_unif_lookup IH split: pterm.splits option.splits)
    then show ?case using "1.hyps" by simp
  qed
qed

lemma no_unif_existsM: "(\<And>x. x \<in> set xs \<Longrightarrow> no_unif (P x)) \<Longrightarrow> no_unif (existsM P xs)"
  by (induction xs) (auto intro!: no_unif_bindM)

lemma no_unif_handle_other:
  "no_unif m \<Longrightarrow> (\<And>e. (\<And>t. e \<noteq> Unif t) \<Longrightarrow> no_unif (h e)) \<Longrightarrow> no_unif (handle m h)"
  by (auto simp: handle_def no_unif_def split: option.splits res.splits)

lemma no_unif_rigid_occurs: "vt_is_empty (tyenv env) \<Longrightarrow> no_unif (rigid_occurs F t env)"
proof (rule no_unif_someI)
  fix r assume "rigid_occurs F t env = Some r" "vt_is_empty (tyenv env)"
  then show "no_unif (Some r)"
  proof (induction F t env r rule: rigid_occurs.raw_induct[rotated, consumes 1])
    case (1 ro F t env r)
    have IH: "no_unif (ro F u env)" for u by (rule no_unif_someI) (rule "1.IH"[OF _ "1.prems"])
    have leaf: "no_unif (handle (ints_of' env ts \<bind> (\<lambda>_. return True))
        (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e))" for ts
      using "1.prems" by (intro no_unif_handle_other no_unif_bindM no_unif_ints_of') (auto split: exn.splits)
    have "no_unif (head_norm env t \<bind> (\<lambda>t'. case t' of
        pterm.Abs _ _ u \<Rightarrow> ro F u env
      | _ \<Rightarrow>
          (let (h, ts) = strip_comb t' in
            (case h of
              pterm.Var G _ \<Rightarrow>
                if G = F then
                  handle (ints_of' env ts \<bind> (\<lambda>_. return True))
                    (\<lambda>e. case e of Pattern \<Rightarrow> return False | _ \<Rightarrow> raise e)
                else return False
            | pterm.Abs _ _ _ \<Rightarrow> return False
            | _ \<Rightarrow> existsM (\<lambda>u. ro F u env) ts))))"
      using "1.prems" by (auto intro!: no_unif_bindM no_unif_head_norm no_unif_existsM IH leaf
        split: pterm.splits prod.splits)
    then show ?case using "1.hyps" by simp
  qed
qed

lemma handle_no_unif:
  "no_unif P \<Longrightarrow> handle P (\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif X) | _ \<Rightarrow> raise e) = P"
  by (auto simp: handle_def no_unif_def raise_def split: option.splits res.splits exn.splits)

lemma flexrigid_complete:
  assumes frg: "flexrigid env binders F Fty is t = Some r"
    and wf: "wf_env ar env" and bok: "binders_ok ar binders" and ety: "env_typed V env"
    and fr: "fresh_env env" and Fm: "snd F \<le> maxidx env" and gF: "ground ar Fty"
    and tys: "has_type V (map snd binders) (app (pterm.Var F Fty) is) T"
    and tyt: "has_type V (map snd binders) t T" and pt: "proper t" "typs_ok ar t"
    and bt: "below (maxidx env) t" and dist: "distinct is"
    and sol: "solution V \<tau>' \<sigma> env"
    and uni: "unifies \<sigma> (tr (app (pterm.Var F Fty) is)) (tr t)"
    and occ: "\<not> ok (rigid_occurs F t env) True"
  shows "no_unif (Some r)" "r = Ok env' \<Longrightarrow> \<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
proof -
  let ?Bs = "map snd binders"
  note ti = has_type_app_Var[OF tys]
  note \<sigma> = solutionD[OF sol]
  let ?u = "\<sigma> (code (AVar F))"
  have cu: "no_loose_bound ?u 0" using closed_onD[OF \<sigma>(1)] by simp
  have eq: "?u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
    using uni by (simp add: unifies_def tr_app' comp_def)
  have "dep_on (set (nats is)) (?u \<degree>\<degree> map BVar (nats is))"
    by (rule dep_onI[OF equiv_refl]) (auto simp: no_loose_bound_loose_BVars[OF cu])
  then have dep: "dep_on (set (nats is)) (mk_subst \<sigma> (tr t))" by (rule dep_on_equiv[OF equiv_sym[OF eq]])
  have isb: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" using ti(1) by simp
  let ?P = "proj t env binders is \<bind> (\<lambda>(u, env'). mkabs binders is u \<bind> (\<lambda>u'. update (F, Fty) u' env'))"
  note pc = proj_complete[OF _ wf bok ety fr pt tyt bt isb sol dep]
  have "no_unif (proj t env binders is)"
    by (rule no_unif_someI) (use pc in blast)
  then have nuP: "no_unif ?P"
    by (auto intro!: no_unif_bindM no_unif_mkabs no_unif_update split: prod.splits)
  let ?O = "rigid_occurs F t env \<bind> (\<lambda>b'. if b' then raise (Unif (Ocheck_Fail F t binders env))
    else raise Pattern)"
  have nuO: "no_unif ?O"
  proof (rule no_unif_bindM[OF no_unif_rigid_occurs[OF wf_envD(1)[OF wf]]])
    fix b' assume "ok (rigid_occurs F t env) b'"
    with occ show "no_unif (if b' then raise (Unif (Ocheck_Fail F t binders env)) else raise Pattern)"
      by (cases b') auto
  qed
  have "flexrigid env binders F Fty is t = occurs F t env \<bind> (\<lambda>b. if b then ?O else
      handle ?P (\<lambda>e. case e of Unif _ \<Rightarrow> raise (Unif (Proj_Fail env binders F is t)) | _ \<Rightarrow> raise e))"
    by (simp add: flexrigid_def)
  also have "\<dots> = occurs F t env \<bind> (\<lambda>b. if b then ?O else ?P)"
    by (simp only: handle_no_unif[OF nuP])
  finally have frg': "occurs F t env \<bind> (\<lambda>b. if b then ?O else ?P) = Some r" using frg by simp
  from frg' show "no_unif (Some r)"
  proof (rule bindM_SomeE)
    fix e assume "occurs F t env = Some (Err e)" "r = Err e"
    with no_unif_occurs[OF wf_envD(1)[OF wf], of F t] show ?thesis by simp
  next
    fix b assume "ok (occurs F t env) b" "(if b then ?O else ?P) = Some r"
    with nuO nuP show ?thesis by (cases b) (auto simp: no_unif_def)
  qed
  assume r: "r = Ok env'"
  from frg' r have "ok ?P env'"
    by (auto simp: bindM_def raise_def split: option.splits res.splits if_splits)
  then obtain u env1 u' where pj: "ok (proj t env binders is) (u, env1)"
    and u': "ok (mkabs binders is u) u'" and upd: "ok (update (F, Fty) u' env1) env'"
    by (auto split: prod.splits)
  from pc[OF pj] obtain V1 \<sigma>1 where e1: "sol_ext ar V \<tau>' \<sigma> env V1 \<sigma>1 env1"
    and bu: "below (maxidx env1) u" and tyu: "has_type V1 (rev (map (\<lambda>i. ?Bs ! nat_of_integer i) is)) u T"
    by auto
  have agV: "agreeV (maxidx env) V V1" and ag: "agree (maxidx env) \<sigma> \<sigma>1"
    and sol1: "solution V1 \<tau>' \<sigma>1 env1" and ety1: "env_typed V1 env1" and fr1: "fresh_env env1"
    and mx: "maxidx env \<le> maxidx env1"
    using e1 by (simp_all add: sol_ext_def)
  note \<sigma>1 = solutionD[OF sol1]
  have isb0: "\<forall>i\<in>set is. 0 \<le> i" using isb by simp
  have nlb: "no_loose_bound (tr t) (length binders)" using has_type_closed[OF tyt] by simp
  note ps = proj_sound[OF pj wf bok pt isb0 nlb]
  have \<sigma>1F: "\<sigma>1 (code (AVar F)) = ?u" by (rule agree_Var[OF ag Fm])
  have t\<sigma>: "mk_subst \<sigma>1 (tr t) = mk_subst \<sigma> (tr t)" by (rule mk_subst_agree[OF bt ag])
  let ?b = "mk_subst \<sigma>1 (tr u)"
  have eqb: "?u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) ?b"
    using equiv_trans[OF eq ps(6)[OF \<sigma>1(1,4), unfolded t\<sigma>]] .
  have tyb: "(bnd_env (rev (map (\<lambda>i. ?Bs ! nat_of_integer i) is)), \<tau>') \<turnstile> ?b : trty T"
    by (rule has_type_subst[OF tyu \<sigma>1(2)])
  have "no_loose_bound ?b (length is)"
    using mk_subst_no_loose_bound[OF ps(5) closed_on_mono[OF \<sigma>1(1)]] by simp
  then have lb: "loose_BVars ?b \<subseteq> {..<length (nats is)}" using no_loose_bound_BVars by fastforce
  define Us where "Us = map (\<lambda>i. ?Bs ! nat_of_integer i) is"
  have Fty: "Fty = foldr fun_type Us T" using ti(3) by (simp add: Us_def)
  have tyuF: "(e, \<tau>') \<turnstile> ?u : map trty Us \<Rrightarrow> trty T" for e
    using typed_onD[OF \<sigma>(2) rangeI[of code "AVar F"], of e] ti(2) Fty by (simp add: trty_foldr)
  have nis: "distinct (nats is)" using dist isb0 by (rule distinct_nats)
  have Fequiv: "?u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length (nats is)) ?b"
    by (rule flex_ren_equiv[OF cu tyuF _ nis tyb lb eqb]) (simp add: Us_def)
  have eqv: "\<sigma>1 (code (AVar F)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma>1 (tr u')"
    using Fequiv \<sigma>1F ok_mkabs[OF u'] by simp
  have VF: "V1 F = Fty" using agreeV_D[OF agV Fm] ti(2) by simp
  have Us_alt: "Us = map (\<lambda>i. snd (binders ! nat_of_integer i)) is"
    unfolding Us_def by (rule map_cong[OF refl]) (use isb in auto)
  have tyu': "has_type V1 [] u' Fty"
    using has_type_mkabs0[OF u' isb tyu[folded Us_def, unfolded Us_alt]] by (simp add: Fty Us_alt)
  have bu': "below (maxidx env1) u'" using vars_mkabs[OF u'] bu by (simp add: below_def)
  have Fm1: "snd F \<le> maxidx env1" using Fm mx by simp
  note up = solution_update[OF sol1 fr1 ety1 upd eqv VF tyu' Fm1 bu']
  have wf': "wf_env ar env'" by (rule flexrigid_sound(2)[OF frg[unfolded r] wf bok gF pt isb0 nlb])
  show "\<exists>V' \<sigma>'. sol_ext ar V \<tau>' \<sigma> env V' \<sigma>' env'"
    using agV ag up wf' mx by (auto simp: sol_ext_def)
qed

end

end
