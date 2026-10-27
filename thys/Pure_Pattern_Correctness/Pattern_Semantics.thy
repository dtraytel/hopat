section \<open>Semantics of Pure Terms as de Bruijn Terms\<close>

theory Pattern_Semantics
  imports
    "Nipkow_Grobauer_Pattern.Unif_Correctness"
    "HOL-Library.Countable"
    "Pure_Pattern.Pure_Pattern"
begin

text \<open>
  We interpret the terms of theory \<^theory>\<open>Pure_Pattern.Pure_Term\<close> as the de Bruijn terms
  \<^typ>\<open>dB\<close> of session \<open>Nipkow_Grobauer_Pattern\<close>. Constants, free variables and schematic variables become
  free variables \<^term>\<open>dB.Var n\<close> of \<^typ>\<open>dB\<close>, encoded injectively (including their
  types). Substitutions that solve unification problems must fix the codes of constants and free
  variables.

  Schematic variables are identified by their index names, as in \<^const>\<open>lookup\<close>, \<^const>\<open>update\<close>
  and \<^const>\<open>occurs\<close>; constants and free variables by their names and types.

  Both libraries use the constructor names \<open>Var\<close>, \<open>Abs\<close> and \<open>App\<close>. The theory
  \<^theory>\<open>Pure_Pattern.Pure_Pattern\<close> is imported last, so these names refer to Pure terms;
  the de Bruijn constructors are written \<^const>\<open>dB.Var\<close>, \<^const>\<open>dB.Abs\<close> and \<open>\<degree>\<close>.
\<close>


subsection \<open>Encoding atoms\<close>

instance String.literal :: countable
  by (rule countable_classI[of "to_nat \<circ> String.explode"]) (simp add: String.explode_inject)

instance integer :: countable
  by (rule countable_classI[of "to_nat \<circ> int_of_integer"]) (simp add: integer_eq_iff)

instance ptyp :: countable
  by countable_datatype

datatype atom = AConst name ptyp | AFree name ptyp | AVar indexname

instance atom :: countable
  by countable_datatype

definition code :: "atom \<Rightarrow> nat" where
  "code a = to_nat a"

lemma code_inj[simp]: "code a = code b \<longleftrightarrow> a = b"
  by (simp add: code_def)

definition atom_of :: "nat \<Rightarrow> atom" where
  "atom_of n = from_nat n"

lemma atom_of_code[simp]: "atom_of (code a) = a"
  by (simp add: atom_of_def code_def)


subsection \<open>Translation of terms\<close>

text \<open>
  Pure terms with negative de Bruijn indices do not occur; we call terms without them
  \<^emph>\<open>proper\<close>. The translation forgets the names and types of bound variables.
\<close>

fun proper :: "pterm \<Rightarrow> bool" where
  "proper (Bound i) \<longleftrightarrow> 0 \<le> i"
| "proper (Abs _ _ t) \<longleftrightarrow> proper t"
| "proper (s $ t) \<longleftrightarrow> proper s \<and> proper t"
| "proper _ \<longleftrightarrow> True"

fun tr :: "pterm \<Rightarrow> dB" where
  "tr (Const a T) = dB.Var (code (AConst a T))"
| "tr (Free a T) = dB.Var (code (AFree a T))"
| "tr (Var x T) = dB.Var (code (AVar x))"
| "tr (Bound i) = BVar (nat_of_integer i)"
| "tr (Abs _ _ t) = dB.Abs (tr t)"
| "tr (s $ t) = tr s \<degree> tr t"

lemmas integer_reps = nat_of_integer.rep_eq less_integer.rep_eq less_eq_integer.rep_eq
  integer_eq_iff

lemma nat_of_integer_less_iff:
  "0 \<le> i \<Longrightarrow> 0 \<le> j \<Longrightarrow> nat_of_integer i < nat_of_integer j \<longleftrightarrow> i < j"
  by (auto simp: integer_reps)

lemma nat_of_integer_eq_iff:
  "0 \<le> i \<Longrightarrow> 0 \<le> j \<Longrightarrow> nat_of_integer i = nat_of_integer j \<longleftrightarrow> i = j"
  by (simp add: integer_reps eq_nat_nat_iff)

lemma nat_of_integer_add:
  "0 \<le> i \<Longrightarrow> 0 \<le> j \<Longrightarrow> nat_of_integer (i + j) = nat_of_integer i + nat_of_integer j"
  by (simp add: nat_of_integer.rep_eq less_eq_integer.rep_eq nat_add_distrib)

lemma nat_of_integer_diff:
  "0 \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> nat_of_integer (i - j) = nat_of_integer i - nat_of_integer j"
  by (simp add: nat_of_integer.rep_eq less_eq_integer.rep_eq nat_diff_distrib)

lemma nat_of_integer_minus_1:
  "0 < i \<Longrightarrow> nat_of_integer (i - 1) = nat_of_integer i - 1"
  by (simp add: nat_of_integer.rep_eq less_integer.rep_eq nat_diff_distrib)

lemma tr_incr_bv:
  "proper t \<Longrightarrow> 0 \<le> inc \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    tr (incr_bv inc lev t) = liftn (nat_of_integer inc) (tr t) (nat_of_integer lev)"
  by (induction inc lev t rule: incr_bv.induct)
    (auto simp: nat_of_integer_less_iff nat_of_integer_add not_less)

lemma proper_incr_bv: "proper t \<Longrightarrow> 0 \<le> inc \<Longrightarrow> proper (incr_bv inc lev t)"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma tr_subst_bound_aux:
  "proper t \<Longrightarrow> proper arg \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    tr (subst_bound_aux arg lev t) = substn (tr t) (tr arg) (nat_of_integer lev)"
  by (induction arg lev t rule: subst_bound_aux.induct)
    (auto simp: nat_of_integer_less_iff nat_of_integer_eq_iff nat_of_integer_add
      nat_of_integer_minus_1 incr_boundvars_def tr_incr_bv not_less)

lemma proper_subst_bound_aux:
  "proper t \<Longrightarrow> proper arg \<Longrightarrow> 0 \<le> lev \<Longrightarrow> proper (subst_bound_aux arg lev t)"
  by (induction arg lev t rule: subst_bound_aux.induct)
    (auto simp: incr_boundvars_def proper_incr_bv integer_reps)

lemma proper_subst_bound: "proper t \<Longrightarrow> proper arg \<Longrightarrow> proper (subst_bound arg t)"
  by (simp add: subst_bound_def proper_subst_bound_aux)

lemma tr_subst_bound:
  "proper t \<Longrightarrow> proper arg \<Longrightarrow> tr (subst_bound arg t) = (tr t)[tr arg/0]"
  by (simp add: subst_bound_def tr_subst_bound_aux substn_subst_0)


subsection \<open>Reasoning about successful computations\<close>

abbreviation ok :: "'a M \<Rightarrow> 'a \<Rightarrow> bool" where
  "ok m x \<equiv> m = Some (Ok x)"

lemma ok_simps[simp]:
  "ok (return x) y \<longleftrightarrow> x = y"
  "\<not> ok (raise e) y"
  "\<not> ok None y"
  by (simp_all add: return_def raise_def)

lemma ok_bindM[simp]: "ok (bindM m f) y \<longleftrightarrow> (\<exists>x. ok m x \<and> ok (f x) y)"
  by (auto simp: bindM_def split: option.splits res.splits)

lemma ok_handle:
  "ok (handle m h) y \<longleftrightarrow> ok m y \<or> (\<exists>e. m = Some (Err e) \<and> ok (h e) y)"
  by (auto simp: handle_def split: option.splits res.splits)

lemma ok_mapM: "ok (mapM f xs) ys \<longleftrightarrow> list_all2 (\<lambda>x y. ok (f x) y) xs ys"
  by (induction xs arbitrary: ys) (auto simp: list_all2_Cons1)

lemma ok_nth: "ok (nth xs i) x \<longleftrightarrow> 0 \<le> i \<and> nat_of_integer i < length xs \<and> x = xs ! nat_of_integer i"
proof (induction xs arbitrary: i)
  case (Cons y ys)
  show ?case
  proof (cases "i \<le> 0")
    case False
    then have "nat_of_integer i = Suc (nat_of_integer (i - 1))"
      by (simp add: integer_reps)
    with False Cons.IH[of "i - 1"] show ?thesis by (auto simp: integer_reps)
  qed (auto simp: integer_reps)
qed simp

lemma ilength_eq: "ilength xs = integer_of_nat (length xs)"
  by (induction xs) (simp_all add: integer_eq_iff)

lemma nat_of_integer_ilength[simp]: "nat_of_integer (ilength xs) = length xs"
  by (simp add: ilength_eq)

lemma ilength_nonneg[simp]: "0 \<le> ilength xs"
  by (simp add: ilength_eq integer_reps)


subsection \<open>Applications and abstractions\<close>

lemma tr_list_comb: "tr (list_comb h ts) = tr h \<degree>\<degree> map tr ts"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma proper_list_comb: "proper (list_comb h ts) \<longleftrightarrow> proper h \<and> (\<forall>t\<in>set ts. proper t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma strip_comb_acc_list_comb: "strip_comb_acc t ts = (h, us) \<Longrightarrow> list_comb t ts = list_comb h us"
  by (induction t ts rule: strip_comb_acc.induct) (simp_all add: list_comb_def)

lemma strip_comb_list_comb: "strip_comb t = (h, ts) \<Longrightarrow> t = list_comb h ts"
  using strip_comb_acc_list_comb[of t "[]" h ts] by (simp add: strip_comb_def list_comb_def)

lemma strip_comb_acc_head: "strip_comb_acc t ts = (h, us) \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)"
  by (induction t ts rule: strip_comb_acc.induct) auto

lemma strip_comb_head: "strip_comb t = (h, ts) \<Longrightarrow> \<not> (\<exists>f u. h = f $ u)"
  by (simp add: strip_comb_def strip_comb_acc_head)

lemma tr_app:
  "tr (app s is) = tr s \<degree>\<degree> map (\<lambda>i. BVar (nat_of_integer i)) is"
  by (induction "is" arbitrary: s) (simp_all add: app_def)

lemma proper_app: "proper (app s is) \<longleftrightarrow> proper s \<and> (\<forall>i\<in>set is. 0 \<le> i)"
  by (induction "is" arbitrary: s) (auto simp: app_def)

lemma ok_mkabs:
  "ok (mkabs binders is t) u \<Longrightarrow> tr u = Abs_m (length is) (tr t) \<and> (proper u \<longleftrightarrow> proper t)"
  by (induction "is" arbitrary: u) (auto split: prod.splits)


subsection \<open>Ground types\<close>

text \<open>
  The core of the verification treats problems without type variables: all types are ground,
  and type constructors are used with fixed arities \<open>ar\<close> (the function type constructor has
  arity 2). Then \<^const>\<open>unify_types\<close> succeeds iff the types are equal, and the type environment
  stays empty. Problems with type variables are reduced to their ground instances (theories
  \<open>Poly_*\<close>).
\<close>

fun ground :: "(name \<Rightarrow> nat) \<Rightarrow> ptyp \<Rightarrow> bool" where
  "ground ar (Type a Ts) \<longleftrightarrow>
    length Ts = (if a = STR ''fun'' then 2 else ar a) \<and> (\<forall>T\<in>set Ts. ground ar T)"
| "ground ar (TFree _ _) \<longleftrightarrow> True"
| "ground ar (TVar _ _) \<longleftrightarrow> False"

fun typs_ok :: "(name \<Rightarrow> nat) \<Rightarrow> pterm \<Rightarrow> bool" where
  "typs_ok ar (Const _ T) \<longleftrightarrow> ground ar T"
| "typs_ok ar (Free _ T) \<longleftrightarrow> ground ar T"
| "typs_ok ar (Var _ T) \<longleftrightarrow> ground ar T"
| "typs_ok ar (Bound _) \<longleftrightarrow> True"
| "typs_ok ar (Abs _ T t) \<longleftrightarrow> ground ar T \<and> typs_ok ar t"
| "typs_ok ar (s $ t) \<longleftrightarrow> typs_ok ar s \<and> typs_ok ar t"

lemma typs_ok_incr_bv: "typs_ok ar (incr_bv inc lev t) \<longleftrightarrow> typs_ok ar t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma typs_ok_subst_bound_aux:
  "typs_ok ar t \<Longrightarrow> typs_ok ar arg \<Longrightarrow> typs_ok ar (subst_bound_aux arg lev t)"
  by (induction arg lev t rule: subst_bound_aux.induct)
    (auto simp: incr_boundvars_def typs_ok_incr_bv)

lemma typs_ok_subst_bound:
  "typs_ok ar t \<Longrightarrow> typs_ok ar arg \<Longrightarrow> typs_ok ar (subst_bound arg t)"
  by (simp add: subst_bound_def typs_ok_subst_bound_aux)

lemma typs_ok_list_comb: "typs_ok ar (list_comb h ts) \<longleftrightarrow> typs_ok ar h \<and> (\<forall>t\<in>set ts. typs_ok ar t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma typs_ok_app: "typs_ok ar (app s is) \<longleftrightarrow> typs_ok ar s"
  by (induction "is" arbitrary: s) (auto simp: app_def)

lemma devar_nonvar: "(\<And>v S. T \<noteq> TVar v S) \<Longrightarrow> devar tye T = return T"
  by (subst devar.simps) (auto split: ptyp.splits)

lemma foldM_zip_eq:
  assumes "length Ts = length Us"
    and "\<And>T U st. T \<in> set Ts \<Longrightarrow> U \<in> set Us \<Longrightarrow> f T U st = (if T = U then return st else raise e)"
  shows "foldM (\<lambda>(T, U) st. f T U st) (zip Ts Us) st = (if Ts = Us then return st else raise e)"
  using assms by (induction Ts Us arbitrary: st rule: list_induct2) auto

lemma unify_aux_ground:
  "ground ar T \<Longrightarrow> ground ar U \<Longrightarrow>
    unify_aux alg T U st = (if T = U then return st else raise TUnify)"
proof (induction T arbitrary: U st)
  case (Type a Ts)
  obtain tye cnt where st: "st = (tye, cnt)" by force
  show ?case
  proof (cases U)
    case (Type b Us)
    show ?thesis
    proof (cases "a = b")
      case True
      with Type.prems \<open>U = Type b Us\<close> have len: "length Ts = length Us" by (simp split: if_splits)
      have "foldM (\<lambda>(T, U) st. unify_aux alg T U st) (zip Ts Us) st =
        (if Ts = Us then return st else raise TUnify)"
        using Type.IH Type.prems \<open>U = Type b Us\<close> by (intro foldM_zip_eq[OF len]) auto
      with True show ?thesis
        by (subst unify_aux.simps) (simp add: st \<open>U = Type b Us\<close> devar_nonvar)
    qed (subst unify_aux.simps; simp add: st \<open>U = Type b Us\<close> devar_nonvar)
  next
    case (TFree b S)
    then show ?thesis by (subst unify_aux.simps) (simp add: st devar_nonvar)
  next
    case (TVar v S)
    with Type.prems show ?thesis by simp
  qed
next
  case (TFree a S)
  then show ?case
    by (cases U; subst unify_aux.simps) (auto simp: devar_nonvar split: prod.splits)
qed simp

lemma unify_types_ground:
  "ground ar T \<Longrightarrow> ground ar U \<Longrightarrow>
    unify_types alg T U env = (if T = U then return env else raise (Unif (Typ_Clash (tyenv env) T U)))"
  by (simp add: unify_types_def type_unify_def unify_aux_ground)


subsection \<open>Environments\<close>

text \<open>
  An environment denotes the set of substitutions that satisfy its bindings modulo \<open>\<beta>\<eta>\<close>.
  Its bindings need not be idempotent or acyclic for this.
\<close>

definition sat :: "(nat \<Rightarrow> dB) \<Rightarrow> env \<Rightarrow> bool" where
  "sat \<sigma> env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> \<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u))"

definition wf_env :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> bool" where
  "wf_env ar env \<longleftrightarrow> vt_is_empty (tyenv env) \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
      proper u \<and> typs_ok ar u \<and> ground ar U \<and> no_loose_bound (tr u) 0)"

lemma satD: "sat \<sigma> env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
    \<sigma> (code (AVar x)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
  by (cases x) (simp add: sat_def)

lemma wf_envD:
  assumes "wf_env ar env"
  shows "vt_is_empty (tyenv env)"
    and "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
      proper u \<and> typs_ok ar u \<and> ground ar U \<and> no_loose_bound (tr u) 0"
  using assms by (cases x; simp add: wf_env_def)+

text \<open>Bindings are only ever added.\<close>

definition extends :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "extends env' env \<longleftrightarrow> (\<forall>x b. vt_lookup (tenv env) x = Some b \<longrightarrow> vt_lookup (tenv env') x = Some b)"

lemma extends_refl[simp]: "extends env env"
  by (simp add: extends_def)

lemma extends_trans: "extends env'' env' \<Longrightarrow> extends env' env \<Longrightarrow> extends env'' env"
  by (simp add: extends_def)

lemma sat_extends: "sat \<sigma> env' \<Longrightarrow> extends env' env \<Longrightarrow> sat \<sigma> env"
  by (simp add: sat_def extends_def)

lemma unified_empty: "vt_is_empty tye \<Longrightarrow> unified tye T U = return (T = U)"
  by (simp add: unified_def)

lemma ok_lookup:
  assumes "vt_is_empty (tyenv env)" "ok (lookup env xi T) r"
  shows "r = None \<and> vt_lookup (tenv env) xi = None \<or>
    (\<exists>u. r = Some u \<and> vt_lookup (tenv env) xi = Some (T, u))"
  using assms
  by (auto simp: lookup_def unified_empty var_clash_def split: option.splits if_splits)

text \<open>Equality of terms modulo \<open>\<beta>\<eta>\<close> under every closed substitution satisfying an environment.\<close>

definition env_equiv :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" (\<open>_ \<Turnstile> _ \<approx> _\<close> [50, 50, 50] 50) where
  "env \<Turnstile> s \<approx> t \<longleftrightarrow>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> env \<longrightarrow> mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t))"

lemma env_equivI:
  "(\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env \<Longrightarrow> mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)) \<Longrightarrow>
    env \<Turnstile> s \<approx> t"
  by (simp add: env_equiv_def)

lemma env_equivD:
  "env \<Turnstile> s \<approx> t \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env \<Longrightarrow>
    mk_subst \<sigma> (tr s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr t)"
  by (simp add: env_equiv_def)

lemma env_equiv_refl[simp, intro]: "env \<Turnstile> t \<approx> t"
  by (simp add: env_equiv_def)

lemma env_equiv_sym: "env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> t \<approx> s"
  by (auto simp: env_equiv_def intro: equiv_sym)

lemma env_equiv_trans[trans]: "env \<Turnstile> r \<approx> s \<Longrightarrow> env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> r \<approx> t"
  by (auto simp: env_equiv_def intro: equiv_trans)

lemma env_equiv_Abs: "env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> pterm.Abs a T s \<approx> pterm.Abs b U t"
  by (auto simp: env_equiv_def intro: equiv_Abs)

lemma env_equiv_App: "env \<Turnstile> s \<approx> s' \<Longrightarrow> env \<Turnstile> t \<approx> t' \<Longrightarrow> env \<Turnstile> s $ t \<approx> s' $ t'"
  by (auto simp: env_equiv_def intro: equiv_App)

lemma env_equiv_extends: "env \<Turnstile> s \<approx> t \<Longrightarrow> extends env' env \<Longrightarrow> env' \<Turnstile> s \<approx> t"
  by (auto simp: env_equiv_def intro: sat_extends)

lemma env_equiv_beta:
  assumes "proper body" "proper u"
  shows "env \<Turnstile> pterm.Abs a T body $ u \<approx> subst_bound u body"
proof (rule env_equivI)
  fix \<sigma> :: "nat \<Rightarrow> dB" assume "closed_on UNIV \<sigma>"
  have "mk_subst \<sigma> (tr (pterm.Abs a T body $ u)) \<rightarrow>\<^sub>\<beta> (mk_subst \<sigma> (tr body))[mk_subst \<sigma> (tr u)/0]"
    by simp
  also have "(mk_subst \<sigma> (tr body))[mk_subst \<sigma> (tr u)/0] = mk_subst \<sigma> (tr (subst_bound u body))"
    using assms \<open>closed_on UNIV \<sigma>\<close> by (simp add: tr_subst_bound mk_subst_subst_on closed_on_mono)
  finally show "mk_subst \<sigma> (tr (pterm.Abs a T body $ u)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (subst_bound u body))"
    by (intro beta_into_equiv) auto
qed

lemma env_equiv_lookup: "vt_lookup (tenv env) x = Some (T, u) \<Longrightarrow> env \<Turnstile> pterm.Var x T \<approx> u"
  by (auto simp: env_equiv_def dest: satD)

lemma no_loose_bound_beta:
  assumes "proper body" "proper u" "no_loose_bound (tr (pterm.Abs a T body)) k"
    "no_loose_bound (tr u) k"
  shows "no_loose_bound (tr (subst_bound u body)) k"
proof -
  have "\<beta>\<eta>cl (tr (pterm.Abs a T body $ u)) ((tr body)[tr u/0])"
    by (intro beta_into_\<beta>\<eta>cl) auto
  from \<beta>\<eta>cl_no_loose_bound[OF this] assms show ?thesis by (simp add: tr_subst_bound)
qed

lemma head_norm_sound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wf_env ar env \<Longrightarrow> proper t \<Longrightarrow> typs_ok ar t \<Longrightarrow>
    proper t' \<and> typs_ok ar t' \<and> env \<Turnstile> t \<approx> t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and t': "ok (case t of
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
  show ?case
  proof (cases t)
    case (Var xi T)
    with t' obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of None \<Rightarrow> return t | Some u \<Rightarrow> hn env u) t'"
      by auto
    from ok_lookup[OF wf_envD(1)[OF wf] lk]
    consider "r' = None" | u where "r' = Some u" "vt_lookup (tenv env) xi = Some (T, u)"
      by auto
    then show ?thesis
    proof cases
      case 1
      with rest 1 show ?thesis using "1.prems" by auto
    next
      case 2
      with wf_envD(2)[OF wf] have u: "proper u" "typs_ok ar u" "no_loose_bound (tr u) 0" by auto
      from 2 rest have "hn env u = Some (Ok t')" by simp
      from "1.IH"[OF this refl wf u(1,2)] 2 Var u(3) show ?thesis
        by (auto intro: env_equiv_trans env_equiv_lookup no_loose_bound_mono)
    qed
  next
    case (Abs a T body)
    with t' obtain b' where "hn env body = Some (Ok b')" "t' = pterm.Abs a T b'" by auto
    with "1.IH"[OF this(1) refl wf] "1.prems" Abs show ?thesis by (auto intro: env_equiv_Abs)
  next
    case (App f u)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a T body where f: "f = pterm.Abs a T body" by (cases f) auto
      with t' App have "hn env (subst_bound u body) = Some (Ok t')" by simp
      from "1.IH"[OF this refl wf] "1.prems" App f show ?thesis
        by (auto simp: proper_subst_bound typs_ok_subst_bound no_loose_bound_beta
          intro: env_equiv_trans env_equiv_beta)
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl wf] "1.prems" App
      have nf': "proper nf" "typs_ok ar nf" "env \<Turnstile> f \<approx> nf"
        "\<And>k. no_loose_bound (tr f) k \<Longrightarrow> no_loose_bound (tr nf) k"
        by auto
      then have fu: "env \<Turnstile> f $ u \<approx> nf $ u" by (auto intro: env_equiv_App)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl wf] "1.prems" App nf' nfa fu show ?thesis
          by (auto simp: proper_subst_bound typs_ok_subst_bound no_loose_bound_beta
            intro: env_equiv_trans[OF fu] env_equiv_trans[OF env_equiv_beta])
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with nf' fu "1.prems" App show ?thesis by auto
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

end
