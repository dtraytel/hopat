section \<open>Typing of Pure Terms\<close>

theory Pattern_Typing
  imports Pattern_Soundness
begin

text \<open>
  Completeness needs types: the occurs check and the unique normal forms of unifiers depend on
  them. Ground types are translated into the simple types of \<^theory>\<open>HOPAT.LambdaType\<close>; the
  types of schematic variables are given by a variable typing \<open>V\<close>.
\<close>

subsection \<open>Types\<close>

fun trty :: "ptyp \<Rightarrow> type" where
  "trty (Type a [T, U]) = (if a = STR ''fun'' then trty T \<Rightarrow> trty U else Atom (to_nat (Type a [T, U])))"
| "trty T = Atom (to_nat T)"

lemma trty_fun[simp]: "trty (T \<rightarrow>\<^sub>T U) = trty T \<Rightarrow> trty U"
  by simp

lemma trty_not_fun: "(\<nexists>T1 T2. T = T1 \<rightarrow>\<^sub>T T2) \<Longrightarrow> trty T = Atom (to_nat T)"
  by (cases T rule: trty.cases) auto

lemma trty_inj: "ground ar T \<Longrightarrow> ground ar U \<Longrightarrow> trty T = trty U \<Longrightarrow> T = U"
proof (induction T arbitrary: U)
  case (Type a Ts)
  show ?case
  proof (cases "\<exists>T1 T2. Type a Ts = T1 \<rightarrow>\<^sub>T T2")
    case True
    then obtain T1 T2 where T: "a = STR ''fun''" "Ts = [T1, T2]" by auto
    show ?thesis
    proof (cases "\<exists>U1 U2. U = U1 \<rightarrow>\<^sub>T U2")
      case True
      then obtain U1 U2 where U: "U = U1 \<rightarrow>\<^sub>T U2" by auto
      with Type.IH[of T1 U1] Type.IH[of T2 U2] Type.prems T show ?thesis by simp
    next
      case False
      with Type.prems T show ?thesis by (simp add: trty_not_fun)
    qed
  next
    case False
    then have "trty (Type a Ts) = Atom (to_nat (Type a Ts))" by (rule trty_not_fun)
    moreover have "\<nexists>U1 U2. U = U1 \<rightarrow>\<^sub>T U2"
      using Type.prems calculation by auto
    ultimately show ?thesis using Type.prems by (simp add: trty_not_fun)
  qed
next
  case (TFree a S)
  then show ?case
    by (cases "\<exists>U1 U2. U = U1 \<rightarrow>\<^sub>T U2") (auto simp: trty_not_fun)
qed simp

definition bnd_env :: "ptyp list \<Rightarrow> nat \<Rightarrow> type" where
  "bnd_env Ts i = trty (Ts ! i)"

lemma bnd_env_Cons: "bnd_env (T # Ts) = (bnd_env Ts)\<langle>0:trty T\<rangle>"
  by (auto simp: bnd_env_def shift_def fun_eq_iff nth_Cons')

definition tau :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> nat \<Rightarrow> type" where
  "tau V n = (case atom_of n of AConst _ T \<Rightarrow> trty T | AFree _ T \<Rightarrow> trty T | AVar x \<Rightarrow> trty (V x))"

lemma tau_code[simp]:
  "tau V (code (AConst a T)) = trty T" "tau V (code (AFree a T)) = trty T"
  "tau V (code (AVar x)) = trty (V x)"
  by (simp_all add: tau_def)


subsection \<open>The typing judgment\<close>

inductive has_type :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  Const: "has_type V Ts (Const a T) T"
| Free: "has_type V Ts (Free a T) T"
| Var: "V x = T \<Longrightarrow> has_type V Ts (Var x T) T"
| Bound: "0 \<le> i \<Longrightarrow> nat_of_integer i < length Ts \<Longrightarrow> T = Ts ! nat_of_integer i \<Longrightarrow>
    has_type V Ts (Bound i) T"
| Abs: "has_type V (T # Ts) t U \<Longrightarrow> has_type V Ts (Abs x T t) (T \<rightarrow>\<^sub>T U)"
| App: "has_type V Ts s (T \<rightarrow>\<^sub>T U) \<Longrightarrow> has_type V Ts t T \<Longrightarrow> has_type V Ts (s $ t) U"

inductive_cases has_type_elims:
  "has_type V Ts (Const a T) U"
  "has_type V Ts (Free a T) U"
  "has_type V Ts (Var x T) U"
  "has_type V Ts (Bound i) U"
  "has_type V Ts (Abs x T t) U"
  "has_type V Ts (s $ t) U"

lemma has_type_Bound_iff:
  "has_type V Ts (Bound i) T \<longleftrightarrow> 0 \<le> i \<and> nat_of_integer i < length Ts \<and> T = Ts ! nat_of_integer i"
  by (auto elim: has_type_elims intro: has_type.Bound)

lemma has_type_tr: "has_type V Ts t T \<Longrightarrow> (bnd_env Ts, tau V) \<turnstile> tr t : trty T"
proof (induction rule: has_type.induct)
  case (Bound i Ts T V)
  then show ?case by (auto simp: bnd_env_def)
next
  case (Abs V T Ts t U x)
  then show ?case by (auto simp: bnd_env_Cons)
qed auto

lemma has_type_proper: "has_type V Ts t T \<Longrightarrow> proper t"
  by (induction rule: has_type.induct) auto

lemma has_type_closed: "has_type V Ts t T \<Longrightarrow> no_loose_bound (tr t) (length Ts)"
  by (induction rule: has_type.induct) auto

lemma has_type_weaken: "has_type V Ts t T \<Longrightarrow> has_type V (Ts @ Us) t T"
  by (induction rule: has_type.induct) (auto intro: has_type.intros simp: nth_append)

lemma nth_take_append_low: "i < l \<Longrightarrow> l \<le> length Ts \<Longrightarrow> (take l Ts @ Us) ! i = Ts ! i"
  by (simp add: nth_append)

lemma nth_take_append_high:
  "l \<le> i \<Longrightarrow> i < length Ts \<Longrightarrow> (take l Ts @ Us @ drop l Ts) ! (i + length Us) = Ts ! i"
  by (simp add: nth_append min_def)

lemma has_type_incr_bv:
  assumes "has_type V Ts t T" "0 \<le> inc" "0 \<le> lev" "nat_of_integer lev \<le> length Ts"
    "nat_of_integer inc = length Us"
  shows "has_type V (take (nat_of_integer lev) Ts @ Us @ drop (nat_of_integer lev) Ts) (incr_bv inc lev t) T"
  using assms
proof (induction arbitrary: lev rule: has_type.induct)
  case (Bound i Ts T V)
  show ?case
  proof (cases "lev \<le> i")
    case True
    then have "nat_of_integer lev \<le> nat_of_integer i" by (simp add: integer_reps nat_mono)
    with Bound True show ?thesis
      using nth_take_append_high[of "nat_of_integer lev" "nat_of_integer i" Ts Us]
      by (auto simp: has_type_Bound_iff nat_of_integer_add)
  next
    case False
    then have "nat_of_integer i < nat_of_integer lev" using Bound by (simp add: nat_of_integer_less_iff)
    with Bound False show ?thesis
      using nth_take_append_low[of "nat_of_integer i" "nat_of_integer lev" Ts "Us @ drop (nat_of_integer lev) Ts"]
      by (auto simp: has_type_Bound_iff)
  qed
next
  case (Abs V T Ts t U x)
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using Abs.prems
    by (simp add: nat_of_integer_add)
  with Abs.IH[of "lev + 1"] Abs.prems show ?case
    by (auto intro!: has_type.Abs)
qed (auto intro: has_type.intros)

lemma has_type_incr_aux:
  assumes "has_type V Ts t T" "0 \<le> d" "nat_of_integer d \<le> length Ts"
  shows "has_type V (take (nat_of_integer d) Ts @ U # drop (nat_of_integer d) Ts) (incr_aux d t) T"
  using assms
proof (induction arbitrary: d rule: has_type.induct)
  case (Bound i Ts T V)
  show ?case
  proof (cases "i < d")
    case False
    then have "nat_of_integer d \<le> nat_of_integer i" by (simp add: integer_reps nat_mono)
    with Bound False show ?thesis
      using nth_take_append_high[of "nat_of_integer d" "nat_of_integer i" Ts "[U]"]
      by (auto simp: has_type_Bound_iff nat_of_integer_add)
  next
    case True
    then have "nat_of_integer i < nat_of_integer d" using Bound by (simp add: nat_of_integer_less_iff)
    with Bound True show ?thesis
      using nth_take_append_low[of "nat_of_integer i" "nat_of_integer d" Ts "U # drop (nat_of_integer d) Ts"]
      by (auto simp: has_type_Bound_iff)
  qed
next
  case (Abs V T Ts t U' x)
  have "nat_of_integer (d + 1) = Suc (nat_of_integer d)" using Abs.prems
    by (simp add: nat_of_integer_add)
  with Abs.IH[of "d + 1"] Abs.prems show ?case
    by (auto intro!: has_type.Abs)
qed (auto intro: has_type.intros)

lemma has_type_incr: "has_type V Ts t T \<Longrightarrow> has_type V (U # Ts) (incr t) T"
  using has_type_incr_aux[of V Ts t T 0 U] by (simp add: incr_def)

lemma has_type_subst_bound_aux:
  "has_type V Ts' body T \<Longrightarrow> Ts' = take (nat_of_integer lev) Ts @ U # drop (nat_of_integer lev) Ts \<Longrightarrow>
    has_type V (drop (nat_of_integer lev) Ts) arg U \<Longrightarrow> 0 \<le> lev \<Longrightarrow>
    nat_of_integer lev \<le> length Ts \<Longrightarrow> has_type V Ts (subst_bound_aux arg lev body) T"
proof (induction arbitrary: Ts lev rule: has_type.induct)
  case (Bound i Ts' T V Ts lev)
  let ?l = "nat_of_integer lev"
  consider "i < lev" | "i = lev" | "lev < i" by fastforce
  then show ?case
  proof cases
    case 1
    then have "nat_of_integer i < ?l" using Bound by (simp add: nat_of_integer_less_iff)
    with Bound 1 show ?thesis
      using nth_take_append_low[of "nat_of_integer i" ?l Ts "U # drop ?l Ts"]
      by (auto simp: has_type_Bound_iff)
  next
    case 2
    have "has_type V (take ?l Ts @ drop ?l Ts) (incr_boundvars lev arg) U"
    proof (cases "lev = 0")
      case True
      with Bound show ?thesis by (simp add: incr_boundvars_def)
    next
      case False
      have "has_type V (take 0 (drop ?l Ts) @ take ?l Ts @ drop 0 (drop ?l Ts)) (incr_bv lev 0 arg) U"
        using has_type_incr_bv[OF Bound(5), of lev 0 "take ?l Ts"] Bound(6,7) by (simp add: min_def)
      with False show ?thesis by (simp add: incr_boundvars_def)
    qed
    with Bound 2 show ?thesis by (auto simp: nth_append min_def has_type_Bound_iff)
  next
    case 3
    then have lt: "?l < nat_of_integer i" "0 < i" using Bound by (simp_all add: nat_of_integer_less_iff)
    then have i1: "nat_of_integer (i - 1) = nat_of_integer i - 1" "0 \<le> i - 1"
      by (simp_all add: nat_of_integer_minus_1 integer_reps)
    have lt': "length (take ?l Ts) = ?l" using Bound(7) by simp
    have "Ts' ! nat_of_integer i = (U # drop ?l Ts) ! (nat_of_integer i - ?l)"
      using Bound(4) lt lt' by (simp add: nth_append)
    also have "nat_of_integer i - ?l = Suc (nat_of_integer i - ?l - 1)" using lt by simp
    also have "(U # drop ?l Ts) ! Suc (nat_of_integer i - ?l - 1) = Ts ! (nat_of_integer i - 1)"
      using lt Bound(7) by simp
    finally have "Ts' ! nat_of_integer i = Ts ! (nat_of_integer i - 1)" .
    moreover have "nat_of_integer i - 1 < length Ts"
      using Bound(2,4,7) lt by auto
    ultimately show ?thesis using Bound 3 lt i1 by (auto simp: has_type_Bound_iff)
  qed
next
  case (Abs V T' Ts' t U' x Ts lev)
  have l1: "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)" using Abs.prems
    by (simp add: nat_of_integer_add)
  have "has_type V (T' # Ts) (subst_bound_aux arg (lev + 1) t) U'"
    by (rule Abs.IH) (use Abs.prems l1 in auto)
  then show ?case by (auto intro!: has_type.Abs)
next
  case (App V Ts' s T U' t Ts lev)
  have "has_type V Ts (subst_bound_aux arg lev s) (T \<rightarrow>\<^sub>T U')"
    by (rule App.IH(1)) (use App.prems in auto)
  moreover have "has_type V Ts (subst_bound_aux arg lev t) T"
    by (rule App.IH(2)) (use App.prems in auto)
  ultimately show ?case by (auto intro: has_type.App)
qed (auto intro: has_type.intros)

lemma has_type_subst_bound:
  assumes "has_type V (U # Ts) body T" "has_type V Ts arg U"
  shows "has_type V Ts (subst_bound arg body) T"
proof -
  have n0: "nat_of_integer 0 = 0" by (simp add: integer_reps)
  have "has_type V Ts (subst_bound_aux arg 0 body) T"
    by (rule has_type_subst_bound_aux[of V "U # Ts" body T 0 Ts U arg, OF assms(1)])
      (simp_all only: n0 take_0 drop_0 append_Nil assms(2) order_refl zero_le le0)
  then show ?thesis by (simp only: subst_bound_def)
qed


subsection \<open>Typed environments\<close>

definition env_typed :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> env \<Rightarrow> bool" where
  "env_typed V env \<longleftrightarrow>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> V x = U \<and> has_type V [] u U)"

lemma env_typedD: "env_typed V env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> V x = U \<and> has_type V [] u U"
  by (cases x) (simp add: env_typed_def)

lemma head_norm_typed:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> wf_env ar env \<Longrightarrow> env_typed V env \<Longrightarrow> has_type V Ts t T \<Longrightarrow> has_type V Ts t' T"
  using assms
proof (induction env t r arbitrary: t' Ts T rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "wf_env ar env" and ty: "env_typed V env" and t': "ok (case t of
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
  note IH = "1.IH"[OF _ refl wf ty]
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
      with rest "1.prems" show ?thesis by auto
    next
      case 2
      with rest have hu: "hn env u = Some (Ok t')" by simp
      from env_typedD[OF ty 2(2)] "1.prems"(4) Var have "has_type V Ts u T"
        using has_type_weaken[of V "[]" u U Ts] by (auto elim: has_type_elims)
      from IH[OF hu this] show ?thesis .
    qed
  next
    case (Abs a U body)
    with t' obtain b' where hb: "hn env body = Some (Ok b')" and tb: "t' = pterm.Abs a U b'" by auto
    from "1.prems"(4) Abs obtain W where "T = U \<rightarrow>\<^sub>T W" "has_type V (U # Ts) body W"
      by (auto elim: has_type_elims)
    with IH[OF hb] tb show ?thesis by (auto intro: has_type.Abs)
  next
    case (App f u)
    from "1.prems"(4) App obtain U where tf: "has_type V Ts f (U \<rightarrow>\<^sub>T T)" and tu: "has_type V Ts u U"
      by (auto elim: has_type_elims)
    have beta: "has_type V Ts (subst_bound u body) T" if "has_type V Ts (pterm.Abs a W body) (U \<rightarrow>\<^sub>T T)"
      for a W body
      using that tu by (auto elim!: has_type_elims intro: has_type_subst_bound)
    show ?thesis
    proof (cases "is_Abs f")
      case True
      then obtain a W body where f: "f = pterm.Abs a W body" by (cases f) auto
      with t' App have "hn env (subst_bound u body) = Some (Ok t')" by simp
      from IH[OF this beta] tf f show ?thesis by simp
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from IH[OF nf tf] have tnf: "has_type V Ts nf (U \<rightarrow>\<^sub>T T)" .
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a W body where nfa: "nf = pterm.Abs a W body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from IH[OF this beta] tnf nfa show ?thesis by simp
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with tnf tu show ?thesis by (auto intro: has_type.App)
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

end
