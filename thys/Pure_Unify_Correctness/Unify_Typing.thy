section \<open>Typing of the Steps\<close>

theory Unify_Typing
  imports Unify_Pull Unify_Lsize
begin

text \<open>
  Completeness needs types (as for pattern unification, theory
  \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Typing\<close>). With an empty type environment, the type
  computations of \<open>unify.ML\<close> are exact on well-typed terms: \<^const>\<open>fastype\<close> returns the type,
  \<^const>\<open>eta_norm\<close> \<open>\<eta>\<close>-expands to a term whose body has a base type, and the type unifications
  in \<^const>\<open>SIMPL\<close> succeed without changing the environment.
\<close>

subsection \<open>Types of terms\<close>

lemma has_type_incr_boundvars1: "has_type V Ts t T \<Longrightarrow> has_type V (U # Ts) (incr_boundvars 1 t) T"
  using has_type_incr_bv[of V Ts t T 1 0 "[U]"] by (simp add: incr_boundvars_def integer_reps)

lemma nth_return: "0 \<le> i \<Longrightarrow> nat_of_integer i < length xs \<Longrightarrow> nth xs i = return (xs ! nat_of_integer i)"
  using ok_nth[of xs i "xs ! nat_of_integer i"] by (simp add: return_def)

lemma type_lookup_empty: "vt_is_empty tye \<Longrightarrow> type_lookup tye v S = return None"
  by (simp add: type_lookup_def vt_is_empty_lookup)

lemma env_fastype_typed:
  assumes "vt_is_empty (tyenv env)"
  shows "has_type V Ts t T \<Longrightarrow> env_fastype env Ts t = return T"
proof (induction rule: has_type.induct)
  case (Bound i Ts T V)
  then show ?case by (simp add: nth_return handle_def return_def)
next
  case (App V Ts s T U t)
  then show ?case by (simp add: devar_empty[OF assms])
qed simp_all

lemma fastype_typed:
  "vt_is_empty (tyenv env) \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow> fastype env rb t = return T"
  by (simp add: fastype_def env_fastype_typed)


subsection \<open>Head-long forms\<close>

text \<open>
  \<open>hlong V Ts t T\<close>: \<open>t\<close> has type \<open>T\<close>, its outer abstractions follow \<open>T\<close>, and its body is not an
  abstraction and has a type that is not a function type.
\<close>

inductive hlong :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> ptyp list \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" for V where
  base: "has_type V Ts t T \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> \<not> is_funT T \<Longrightarrow> hlong V Ts t T"
| Abs: "hlong V (A # Ts) b U \<Longrightarrow> hlong V Ts (Abs a A b) (A \<rightarrow>\<^sub>T U)"

lemma hlong_typed: "hlong V Ts t T \<Longrightarrow> has_type V Ts t T"
  by (induction rule: hlong.induct) (auto intro: has_type.Abs)

lemma is_funT_fun: "is_funT T \<longleftrightarrow> (\<exists>A U. T = A \<rightarrow>\<^sub>T U)"
  by (cases T rule: is_funT.cases) auto

lemma etif_hlong:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> vt_is_empty tye \<Longrightarrow> has_type V Ts t T \<Longrightarrow> \<not> is_Abs t \<Longrightarrow> hlong V Ts t' T"
  using assms
proof (induction tye T t r arbitrary: Ts t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 et tye T t r)
  have e: "vt_is_empty tye" and ty: "has_type V Ts t T" and nA: "\<not> is_Abs t"
    and body: "ok (case T of
      Type a Ts \<Rightarrow>
        (case Ts of
          [T1, U] \<Rightarrow>
            if a = STR ''fun'' then do {
              u \<leftarrow> et tye U (incr_boundvars 1 t $ Bound 0);
              return (Abs STR '''' T1 u)}
            else return t
        | _ \<Rightarrow> return t)
    | TVar v S \<Rightarrow> do {
        r \<leftarrow> type_lookup tye v S;
        case r of None \<Rightarrow> return t | Some T' \<Rightarrow> et tye T' t}
    | _ \<Rightarrow> return t) t'"
    using 1 by simp_all
  show ?case
  proof (cases "is_funT T")
    case True
    then obtain A U where T: "T = A \<rightarrow>\<^sub>T U" by (auto simp: is_funT_fun)
    with body obtain u where u: "et tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' A u" by auto
    have "has_type V (A # Ts) (incr_boundvars 1 t $ Bound 0) U"
      by (rule has_type.App[OF has_type_incr_boundvars1[OF ty[unfolded T], of A]])
        (simp add: has_type_Bound_iff)
    from "1.IH"[OF u refl e this] show ?thesis by (simp add: t' T hlong.Abs)
  next
    case False
    have "t' = t"
    proof (cases T)
      case (Type a Ts)
      with False body show ?thesis by (auto split: list.splits if_splits)
    next
      case (TVar v S)
      with body e show ?thesis by (auto simp: type_lookup_empty)
    qed (use body in auto)
    with ty nA False show ?thesis by (simp add: hlong.base)
  qed
qed

lemma eta_norm_hlong:
  "vt_is_empty (tyenv env) \<Longrightarrow> has_type V (map snd rb) t T \<Longrightarrow> ok (eta_norm env rb t) t' \<Longrightarrow>
    hlong V (map snd rb) t' T"
proof (induction env rb t arbitrary: T t' rule: eta_norm.induct)
  case (1 env rb a A body)
  from "1.prems"(2) obtain U where T: "T = A \<rightarrow>\<^sub>T U" and tb: "has_type V (A # map snd rb) body U"
    by (auto elim: has_type_elims)
  from "1.prems"(3) obtain b' where b': "ok (eta_norm env ((a, A) # rb) body) b'"
    and t': "t' = Abs a A b'" by auto
  from "1.IH"[OF "1.prems"(1) _ b'] tb show ?case by (simp add: t' T hlong.Abs)
qed (auto simp: fastype_typed intro: etif_hlong)

subsection \<open>Type operations\<close>

lemma body_type_fun: "body_type env (A \<rightarrow>\<^sub>T U) = body_type env U"
  by (subst body_type.simps) simp

lemma body_type_base:
  assumes "vt_is_empty (tyenv env)" "\<not> is_funT B"
  shows "body_type env (foldr fun_type Us B) = return B"
proof (induction Us)
  case Nil
  show ?case
  proof (cases B)
    case (Type a Ts)
    with assms(2) show ?thesis
      by (subst body_type.simps) (auto split: list.splits if_splits)
  next
    case (TVar v S)
    with assms(1) show ?thesis by (subst body_type.simps) (simp add: type_lookup_empty)
  qed (subst body_type.simps, simp)+
qed (simp add: body_type_fun)

lemma binder_types_fun: "binder_types env (A \<rightarrow>\<^sub>T U) = do {Us \<leftarrow> binder_types env U; return (A # Us)}"
  by (subst binder_types.simps) simp

lemma binder_types_base:
  assumes "vt_is_empty (tyenv env)" "\<not> is_funT B"
  shows "binder_types env (foldr fun_type Us B) = return Us"
proof (induction Us)
  case Nil
  show ?case
  proof (cases B)
    case (Type a Ts)
    with assms(2) show ?thesis
      by (subst binder_types.simps) (auto split: list.splits if_splits)
  next
    case (TVar v S)
    with assms(1) show ?thesis by (subst binder_types.simps) (simp add: type_lookup_empty)
  qed (subst binder_types.simps, simp)+
qed (simp add: binder_types_fun)

text \<open>Every type is a base type after stripping its arguments.\<close>

fun arg_types :: "ptyp \<Rightarrow> ptyp list" where
  "arg_types (Type a [A, U]) = (if a = STR ''fun'' then A # arg_types U else [])"
| "arg_types _ = []"

fun res_type :: "ptyp \<Rightarrow> ptyp" where
  "res_type (Type a [A, U]) = (if a = STR ''fun'' then res_type U else Type a [A, U])"
| "res_type T = T"

lemma arg_res_type: "foldr fun_type (arg_types T) (res_type T) = T"
  by (induction T rule: arg_types.induct) auto

lemma res_type_base: "\<not> is_funT (res_type T)"
  by (induction T rule: res_type.induct) auto

lemma arg_res_type_fun:
  "\<not> is_funT B \<Longrightarrow> arg_types (foldr fun_type Us B) = Us \<and> res_type (foldr fun_type Us B) = B"
  by (induction Us) (auto elim: is_funT.elims)

lemma unify_types_same: "unify_types alg T T env = return env"
  by (simp add: unify_types_def)

lemma cunify_types_same: "cunify_types alg T T env = returnW env"
  by (simp add: cunify_types_def unify_types_same return_def)


subsection \<open>Disagreement pairs\<close>

text \<open>\<^const>\<open>new_dpair\<close> strips the common abstractions of two head-long terms of the same type.\<close>

lemma new_dpair_hlong:
  assumes "hlong V (map snd rb) t T" "hlong V (map snd rb) u T"
  shows "\<exists>rb'. new_dpair alg rb t u env = returnW ((rb', strip_abs_body t, strip_abs_body u), env) \<and>
    map snd rb' = rev (arg_types T) @ map snd rb \<and>
    has_type V (map snd rb') (strip_abs_body t) (res_type T) \<and>
    has_type V (map snd rb') (strip_abs_body u) (res_type T) \<and>
    \<not> is_Abs (strip_abs_body t) \<and> \<not> is_Abs (strip_abs_body u)"
  using assms
proof (induction "map snd rb" t T arbitrary: rb u rule: hlong.induct)
  case (base t T)
  from base.prems have tu: "has_type V (map snd rb) u T" "\<not> is_Abs u"
    using base.hyps(3) by (auto elim: hlong.cases)
  have "arg_types T = []" "res_type T = T"
    using base.hyps(3) by (cases T rule: arg_types.cases; auto)+
  with base.hyps tu show ?case
    by (cases t; cases u) (auto simp: returnW_def)
next
  case (Abs A b U a)
  from Abs.prems obtain c ub where u: "u = pterm.Abs c A ub" and hub: "hlong V (A # map snd rb) ub U"
    by (auto elim: hlong.cases)
  define n where "n = (if a = STR '''' then c else a)"
  have m: "A # map snd rb = map snd ((n, A) # rb)" by simp
  from Abs.hyps(2)[OF m hub[unfolded m]] obtain rb' where
    r: "new_dpair alg ((n, A) # rb) b ub env = returnW ((rb', strip_abs_body b, strip_abs_body ub), env)"
      "map snd rb' = rev (arg_types U) @ map snd ((n, A) # rb)"
      "has_type V (map snd rb') (strip_abs_body b) (res_type U)"
      "has_type V (map snd rb') (strip_abs_body ub) (res_type U)"
      "\<not> is_Abs (strip_abs_body b)" "\<not> is_Abs (strip_abs_body ub)"
    by blast
  show ?case
    using r by (auto simp: u n_def Let_def cunify_types_same intro!: exI[of _ rb'])
qed

end
