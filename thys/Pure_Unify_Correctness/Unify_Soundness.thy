section \<open>Soundness of the Assignment and Decomposition Steps\<close>

theory Unify_Soundness
  imports Unify_Semantics
begin

text \<open>
  We prove that the individual steps of \<open>unify.ML\<close> are sound: whenever they return an
  environment (or a binding), that environment solves the disagreement pair they process, in
  the sense of \<^const>\<open>env_equiv\<close>. A disagreement pair \<open>(rbinder, s, t)\<close> is turned into the
  closed terms \<open>rlist_abs rbinder s\<close> and \<open>rlist_abs rbinder t\<close>, whose translations are compared
  modulo \<open>\<beta>\<eta>\<close>.
\<close>


subsection \<open>Abstractions over a binder\<close>

lemma tr_rlist_abs: "tr (rlist_abs rbinder t) = Abs_m (length rbinder) (tr t)"
proof (induction rbinder arbitrary: t)
  case (Cons aT rbinder)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T t"] show ?case by (simp add: Abs_m)
qed simp



subsection \<open>The eta-variable of a flexible term\<close>

text \<open>
  If \<open>get_eta_var rbinder 0 t = (v, T)\<close>, then \<open>t\<close> is \<open>?v\<close> applied to the bound variables of
  \<open>rbinder\<close> in order, so \<open>rlist_abs rbinder t\<close> is the \<open>\<eta>\<close>-long form of \<open>?v\<close> and is
  \<open>\<beta>\<eta>\<close>-equivalent to it.
\<close>

lemma downs_Suc: "downs (Suc m) = map Suc (downs m) @ [0]"
  by (simp add: rev_map upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)

lemma list_app_downs_Suc:
  "(h \<degree>\<degree> map (\<lambda>k. BVar (Suc (j + k))) (downs m)) \<degree> BVar j =
    h \<degree>\<degree> map (\<lambda>k. BVar (j + k)) (downs (Suc m))"
  unfolding downs_Suc by (simp add: comp_def)

lemma get_eta_var_tr:
  "okW (get_eta_var rbinder n t) (v, T) \<Longrightarrow> 0 \<le> n \<Longrightarrow>
    tr t = dB.Var (code (AVar v)) \<degree>\<degree> map (\<lambda>k. BVar (nat_of_integer n + k)) (downs (length rbinder))
    \<and> proper t"
proof (induction rbinder arbitrary: n t)
  case Nil
  then show ?case by (cases t) auto
next
  case (Cons aT rbinder)
  from Cons.prems(1) obtain f where t: "t = f $ Bound n"
    and rec: "okW (get_eta_var rbinder (n + 1) f) (v, T)"
    by (cases "(aT # rbinder, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  have n1: "0 \<le> n + 1" using Cons.prems(2) by simp
  note IH = Cons.IH[OF rec n1]
  have shift: "nat_of_integer (n + 1) = Suc (nat_of_integer n)"
    using Cons.prems(2) by (simp add: integer_reps)
  have "tr t = (dB.Var (code (AVar v)) \<degree>\<degree>
      map (\<lambda>k. BVar (Suc (nat_of_integer n + k))) (downs (length rbinder))) \<degree> BVar (nat_of_integer n)"
    using IH t by (simp add: shift)
  also have "\<dots> = dB.Var (code (AVar v)) \<degree>\<degree>
      map (\<lambda>k. BVar (nat_of_integer n + k)) (downs (Suc (length rbinder)))"
    by (rule list_app_downs_Suc)
  finally have "tr t = dB.Var (code (AVar v)) \<degree>\<degree>
      map (\<lambda>k. BVar (nat_of_integer n + k)) (downs (length (aT # rbinder)))" by simp
  moreover have "proper t" using IH t Cons.prems(2) by (simp add: integer_reps)
  ultimately show ?case by blast
qed

lemma get_eta_var_equiv:
  assumes "okW (get_eta_var rbinder 0 t) (v, T)"
  shows "tr (rlist_abs rbinder t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AVar v)) \<and> proper t"
proof -
  from get_eta_var_tr[OF assms] have trt: "tr t = dB.Var (code (AVar v)) \<degree>\<degree> map BVar (downs (length rbinder))"
    and proper_t: "proper t" by (simp_all add: comp_def)
  have "tr (rlist_abs rbinder t) = Abs_m (length rbinder) (tr t)" by (rule tr_rlist_abs)
  with trt have "tr (rlist_abs rbinder t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Var (code (AVar v))"
    by (simp add: eta_expand_equiv)
  with proper_t show ?thesis by blast
qed


subsection \<open>Type unification keeps the term environment\<close>

lemma unify_types_tenv: "ok (unify_types alg T U env) env' \<Longrightarrow> tenv env' = tenv env"
proof (cases "T = U")
  case False
  assume *: "ok (unify_types alg T U env) env'"
  have hr: "\<not> ok ((\<lambda>e. case e of TUnify \<Rightarrow> raise (Unif (Typ_Clash (tyenv env) T U))
      | _ \<Rightarrow> raise e) e) y" for e y
    by (cases e) simp_all
  from * False have "ok (do {(tye', maxidx') \<leftarrow> type_unify alg U T (tyenv env, maxidx env);
      return (Envir maxidx' (tenv env) tye')}) env'"
    by (auto simp: unify_types_def ok_handle hr)
  then show ?thesis by (auto split: prod.splits)
qed (auto simp: unify_types_def)

lemma cunify_types_tenv: "okW (cunify_types alg T U env) env' \<Longrightarrow> tenv env' = tenv env"
  by (auto simp: cunify_types_def unify_types_tenv
      split: option.splits res.splits exn.splits)

lemma cunify_types_extends: "okW (cunify_types alg T U env) env' \<Longrightarrow> extends env env'"
  by (simp add: cunify_types_tenv extends_def)


subsection \<open>From a beta-eta-equivalence to an environment equivalence\<close>

lemma equiv_env_equiv: "tr s \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u \<Longrightarrow> env \<Turnstile> s \<approx> u"
  by (auto intro!: env_equivI mk_subst_equiv)


subsection \<open>Soundness of assignment\<close>

text \<open>
  \<open>assignment\<close> solves the disagreement pair it processes: if it returns \<open>env'\<close>, then \<open>env'\<close>
  extends \<open>env\<close> and every closed substitution satisfying \<open>env'\<close> makes the (abstractions over
  the binder of the) two sides \<open>\<beta>\<eta>\<close>-equal.
\<close>

lemma assignment_sound:
  assumes "okW (assignment alg rbinder t u env) env'"
  shows "extends env env' \<and> env' \<Turnstile> rlist_abs rbinder t \<approx> rlist_abs rbinder u"
proof -
  from assms obtain v T oc where gev: "okW (get_eta_var rbinder 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rbinder u);
          env' \<leftarrow> cunify_types alg T1 T2 env; liftM (update (v, T) (rlist_abs rbinder u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def okW_bindW)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where
    cu: "okW (cunify_types alg T1 T2 env) env1" and
    upd: "ok (update (v, T) (rlist_abs rbinder u) env1) env'"
    by (auto simp: okW_bindW)
  have "extends env env1" by (rule cunify_types_extends[OF cu])
  moreover have "extends env1 env'" by (rule ok_update_extends[OF upd])
  ultimately have ext: "extends env env'" by (rule extends_trans)
  have lk: "vt_lookup (tenv env') v = Some (T, rlist_abs rbinder u)"
    by (rule ok_update_lookup[OF upd])
  have e1: "env' \<Turnstile> Var v T \<approx> rlist_abs rbinder u" by (rule env_equiv_lookup[OF lk])
  have "tr (rlist_abs rbinder t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Var v T)" using get_eta_var_equiv[OF gev] by simp
  then have "env' \<Turnstile> rlist_abs rbinder t \<approx> Var v T" by (rule equiv_env_equiv)
  from env_equiv_trans[OF this e1] ext show ?thesis by blast
qed

end
