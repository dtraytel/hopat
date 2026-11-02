section \<open>Semantics of the Operations of \<open>unify.ML\<close>\<close>

theory Unify_Semantics
  imports
    "Pure_Pattern_Correctness.Pattern_Step_Soundness"
    "Pure_Unify.Pure_Unify"
begin

text \<open>
  We prove the operations of \<^file>\<open>~~/src/Pure/unify.ML\<close> sound with respect to the semantics
  of \<^theory>\<open>Pure_Pattern_Correctness.Pattern_Semantics\<close>: Pure terms are translated into the de
  Bruijn terms \<^typ>\<open>dB\<close> of session \<open>Nipkow_Grobauer_Pattern\<close>, and an environment denotes the
  closed substitutions \<open>\<sigma>\<close> that satisfy its bindings modulo \<open>\<beta>\<eta>\<close> (\<^const>\<open>sat\<close>). As for
  \<^const>\<open>Pure_Pattern.unify\<close>, we work with ground types (predicate \<^const>\<open>ground\<close>); problems
  with type variables are not instantiated here.

  Throughout, \<open>env \<Turnstile> s \<approx> t\<close> (\<^const>\<open>env_equiv\<close>) means that every closed \<open>\<sigma>\<close> satisfying
  \<open>env\<close> makes the translations of \<open>s\<close> and \<open>t\<close> \<open>\<beta>\<eta>\<close>-equal. A disagreement pair
  \<open>(rbinder, s, t)\<close> is \<^emph>\<open>solved\<close> by \<open>\<sigma>\<close> if \<open>\<sigma>\<close> makes the abstractions \<open>rlist_abs rbinder s\<close>
  and \<open>rlist_abs rbinder t\<close> \<open>\<beta>\<eta>\<close>-equal.
\<close>


subsection \<open>Successful computations in the writer monad\<close>

text \<open>
  A computation of type \<^typ>\<open>'a W\<close> \<^emph>\<open>succeeds\<close> with value \<open>x\<close> if it returns \<open>x\<close> after
  emitting some events. The emitted events are irrelevant to correctness (they only drive
  tracing), so we abstract over them.
\<close>

abbreviation okW :: "'a W \<Rightarrow> 'a \<Rightarrow> bool" where
  "okW m x \<equiv> (\<exists>evs. m = Some (evs, UOk x))"

lemma okW_returnW[simp]: "okW (returnW x) y \<longleftrightarrow> y = x"
  by (auto simp: returnW_def)

lemma okW_raiseW[simp]: "\<not> okW (raiseW e) y"
  by (auto simp: raiseW_def)

lemma okW_emit[simp]: "okW (emit e) y \<longleftrightarrow> y = ()"
  by (auto simp: emit_def)

lemma not_okW_None[simp]: "\<not> okW None y"
  by auto

lemma okW_bindW[simp]: "okW (bindW m f) y \<longleftrightarrow> (\<exists>x. okW m x \<and> okW (f x) y)"
  by (auto simp: bindW_def map_option_eq_Some split: option.splits ures.splits)

lemma okW_whenW: "okW (whenW b m) y \<longleftrightarrow> (if b then okW m y else y = ())"
  by (auto simp: whenW_def)

lemma okW_handleW:
  "okW (handleW m h) y \<longleftrightarrow> okW m y \<or> (\<exists>evs e. m = Some (evs, UErr e) \<and> okW (h e) y)"
  by (auto simp: handleW_def map_option_eq_Some split: option.splits ures.splits)

lemma okW_liftM[simp]: "okW (liftM m) y \<longleftrightarrow> ok m y"
  by (auto simp: liftM_def split: option.splits res.splits)

subsection \<open>Soundness of \<open>\<eta>\<close>-normalization\<close>

text \<open>
  \<^const>\<open>etif\<close> \<open>\<eta>\<close>-expands a proper term according to a type; the result is
  \<open>\<beta>\<eta>\<close>-equivalent to the input. We only need this for an empty type environment (as in
  \<^const>\<open>Pure_Pattern.unify\<close> on ground problems), so \<^const>\<open>etif\<close> never follows a type binding
  and terminates by recursion on the type.
\<close>

lemma vt_is_empty_lookup: "vt_is_empty t \<Longrightarrow> vt_lookup t k = None"
  by transfer simp

lemma devar_empty: "vt_is_empty tye \<Longrightarrow> devar tye T = return T"
  by (subst devar.simps) (auto simp: type_lookup_def vt_is_empty_lookup split: ptyp.splits)

lemma tr_incr_boundvars1: "proper t \<Longrightarrow> tr (incr_boundvars 1 t) = lift (tr t) 0"
  by (simp add: incr_boundvars_def tr_incr_bv liftn_lift[where n=0, simplified] integer_reps)

lemma eta_Abs_lift: "dB.Abs (lift s 0 \<degree> BVar 0) \<rightarrow>\<^sub>\<eta> s"
proof -
  have "\<not> free (lift s 0) 0" by simp
  from eta.eta[OF this] show ?thesis by simp
qed

lemma etif_equiv:
  assumes "vt_is_empty tye"
  shows "ok (etif tye T t) t' \<Longrightarrow> proper t \<Longrightarrow> tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t'"
proof (induction T arbitrary: t t')
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
    case True
    then obtain T1 U where Ts: "Ts = [T1, U]" by auto
    with True Type.prems(1) obtain u where u: "ok (etif tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u"
      by (subst (asm) etif.simps) (auto split: ptyp.splits list.splits if_splits)
    have pr: "proper (incr_boundvars 1 t $ Bound 0)"
      using Type.prems(2) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
    from Ts have "U \<in> set Ts" by simp
    note IH = Type.IH[OF this u pr]
    have e2: "tr (incr_boundvars 1 t $ Bound 0) = lift (tr t) 0 \<degree> BVar 0"
      using Type.prems(2) by (simp add: tr_incr_boundvars1)
    have equ: "tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (tr t) 0 \<degree> BVar 0" using conjunct1[OF IH] unfolding e2 .
    have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (lift (tr t) 0 \<degree> BVar 0)"
      unfolding t' tr.simps by (rule equiv_Abs[OF equ])
    also have "dB.Abs (lift (tr t) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t"
      by (rule eta_into_equiv[OF eta_Abs_lift])
    finally have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t" .
    moreover have "proper t'" using IH t' by simp
    ultimately show ?thesis by blast
  next
    case False
    with Type.prems have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits if_splits)
    with Type.prems(2) show ?thesis by simp
  qed
next
  case (TFree a S)
  from TFree.prems have "t' = t" by (subst (asm) etif.simps) auto
  with TFree.prems(2) show ?case by simp
next
  case (TVar v S)
  from assms have "type_lookup tye v S = return None"
    by (simp add: type_lookup_def vt_is_empty_lookup)
  with TVar.prems have "t' = t" by (subst (asm) etif.simps) simp
  with TVar.prems(2) show ?case by simp
qed

text \<open>\<^const>\<open>eta_norm\<close> only \<open>\<eta>\<close>-expands, so it preserves properness and gives a
  \<open>\<beta>\<eta>\<close>-equivalent term.\<close>

lemma eta_norm_nonAbs:
  "\<not> is_Abs t \<Longrightarrow> eta_norm env rbinder t = do {T \<leftarrow> fastype env rbinder t; etif (tyenv env) T t}"
  by (cases t) (simp_all add: fastype_def)

lemma eta_norm_nonAbs_equiv:
  assumes "vt_is_empty (tyenv env)" "\<not> is_Abs t" "ok (eta_norm env rbinder t) t'" "proper t"
  shows "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t'"
proof -
  from assms(3) obtain T where "ok (etif (tyenv env) T t) t'"
    using assms(2) by (auto simp: eta_norm_nonAbs)
  from etif_equiv[OF assms(1) this assms(4)] show ?thesis .
qed

lemma eta_norm_equiv:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (eta_norm env rbinder t) t' \<Longrightarrow> proper t \<Longrightarrow> tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t'"
proof (induction t arbitrary: rbinder t')
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rbinder) body) b'"
    and t': "t' = Abs a T b'" by auto
  from Abs.prems(2) have "proper body" by simp
  note ih = Abs.IH[OF b' this]
  have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Abs a T body)"
    unfolding t' tr.simps by (rule equiv_Abs[OF conjunct1[OF ih]])
  moreover have "proper t'" using ih t' by simp
  ultimately show ?case by blast
qed (rule eta_norm_nonAbs_equiv[OF assms]; simp)+

lemma env_equiv_eta_norm:
  assumes "vt_is_empty (tyenv env)" "ok (eta_norm env rbinder t) t'" "proper t"
  shows "env \<Turnstile> t \<approx> t'"
  using eta_norm_equiv[OF assms(1,2,3)]
  by (auto intro!: env_equivI mk_subst_equiv simp: equiv_sym)

end
