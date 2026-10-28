section \<open>Soundness of the Simplification Phase\<close>

theory Unify_Simpl
  imports Unify_Soundness
begin

text \<open>
  We prove that \<open>SIMPL0\<close> and \<open>SIMPL\<close> of \<^file>\<open>~~/src/Pure/unify.ML\<close> are sound: the
  state \<open>(env', ffs, frs)\<close> they return is a sound simplification of the disagreement pairs
  they are given. Concretely, every closed substitution that satisfies \<open>env'\<close> and solves all
  the residual flex-flex and flex-rigid pairs already solves the input pairs. As for the rest
  of the development, we work with ground types (predicate \<^const>\<open>ground\<close>), where
  \<^const>\<open>unify_types\<close> keeps the environment and only checks type equality.
\<close>


subsection \<open>Solved disagreement pairs\<close>

text \<open>
  A substitution \<^emph>\<open>solves\<close> a disagreement pair \<open>(rbinder, s, t)\<close> if it makes the two sides,
  closed by abstracting over the binder, \<open>\<beta>\<eta>\<close>-equal.
\<close>

definition dsolved :: "(nat \<Rightarrow> dB) \<Rightarrow> dpair \<Rightarrow> bool" where
  "dsolved \<sigma> dp \<longleftrightarrow> (case dp of (rb, s, t) \<Rightarrow>
     mk_subst \<sigma> (tr (rlist_abs rb s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t)))"

abbreviation dsolved_all :: "(nat \<Rightarrow> dB) \<Rightarrow> dpair list \<Rightarrow> bool" where
  "dsolved_all \<sigma> dps \<equiv> (\<forall>dp\<in>set dps. dsolved \<sigma> dp)"

lemma dsolvedI:
  "mk_subst \<sigma> (tr (rlist_abs rb s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t)) \<Longrightarrow> dsolved \<sigma> (rb, s, t)"
  by (simp add: dsolved_def)

lemma dsolvedD:
  "dsolved \<sigma> (rb, s, t) \<Longrightarrow> mk_subst \<sigma> (tr (rlist_abs rb s)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (rlist_abs rb t))"
  by (simp add: dsolved_def)

lemma dsolved_refl[simp]: "dsolved \<sigma> (rb, s, s)"
  by (simp add: dsolved_def)

lemma dsolved_sym: "dsolved \<sigma> (rb, s, t) \<Longrightarrow> dsolved \<sigma> (rb, t, s)"
  by (simp add: dsolved_def equiv_sym)

text \<open>Solving a pair is exactly what an environment equivalence of the abstracted sides gives.\<close>

lemma env_equiv_dsolved:
  "env \<Turnstile> rlist_abs rb s \<approx> rlist_abs rb t \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> env \<Longrightarrow> dsolved \<sigma> (rb, s, t)"
  by (simp add: dsolved_def env_equivD)


subsection \<open>Decomposition of rigid-rigid pairs\<close>

text \<open>
  \<^const>\<open>mk_subst\<close> is a homomorphism and commutes with the iterated abstraction
  \<^const>\<open>Abs_m\<close>; an abstraction reflects \<open>\<beta>\<eta>\<close>-equivalence (as in theory
  \<open>Match_Complete\<close>). These give the congruence we need for the rigid-rigid case of
  \<open>SIMPL0\<close>: if \<open>\<sigma>\<close> solves the two argument pairs it solves the application.
\<close>

lemma subst_lift_Suc_BVar: "(lift t (Suc k))[BVar k/k] = t"
  by (induction t arbitrary: k) auto

lemma equiv_Abs_reflect: "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  assume "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t"
  then have "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (dB.Abs t) 0 \<degree> BVar 0" by (simp add: fact6)
  moreover have "lift (dB.Abs t) 0 \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> t"
    using beta.beta[of "lift t (Suc 0)" "BVar 0"] by (simp add: subst_lift_Suc_BVar)
  then have "lift (dB.Abs t) 0 \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" by (intro beta_into_equiv r_into_rtranclp)
  ultimately show ?thesis by (rule equiv_trans)
qed

lemma mk_subst_Abs_m: "mk_subst \<sigma> (Abs_m n t) = Abs_m n (mk_subst \<sigma> t)"
  by (induction n) simp_all

lemma Abs_m_equiv_reflect: "Abs_m n s \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m n t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
  by (induction n) (auto dest: equiv_Abs_reflect)

lemma dsolved_App:
  assumes "dsolved \<sigma> (rb, f, g)" "dsolved \<sigma> (rb, t, u)"
  shows "dsolved \<sigma> (rb, f $ t, g $ u)"
proof -
  let ?n = "length rb"
  have f: "mk_subst \<sigma> (tr f) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr g)"
    using assms(1) by (auto simp: dsolved_def tr_rlist_abs mk_subst_Abs_m dest: Abs_m_equiv_reflect)
  have t: "mk_subst \<sigma> (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr u)"
    using assms(2) by (auto simp: dsolved_def tr_rlist_abs mk_subst_Abs_m dest: Abs_m_equiv_reflect)
  have "mk_subst \<sigma> (tr (f $ t)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst \<sigma> (tr (g $ u))"
    using f t by (simp add: equiv_App)
  then show ?thesis
    by (simp add: dsolved_def tr_rlist_abs mk_subst_Abs_m equiv_Abs_m)
qed


subsection \<open>Ground types\<close>

text \<open>
  With an empty type environment, the types computed by \<open>unify.ML\<close> from ground types are
  ground, and \<^const>\<open>cunify_types\<close> on ground types keeps the environment and succeeds iff the
  types are equal.
\<close>

lemma cunify_types_ground:
  assumes "ground ar T" "ground ar U" "okW (cunify_types alg T U env) env'"
  shows "env' = env \<and> T = U"
proof (cases "T = U")
  case True
  with assms show ?thesis by (simp add: cunify_types_def unify_types_ground return_def)
next
  case False
  with assms show ?thesis by (simp add: cunify_types_def unify_types_ground raise_def)
qed

lemma cunify_types_ground_eq:
  "cunify_types alg T U env = Some (evs, UOk env') \<Longrightarrow> ground ar T \<Longrightarrow> ground ar U \<Longrightarrow>
    env' = env \<and> T = U"
  using cunify_types_ground[of ar T U alg env env'] by blast

lemma body_type_ground:
  assumes "vt_is_empty (tyenv env)"
  shows "ground ar T \<Longrightarrow> ok (body_type env T) U \<Longrightarrow> ground ar U"
proof (induction T arbitrary: U)
  case (Type a Ts)
  note gr = Type.prems(1) and bt = Type.prems(2)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U'. Ts = [T1, U'])")
    case True
    then obtain T1 U' where Ts: "Ts = [T1, U']" and a: "a = STR ''fun''" by auto
    from bt Ts a have "ok (body_type env U') U" by (subst (asm) body_type.simps) simp
    moreover have "ground ar U'" using gr Ts by simp
    ultimately show ?thesis using Type.IH[of U'] Ts by simp
  next
    case False
    from bt False have "U = Type a Ts"
      by (subst (asm) body_type.simps) (auto split: list.splits if_splits)
    with gr show ?thesis by simp
  qed
next
  case (TFree a S)
  then show ?case by (subst (asm) body_type.simps) auto
qed simp

lemma binder_types_ground:
  assumes "vt_is_empty (tyenv env)"
  shows "ground ar T \<Longrightarrow> ok (binder_types env T) Us \<Longrightarrow> \<forall>U\<in>set Us. ground ar U"
proof (induction T arbitrary: Us)
  case (Type a Ts)
  note gr = Type.prems(1) and bt = Type.prems(2)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U'. Ts = [T1, U'])")
    case True
    then obtain T1 U' where Ts: "Ts = [T1, U']" and a: "a = STR ''fun''" by auto
    from bt Ts a obtain Us' where "ok (binder_types env U') Us'" "Us = T1 # Us'"
      by (subst (asm) binder_types.simps) auto
    moreover have "ground ar U'" "ground ar T1" using gr Ts by simp_all
    ultimately show ?thesis using Type.IH[of U'] Ts by simp
  next
    case False
    from bt False have "Us = []"
      by (subst (asm) binder_types.simps) (auto split: list.splits if_splits)
    then show ?thesis by simp
  qed
next
  case (TFree a S)
  then show ?case by (subst (asm) binder_types.simps) simp
qed simp

lemma not_ok_reraise: "\<not> ok (case e of Subscript \<Rightarrow> raise x | _ \<Rightarrow> raise e) y"
  by (cases e) simp_all

lemma env_fastype_ground:
  "vt_is_empty (tyenv env) \<Longrightarrow> \<forall>U\<in>set Ts. ground ar U \<Longrightarrow> typs_ok ar t \<Longrightarrow>
    ok (env_fastype env Ts t) T \<Longrightarrow> ground ar T"
proof (induction env Ts t arbitrary: T rule: env_fastype.induct)
  case (1 env' Ts f u)
  from "1.prems"(4) obtain T0 T' where f: "ok (env_fastype env' Ts f) T0"
    and dv: "ok (devar (tyenv env') T0) T'"
    and rest: "ok (case T' of
        Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
          else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by auto
  have "ground ar T0" using "1.IH"[OF "1.prems"(1,2) _ f] "1.prems"(3) by simp
  moreover from rest obtain A where "T' = Type STR ''fun'' [A, T]"
    by (auto split: ptyp.splits list.splits if_splits)
  moreover have "T' = T0" using dv by (simp add: devar_empty[OF "1.prems"(1)])
  ultimately show ?case by simp
next
  case (4 env' Ts i)
  then have "ok (nth Ts i) T" by (auto simp: ok_handle not_ok_reraise)
  with "4.prems"(2) show ?case by (auto simp: ok_nth dest!: nth_mem)
qed auto

lemma fastype_ground:
  assumes "vt_is_empty (tyenv env)" "binders_ok ar rb" "typs_ok ar t" "ok (fastype env rb t) T"
  shows "ground ar T"
proof -
  have "\<forall>U\<in>set (map snd rb). ground ar U" using assms(2) by (auto simp: binders_ok_def)
  from env_fastype_ground[OF assms(1) this assms(3)] assms(4) show ?thesis
    by (simp add: fastype_def)
qed


subsection \<open>Well-formed disagreement pairs\<close>

text \<open>
  A term of a disagreement pair with binder \<open>rb\<close> is well-formed if it is proper, has ground
  types and its loose bound variables refer to the binder. Then its abstraction over the binder
  is a closed term, as required for the bindings of a well-formed environment.
\<close>

definition wf_tm :: "(name \<Rightarrow> nat) \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "wf_tm ar rb t \<longleftrightarrow> proper t \<and> typs_ok ar t \<and> no_loose_bound (tr t) (length rb)"

definition wf_dp :: "(name \<Rightarrow> nat) \<Rightarrow> dpair \<Rightarrow> bool" where
  "wf_dp ar dp \<longleftrightarrow> (case dp of (rb, s, t) \<Rightarrow> binders_ok ar rb \<and> wf_tm ar rb s \<and> wf_tm ar rb t)"

lemma wf_dp_simp[simp]: "wf_dp ar (rb, s, t) \<longleftrightarrow> binders_ok ar rb \<and> wf_tm ar rb s \<and> wf_tm ar rb t"
  by (simp add: wf_dp_def)

lemma wf_dp_sym: "wf_dp ar (rb, s, t) \<Longrightarrow> wf_dp ar (rb, t, s)"
  by simp

lemma no_loose_bound_tr_rlist_abs:
  "no_loose_bound (tr (rlist_abs rb t)) k \<longleftrightarrow> no_loose_bound (tr t) (length rb + k)"
proof (induction rb arbitrary: t k)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T t"] show ?case by simp
qed simp

lemma typs_ok_rlist_abs:
  "binders_ok ar rb \<Longrightarrow> typs_ok ar (rlist_abs rb t) \<longleftrightarrow> typs_ok ar t"
proof (induction rb arbitrary: t)
  case (Cons aT rb)
  obtain a T where aT: "aT = (a, T)" by (cases aT)
  with Cons.prems have "binders_ok ar rb" "ground ar T" by (auto simp: binders_ok_def)
  with Cons.IH[of "Abs a T t"] aT show ?case by simp
qed simp

lemma proper_rlist_abs: "proper (rlist_abs rb t) \<longleftrightarrow> proper t"
proof (induction rb arbitrary: t)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[of "Abs a T t"] show ?case by simp
qed simp

text \<open>The abstraction of a well-formed term over its binder can be bound in an environment.\<close>

lemma wf_tm_binding:
  "binders_ok ar rb \<Longrightarrow> wf_tm ar rb u \<Longrightarrow>
    proper (rlist_abs rb u) \<and> typs_ok ar (rlist_abs rb u) \<and> no_loose_bound (tr (rlist_abs rb u)) 0"
  by (simp add: wf_tm_def proper_rlist_abs typs_ok_rlist_abs no_loose_bound_tr_rlist_abs)

text \<open>Environment equivalence is a congruence for abstraction over a binder.\<close>

lemma env_equiv_rlist_abs: "env \<Turnstile> s \<approx> t \<Longrightarrow> env \<Turnstile> rlist_abs rb s \<approx> rlist_abs rb t"
proof (induction rb arbitrary: s t)
  case (Cons aT rb)
  obtain a T where "aT = (a, T)" by (cases aT)
  with Cons.IH[OF env_equiv_Abs[OF Cons.prems]] show ?case by simp
qed simp


subsection \<open>Head normalization of disagreement pairs\<close>

text \<open>\<open>\<eta>\<close>-expansion keeps terms well-formed.\<close>

lemma etif_wf:
  assumes "vt_is_empty tye"
  shows "ok (etif tye T t) t' \<Longrightarrow> ground ar T \<Longrightarrow> proper t \<Longrightarrow> typs_ok ar t \<Longrightarrow>
    no_loose_bound (tr t) k \<Longrightarrow> typs_ok ar t' \<and> no_loose_bound (tr t') k"
proof (induction T arbitrary: t t' k)
  case (Type a Ts)
  show ?case
  proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
    case True
    then obtain T1 U where Ts: "Ts = [T1, U]" by auto
    with True Type.prems(1) obtain u where u: "ok (etif tye U (incr_boundvars 1 t $ Bound 0)) u"
      and t': "t' = Abs STR '''' T1 u"
      by (subst (asm) etif.simps) (auto split: ptyp.splits list.splits if_splits)
    have pr: "proper (incr_boundvars 1 t $ Bound 0)"
      using Type.prems(3) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
    have ty: "typs_ok ar (incr_boundvars 1 t $ Bound 0)"
      using Type.prems(4) by (simp add: incr_boundvars_def typs_ok_incr_bv)
    have nlb: "no_loose_bound (tr (incr_boundvars 1 t $ Bound 0)) (Suc k)"
      using Type.prems(3,5) by (simp add: tr_incr_boundvars1 no_loose_bound_lift)
    have gr: "ground ar T1" "ground ar U" using Type.prems(2) Ts by simp_all
    from Ts have "U \<in> set Ts" by simp
    from Type.IH[OF this u gr(2) pr ty nlb] t' gr(1) show ?thesis by simp
  next
    case False
    with Type.prems have "t' = t" by (subst (asm) etif.simps) (auto split: list.splits if_splits)
    with Type.prems show ?thesis by simp
  qed
next
  case (TFree a S)
  then show ?case by (subst (asm) etif.simps) auto
qed simp

lemma eta_norm_nonAbs_wf:
  assumes "vt_is_empty (tyenv env)" "\<not> is_Abs t" "ok (eta_norm env rb t) t'" "binders_ok ar rb"
    "proper t" "typs_ok ar t" "no_loose_bound (tr t) k"
  shows "typs_ok ar t' \<and> no_loose_bound (tr t') k"
proof -
  from assms(3) obtain T where T: "ok (fastype env rb t) T" and e: "ok (etif (tyenv env) T t) t'"
    using assms(2) by (auto simp: eta_norm_nonAbs)
  have "ground ar T" by (rule fastype_ground[OF assms(1,4,6) T])
  from etif_wf[OF assms(1) e this assms(5-7)] show ?thesis .
qed

lemma eta_norm_wf:
  assumes "vt_is_empty (tyenv env)"
  shows "ok (eta_norm env rb t) t' \<Longrightarrow> binders_ok ar rb \<Longrightarrow> proper t \<Longrightarrow> typs_ok ar t \<Longrightarrow>
    no_loose_bound (tr t) k \<Longrightarrow> typs_ok ar t' \<and> no_loose_bound (tr t') k"
proof (induction t arbitrary: rb t' k)
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rb) body) b'"
    and t': "t' = Abs a T b'" by auto
  have "binders_ok ar ((a, T) # rb)" using Abs.prems(2,4) by (simp add: binders_ok_def)
  from Abs.IH[OF b' this] Abs.prems(3-5) t' show ?case by simp
qed (erule eta_norm_nonAbs_wf[OF assms, rotated]; simp)+

text \<open>\<^const>\<open>new_dpair\<close> only moves common abstractions into the binder; the translations of the
  abstracted terms do not change, since they forget names and types of bound variables.\<close>

lemma new_dpair_sound:
  "okW (new_dpair alg rb t u env) ((rb', t', u'), env') \<Longrightarrow> wf_dp ar (rb, t, u) \<Longrightarrow>
    env' = env \<and> wf_dp ar (rb', t', u') \<and>
    tr (rlist_abs rb' t') = tr (rlist_abs rb t) \<and> tr (rlist_abs rb' u') = tr (rlist_abs rb u)"
proof (induction alg rb t u env rule: new_dpair.induct)
  case (1 alg rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg T U env) env1"
    and rec: "okW (new_dpair alg ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  have gT: "ground ar T" "ground ar U" using "1.prems"(2) by (simp_all add: wf_tm_def)
  from cunify_types_ground[OF gT cu] have e1: "env1 = env" and TU: "T = U" by simp_all
  have wf1: "wf_dp ar ((c, T) # rb, body1, body2)"
    using "1.prems"(2) TU by (auto simp: wf_tm_def binders_ok_def)
  from "1.IH"[OF cu c_def rec wf1] e1 TU show ?case by (simp add: tr_rlist_abs)
qed auto

lemma head_norm_wf_tm:
  assumes "ok (head_norm env t) t'" "wf_env ar env" "wf_tm ar rb t"
  shows "wf_tm ar rb t' \<and> env \<Turnstile> t \<approx> t'"
  using head_norm_sound[OF assms(1) refl assms(2)] assms(3) by (auto simp: wf_tm_def)

lemma eta_norm_wf_tm:
  assumes "ok (eta_norm env rb t) t'" "wf_env ar env" "binders_ok ar rb" "wf_tm ar rb t"
  shows "wf_tm ar rb t' \<and> env \<Turnstile> t \<approx> t'"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  from assms(4) have "proper t" "typs_ok ar t" "no_loose_bound (tr t) (length rb)"
    by (simp_all add: wf_tm_def)
  with eta_norm_wf[OF e assms(1) assms(3)] eta_norm_equiv[OF e assms(1)]
    env_equiv_eta_norm[OF e assms(1)]
  show ?thesis by (simp add: wf_tm_def)
qed

lemma head_norm_dpair_sound:
  assumes "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')"
    "wf_env ar env" "wf_dp ar (rb, t, u)"
  shows "env' = env" "wf_dp ar (rb', t', u')"
    "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'" "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
proof -
  from assms(1) obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env rb t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env rb u1) u2" and
    nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def)
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    using assms(3) by simp_all
  from head_norm_wf_tm[OF ht assms(2) wt] eta_norm_wf_tm[OF et assms(2) bok]
  have t2: "wf_tm ar rb t2" "env \<Turnstile> t \<approx> t2" by (auto intro: env_equiv_trans)
  from head_norm_wf_tm[OF hu assms(2) wu] eta_norm_wf_tm[OF eu assms(2) bok]
  have u2: "wf_tm ar rb u2" "env \<Turnstile> u \<approx> u2" by (auto intro: env_equiv_trans)
  have "wf_dp ar (rb, t2, u2)" using bok t2(1) u2(1) by simp
  note nds = new_dpair_sound[OF nd this]
  show "env' = env" "wf_dp ar (rb', t', u')" using nds by simp_all
  show "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'"
    using env_equiv_rlist_abs[OF t2(2)] env_equiv_tr_eq[of "rlist_abs rb t2" "rlist_abs rb' t'"] nds
    by (auto intro: env_equiv_trans)
  show "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
    using env_equiv_rlist_abs[OF u2(2)] env_equiv_tr_eq[of "rlist_abs rb u2" "rlist_abs rb' u'"] nds
    by (auto intro: env_equiv_trans)
qed


subsection \<open>Assignments keep environments well-formed\<close>

lemma get_eta_var_ground:
  "okW (get_eta_var rb n t) (v, T) \<Longrightarrow> typs_ok ar t \<Longrightarrow> ground ar T"
proof (induction rb arbitrary: n t)
  case Nil
  then show ?case by (cases t) auto
next
  case (Cons aT rb)
  from Cons.prems(1) obtain f where t: "t = f $ Bound n"
    and rec: "okW (get_eta_var rb (n + 1) f) (v, T)"
    by (cases "(aT # rb, n, t)" rule: get_eta_var.cases) (auto split: if_splits)
  with Cons.IH[OF rec] Cons.prems(2) show ?case by simp
qed

lemma assignment_wf:
  assumes "okW (assignment alg rb t u env) env'" "wf_env ar env" "wf_dp ar (rb, t, u)"
  shows "wf_env ar env'"
proof -
  have e: "vt_is_empty (tyenv env)" by (rule wf_envD(1)[OF assms(2)])
  have bok: "binders_ok ar rb" and wt: "wf_tm ar rb t" and wu: "wf_tm ar rb u"
    using assms(3) by simp_all
  from assms(1) obtain v T oc where gev: "okW (get_eta_var rb 0 t) (v, T)"
    and oc: "ok (rigid_occurs_term env v u) oc"
    and rest: "okW (case oc of
        NoOcc \<Rightarrow> do {T1 \<leftarrow> liftM (body_type env T); T2 \<leftarrow> liftM (fastype env rb u);
          env' \<leftarrow> cunify_types alg T1 T2 env; liftM (update (v, T) (rlist_abs rb u) env')}
      | Nonrigid \<Rightarrow> raiseW ASSIGN | Rigid \<Rightarrow> raiseW CANTUNIFY) env'"
    by (auto simp: assignment_def)
  from rest have "oc = NoOcc" by (cases oc) auto
  with rest obtain T1 T2 env1 where b: "ok (body_type env T) T1" and f: "ok (fastype env rb u) T2"
    and cu: "okW (cunify_types alg T1 T2 env) env1"
    and upd: "ok (update (v, T) (rlist_abs rb u) env1) env'"
    by auto
  have gT: "ground ar T" using get_eta_var_ground[OF gev] wt by (simp add: wf_tm_def)
  have "ground ar T1" by (rule body_type_ground[OF e gT b])
  moreover have "ground ar T2" using fastype_ground[OF e bok _ f] wu by (simp add: wf_tm_def)
  ultimately have "env1 = env" using cunify_types_ground cu by blast
  with ok_update_wf_env[OF upd] assms(2) gT wf_tm_binding[OF bok wu] show ?thesis by simp
qed


subsection \<open>Simplification states\<close>

text \<open>
  A state \<open>(env, ffs, frs)\<close> of \<open>SIMPL0\<close> is well-formed if its environment and its pairs are.
  A step from \<open>st\<close> to \<open>st'\<close> \<^emph>\<open>soundly simplifies\<close> the pairs \<open>dps\<close> if the environment only grows,
  and every closed substitution satisfying the new environment and solving the new pairs solves
  \<open>dps\<close> and the old pairs.
\<close>

fun st_pairs :: "sstate \<Rightarrow> dpair list" where
  "st_pairs (env, ffs, frs) = ffs @ frs"

definition wf_st :: "(name \<Rightarrow> nat) \<Rightarrow> sstate \<Rightarrow> bool" where
  "wf_st ar st \<longleftrightarrow> wf_env ar (fst st) \<and> (\<forall>dp\<in>set (st_pairs st). wf_dp ar dp)"

definition simp_rel :: "dpair list \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "simp_rel dps st st' \<longleftrightarrow> extends (fst st') (fst st) \<and>
    (\<forall>\<sigma>. closed_on UNIV \<sigma> \<longrightarrow> sat \<sigma> (fst st') \<longrightarrow> dsolved_all \<sigma> (st_pairs st') \<longrightarrow>
      dsolved_all \<sigma> (dps @ st_pairs st))"

lemma wf_st_simp[simp]:
  "wf_st ar (env, ffs, frs) \<longleftrightarrow> wf_env ar env \<and> (\<forall>dp\<in>set ffs. wf_dp ar dp) \<and> (\<forall>dp\<in>set frs. wf_dp ar dp)"
  by (auto simp: wf_st_def)

lemma simp_relI:
  assumes "extends (fst st') (fst st)"
    "\<And>\<sigma>. closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow>
      dsolved_all \<sigma> (dps @ st_pairs st)"
  shows "simp_rel dps st st'"
  using assms by (simp add: simp_rel_def)

lemma simp_relD:
  "simp_rel dps st st' \<Longrightarrow> extends (fst st') (fst st)"
  "simp_rel dps st st' \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> sat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow>
    dsolved_all \<sigma> (dps @ st_pairs st)"
  by (simp_all add: simp_rel_def)

lemma simp_rel_refl: "simp_rel [] st st"
  by (simp add: simp_rel_def)

lemma simp_rel_trans:
  assumes "simp_rel dps1 st1 st2" "simp_rel dps2 st2 st3"
  shows "simp_rel (dps1 @ dps2) st1 st3"
proof (rule simp_relI)
  show "extends (fst st3) (fst st1)" using simp_relD(1)[OF assms(2)] simp_relD(1)[OF assms(1)]
    by (rule extends_trans)
next
  fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (fst st3)" and s3: "dsolved_all \<sigma> (st_pairs st3)"
  have sat2: "sat \<sigma> (fst st2)" by (rule sat_extends[OF \<sigma>(2) simp_relD(1)[OF assms(2)]])
  from simp_relD(2)[OF assms(2) \<sigma> s3] have "dsolved_all \<sigma> dps2" "dsolved_all \<sigma> (st_pairs st2)"
    by auto
  with simp_relD(2)[OF assms(1) \<sigma>(1) sat2] show "dsolved_all \<sigma> ((dps1 @ dps2) @ st_pairs st1)"
    by auto
qed


subsection \<open>Simplifying the arguments of rigid-rigid pairs\<close>

text \<open>
  If each call of the parameter \<open>F\<close> (the recursive call of \<open>SIMPL0\<close>) soundly simplifies its
  pair, then \<^const>\<open>simrands\<close> soundly simplifies a pair of applications with equal heads: a
  substitution that solves the pairs of arguments solves the pair, by \<open>dsolved_App\<close>.
\<close>

lemma wf_tm_App: "wf_tm ar rb (f $ t) \<longleftrightarrow> wf_tm ar rb f \<and> wf_tm ar rb t"
  by (auto simp: wf_tm_def)

lemma simp_rel_triv: "simp_rel [(rb, t, t)] st st"
  by (simp add: simp_rel_def)

lemma simrands_sound:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow>
      wf_st ar st' \<and> simp_rel [dp] st st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar (rb, t, u) \<Longrightarrow>
    head_of t = head_of u \<Longrightarrow> wf_st ar st' \<and> simp_rel [(rb, t, u)] st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have w1: "wf_dp ar (rb, f1, g1)" and w2: "wf_dp ar (rb, t, u)"
    using "1.prems"(4) by (simp_all add: wf_tm_App)
  from "1.IH"[OF F r "1.prems"(3) w1] "1.prems"(5)
  have i1: "wf_st ar st1" "simp_rel [(rb, f1, g1)] st st1" by simp_all
  from F[OF s i1(1) w2] have i2: "wf_st ar st'" "simp_rel [(rb, t, u)] st1 st'" by simp_all
  have "simp_rel [(rb, f1 $ t, g1 $ u)] st st'"
  proof (rule simp_relI)
    show "extends (fst st') (fst st)"
      using simp_relD(1)[OF i2(2)] simp_relD(1)[OF i1(2)] by (rule extends_trans)
  next
    fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from simp_rel_trans[OF i1(2) i2(2)] \<sigma> s' have "dsolved_all \<sigma> ([(rb, f1, g1), (rb, t, u)] @ st_pairs st)"
      by (auto dest: simp_relD(2))
    then show "dsolved_all \<sigma> ([(rb, f1 $ t, g1 $ u)] @ st_pairs st)"
      by (auto intro: dsolved_App)
  qed
  with i2(1) show ?case by simp
qed (auto simp: simp_rel_triv)


subsection \<open>One step of \<open>SIMPL0\<close>\<close>

text \<open>
  \<open>SIMPL0\<close> head-normalizes its pair and then treats it according to the heads of its sides.
  We name the second part \<open>SIMPL0_step\<close>, with the recursive call abstracted as \<open>F\<close>.
\<close>

definition SIMPL0_step :: "algebra \<Rightarrow> (dpair \<Rightarrow> sstate \<Rightarrow> sstate W) \<Rightarrow> dpair \<Rightarrow> env \<Rightarrow>
    dpair list \<Rightarrow> dpair list \<Rightarrow> sstate W" where
  "SIMPL0_step alg F dp env ffs frs =
    (case dp of (rbinder, t, u) \<Rightarrow>
      (case (head_of t, head_of u) of
        (Var _ T, Var _ U) \<Rightarrow> do {
          T' \<leftarrow> liftM (body_type env T);
          U' \<leftarrow> liftM (body_type env U);
          env \<leftarrow> cunify_types alg T' U' env;
          returnW (env, dp # ffs, frs)}
      | (Var _ _, _) \<Rightarrow>
          handleW (do {env' \<leftarrow> assignment alg rbinder t u env; returnW (env', ffs, frs)})
            (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, dp # frs) | _ \<Rightarrow> raiseW e)
      | (_, Var _ _) \<Rightarrow>
          handleW (do {env' \<leftarrow> assignment alg rbinder u t env; returnW (env', ffs, frs)})
            (\<lambda>e. case e of
              ASSIGN \<Rightarrow> returnW (env, ffs, (rbinder, u, t) # frs)
            | _ \<Rightarrow> raiseW e)
      | (Const a T, Const b U) \<Rightarrow>
          if a = b then do {
            env' \<leftarrow> cunify_types alg T U env;
            simrands F rbinder u t u (env', ffs, frs)}
          else raiseW CANTUNIFY
      | (Bound i, Bound j) \<Rightarrow>
          if i = j then simrands F rbinder u t u (env, ffs, frs)
          else raiseW CANTUNIFY
      | (Free a T, Free b U) \<Rightarrow>
          if a = b then do {
            env' \<leftarrow> cunify_types alg T U env;
            simrands F rbinder u t u (env', ffs, frs)}
          else raiseW CANTUNIFY
      | _ \<Rightarrow> raiseW CANTUNIFY))"

lemma SIMPL0_unfold:
  "SIMPL0 alg dp0 st = (case st of (env, ffs, frs) \<Rightarrow> do {
      (dp, env) \<leftarrow> head_norm_dpair alg env dp0; SIMPL0_step alg (SIMPL0 alg) dp env ffs frs})"
  by (subst SIMPL0.simps) (simp only: SIMPL0_step_def)

lemma typs_ok_head_of: "typs_ok ar t \<Longrightarrow> typs_ok ar (head_of t)"
  by (induction t rule: head_of.induct) auto

lemma okW_ASSIGN_handler:
  "okW (case e of ASSIGN \<Rightarrow> returnW x | _ \<Rightarrow> raiseW e) y \<Longrightarrow> e = ASSIGN \<and> y = x"
  by (cases e) auto

text \<open>A flex-flex pair is kept.\<close>

lemma SIMPL0_flexflex_sound:
  assumes "okW (do {T' \<leftarrow> liftM (body_type env T); U' \<leftarrow> liftM (body_type env U);
      env' \<leftarrow> cunify_types alg T' U' env; returnW (env', dp # ffs, frs)}) st'"
    "ground ar T" "ground ar U" "wf_st ar (env, ffs, frs)" "wf_dp ar dp"
  shows "wf_st ar st' \<and> simp_rel [dp] (env, ffs, frs) st'"
proof -
  have e: "vt_is_empty (tyenv env)" using assms(4) by (auto dest: wf_envD(1))
  from assms(1) obtain T' U' env' where "ok (body_type env T) T'" "ok (body_type env U) U'"
    and cu: "okW (cunify_types alg T' U' env) env'" and st': "st' = (env', dp # ffs, frs)"
    by auto
  with body_type_ground[OF e] assms(2,3) have "ground ar T'" "ground ar U'" by blast+
  with cu have "env' = env" by (blast dest: cunify_types_ground)
  with st' assms(4,5) show ?thesis by (auto simp: simp_rel_def)
qed

text \<open>A flex-rigid pair is solved by assignment, or kept if the assignment is not possible.\<close>

lemma SIMPL0_assign_sound:
  assumes "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
    "wf_st ar (env, ffs, frs)" "wf_dp ar (rb, t, u)"
  shows "wf_st ar st' \<and> simp_rel [(rb, t, u)] (env, ffs, frs) st'"
proof -
  have "okW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)}) st' \<or>
    (\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e) st')"
    using assms(1) unfolding okW_handleW by blast
  then show ?thesis
  proof
    assume "okW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)}) st'"
    then obtain env' where a: "okW (assignment alg rb t u env) env'"
      and st': "st' = (env', ffs, frs)"
      by auto
    have wf': "wf_env ar env'" by (rule assignment_wf[OF a]) (use assms(2,3) in simp_all)
    note as = assignment_sound[OF a]
    have "simp_rel [(rb, t, u)] (env, ffs, frs) st'"
      using as by (auto simp: simp_rel_def st' intro: env_equiv_dsolved)
    with wf' st' assms(2) show ?thesis by simp
  next
    assume "\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e) st'"
    then obtain e where "okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs)
      | _ \<Rightarrow> raiseW e) st'" by blast
    from okW_ASSIGN_handler[OF this] have st': "st' = (env, ffs, (rb, t, u) # frs)" by simp
    with assms(2,3) show ?thesis by (auto simp: simp_rel_def)
  qed
qed

lemma SIMPL0_assign_sound':
  assumes "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
    "wf_st ar (env, ffs, frs)" "wf_dp ar (rb, t, u)"
  shows "wf_st ar st' \<and> simp_rel [(rb, t, u)] (env, ffs, frs) st'"
proof -
  from SIMPL0_assign_sound[OF assms(1,2) wf_dp_sym[OF assms(3)]]
  have "wf_st ar st'" "simp_rel [(rb, u, t)] (env, ffs, frs) st'" by simp_all
  then show ?thesis by (auto simp: simp_rel_def intro: dsolved_sym)
qed

text \<open>A rigid-rigid pair with equal heads is decomposed into the pairs of its arguments.\<close>

lemma SIMPL0_step_sound:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow>
      wf_st ar st' \<and> simp_rel [dp] st st'"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
    and wst: "wf_st ar (env, ffs, frs)" and wdp: "wf_dp ar (rb, t, u)"
  shows "wf_st ar st' \<and> simp_rel [(rb, t, u)] (env, ffs, frs) st'"
proof -
  have ht: "typs_ok ar (head_of t)" and hu: "typs_ok ar (head_of u)"
    using wdp by (simp_all add: wf_tm_def typs_ok_head_of)
  consider (VV) x T y U where "head_of t = Var x T" "head_of u = Var y U"
    | (VR) x T where "head_of t = Var x T" "\<not> is_Var (head_of u)"
    | (RV) y U where "\<not> is_Var (head_of t)" "head_of u = Var y U"
    | (RR) "\<not> is_Var (head_of t)" "\<not> is_Var (head_of u)"
    by (cases "head_of t"; cases "head_of u") auto
  then show ?thesis
  proof cases
    case VV
    with ok have "okW (do {T' \<leftarrow> liftM (body_type env T); U' \<leftarrow> liftM (body_type env U);
        env' \<leftarrow> cunify_types alg T' U' env; returnW (env', (rb, t, u) # ffs, frs)}) st'"
      by (simp add: SIMPL0_step_def)
    moreover have "ground ar T" "ground ar U" using VV ht hu by simp_all
    ultimately show ?thesis using SIMPL0_flexflex_sound wst wdp by blast
  next
    case VR
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    then show ?thesis using SIMPL0_assign_sound wst wdp by blast
  next
    case RV
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    then show ?thesis using SIMPL0_assign_sound' wst wdp by blast
  next
    case RR
    have "head_of t = head_of u \<and> okW (simrands F rb u t u (env, ffs, frs)) st'"
      using ok RR ht hu
      by (cases "head_of t"; cases "head_of u")
        (auto simp: SIMPL0_step_def split: if_splits dest: cunify_types_ground_eq)
    then show ?thesis using simrands_sound[OF F] wst wdp by blast
  qed
qed


subsection \<open>Soundness of \<open>SIMPL0\<close>\<close>

text \<open>A substitution solving the head-normalized pair solves the original one.\<close>

lemma dsolved_env_equiv:
  assumes "env \<Turnstile> rlist_abs rb0 t0 \<approx> rlist_abs rb t" "env \<Turnstile> rlist_abs rb0 u0 \<approx> rlist_abs rb u"
    "closed_on UNIV \<sigma>" "sat \<sigma> env" "dsolved \<sigma> (rb, t, u)"
  shows "dsolved \<sigma> (rb0, t0, u0)"
proof -
  note e = env_equivD[OF assms(1) assms(3,4)] env_equivD[OF assms(2) assms(3,4)]
  from e(1) dsolvedD[OF assms(5)] equiv_sym[OF e(2)] show ?thesis
    by (auto intro!: dsolvedI intro: equiv_trans)
qed

theorem SIMPL0_sound:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp0 \<Longrightarrow>
    wf_st ar st' \<and> simp_rel [dp0] st st'"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "wf_st ar st2 \<and> simp_rel [dp] st1 st2"
    if "okW (S alg dp st1) st2" "wf_st ar st1" "wf_dp ar dp" for dp st1 st2
  proof -
    from that(1) obtain evs where "S alg dp st1 = Some (evs, UOk st2)" by blast
    from "1.IH"[OF this _ that(2,3)] show ?thesis by simp
  qed
  obtain env ffs frs where st: "st = (env, ffs, frs)" by (cases st)
  obtain rb0 t0 u0 where dp0: "dp0 = (rb0, t0, u0)" by (cases dp0)
  have "(case st of (env, ffs, frs) \<Rightarrow> do {
      (dp, env) \<leftarrow> head_norm_dpair alg env dp0; SIMPL0_step alg (S alg) dp env ffs frs}) = Some r"
    using "1.hyps" by (simp only: SIMPL0_step_def)
  with "1.prems"(1) st
  have "okW (head_norm_dpair alg env dp0 \<bind>
      (\<lambda>(dp, env). SIMPL0_step alg (S alg) dp env ffs frs)) st'"
    by (cases r) auto
  then obtain dp env1 where hnd: "okW (head_norm_dpair alg env dp0) (dp, env1)"
    and step: "okW (SIMPL0_step alg (S alg) dp env1 ffs frs) st'"
    by (auto split: prod.splits)
  obtain rb t u where dp: "dp = (rb, t, u)" by (cases dp)
  have wenv: "wf_env ar env" using "1.prems"(2) st by simp
  note hs = head_norm_dpair_sound[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  from SIMPL0_step_sound[OF IH step[unfolded dp hs(1)]] "1.prems"(2) hs(2) st
  have ss: "wf_st ar st'" "simp_rel [(rb, t, u)] (env, ffs, frs) st'" by auto
  have "simp_rel [dp0] st st'"
  proof (rule simp_relI)
    show "extends (fst st') (fst st)" using simp_relD(1)[OF ss(2)] st by simp
  next
    fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from simp_relD(2)[OF ss(2) \<sigma> s'] have "dsolved \<sigma> (rb, t, u)" "dsolved_all \<sigma> (ffs @ frs)" by auto
    moreover have "sat \<sigma> env" using sat_extends[OF \<sigma>(2) simp_relD(1)[OF ss(2)]] by simp
    ultimately show "dsolved_all \<sigma> ([dp0] @ st_pairs st)"
      using dsolved_env_equiv[OF hs(3,4) \<sigma>(1)] dp0 st by auto
  qed
  with ss(1) show ?case by simp
qed

lemma okW_of: "m = Some r \<Longrightarrow> snd r = UOk x \<Longrightarrow> okW m x"
  by (cases r) auto

corollary SIMPL0_sound':
  "okW (SIMPL0 alg dp st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> wf_dp ar dp \<Longrightarrow>
    wf_st ar st' \<and> simp_rel [dp] st st'"
  using SIMPL0_sound by fastforce


subsection \<open>Soundness of \<open>SIMPL\<close>\<close>

lemma simp_rel_set: "set dps' \<subseteq> set dps \<Longrightarrow> simp_rel dps st st' \<Longrightarrow> simp_rel dps' st st'"
  by (auto simp: simp_rel_def)

lemma foldrW_SIMPL0_sound:
  "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> wf_st ar st \<Longrightarrow> \<forall>dp\<in>set dps. wf_dp ar dp \<Longrightarrow>
    wf_st ar st' \<and> simp_rel dps st st'"
proof (induction dps arbitrary: st')
  case Nil
  then show ?case by (simp add: simp_rel_refl)
next
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3)
  have i1: "wf_st ar st1" "simp_rel dps st st1" by simp_all
  from SIMPL0_sound'[OF s i1(1)] Cons.prems(3)
  have i2: "wf_st ar st'" "simp_rel [dp] st1 st'" by simp_all
  from simp_rel_trans[OF i1(2) i2(2)] have "simp_rel (dp # dps) st st'"
    by (rule simp_rel_set[rotated]) auto
  with i2(1) show ?case by simp
qed

lemma SIMPL_bodyE:
  assumes "okW (foldrW (SIMPL0 alg) dpairs (env, [], []) \<bind> (\<lambda>st. case st of (env', ffs, frs) \<Rightarrow>
      let dps = frs @ ffs in
      liftM (existsM (\<lambda>(_, t, u). changed env' t \<bind> (\<lambda>b. if b then return True else changed env' u))
        dps) \<bind> (\<lambda>b. if b then S env' dps else returnW st))) st'"
  obtains env1 ffs frs where "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
    "okW (S env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
proof -
  from assms obtain st1 where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) st1"
    and r: "okW (case st1 of (env', ffs, frs) \<Rightarrow>
      let dps = frs @ ffs in
      liftM (existsM (\<lambda>(_, t, u). changed env' t \<bind> (\<lambda>b. if b then return True else changed env' u))
        dps) \<bind> (\<lambda>b. if b then S env' dps else returnW st1)) st'"
    by auto
  obtain env1 ffs frs where st1: "st1 = (env1, ffs, frs)" by (cases st1)
  from r st1 have "okW (S env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (auto simp: Let_def split: if_splits)
  with f st1 that show thesis by blast
qed

text \<open>
  \<open>SIMPL\<close> repeats \<open>SIMPL0\<close> on the remaining pairs while variables get assigned. Every
  closed substitution that satisfies the resulting environment and solves the remaining
  flex-flex and flex-rigid pairs solves the original pairs.
\<close>

theorem SIMPL_sound:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> wf_env ar env \<Longrightarrow> \<forall>dp\<in>set dpairs. wf_dp ar dp \<Longrightarrow>
    wf_st ar st' \<and> simp_rel dpairs (env, [], []) st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have w0: "wf_st ar (env, [], [])" using "1.prems"(2) by simp
  note fs = foldrW_SIMPL0_sound[OF f w0 "1.prems"(3)]
  have i1: "wf_st ar (env1, ffs, frs)" "simp_rel dpairs (env, [], []) (env1, ffs, frs)"
    using fs by blast+
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where S_ok: "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    have w1: "wf_env ar env1" "\<forall>dp\<in>set (frs @ ffs). wf_dp ar dp" using i1(1) by auto
    note ih = "1.IH"[OF S_ok snd_conv w1(1) w1(2)]
    have i2: "wf_st ar st'" "simp_rel (frs @ ffs) (env1, [], []) st'" using ih by blast+
    have "simp_rel dpairs (env, [], []) st'"
    proof (rule simp_relI)
      show "extends (fst st') (fst (env, [], []))"
        using simp_relD(1)[OF i2(2)] simp_relD(1)[OF i1(2)] by (auto intro: extends_trans)
    next
      fix \<sigma> assume \<sigma>: "closed_on UNIV \<sigma>" "sat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
      from simp_relD(2)[OF i2(2) \<sigma> s'] have "dsolved_all \<sigma> (ffs @ frs)" by auto
      moreover have "sat \<sigma> env1" using sat_extends[OF \<sigma>(2) simp_relD(1)[OF i2(2)]] by simp
      ultimately show "dsolved_all \<sigma> (dpairs @ st_pairs (env, [], []))"
        using simp_relD(2)[OF i1(2) \<sigma>(1)] by simp
    qed
    with i2(1) show ?thesis by simp
  next
    case False
    with r have "st' = (env1, ffs, frs)" by blast
    with i1 show ?thesis by simp
  qed
qed

end
