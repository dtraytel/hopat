section \<open>Problems with Type Variables: Soundness of \<open>SIMPL\<close>\<close>

theory Unify_Poly_Simpl
  imports Unify_Poly_Types
begin

text \<open>
  The soundness proofs of theory \<^theory>\<open>Pure_Unify_Correctness.Unify_Simpl\<close> for problems
  whose types contain type variables. Terms are well-formed if they are proper, their types are
  well-formed (\<^const>\<open>wft\<close>), and their loose bound variables refer to the binder; types need not
  be ground, and the type environment need not be empty. Substitutions range over those that
  satisfy the environment and respect its type environment (\<^const>\<open>psat\<close>).
\<close>

subsection \<open>Well-formed terms\<close>

fun twft :: "(name \<Rightarrow> nat) \<Rightarrow> pterm \<Rightarrow> bool" where
  "twft ar (Const _ T) \<longleftrightarrow> wft ar T"
| "twft ar (Free _ T) \<longleftrightarrow> wft ar T"
| "twft ar (Var _ T) \<longleftrightarrow> wft ar T"
| "twft ar (Bound _) \<longleftrightarrow> True"
| "twft ar (Abs _ T t) \<longleftrightarrow> wft ar T \<and> twft ar t"
| "twft ar (s $ t) \<longleftrightarrow> twft ar s \<and> twft ar t"

definition sbinders :: "(name \<Rightarrow> nat) \<Rightarrow> binders \<Rightarrow> bool" where
  "sbinders ar rb \<longleftrightarrow> (\<forall>(a, T)\<in>set rb. wft ar T)"

definition swf_tm :: "(name \<Rightarrow> nat) \<Rightarrow> binders \<Rightarrow> pterm \<Rightarrow> bool" where
  "swf_tm ar rb t \<longleftrightarrow> proper t \<and> twft ar t \<and> no_loose_bound (tr t) (length rb)"

definition swf_dp :: "(name \<Rightarrow> nat) \<Rightarrow> dpair \<Rightarrow> bool" where
  "swf_dp ar dp \<longleftrightarrow> (case dp of (rb, s, t) \<Rightarrow> sbinders ar rb \<and> swf_tm ar rb s \<and> swf_tm ar rb t)"

definition swf_env :: "(name \<Rightarrow> nat) \<Rightarrow> env \<Rightarrow> bool" where
  "swf_env ar env \<longleftrightarrow> twf ar (tyenv env) \<and> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow>
     proper u \<and> twft ar u \<and> wft ar U \<and> no_loose_bound (tr u) 0)"

lemma swf_dp_simp[simp]: "swf_dp ar (rb, s, t) \<longleftrightarrow> sbinders ar rb \<and> swf_tm ar rb s \<and> swf_tm ar rb t"
  by (simp add: swf_dp_def)

lemma swf_dp_sym: "swf_dp ar (rb, s, t) \<Longrightarrow> swf_dp ar (rb, t, s)"
  by simp

lemma sbinders_simps[simp]: "sbinders ar []" "sbinders ar ((a, T) # rb) \<longleftrightarrow> wft ar T \<and> sbinders ar rb"
  "sbinders ar (rb @ rb') \<longleftrightarrow> sbinders ar rb \<and> sbinders ar rb'"
  by (auto simp: sbinders_def)

lemma swf_envD:
  "swf_env ar env \<Longrightarrow> twf ar (tyenv env)"
  "swf_env ar env \<Longrightarrow> vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow>
    proper u \<and> twft ar u \<and> wft ar U \<and> no_loose_bound (tr u) 0"
  unfolding swf_env_def by blast+

lemma twft_incr_bv: "twft ar (incr_bv inc lev t) \<longleftrightarrow> twft ar t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma twft_incr_boundvars: "twft ar (incr_boundvars inc t) \<longleftrightarrow> twft ar t"
  by (simp add: incr_boundvars_def twft_incr_bv)

lemma twft_subst_bound_aux: "twft ar t \<Longrightarrow> twft ar arg \<Longrightarrow> twft ar (subst_bound_aux arg lev t)"
  by (induction arg lev t rule: subst_bound_aux.induct) (auto simp: twft_incr_boundvars)

lemma twft_subst_bound: "twft ar t \<Longrightarrow> twft ar arg \<Longrightarrow> twft ar (subst_bound arg t)"
  by (simp add: subst_bound_def twft_subst_bound_aux)

lemma twft_list_comb: "twft ar (list_comb h ts) \<longleftrightarrow> twft ar h \<and> (\<forall>t\<in>set ts. twft ar t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma twft_head_of: "twft ar t \<Longrightarrow> twft ar (head_of t)"
  by (induction t rule: head_of.induct) auto

lemma twft_rlist_abs: "sbinders ar rb \<Longrightarrow> twft ar (rlist_abs rb t) \<longleftrightarrow> twft ar t"
  by (induction rb t rule: rlist_abs.induct) auto

lemma swf_tm_binding:
  "sbinders ar rb \<Longrightarrow> swf_tm ar rb u \<Longrightarrow>
    proper (rlist_abs rb u) \<and> twft ar (rlist_abs rb u) \<and> no_loose_bound (tr (rlist_abs rb u)) 0"
  by (simp add: swf_tm_def proper_rlist_abs twft_rlist_abs no_loose_bound_tr_rlist_abs)

lemma swf_tm_App: "swf_tm ar rb (f $ t) \<longleftrightarrow> swf_tm ar rb f \<and> swf_tm ar rb t"
  by (auto simp: swf_tm_def)


subsection \<open>Type computations\<close>

lemma body_type_wft:
  assumes "body_type env T = Some r"
  shows "r = Ok B \<Longrightarrow> twf ar (tyenv env) \<Longrightarrow> wft ar T \<Longrightarrow> wft ar B"
  using assms
proof (induction env T r arbitrary: B rule: body_type.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (Type a Ts)
    with "1.hyps" "1.prems" show ?thesis
      by (auto simp: return_def split: list.splits if_splits intro: "1.IH")
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) v S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return T | Some T' \<Rightarrow> bt env T') B"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest "1.prems" show ?thesis by (simp add: return_def)
    next
      fix U assume "r' = Some U" "vt_lookup (tyenv env) v = Some (S, U)"
      with rest "1.IH"[of env U "Ok B" B] "1.prems"(2) show ?thesis by (auto dest: twfD)
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma binder_types_wft:
  assumes "binder_types env T = Some r"
  shows "r = Ok Us \<Longrightarrow> twf ar (tyenv env) \<Longrightarrow> wft ar T \<Longrightarrow> \<forall>U\<in>set Us. wft ar U"
  using assms
proof (induction env T r arbitrary: Us rule: binder_types.raw_induct[rotated, consumes 1])
  case (1 bt env T r)
  show ?case
  proof (cases T)
    case (Type a Ts)
    show ?thesis
    proof (cases "a = STR ''fun'' \<and> (\<exists>T1 U. Ts = [T1, U])")
      case True
      then obtain T1 U where Ts: "Ts = [T1, U]" and a: "a = STR ''fun''" by auto
      from "1.hyps" "1.prems"(1) Type Ts a obtain Us' where r: "bt env U = Some (Ok Us')" and Us: "Us = T1 # Us'"
        by (auto simp: bind_def return_def split: option.splits res.splits)
      from "1.IH"[OF r refl "1.prems"(2)] "1.prems"(3) Type Ts Us show ?thesis by simp
    next
      case False
      with "1.hyps" "1.prems"(1) Type show ?thesis
        by (auto simp: return_def split: list.splits if_splits)
    qed
  next
    case (TVar v S)
    from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup (tyenv env) v S) r'"
      and rest: "ok (case r' of None \<Rightarrow> return [] | Some T' \<Rightarrow> bt env T') Us"
      by (auto simp: bind_def split: option.splits res.splits)
    from ok_type_lookup[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest show ?thesis by (simp add: return_def)
    next
      fix U assume "r' = Some U" "vt_lookup (tyenv env) v = Some (S, U)"
      with rest "1.IH"[of env U "Ok Us" Us] "1.prems"(2) show ?thesis by (auto dest: twfD)
    qed
  qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
qed

lemma strip_type_wft:
  "ok (strip_type env T) (Us, B) \<Longrightarrow> twf ar (tyenv env) \<Longrightarrow> wft ar T \<Longrightarrow>
    (\<forall>U\<in>set Us. wft ar U) \<and> wft ar B"
  by (auto simp: strip_type_def bind_def return_def split: option.splits res.splits
      dest: body_type_wft binder_types_wft)

lemma env_fastype_wft:
  "ok (env_fastype env Ts t) T \<Longrightarrow> twf ar (tyenv env) \<Longrightarrow> \<forall>U\<in>set Ts. wft ar U \<Longrightarrow> twft ar t \<Longrightarrow> wft ar T"
proof (induction env Ts t arbitrary: T rule: env_fastype.induct)
  case (1 env Ts f u)
  from "1.prems"(1) obtain T0 T' where f: "ok (env_fastype env Ts f) T0"
    and dv: "ok (devar (tyenv env) T0) T'"
    and rest: "ok (case T' of
      Type a Us \<Rightarrow> (case Us of [_, U] \<Rightarrow> if a = STR ''fun'' then return U
        else raise (Term_Error funerr [f $ u]) | _ \<Rightarrow> raise (Term_Error funerr [f $ u]))
      | _ \<Rightarrow> raise (Term_Error funerr [f $ u])) T"
    by (auto simp: bind_def split: option.splits res.splits)
  have "wft ar T0" using "1.IH"[OF f "1.prems"(2,3)] "1.prems"(4) by simp
  then have "wft ar T'" using ok_devar_sound(2)[OF dv "1.prems"(2)] by simp
  with rest show ?case by (auto simp: return_def raise_def split: ptyp.splits list.splits if_splits)
next
  case (4 env Ts i)
  then have "ok (nth Ts i) T" by (auto simp: ok_handle not_ok_reraise)
  with "4.prems"(3) show ?case by (auto simp: ok_nth dest!: nth_mem)
next
  case (6 env Ts uu T u)
  then show ?case by (auto simp: bind_def return_def tarity_def split: option.splits res.splits)
qed (simp_all add: return_def)

lemma fastype_wft:
  "ok (fastype env rb t) T \<Longrightarrow> twf ar (tyenv env) \<Longrightarrow> sbinders ar rb \<Longrightarrow> twft ar t \<Longrightarrow> wft ar T"
  unfolding fastype_def by (erule env_fastype_wft) (auto simp: sbinders_def)


subsection \<open>Head normalization\<close>

lemma ok_lookup_some: "ok (lookup env xi T) r \<Longrightarrow> r = None \<or> (\<exists>U u. r = Some u \<and> vt_lookup (tenv env) xi = Some (U, u))"
  by (auto simp: lookup_def bind_def return_def var_clash_def raise_def split: option.splits if_splits
      res.splits)

lemma env_equiv_lookup': "vt_lookup (tenv env) x = Some (U, u) \<Longrightarrow> env \<Turnstile> pterm.Var x T \<approx> u"
  by (auto simp: env_equiv_def dest: satD)

lemma head_norm_ssound:
  assumes "head_norm env t = Some r"
  shows "r = Ok t' \<Longrightarrow> swf_env ar env \<Longrightarrow> proper t \<Longrightarrow> twft ar t \<Longrightarrow>
    proper t' \<and> twft ar t' \<and> env \<Turnstile> t \<approx> t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction env t r arbitrary: t' rule: head_norm.raw_induct[rotated, consumes 1])
  case (1 hn env t r)
  have wf: "swf_env ar env" and t': "ok (case t of
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
    from ok_lookup_some[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume "r' = None"
      with rest "1.prems" show ?thesis by auto
    next
      fix U u assume r': "r' = Some u" and l: "vt_lookup (tenv env) xi = Some (U, u)"
      with swf_envD(2)[OF wf] have u: "proper u" "twft ar u" "no_loose_bound (tr u) 0" by auto
      from r' rest have "hn env u = Some (Ok t')" by simp
      from "1.IH"[OF this refl wf u(1,2)] env_equiv_lookup'[OF l, of T] Var u(3) show ?thesis
        by (auto intro: env_equiv_trans no_loose_bound_mono)
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
        by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
          intro: env_equiv_trans env_equiv_beta)
    next
      case False
      with t' App obtain nf where nf: "hn env f = Some (Ok nf)"
        and rest: "ok (case nf of pterm.Abs _ _ body \<Rightarrow> hn env (subst_bound u body)
          | _ \<Rightarrow> return (nf $ u)) t'"
        by (cases f) auto
      from "1.IH"[OF nf refl wf] "1.prems" App
      have nf': "proper nf" "twft ar nf" "env \<Turnstile> f \<approx> nf"
        "\<And>k. no_loose_bound (tr f) k \<Longrightarrow> no_loose_bound (tr nf) k"
        by auto
      then have fu: "env \<Turnstile> f $ u \<approx> nf $ u" by (auto intro: env_equiv_App)
      show ?thesis
      proof (cases "is_Abs nf")
        case True
        then obtain a T body where nfa: "nf = pterm.Abs a T body" by (cases nf) auto
        with rest have "hn env (subst_bound u body) = Some (Ok t')" by simp
        from "1.IH"[OF this refl wf] "1.prems" App nf' nfa fu show ?thesis
          by (auto simp: proper_subst_bound twft_subst_bound no_loose_bound_beta
            intro: env_equiv_trans[OF fu] env_equiv_trans[OF env_equiv_beta])
      next
        case False
        with rest have "t' = nf $ u" by (cases nf) auto
        with nf' fu "1.prems" App show ?thesis by auto
      qed
    qed
  qed (use t' "1.prems" in auto)
qed

lemma head_norm_swf_tm:
  assumes "ok (head_norm env t) t'" "swf_env ar env" "swf_tm ar rb t"
  shows "swf_tm ar rb t' \<and> env \<Turnstile> t \<approx> t'"
  using head_norm_ssound[OF assms(1) refl assms(2)] assms(3) by (auto simp: swf_tm_def)


subsection \<open>\<open>\<eta>\<close>-normalization\<close>

lemma etif_ssound:
  assumes "etif tye T t = Some r"
  shows "r = Ok t' \<Longrightarrow> proper t \<Longrightarrow> twf ar tye \<Longrightarrow> wft ar T \<Longrightarrow> twft ar t \<Longrightarrow>
    tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t' \<and> twft ar t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
  using assms
proof (induction tye T t r arbitrary: t' rule: etif.raw_induct[rotated, consumes 1])
  case (1 ef tye T t r)
  show ?case
  proof (cases "\<exists>T1 U. T = Type STR ''fun'' [T1, U]")
    case True
    then obtain T1 U where T: "T = Type STR ''fun'' [T1, U]" by auto
    from "1.hyps" "1.prems"(1) T obtain u where u: "ef tye U (incr_boundvars 1 t $ Bound 0) = Some (Ok u)"
      and t': "t' = Abs STR '''' T1 u"
      by (auto simp: bind_def return_def split: option.splits res.splits)
    have pr: "proper (incr_boundvars 1 t $ Bound 0)"
      using "1.prems"(2) by (simp add: incr_boundvars_def proper_incr_bv integer_reps)
    have tw: "twft ar (incr_boundvars 1 t $ Bound 0)" using "1.prems"(5) by (simp add: twft_incr_boundvars)
    have wU: "wft ar T1" "wft ar U" using "1.prems"(4) T by (simp_all add: tarity_def)
    note IH = "1.IH"[OF u refl pr "1.prems"(3) wU(2) tw]
    have e2: "tr (incr_boundvars 1 t $ Bound 0) = lift (tr t) 0 \<degree> BVar 0"
      using "1.prems"(2) by (simp add: tr_incr_boundvars1)
    have equ: "tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (tr t) 0 \<degree> BVar 0" using conjunct1[OF IH] unfolding e2 .
    have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs (lift (tr t) 0 \<degree> BVar 0)"
      unfolding t' tr.simps by (rule equiv_Abs[OF equ])
    also have "dB.Abs (lift (tr t) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t"
      by (rule eta_into_equiv[OF eta_Abs_lift])
    finally have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t" .
    moreover have "no_loose_bound (tr t') k" if "no_loose_bound (tr t) k" for k
    proof -
      have "no_loose_bound (tr (incr_boundvars 1 t $ Bound 0)) (Suc k)"
        using that "1.prems"(2) by (simp add: tr_incr_boundvars1 no_loose_bound_lift)
      with IH t' show ?thesis by simp
    qed
    moreover have "proper t' \<and> twft ar t'" using IH t' wU by simp
    ultimately show ?thesis by blast
  next
    case nf: False
    show ?thesis
    proof (cases T)
      case (TVar v S)
      from "1.hyps" "1.prems"(1) TVar obtain r' where lk: "ok (type_lookup tye v S) r'"
        and rest: "ok (case r' of None \<Rightarrow> return t | Some T' \<Rightarrow> ef tye T' t) t'"
        by (auto simp: bind_def split: option.splits res.splits)
      from ok_type_lookup[OF lk] show ?thesis
      proof (elim disjE exE conjE)
        assume "r' = None"
        with rest "1.prems" show ?thesis by (simp add: return_def)
      next
        fix U assume "r' = Some U" "vt_lookup tye v = Some (S, U)"
        with rest "1.IH"[of tye U t "Ok t'" t'] "1.prems" show ?thesis by (auto dest: twfD)
      qed
    next
      case (Type a Ts)
      with nf "1.hyps" "1.prems" have "t' = t"
        by (auto simp: return_def split: list.splits if_splits)
      with "1.prems" show ?thesis by simp
    qed (use "1.hyps" "1.prems" in \<open>simp_all add: return_def\<close>)
  qed
qed

lemma eta_norm_nonAbs_ssound:
  assumes "ok (eta_norm env rb t) t'" "\<not> is_Abs t" "swf_env ar env" "sbinders ar rb" "proper t" "twft ar t"
  shows "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t' \<and> twft ar t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
proof -
  from assms(1,2) obtain T where T: "ok (fastype env rb t) T" and e: "ok (etif (tyenv env) T t) t'"
    by (auto simp: eta_norm_nonAbs)
  have "wft ar T" by (rule fastype_wft[OF T swf_envD(1)[OF assms(3)] assms(4,6)])
  from etif_ssound[OF e refl assms(5) swf_envD(1)[OF assms(3)] this assms(6)] show ?thesis .
qed

lemma eta_norm_ssound:
  "ok (eta_norm env rb t) t' \<Longrightarrow> swf_env ar env \<Longrightarrow> sbinders ar rb \<Longrightarrow> proper t \<Longrightarrow> twft ar t \<Longrightarrow>
    tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t \<and> proper t' \<and> twft ar t' \<and>
    (\<forall>k. no_loose_bound (tr t) k \<longrightarrow> no_loose_bound (tr t') k)"
proof (induction t arbitrary: rb t')
  case (Abs a T body)
  from Abs.prems(1) obtain b' where b': "ok (eta_norm env ((a, T) # rb) body) b'"
    and t': "t' = Abs a T b'" by auto
  have "sbinders ar ((a, T) # rb)" "proper body" "twft ar body" using Abs.prems by simp_all
  note ih = Abs.IH[OF b' Abs.prems(2) this]
  have "tr t' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Abs a T body)"
    unfolding t' tr.simps by (rule equiv_Abs[OF conjunct1[OF ih]])
  moreover have "proper t' \<and> twft ar t' \<and>
      (\<forall>k. no_loose_bound (tr (Abs a T body)) k \<longrightarrow> no_loose_bound (tr t') k)"
    using ih t' Abs.prems by auto
  ultimately show ?case by blast
qed (rule eta_norm_nonAbs_ssound; simp)+

lemma eta_norm_swf_tm:
  assumes "ok (eta_norm env rb t) t'" "swf_env ar env" "sbinders ar rb" "swf_tm ar rb t"
  shows "swf_tm ar rb t' \<and> env \<Turnstile> t \<approx> t'"
  using eta_norm_ssound[OF assms(1-3)] assms(4)
  by (auto simp: swf_tm_def equiv_sym intro!: env_equivI mk_subst_equiv)

subsection \<open>Disagreement pairs\<close>

lemma new_dpair_ssound:
  "okW (new_dpair alg rb t u env) ((rb', t', u'), env') \<Longrightarrow> swf_env ar env \<Longrightarrow> swf_dp ar (rb, t, u) \<Longrightarrow>
    pextends env' env \<and> tenv env' = tenv env \<and> swf_env ar env' \<and> swf_dp ar (rb', t', u') \<and>
    tr (rlist_abs rb' t') = tr (rlist_abs rb t) \<and> tr (rlist_abs rb' u') = tr (rlist_abs rb u)"
proof (induction alg rb t u env rule: new_dpair.induct)
  case (1 alg rb a T body1 b U body2 env)
  define c where "c = (if a = STR '''' then b else a)"
  from "1.prems"(1) obtain env1 where cu: "okW (cunify_types alg T U env) env1"
    and rec: "okW (new_dpair alg ((c, T) # rb) body1 body2 env1) ((rb', t', u'), env')"
    by (auto simp: c_def Let_def)
  have wT: "wft ar T" "wft ar U" using "1.prems"(3) by (simp_all add: swf_tm_def)
  note cs = cunify_types_psound[OF cu swf_envD(1)[OF "1.prems"(2)] wT]
  have we1: "swf_env ar env1" using cs(1,3) "1.prems"(2) by (auto simp: swf_env_def)
  have wf1: "swf_dp ar ((c, T) # rb, body1, body2)" using "1.prems"(3) wT by (auto simp: swf_tm_def)
  from "1.IH"[OF cu c_def rec we1 wf1] cs show ?case by (auto simp: tr_rlist_abs intro: pextends_trans)
qed auto

lemma head_norm_dpair_ssound:
  assumes "okW (head_norm_dpair alg env (rb, t, u)) ((rb', t', u'), env')"
    "swf_env ar env" "swf_dp ar (rb, t, u)"
  shows "pextends env' env" "tenv env' = tenv env" "swf_env ar env'" "swf_dp ar (rb', t', u')"
    "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'" "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
proof -
  from assms(1) obtain t1 t2 u1 u2 where
    ht: "ok (head_norm env t) t1" and et: "ok (eta_norm env rb t1) t2" and
    hu: "ok (head_norm env u) u1" and eu: "ok (eta_norm env rb u1) u2" and
    nd: "okW (new_dpair alg rb t2 u2 env) ((rb', t', u'), env')"
    by (auto simp: head_norm_dpair_def)
  have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u"
    using assms(3) by simp_all
  from head_norm_swf_tm[OF ht assms(2) wt] eta_norm_swf_tm[OF et assms(2) bok]
  have t2: "swf_tm ar rb t2" "env \<Turnstile> t \<approx> t2" by (auto intro: env_equiv_trans)
  from head_norm_swf_tm[OF hu assms(2) wu] eta_norm_swf_tm[OF eu assms(2) bok]
  have u2: "swf_tm ar rb u2" "env \<Turnstile> u \<approx> u2" by (auto intro: env_equiv_trans)
  have "swf_dp ar (rb, t2, u2)" using bok t2(1) u2(1) by simp
  note nds = new_dpair_ssound[OF nd assms(2) this]
  show "pextends env' env" "tenv env' = tenv env" "swf_env ar env'" "swf_dp ar (rb', t', u')"
    using nds by simp_all
  show "env \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb' t'"
    using env_equiv_rlist_abs[OF t2(2)] env_equiv_tr_eq[of "rlist_abs rb t2" "rlist_abs rb' t'"] nds
    by (auto intro: env_equiv_trans)
  show "env \<Turnstile> rlist_abs rb u \<approx> rlist_abs rb' u'"
    using env_equiv_rlist_abs[OF u2(2)] env_equiv_tr_eq[of "rlist_abs rb u2" "rlist_abs rb' u'"] nds
    by (auto intro: env_equiv_trans)
qed


subsection \<open>Assignments\<close>

lemma get_eta_var_wft:
  "okW (get_eta_var rb n t) (v, T) \<Longrightarrow> twft ar t \<Longrightarrow> wft ar T"
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

lemma ok_update_swf_env:
  assumes "ok (update (F, T) t env) env'" "swf_env ar env"
    "proper t" "twft ar t" "wft ar T" "no_loose_bound (tr t) 0"
  shows "swf_env ar env'"
  using assms ok_update[OF assms(1)] by (auto simp: swf_env_def)

lemma assignment_ssound:
  assumes "okW (assignment alg rb t u env) env'" "swf_env ar env" "swf_dp ar (rb, t, u)"
  shows "pextends env' env \<and> swf_env ar env' \<and> env' \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb u"
proof -
  have bok: "sbinders ar rb" and wt: "swf_tm ar rb t" and wu: "swf_tm ar rb u"
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
  have tw: "twf ar (tyenv env)" by (rule swf_envD(1)[OF assms(2)])
  have wT: "wft ar T" using get_eta_var_wft[OF gev] wt by (simp add: swf_tm_def)
  have "wft ar T1" by (rule body_type_wft[OF b refl tw wT])
  moreover have "wft ar T2" using fastype_wft[OF f tw bok] wu by (simp add: swf_tm_def)
  ultimately have w12: "wft ar T1" "wft ar T2" by simp_all
  note cs = cunify_types_psound[OF cu tw w12]
  have we1: "swf_env ar env1" using cs(1,3) assms(2) by (auto simp: swf_env_def)
  have we': "swf_env ar env'"
    using ok_update_swf_env[OF upd we1 _ _ wT] swf_tm_binding[OF bok wu] by simp
  have "pextends env' env1"
    using ok_update[OF upd] by (simp add: pextends_def ok_update_extends[OF upd])
  from this cs(2) have "pextends env' env" by (rule pextends_trans)
  with we' assignment_sound[OF assms(1)] show ?thesis by simp
qed


subsection \<open>Simplification states\<close>

definition swf_st :: "(name \<Rightarrow> nat) \<Rightarrow> sstate \<Rightarrow> bool" where
  "swf_st ar st \<longleftrightarrow> swf_env ar (fst st) \<and> (\<forall>dp\<in>set (st_pairs st). swf_dp ar dp)"

definition psimp_rel :: "dpair list \<Rightarrow> sstate \<Rightarrow> sstate \<Rightarrow> bool" where
  "psimp_rel dps st st' \<longleftrightarrow> pextends (fst st') (fst st) \<and>
    (\<forall>\<sigma>. psat \<sigma> (fst st') \<longrightarrow> dsolved_all \<sigma> (st_pairs st') \<longrightarrow> dsolved_all \<sigma> (dps @ st_pairs st))"

lemma swf_st_simp[simp]:
  "swf_st ar (env, ffs, frs) \<longleftrightarrow> swf_env ar env \<and> (\<forall>dp\<in>set ffs. swf_dp ar dp) \<and> (\<forall>dp\<in>set frs. swf_dp ar dp)"
  by (auto simp: swf_st_def)

lemma psimp_relI:
  assumes "pextends (fst st') (fst st)"
    "\<And>\<sigma>. psat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow> dsolved_all \<sigma> (dps @ st_pairs st)"
  shows "psimp_rel dps st st'"
  using assms by (simp add: psimp_rel_def)

lemma psimp_relD:
  "psimp_rel dps st st' \<Longrightarrow> pextends (fst st') (fst st)"
  "psimp_rel dps st st' \<Longrightarrow> psat \<sigma> (fst st') \<Longrightarrow> dsolved_all \<sigma> (st_pairs st') \<Longrightarrow>
    dsolved_all \<sigma> (dps @ st_pairs st)"
  by (simp_all add: psimp_rel_def)

lemma psimp_rel_refl: "psimp_rel [] st st"
  by (simp add: psimp_rel_def)

lemma psimp_rel_trans:
  assumes "psimp_rel dps1 st1 st2" "psimp_rel dps2 st2 st3"
  shows "psimp_rel (dps1 @ dps2) st1 st3"
proof (rule psimp_relI)
  show "pextends (fst st3) (fst st1)" using psimp_relD(1)[OF assms(2)] psimp_relD(1)[OF assms(1)]
    by (rule pextends_trans)
next
  fix \<sigma> assume \<sigma>: "psat \<sigma> (fst st3)" and s3: "dsolved_all \<sigma> (st_pairs st3)"
  have sat2: "psat \<sigma> (fst st2)" by (rule psat_pextends[OF \<sigma> psimp_relD(1)[OF assms(2)]])
  from psimp_relD(2)[OF assms(2) \<sigma> s3] have "dsolved_all \<sigma> dps2" "dsolved_all \<sigma> (st_pairs st2)"
    by auto
  with psimp_relD(2)[OF assms(1) sat2] show "dsolved_all \<sigma> ((dps1 @ dps2) @ st_pairs st1)"
    by auto
qed

lemma psimp_rel_set: "set dps' \<subseteq> set dps \<Longrightarrow> psimp_rel dps st st' \<Longrightarrow> psimp_rel dps' st st'"
  by (auto simp: psimp_rel_def)

lemma penv_equiv_dsolved:
  "env \<Turnstile> rlist_abs rb s \<approx> rlist_abs rb t \<Longrightarrow> psat \<sigma> env \<Longrightarrow> dsolved \<sigma> (rb, s, t)"
  by (auto simp: psat_def intro: env_equiv_dsolved)


subsection \<open>Rigid-rigid pairs\<close>

text \<open>
  The heads of a rigid-rigid pair are equal in all solutions of the type environment after the
  unification of their types.
\<close>

definition heads_eq :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "heads_eq env h h' \<longleftrightarrow> (\<forall>\<sigma>. psat \<sigma> env \<longrightarrow> mk_subst \<sigma> (tr h) = mk_subst \<sigma> (tr h'))"

lemma heads_eq_pextends: "heads_eq env h h' \<Longrightarrow> pextends env' env \<Longrightarrow> heads_eq env' h h'"
  by (auto simp: heads_eq_def intro: psat_pextends)

lemma heads_eq_dsolved:
  assumes "heads_eq env t u" "psat \<sigma> env"
  shows "dsolved \<sigma> (rb, t, u)"
  using assms by (simp add: heads_eq_def dsolved_def tr_rlist_abs mk_subst_Abs_m)

lemma psimp_rel_triv: "heads_eq (fst st) t u \<Longrightarrow> psimp_rel [(rb, t, u)] st st"
  by (auto simp: psimp_rel_def intro: heads_eq_dsolved)

lemma psimrands_sound:
  "(\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow>
      swf_st ar st' \<and> psimp_rel [dp] st st') \<Longrightarrow>
    okW (simrands F rb u0 t u st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar (rb, t, u) \<Longrightarrow>
    heads_eq (fst st) (head_of t) (head_of u) \<Longrightarrow> swf_st ar st' \<and> psimp_rel [(rb, t, u)] st st'"
proof (induction F rb u0 t u st arbitrary: st' rule: simrands.induct)
  case (1 F rb u0 f1 t g1 u st)
  note F = "1.prems"(1)
  from "1.prems"(2) obtain st1 where r: "okW (simrands F rb u0 f1 g1 st) st1"
    and s: "okW (F (rb, t, u) st1) st'" by auto
  have w1: "swf_dp ar (rb, f1, g1)" and w2: "swf_dp ar (rb, t, u)"
    using "1.prems"(4) by (simp_all add: swf_tm_App)
  from "1.IH"[OF F r "1.prems"(3) w1] "1.prems"(5)
  have i1: "swf_st ar st1" "psimp_rel [(rb, f1, g1)] st st1" by simp_all
  from F[OF s i1(1) w2] have i2: "swf_st ar st'" "psimp_rel [(rb, t, u)] st1 st'" by simp_all
  have "psimp_rel [(rb, f1 $ t, g1 $ u)] st st'"
  proof (rule psimp_relI)
    show "pextends (fst st') (fst st)"
      using psimp_relD(1)[OF i2(2)] psimp_relD(1)[OF i1(2)] by (rule pextends_trans)
  next
    fix \<sigma> assume \<sigma>: "psat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from psimp_rel_trans[OF i1(2) i2(2)] \<sigma> s' have "dsolved_all \<sigma> ([(rb, f1, g1), (rb, t, u)] @ st_pairs st)"
      by (auto dest: psimp_relD(2))
    then show "dsolved_all \<sigma> ([(rb, f1 $ t, g1 $ u)] @ st_pairs st)"
      by (auto intro: dsolved_App)
  qed
  with i2(1) show ?case by simp
qed (auto intro: psimp_rel_triv)

text \<open>The type unifications of the heads of rigid-rigid pairs:\<close>

lemma heads_eq_cunify:
  assumes "okW (cunify_types alg T U env) env'" "twf ar (tyenv env)" "wft ar T" "wft ar U"
  shows "heads_eq env' (Const a T) (Const a U)" "heads_eq env' (Free a T) (Free a U)"
proof -
  have eq: "\<And>\<rho>. tsol (tyenv env') \<rho> \<Longrightarrow> tsubst \<rho> T = tsubst \<rho> U"
    by (rule cunify_types_psound(4)[OF assms])
  show "heads_eq env' (Const a T) (Const a U)" "heads_eq env' (Free a T) (Free a U)"
    unfolding heads_eq_def psat_def by (auto dest: trespD[OF _ eq])
qed


subsection \<open>Soundness of \<open>SIMPL0\<close>\<close>

lemma SIMPL0_flexflex_ssound:
  assumes "okW (do {T' \<leftarrow> liftM (body_type env T); U' \<leftarrow> liftM (body_type env U);
      env' \<leftarrow> cunify_types alg T' U' env; returnW (env', dp # ffs, frs)}) st'"
    "wft ar T" "wft ar U" "swf_st ar (env, ffs, frs)" "swf_dp ar dp"
  shows "swf_st ar st' \<and> psimp_rel [dp] (env, ffs, frs) st'"
proof -
  have tw: "twf ar (tyenv env)" using assms(4) by (auto dest: swf_envD(1))
  from assms(1) obtain T' U' env' where b1: "ok (body_type env T) T'" and b2: "ok (body_type env U) U'"
    and cu: "okW (cunify_types alg T' U' env) env'" and st': "st' = (env', dp # ffs, frs)"
    by auto
  have "wft ar T'" "wft ar U'" using body_type_wft[OF b1 refl tw assms(2)] body_type_wft[OF b2 refl tw assms(3)]
    by simp_all
  note cs = cunify_types_psound[OF cu tw this]
  have "swf_env ar env'" using cs(1,3) assms(4) by (auto simp: swf_env_def)
  with st' assms(4,5) cs(2) show ?thesis by (auto simp: psimp_rel_def)
qed

lemma SIMPL0_assign_ssound:
  assumes "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
    "swf_st ar (env, ffs, frs)" "swf_dp ar (rb, t, u)"
  shows "swf_st ar st' \<and> psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
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
    from assignment_ssound[OF a] assms(2,3)
    have as: "pextends env' env" "swf_env ar env'" "env' \<Turnstile> rlist_abs rb t \<approx> rlist_abs rb u" by auto
    have "psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
      using as by (auto simp: psimp_rel_def st' intro: penv_equiv_dsolved)
    with as(2) st' assms(2) show ?thesis by simp
  next
    assume "\<exists>e. okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e) st'"
    then obtain e where "okW (case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs)
      | _ \<Rightarrow> raiseW e) st'" by blast
    from okW_ASSIGN_handler[OF this] have st': "st' = (env, ffs, (rb, t, u) # frs)" by simp
    with assms(2,3) show ?thesis by (auto simp: psimp_rel_def)
  qed
qed

lemma SIMPL0_assign_ssound':
  assumes "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
    "swf_st ar (env, ffs, frs)" "swf_dp ar (rb, t, u)"
  shows "swf_st ar st' \<and> psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
proof -
  from SIMPL0_assign_ssound[OF assms(1,2) swf_dp_sym[OF assms(3)]]
  have "swf_st ar st'" "psimp_rel [(rb, u, t)] (env, ffs, frs) st'" by simp_all
  then show ?thesis by (auto simp: psimp_rel_def intro: dsolved_sym)
qed

lemma SIMPL0_step_ssound:
  assumes F: "\<And>dp st st'. okW (F dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow>
      swf_st ar st' \<and> psimp_rel [dp] st st'"
    and ok: "okW (SIMPL0_step alg F (rb, t, u) env ffs frs) st'"
    and wst: "swf_st ar (env, ffs, frs)" and wdp: "swf_dp ar (rb, t, u)"
  shows "swf_st ar st' \<and> psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
proof -
  have ht: "twft ar (head_of t)" and hu: "twft ar (head_of u)"
    using wdp by (simp_all add: swf_tm_def twft_head_of)
  have tw: "twf ar (tyenv env)" using wst by (auto dest: swf_envD(1))
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
    moreover have "wft ar T" "wft ar U" using VV ht hu by simp_all
    ultimately show ?thesis using SIMPL0_flexflex_ssound wst wdp by blast
  next
    case VR
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb t u env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, t, u) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of u") (simp_all add: SIMPL0_step_def)
    then show ?thesis using SIMPL0_assign_ssound wst wdp by blast
  next
    case RV
    with ok have "okW (handleW (do {env' \<leftarrow> assignment alg rb u t env; returnW (env', ffs, frs)})
      (\<lambda>e. case e of ASSIGN \<Rightarrow> returnW (env, ffs, (rb, u, t) # frs) | _ \<Rightarrow> raiseW e)) st'"
      by (cases "head_of t") (simp_all add: SIMPL0_step_def)
    then show ?thesis using SIMPL0_assign_ssound' wst wdp by blast
  next
    case RR
    have "\<exists>env'. pextends env' env \<and> twf ar (tyenv env') \<and> tenv env' = tenv env \<and>
        heads_eq env' (head_of t) (head_of u) \<and> okW (simrands F rb u t u (env', ffs, frs)) st'"
    proof (cases "head_of t"; cases "head_of u")
      fix a T b U assume h: "head_of t = Const a T" "head_of u = Const b U"
      with ok RR obtain env' where ab: "a = b" and cu: "okW (cunify_types alg T U env) env'"
        and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      have "wft ar T" "wft ar U" using h ht hu by simp_all
      from cunify_types_psound[OF cu tw this] heads_eq_cunify[OF cu tw this] h ab s show ?thesis by auto
    next
      fix a T b U assume h: "head_of t = Free a T" "head_of u = Free b U"
      with ok RR obtain env' where ab: "a = b" and cu: "okW (cunify_types alg T U env) env'"
        and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      have "wft ar T" "wft ar U" using h ht hu by simp_all
      from cunify_types_psound[OF cu tw this] heads_eq_cunify[OF cu tw this] h ab s show ?thesis by auto
    next
      fix i j assume h: "head_of t = Bound i" "head_of u = Bound j"
      with ok RR have "i = j" "okW (simrands F rb u t u (env, ffs, frs)) st'"
        by (auto simp: SIMPL0_step_def split: if_splits)
      with h tw show ?thesis by (intro exI[of _ env]) (simp add: heads_eq_def)
    qed (use ok RR in \<open>auto simp: SIMPL0_step_def\<close>)
    then obtain env' where e': "pextends env' env" "twf ar (tyenv env')" "tenv env' = tenv env"
      "heads_eq env' (head_of t) (head_of u)" and s: "okW (simrands F rb u t u (env', ffs, frs)) st'"
      by blast
    have w': "swf_st ar (env', ffs, frs)" using wst e'(2,3) by (auto simp: swf_env_def)
    from psimrands_sound[OF F s w' wdp] e'(4)
    have r: "swf_st ar st'" "psimp_rel [(rb, t, u)] (env', ffs, frs) st'" by simp_all
    have "psimp_rel [(rb, t, u)] (env, ffs, frs) st'"
    proof (rule psimp_relI)
      show "pextends (fst st') (fst (env, ffs, frs))"
        using pextends_trans[OF psimp_relD(1)[OF r(2), simplified] e'(1)] by simp
    next
      fix \<sigma> assume "psat \<sigma> (fst st')" "dsolved_all \<sigma> (st_pairs st')"
      from psimp_relD(2)[OF r(2) this] show "dsolved_all \<sigma> ([(rb, t, u)] @ st_pairs (env, ffs, frs))"
        by simp
    qed
    with r(1) show ?thesis by simp
  qed
qed

theorem SIMPL0_ssound:
  assumes "SIMPL0 alg dp0 st = Some r"
  shows "snd r = UOk st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp0 \<Longrightarrow>
    swf_st ar st' \<and> psimp_rel [dp0] st st'"
  using assms
proof (induction alg dp0 st r arbitrary: st' rule: SIMPL0.raw_induct[rotated, consumes 1])
  case (1 S alg dp0 st r)
  have IH: "swf_st ar st2 \<and> psimp_rel [dp] st1 st2"
    if "okW (S alg dp st1) st2" "swf_st ar st1" "swf_dp ar dp" for dp st1 st2
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
  have wenv: "swf_env ar env" using "1.prems"(2) st by simp
  note hs = head_norm_dpair_ssound[OF hnd[unfolded dp0 dp] wenv "1.prems"(3)[unfolded dp0]]
  have w1: "swf_st ar (env1, ffs, frs)" using "1.prems"(2) st hs(3) by simp
  from SIMPL0_step_ssound[OF IH step[unfolded dp] w1 hs(4)]
  have ss: "swf_st ar st'" "psimp_rel [(rb, t, u)] (env1, ffs, frs) st'" by blast+
  have ext: "pextends (fst st') env" using pextends_trans[OF psimp_relD(1)[OF ss(2), simplified] hs(1)] .
  have "psimp_rel [dp0] st st'"
  proof (rule psimp_relI)
    show "pextends (fst st') (fst st)" using ext st by (simp only: fst_conv)
  next
    fix \<sigma> assume \<sigma>: "psat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
    from psimp_relD(2)[OF ss(2) \<sigma> s'] have "dsolved \<sigma> (rb, t, u)" "dsolved_all \<sigma> (ffs @ frs)" by auto
    moreover have "psat \<sigma> env" by (rule psat_pextends[OF \<sigma> ext])
    ultimately show "dsolved_all \<sigma> ([dp0] @ st_pairs st)"
      using dsolved_env_equiv[OF hs(5,6)] psatD[of \<sigma> env] dp0 st by auto
  qed
  with ss(1) show ?case by simp
qed

corollary SIMPL0_ssound':
  "okW (SIMPL0 alg dp st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> swf_dp ar dp \<Longrightarrow>
    swf_st ar st' \<and> psimp_rel [dp] st st'"
  using SIMPL0_ssound by fastforce


subsection \<open>Soundness of \<open>SIMPL\<close>\<close>

lemma foldrW_SIMPL0_ssound:
  "okW (foldrW (SIMPL0 alg) dps st) st' \<Longrightarrow> swf_st ar st \<Longrightarrow> \<forall>dp\<in>set dps. swf_dp ar dp \<Longrightarrow>
    swf_st ar st' \<and> psimp_rel dps st st'"
proof (induction dps arbitrary: st')
  case Nil
  then show ?case by (simp add: psimp_rel_refl)
next
  case (Cons dp dps)
  from Cons.prems(1) obtain st1 where f: "okW (foldrW (SIMPL0 alg) dps st) st1"
    and s: "okW (SIMPL0 alg dp st1) st'" by auto
  from Cons.IH[OF f Cons.prems(2)] Cons.prems(3)
  have i1: "swf_st ar st1" "psimp_rel dps st st1" by simp_all
  from SIMPL0_ssound'[OF s i1(1)] Cons.prems(3)
  have i2: "swf_st ar st'" "psimp_rel [dp] st1 st'" by simp_all
  from psimp_rel_trans[OF i1(2) i2(2)] have "psimp_rel (dp # dps) st st'"
    by (rule psimp_rel_set[rotated]) auto
  with i2(1) show ?case by simp
qed

theorem SIMPL_ssound:
  assumes "SIMPL alg env dpairs = Some r"
  shows "snd r = UOk st' \<Longrightarrow> swf_env ar env \<Longrightarrow> \<forall>dp\<in>set dpairs. swf_dp ar dp \<Longrightarrow>
    swf_st ar st' \<and> psimp_rel dpairs (env, [], []) st'"
  using assms
proof (induction alg env dpairs r arbitrary: st' rule: SIMPL.raw_induct[rotated, consumes 1])
  case (1 S alg env dpairs r)
  note body = okW_of[OF "1.hyps" "1.prems"(1)]
  from body obtain env1 ffs frs
    where f: "okW (foldrW (SIMPL0 alg) dpairs (env, [], [])) (env1, ffs, frs)"
      and r: "okW (S alg env1 (frs @ ffs)) st' \<or> st' = (env1, ffs, frs)"
    by (rule SIMPL_bodyE)
  have w0: "swf_st ar (env, [], [])" using "1.prems"(2) by simp
  note fs = foldrW_SIMPL0_ssound[OF f w0 "1.prems"(3)]
  have i1: "swf_st ar (env1, ffs, frs)" "psimp_rel dpairs (env, [], []) (env1, ffs, frs)"
    using fs by blast+
  show ?case
  proof (cases "okW (S alg env1 (frs @ ffs)) st'")
    case True
    then obtain evs where S_ok: "S alg env1 (frs @ ffs) = Some (evs, UOk st')" by blast
    have w1: "swf_env ar env1" "\<forall>dp\<in>set (frs @ ffs). swf_dp ar dp" using i1(1) by auto
    note ih = "1.IH"[OF S_ok snd_conv w1(1) w1(2)]
    have i2: "swf_st ar st'" "psimp_rel (frs @ ffs) (env1, [], []) st'" using ih by blast+
    have "psimp_rel dpairs (env, [], []) st'"
    proof (rule psimp_relI)
      show "pextends (fst st') (fst (env, [], []))"
        using psimp_relD(1)[OF i2(2)] psimp_relD(1)[OF i1(2)] by (auto intro: pextends_trans)
    next
      fix \<sigma> assume \<sigma>: "psat \<sigma> (fst st')" and s': "dsolved_all \<sigma> (st_pairs st')"
      from psimp_relD(2)[OF i2(2) \<sigma> s'] have "dsolved_all \<sigma> (ffs @ frs)" by auto
      moreover have "psat \<sigma> env1" using psat_pextends[OF \<sigma> psimp_relD(1)[OF i2(2)]] by simp
      ultimately show "dsolved_all \<sigma> (dpairs @ st_pairs (env, [], []))"
        using psimp_relD(2)[OF i1(2)] by simp
    qed
    with i2(1) show ?thesis by simp
  next
    case False
    with r have "st' = (env1, ffs, frs)" by blast
    with i1 show ?thesis by simp
  qed
qed

end
