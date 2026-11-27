section \<open>Proof by assumption and flex-flex pairs on the abstract type of theorems\<close>

theory Thm_Assumption
  imports Thm_Subst_Rules
begin

text \<open>
  \<open>Thm.eq_assumption\<close> on theorems (\<^typ>\<open>'u pure_thm\<close>), in the style of
  \<^theory>\<open>Thm_Soundness.Thm_Rules\<close>; \<open>Thm.assumption\<close> and \<open>Thm.flexflex_rule\<close> as operations on
  theorems. The lazy result
  sequences of the latter two are evaluated to the lists of their results, which exist for every
  theorem; each result is a theorem, the instance of the proof state (or of the theorem) by a
  unifier of the model of \<open>Unify\<close>.
\<close>

subsection \<open>Proof by an equivalent assumption\<close>

context pure_sig_gen
begin

lemma wtp_list_implies_butlast:
  assumes w: "wtp (list_implies (Bs @ [Bi]) C)"
  shows "wtp (list_implies Bs C)" "wtp Bi"
proof -
  note t = wtpD(2)[OF w]
  note tD = typing_list_impliesD[OF t]
  have imp: "cert_typ alg ar imp_type" using typing_list_implies_imp[OF t] by simp
  show "wtp (list_implies Bs C)"
  proof (rule wtpI)
    show "closed (list_implies Bs C)" using wtpD(1)[OF w] by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> list_implies Bs C : propT" using tD imp by (intro typing_list_impliesI) auto
  qed
  show "wtp Bi"
  proof (rule wtpI)
    show "closed Bi" using wtpD(1)[OF w] by (simp add: closed_def loose_bvar_list_implies)
    show "(\<lambda>_. propT) \<turnstile> Bi : propT" using tD by simp
  qed
qed

end

context pure_sig_gen
begin

lemma eq_assumption_shape:
  assumes ok: "okT (eq_assumption i state) (n, th)" and d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
  shows "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = th_tpairs state, th_prop = list_implies Bs C\<rparr>"
proof -
  from eq_assumption_ok[OF ok] obtain tpairs' Bs' Bi' C' where d': "okT (dest_state state i) (tpairs', Bs', Bi', C')"
    and th: "th = \<lparr>th_maxidx = th_maxidx state, th_tpairs = tpairs', th_prop = list_implies Bs' C'\<rparr>" by blast
  from d d' have "tpairs' = tpairs" "Bs' = Bs" "C' = C" by auto
  with th okT_dest_state(1)[OF d] show ?thesis by simp
qed

end

lemma thm_sem_eq_assumption:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (eq_assumption i (rep_of th)) (n, r)" and d: "okT (dest_state (rep_of th) i) (tpairs, Bs, Bi, C)"
  shows "thm_sem TYPE('u) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (assumption_proof Bs Bi n p)))
    (bindM (zproof_of th) (eq_assumption_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi n)))"
    (is "thm_sem _ ?th")
proof -
  let ?c = "sign_of th"
  have P: "th_prop (rep_of th) = list_implies (Bs @ [Bi]) C"
    if w: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (th_prop (rep_of th))" and ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    show ?thesis using list_implies_strip_prems[OF okT_dest_state(2)[OF d] wtpD(2)[OF w, of "\<lambda>_. propT"]] by simp
  qed
  show ?thesis
  proof (rule thm_semI)
    assume "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))"
    then have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" by simp
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    note r = eq_assumption_shape[OF ok d]
    have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_wf[of th] ps by simp
    have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
    note P' = P[OF w ps]
    have "thm_wf (max (th_maxidx (rep_of th)) (th_maxidx (rep_of th))) (hyps_of th) (th_tpairs (rep_of th)) (list_implies Bs C)"
    proof (rule thm_wf_extend[OF w0, where V = "{}" and TV = "{}"])
      show "wtp (list_implies Bs C)" using wtp_list_implies_butlast(1) w P' by simp
      show "vars (list_implies Bs C) \<subseteq> vars (th_prop (rep_of th)) \<union> {}" using P' by (auto simp: vars_list_implies)
      show "ttvars (list_implies Bs C) \<subseteq> ttvars (th_prop (rep_of th)) \<union> {}" using P' by (auto simp: ttvars_list_implies_eq)
    qed simp_all
    then show "pure_sig.thm_wf (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th)) (sg_consts (th_sign ?th))
        (th_maxidx ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: r)
  next
    fix M :: "'u model"
    assume ps: "pure_sig (sg_alg (th_sign ?th)) (sg_ar (th_sign ?th))" and M: "is_model (th_sign ?th) M"
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD) (use M in simp)
    note r = eq_assumption_shape[OF ok d]
    have ps': "pure_sig (sg_alg ?c) (sg_ar ?c)" using ps by simp
    have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps' by (simp add: thm_wf_def wt_thm_def)
    have "valid (shyps_of th) (hyps_of th) (th_tpairs r) (th_prop r)"
      by (rule eq_assumption_valid[OF ok _ w]) (use pure_thm_valid_in[of th M] M in simp)
    then show "valid_in (th_sign ?th) M (th_shyps ?th) (th_hyps ?th) (th_tpairs ?th) (th_prop ?th)"
      by (simp add: valid_in_def)
  qed
qed

subsection \<open>Proof by assumption\<close>

text \<open>The results of the result sequence of \<^const>\<open>assumption\<close>, and its evaluation to a list.\<close>

inductive aresult :: "'u bops \<Rightarrow> 'u aseq \<Rightarrow> ares \<Rightarrow> bool" for ops where
  First: "okT (apull ops s) (Some (r, s')) \<Longrightarrow> aresult ops s r"
| Next: "okT (apull ops s) (Some (r', s')) \<Longrightarrow> aresult ops s' r \<Longrightarrow> aresult ops s r"

inductive aevals :: "'u bops \<Rightarrow> 'u aseq \<Rightarrow> ares list \<Rightarrow> bool" for ops where
  Nil: "okT (apull ops s) None \<Longrightarrow> aevals ops s []"
| Cons: "okT (apull ops s) (Some (r, s')) \<Longrightarrow> aevals ops s' rs \<Longrightarrow> aevals ops s (r # rs)"

lemma aevals_aresult: "aevals ops s xs \<Longrightarrow> r \<in> set xs \<Longrightarrow> aresult ops s r"
  by (induction rule: aevals.induct) (auto intro: aresult.First aresult.Next)

text \<open>The problem of an assumption of the subgoal:\<close>

definition aprob :: "actx \<Rightarrow> pterm \<Rightarrow> (pterm \<times> pterm) list" where
  "aprob ctx asm = (rlist_abs (ac_params ctx) asm, rlist_abs (ac_params ctx) (ac_concl ctx)) # ac_tpairs ctx"

context pure_sig_gen
begin

text \<open>The problems of the assumptions of a subgoal of a theorem are well-formed:\<close>

lemma assumption_sinv:
  assumes st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems k Bi = (params, asms, concl)"
    and asm: "asm \<in> set asms"
  shows "sinv (tvars_thm (th_tpairs state) (th_prop state)) (tvars_thm (th_tpairs state) (th_prop state))
    (vars_thm (th_tpairs state) (th_prop state)) (empty_env (th_maxidx state))
    (tdps ((rlist_abs params asm, rlist_abs params concl) # tpairs))"
proof -
  let ?A = "tvars_thm (th_tpairs state) (th_prop state)" and ?X = "vars_thm (th_tpairs state) (th_prop state)"
  let ?m = "th_maxidx state"
  have ws: "wt_thm ?m hs (th_tpairs state) (th_prop state)" using st by (simp add: thm_inv_def)
  note ds = okT_dest_state[OF d]
  have wS: "wtp (th_prop state)" using ws by (simp add: wt_thm_def)
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF ds(2) wtpD(2)[OF wS, of "\<lambda>_. propT"]] by simp
  have wBi: "wtp Bi" using wtp_list_implies[of "Bs @ [Bi]" "Bs @ [Bi]" C C] wS P by simp
  have vB: "vars Bi \<subseteq> ?X" "ttvars Bi \<subseteq> ?A"
    using ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C] P
    by (auto simp: vars_thm_def tvars_thm_def vars_list_implies)
  have tA: "tcert alg ?A"
  proof -
    have tc: "\<forall>p\<in>ttvars t. sort_ok alg (snd p)" if "\<exists>T. \<forall>e. e \<turnstile> t : T" for t
      using that tcert_ttvars unfolding tcert_def by blast
    have "sort_ok alg (snd p)" if p: "p \<in> ?A" for p
    proof -
      from p consider "p \<in> ttvars (th_prop state)" | t u where "(t, u) \<in> set (th_tpairs state)" "p \<in> ttvars t \<union> ttvars u"
        unfolding tvars_thm_def by blast
      then show ?thesis
      proof cases
        case 1
        with tc[of "th_prop state"] wS show ?thesis by (auto simp: wtp_def)
      next
        case 2
        then obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" using ws unfolding wt_thm_def by blast
        with 2(2) tc[of t] tc[of u] show ?thesis by blast
      qed
    qed
    then show ?thesis unfolding tcert_def by blast
  qed
  have ei: "einv ?A ?A (empty_env ?m)"
    by (rule einv_empty_env) (use st wt_thm_below[OF ws] tA in \<open>auto simp: thm_inv_def\<close>)
  show ?thesis
  proof (rule sinv_intro[OF ei])
    show "vt_is_empty (tenv (empty_env ?m))" by simp
    show "finite ?X" by simp
    show "below (maxidx (empty_env ?m)) ?X" using wt_thm_below(1)[OF ws] by (auto simp: below_def)
    show "vtvars ?X \<subseteq> tvars_env (tyenv (empty_env ?m)) \<union> ?A"
      by (auto simp: vtvars_def vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
    show "vcons \<rho> ?X" for \<rho> by (rule lvtcons_vcons) (use st in \<open>simp add: thm_inv_def\<close>)
    show "\<forall>(t, u)\<in>set ((rlist_abs params asm, rlist_abs params concl) # tpairs).
        vars t \<union> vars u \<subseteq> ?X \<and> ttvars t \<union> ttvars u \<subseteq> ?A \<and> closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set ((rlist_abs params asm, rlist_abs params concl) # tpairs)"
      then consider "t = rlist_abs params asm" "u = rlist_abs params concl" | "(t, u) \<in> set (th_tpairs state)"
        using ds(1) by auto
      then show "vars t \<union> vars u \<subseteq> ?X \<and> ttvars t \<union> ttvars u \<subseteq> ?A \<and> closed t \<and> closed u \<and>
          (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      proof cases
        case 1
        note c1 = eres_closure_typed[OF ap wBi, of asm] and c2 = eres_closure_typed[OF ap wBi, of concl]
        have "\<exists>T. \<forall>e. e \<turnstile> rlist_abs params asm : T \<and> e \<turnstile> rlist_abs params concl : T"
          using c1(2) c2(2) asm by blast
        then show ?thesis using c1 c2 asm vB 1 by auto
      next
        case 2
        then show ?thesis using ws vars_tvars_thm(3,4)[OF 2] by (auto simp: wt_thm_def)
      qed
    qed
  qed
qed

text \<open>The results of the result sequence: new theorems of unifiers of the problems of the assumptions.\<close>

definition achar :: "actx \<Rightarrow> pterm list \<Rightarrow> ares \<Rightarrow> bool" where
  "achar ctx asms r \<longleftrightarrow> (\<exists>l env tps. l < length asms \<and>
    ures (empty_env (ac_maxidx ctx)) (aprob ctx (asms ! l)) (El_R env tps) \<and>
    okT (newth ctx (integer_of_nat l + 1) (env, tps)) r)"

inductive ainv :: "cfg \<Rightarrow> actx \<Rightarrow> pterm list \<Rightarrow> seq aseq \<Rightarrow> bool" for cfg ctx asms where
  Try: "n = integer_of_nat k + 1 \<Longrightarrow> ainv cfg ctx asms (AQ_Try ctx (drop k asms) n)"
| Map: "k < length asms \<Longrightarrow> cfin cfg us (ures (empty_env (ac_maxidx ctx)) (aprob ctx (asms ! k))) \<Longrightarrow>
    n = integer_of_nat k + 1 \<Longrightarrow> m = n + 1 \<Longrightarrow> ainv cfg ctx asms (AQ_Map ctx n us (drop (Suc k) asms) m)"

lemma drop_Cons_nth:
  assumes "drop k xs = x # ys"
  shows "k < length xs" "xs ! k = x" "drop (Suc k) xs = ys"
proof -
  show k: "k < length xs" using assms by (metis drop_all list.distinct(1) not_le_imp_less)
  show "xs ! k = x" using assms k by (metis Cons_nth_drop_Suc list.inject)
  show "drop (Suc k) xs = ys" using assms k by (metis Cons_nth_drop_Suc list.inject)
qed

lemma integer_of_nat_Suc: "integer_of_nat (Suc k) = integer_of_nat k + 1"
  by (simp add: integer_of_nat_eq_of_nat)

lemma apull_ainv:
  assumes cfg: "cfg_alg cfg = alg" and pw: "\<forall>asm\<in>set asms. pwf (empty_env (ac_maxidx ctx)) (aprob ctx asm)"
  shows "apull ops s = Some r0 \<Longrightarrow> ops = unify_ops cfg vl \<Longrightarrow>
    snd r0 = Ok (Some (r, s')) \<Longrightarrow> ainv cfg ctx asms s \<Longrightarrow> achar ctx asms r \<and> ainv cfg ctx asms s'"
proof (induction ops s r0 arbitrary: r s' rule: apull.raw_induct[rotated, consumes 1])
  case (1 P ops s r0)
  note ops = "1.prems"(1)
  have IH: "achar ctx asms r1 \<and> ainv cfg ctx asms s1'" if "okT (P ops s1) (Some (r1, s1'))" "ainv cfg ctx asms s1"
    for s1 r1 s1'
  proof -
    from that(1) obtain evs where "P ops s1 = Some (evs, Ok (Some (r1, s1')))" by blast
    from "1.IH"[OF this ops _ that(2)] show ?thesis by simp
  qed
  note hyps = okT_of[OF "1.hyps" "1.prems"(2)]
  from "1.prems"(3) show ?case
  proof cases
    case (Try n k)
    show ?thesis
    proof (cases "drop k asms")
      case Nil
      with hyps Try show ?thesis by simp
    next
      case (Cons asm rest)
      note dk = drop_Cons_nth[OF Cons]
      have ai: "ainv cfg ctx asms (AQ_Try ctx rest (n + 1))"
        using ainv.Try[of "n + 1" "Suc k" cfg ctx asms] dk(3) Try(2) by (simp add: integer_of_nat_Suc)
      show ?thesis
      proof (cases "could_unify asm (ac_concl ctx)")
        case False
        with hyps Try Cons have "okT (P ops (AQ_Try ctx rest (n + 1))) (Some (r, s'))" by simp
        from IH[OF this ai] show ?thesis .
      next
        case True
        with hyps Try Cons obtain us where
          us: "okT (bo_unifiers ops (empty_env (ac_maxidx ctx)) (aprob ctx asm)) us"
          and p: "okT (P ops (AQ_Map ctx n us rest (n + 1))) (Some (r, s'))"
          by (auto simp: aprob_def)
        have "asm \<in> set asms" using dk by (metis nth_mem)
        with pw have "pwf (empty_env (ac_maxidx ctx)) (aprob ctx asm)" by blast
        from unifiers_ures[OF cfg this] us ops have "cfin cfg us (ures (empty_env (ac_maxidx ctx)) (aprob ctx (asms ! k)))"
          using dk(2) by simp
        from ainv.Map[OF dk(1) this Try(2) HOL.refl] dk(3) have "ainv cfg ctx asms (AQ_Map ctx n us rest (n + 1))"
          by simp
        from IH[OF p this] show ?thesis .
      qed
    qed
  next
    case (Map k us n m)
    from hyps Map obtain rr where rr: "okT (bo_pull ops us) rr"
      and cont: "okT (case rr of None \<Rightarrow> P ops (AQ_Try ctx (drop (Suc k) asms) m)
        | Some (et, us') \<Rightarrow> do {th \<leftarrow> newth ctx n et;
            returnW (Some (th, AQ_Map ctx n us' (drop (Suc k) asms) m))})
        (Some (r, s'))"
      by auto
    show ?thesis
    proof (cases rr)
      case None
      with cont have "okT (P ops (AQ_Try ctx (drop (Suc k) asms) m)) (Some (r, s'))" by simp
      moreover have "ainv cfg ctx asms (AQ_Try ctx (drop (Suc k) asms) m)"
        by (rule ainv.Try) (simp add: Map integer_of_nat_Suc)
      ultimately show ?thesis by (rule IH)
    next
      case (Some c)
      then obtain env' tps us' where c: "rr = Some ((env', tps), us')" by (cases c) auto
      have "okT (upull cfg us) (Some ((env', tps), us'))" using rr c ops by (simp add: unify_ops_def)
      note u = upull_fin[OF Map(3) this]
      from cont c have th: "okT (newth ctx n (env', tps)) r"
        and s': "s' = AQ_Map ctx n us' (drop (Suc k) asms) m"
        by auto
      have "achar ctx asms r" unfolding achar_def using Map(2,4) u th by blast
      moreover have "ainv cfg ctx asms s'" unfolding s' by (rule ainv.Map[OF Map(2) conjunct2[OF u] Map(4,5)])
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma aresult_achar:
  assumes "aresult (unify_ops cfg vl) s r" "ainv cfg ctx asms s"
    "cfg_alg cfg = alg" "\<forall>asm\<in>set asms. pwf (empty_env (ac_maxidx ctx)) (aprob ctx asm)"
  shows "achar ctx asms r"
  using assms(1,2)
proof (induction rule: aresult.induct)
  case (First s r s')
  then obtain r0 where "apull (unify_ops cfg vl) s = Some r0" "snd r0 = Ok (Some (r, s'))"
    by (cases "apull (unify_ops cfg vl) s") auto
  from apull_ainv[OF assms(3,4) this(1) HOL.refl this(2) First.prems] show ?case by simp
next
  case (Next s r' s' r)
  then obtain r0 where "apull (unify_ops cfg vl) s = Some r0" "snd r0 = Ok (Some (r', s'))"
    by (cases "apull (unify_ops cfg vl) s") auto
  from apull_ainv[OF assms(3,4) this(1) HOL.refl this(2) Next.prems] Next.IH show ?case by simp
qed

text \<open>The results of \<^const>\<open>assumption\<close> on a theorem:\<close>

lemma okT_assumption:
  assumes "okT (assumption i state) s0"
  obtains tpairs Bs Bi C params asms concl where
    "okT (dest_state state i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1"
proof -
  from assms obtain dd where d: "okT (dest_state state i) dd"
    and c: "okT (case dd of (tpairs, Bs, Bi, C) \<Rightarrow> (case assum_problems (-1) Bi of (params, asms, concl) \<Rightarrow>
      returnW (AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1))) s0"
    by (auto simp: assumption_def)
  obtain tpairs Bs Bi C where dd: "dd = (tpairs, Bs, Bi, C)" by (cases dd) auto
  obtain params asms concl where ap: "assum_problems (-1) Bi = (params, asms, concl)"
    by (cases "assum_problems (-1) Bi") auto
  from c dd ap have "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" by simp
  with d dd ap show thesis by (intro that) auto
qed

theorem assumption_result:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
  obtains tpairs Bs Bi C params asms concl l env tps where
    "okT (dest_state state i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "sinv (tvars_thm (th_tpairs state) (th_prop state)) (tvars_thm (th_tpairs state) (th_prop state))
      (vars_thm (th_tpairs state) (th_prop state)) (empty_env (th_maxidx state))
      (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
proof -
  from okT_assumption[OF a] obtain tpairs Bs Bi C params asms concl where d: "okT (dest_state state i) (tpairs, Bs, Bi, C)"
    and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and s0: "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" .
  let ?ctx = "ACtx (th_maxidx state) tpairs Bs Bi C params concl"
  note si = assumption_sinv[OF st d ap]
  have pw: "\<forall>asm\<in>set asms. pwf (empty_env (ac_maxidx ?ctx)) (aprob ?ctx asm)"
  proof
    fix asm assume "asm \<in> set asms"
    from si[OF this] have "sinv (tvars_thm (th_tpairs state) (th_prop state)) (tvars_thm (th_tpairs state) (th_prop state))
      (vars_thm (th_tpairs state) (th_prop state)) (empty_env (ac_maxidx ?ctx)) (tdps (aprob ?ctx asm))"
      by (simp add: aprob_def)
    then show "pwf (empty_env (ac_maxidx ?ctx)) (aprob ?ctx asm)"
      unfolding pwf_def
      by (intro exI[of _ "tvars_thm (th_tpairs state) (th_prop state)"] exI[of _ "vars_thm (th_tpairs state) (th_prop state)"]
          conjI finite_vars_thm finite_tvars_thm)
  qed
  have "ainv cfg ?ctx asms s0" using ainv.Try[of 1 0 cfg ?ctx asms] s0 by simp
  from aresult_achar[OF res this cfg pw] obtain l env tps where
    "l < length asms" "ures (empty_env (th_maxidx state)) (aprob ?ctx (asms ! l)) (El_R env tps)"
    "okT (newth ?ctx (integer_of_nat l + 1) (env, tps)) r"
    by (auto simp: achar_def)
  with d ap s0 si[of "asms ! l"] show thesis by (intro that) (auto simp: aprob_def)
qed


text \<open>The environments of the results: the invariants that the proofs of the results need.\<close>

definition env_inv :: "env \<Rightarrow> bool" where
  "env_inv env \<longleftrightarrow> closed_env env \<and> tacyc (tyenv env) \<and> tcons_env (tyenv env) \<and>
    (\<forall>(x, T)\<in>evars env. 0 \<le> snd x) \<and> (\<forall>p\<in>tvars_env (tyenv env). 0 \<le> snd (fst p)) \<and>
    (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p)))"

text \<open>Variables that are not in a problem and not above its maximal index do not occur in a solution (as \<open>unifiers_fresh\<close>):\<close>

lemma dstep_fresh:
  assumes ds: "dstep env (tdps tus) env' (tdps tps)" and ei': "einvw A' K' env'" and si: "sinv A K X env (tdps tus)"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
    and nl: "v \<notin> loose"
  shows "v \<notin> fst ` (evars env' \<union> dvars (tdps tps))"
proof
  assume vin: "v \<in> fst ` (evars env' \<union> dvars (tdps tps))"
  let ?\<rho> = "tnorm_inst (tyenv env')"
  note r0 = einvw_rho0[OF ei']
  have t: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF r0(1) dstepD(1)[OF ds]])
  from sinv_gtyped[OF si] t r0(2) have w: "wt_env ?\<rho> env" "dtyped ?\<rho> (tdps tus)" "vinv ?\<rho> env (dvars (tdps tus))"
    unfolding gtyped_def by blast+
  have vT: "vinv ?\<rho> env' ({(v, T)} \<union> dvars (tdps tps))" for T
  proof -
    have "vinv ?\<rho> env ({(v, T)} \<union> dvars (tdps tus))" by (rule ur_vinv_fresh[OF w(3)]) (use v in auto)
    from dstepDg(1)[OF ds r0(1) extends_refl w(1,2) this] show ?thesis by blast
  qed
  from vin obtain U where U: "(v, U) \<in> evars env' \<union> dvars (tdps tps)" by force
  have "vcons ?\<rho> ({(v, U \<rightarrow>\<^sub>T U)} \<union> dvars (tdps tps) \<union> evars env')"
    using vT[of "U \<rightarrow>\<^sub>T U"] by (simp add: vinv_def)
  from vconsD[OF this nl, of "U \<rightarrow>\<^sub>T U" U] U have "tsubst ?\<rho> (U \<rightarrow>\<^sub>T U) = tsubst ?\<rho> U" by blast
  with ur_fun_type_neq[of "tsubst ?\<rho> U"] show False by simp
qed

text \<open>Consistent variables stay consistent in a solution (as \<open>uresult_winv\<close>):\<close>

lemma dstep_winv_sub:
  assumes ds: "dstep env (tdps tus) env' (tdps tps)" and si: "sinv A K X env (tdps tus)"
    and wy: "winv env (Y \<union> dvars (tdps tus))"
  shows "winv env' Y"
proof -
  have "winv env' (Y \<union> dvars (tdps tps))"
    unfolding winv_def
  proof (intro allI impI)
    fix \<rho> assume t': "tsol (tyenv env') \<rho>" and c: "cert_inst \<rho>"
    have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
    from winvD[OF wy t c] have w: "wt_env \<rho> env" "vinv \<rho> env (Y \<union> dvars (tdps tus))" by blast+
    from dstepDg(1)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t c] w(2)]
    show "wt_env \<rho> env' \<and> vinv \<rho> env' (Y \<union> dvars (tdps tps))" by blast
  qed
  then show ?thesis by (rule ur_winv_sub) blast
qed

text \<open>
  A theorem instantiated by a solution of a problem on its terms, with the flex-flex pairs of the
  solution, normalized or (with an empty environment) unchanged, is a theorem:
\<close>

theorem unif_thm_inv:
  assumes st: "thm_inv m hs tps0 P0"
    and si: "sinv (tvars_thm tps0 P0) K0 (vars_thm tps0 P0) (empty_env m) (tdps tus)"
    and ds: "dstep (empty_env m) (tdps tus) env' (tdps tps)"
    and ei': "einvw A' K' env'" and wi': "winv env' X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env' [] X' t u"
    and AA: "tvars_thm tps0 P0 \<subseteq> A'"
    and tA: "tvars_env (tyenv env') \<union> A' \<subseteq> tvars_thm tps0 P0 \<union> {p. m < snd (fst p)}"
    and ZP: "wtp P" "vars P \<subseteq> vars_thm tps0 P0" "ttvars P \<subseteq> tvars_thm tps0 P0"
    and qs: "\<forall>(t, u)\<in>set qs. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and>
      vars t \<union> vars u \<subseteq> vars_thm tps0 P0 \<and> ttvars t \<union> ttvars u \<subseteq> tvars_thm tps0 P0"
    and new: "env_is_empty env' \<and> ntps = tps \<and> P' = P \<or>
      (\<exists>ntps0. list_all2 (\<lambda>tu tu'. ok (norm_term env' (fst tu)) (fst tu') \<and> ok (norm_term env' (snd tu)) (snd tu'))
        (tps @ qs) ntps0 \<and> set ntps \<subseteq> set ntps0) \<and> ok (norm_term env' P) P'"
    and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "thm_inv (maxidx env') hs ntps P' \<and> env_inv env'"
proof -
  let ?A = "tvars_thm tps0 P0" and ?X = "vars_thm tps0 P0" and ?env = "empty_env m"
  have ws: "wt_thm m hs tps0 P0" and sm: "-1 \<le> m"
    and nnX: "\<forall>v\<in>?X. 0 \<le> snd (fst v)" and nnA0: "\<forall>v\<in>?A. 0 \<le> snd (fst v)"
    using st by (simp_all add: thm_inv_def)
  have ev: "evars ?env = {}" by (simp add: evars_def bnds_def vt_is_empty_lookup)
  have dX: "dvars (tdps tus) \<subseteq> ?X" using sinv_dvars[OF si] ev by simp
  have wX: "winv ?env ?X" using si by (simp add: sinv_def)
  have wZ: "winv ?env (?X \<union> dvars (tdps tus))" using wX dX by (simp add: sup_absorb1)
  have wY': "winv env' ?X" by (rule dstep_winv_sub[OF ds si wZ])
  have ext: "extends ?env env'" by (rule dstepD(1)[OF ds])
  have mx': "m \<le> maxidx env'" using ext by (simp add: extends_def)
  let ?\<theta> = "tyenv env'" and ?\<rho> = "tnorm_inst (tyenv env')"
  note e' = einvwD[OF ei'] and r0 = einvw_rho0[OF ei']
  have ac': "tacyc ?\<theta>" by (rule e'(6))
  have t0: "tsol (tyenv ?env) ?\<rho>" by (rule extends_tsol[OF r0(1) ext])
  from winvD[OF wZ t0 r0(2)] have w0: "wt_env ?\<rho> ?env" and v0: "vinv ?\<rho> ?env (?X \<union> dvars (tdps tus))"
    by blast+
  have "vinv ?\<rho> env' (?X \<union> dvars (tdps tps))"
    using dstepDg(1)[OF ds r0(1) extends_refl w0 sinv_dtyped[OF si t0 r0(2)] v0] by blast
  define S0 where "S0 = ?X \<union> dvars (tdps tps) \<union> evars env'"
  have vS: "vcons ?\<rho> S0" "below (maxidx env') S0"
    using \<open>vinv ?\<rho> env' (?X \<union> dvars (tdps tps))\<close> by (simp_all add: vinv_def S0_def Un_assoc)
  have vtS: "lvtcons (vimg ?\<theta> S0)" by (rule lvtcons_vimg[OF vS(1)])
  have nnS0: "0 \<le> snd x" if xS: "(x, T) \<in> S0" for x T
  proof -
    consider "(x, T) \<in> ?X" | "(x, T) \<in> dvars (tdps tps) \<union> evars env'"
      using xS unfolding S0_def by blast
    then show ?thesis
    proof cases
      case 1
      with nnX show ?thesis by force
    next
      case 2
      show ?thesis
      proof (cases "x \<in> loose")
        case True
        with l0 show ?thesis by blast
      next
        case nl: False
        show ?thesis
        proof (cases "snd x \<le> m")
          case True
          have "x \<in> fst ` (evars ?env \<union> dvars (tdps tus))"
          proof (rule ccontr)
            assume "x \<notin> fst ` (evars ?env \<union> dvars (tdps tus))"
            from dstep_fresh[OF ds ei' si this _ nl] True 2 show False by force
          qed
          then obtain U where "(x, U) \<in> dvars (tdps tus)" using ev by auto
          with dX have "(x, U) \<in> ?X" by blast
          with nnX show ?thesis by force
        next
          case False
          from above_m1[OF sm, of m m] False show ?thesis by simp
        qed
      qed
    qed
  qed
  have nnA: "\<forall>p\<in>tvars_env ?\<theta> \<union> A'. 0 \<le> snd (fst p)"
  proof
    fix p assume "p \<in> tvars_env ?\<theta> \<union> A'"
    with tA consider "p \<in> ?A" | "m < snd (fst p)" by blast
    then show "0 \<le> snd (fst p)"
    proof cases
      case 1
      with nnA0 show ?thesis by blast
    next
      case 2
      then have "\<not> snd (fst p) \<le> m" by simp
      from above_m1[OF sm, of m m] this show ?thesis by simp
    qed
  qed
  have ti: "tinv ar (maxidx env') ?\<theta> A'" by (rule e'(2))
  have scA: "scons (tvars_env ?\<theta> \<union> A')" and bA: "\<forall>p\<in>tvars_env ?\<theta> \<union> A'. snd (fst p) \<le> maxidx env'"
    using ti by (simp_all add: tinv_def)
  let ?good = "\<lambda>Z. vars Z \<subseteq> vimg ?\<theta> S0 \<and> ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'"
  have gib: "ibelow (maxidx env') Z" if "?good Z" for Z
  proof (rule ibelowI)
    show "\<forall>v\<in>vars Z. snd (fst v) \<le> maxidx env'"
    proof
      fix v assume "v \<in> vars Z"
      with that have "fst v \<in> fst ` S0" by (metis fst_vimg image_eqI subsetD)
      with vS(2) show "snd (fst v) \<le> maxidx env'" by (auto simp: below_def)
    qed
    show "\<forall>p\<in>ttvars Z. snd (fst p) \<le> maxidx env'" using that bA by blast
  qed
  have c': "cert_inst (tsol0 ?\<theta>)" "tsol ?\<theta> (tsol0 ?\<theta>)"
    by (rule canonical_tsol0[OF ei' wi'])+
  have SV: "?X \<subseteq> S0" "evars env' \<subseteq> S0" "dvars (tdps tps) \<subseteq> S0" by (auto simp: S0_def)
  text \<open>The proposition:\<close>
  have gN: "wtp P' \<and> ?good P'" if nP: "ok (norm_term env' P) P'"
  proof -
    have ty: "(\<lambda>_. propT) \<turnstile> inst (tsol0 ?\<theta>) P : propT"
      using typing_inst[OF wtpD(2)[OF ZP(1), of "\<lambda>_. propT"] cert_inst_inst_ok[OF c'(1)]] by simp
    have "ttvars P \<subseteq> tvars_env ?\<theta> \<union> A'" using ZP(3) AA by blast
    note n = norm_term_props[OF ei' wY' _ this ty _ _ nP]
    have "vars P \<subseteq> ?X \<union> evars env'" using ZP(2) by blast
    note n = n[OF this, of 0]
    have cl: "\<not> loose_bvar P 0" using wtpD(1)[OF ZP(1)] by (simp add: closed_def)
    have "wtp P'" by (rule wtpI[OF _ n(1)[OF cl]]) (use n(2)[OF cl] in \<open>simp_all add: closed_def\<close>)
    moreover have "vimg ?\<theta> (vars P \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      by (rule vimg_mono) (use ZP(2) SV in blast)
    ultimately show ?thesis using n(3,4)[OF cl] by blast
  qed
  text \<open>The flex-flex pairs:\<close>
  have gT: "closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and> ?good t' \<and> ?good u'"
    if tu: "(t, u) \<in> set tps" and nt: "ok (norm_term env' t) t'" and nu: "ok (norm_term env' u) u'" for t u t' u'
  proof -
    from tpok tu have p: "upok A' env' [] X' t u" by blast
    from upokD(9)[OF p c'(2,1)] obtain e T where tyt: "e \<turnstile> inst (tsol0 ?\<theta>) t : T" and tyu: "e \<turnstile> inst (tsol0 ?\<theta>) u : T"
      by auto
    note nt' = norm_term_props[OF ei' wi' upokD(1)[OF p] upokD(3)[OF p] tyt _ _ nt]
    note nu' = norm_term_props[OF ei' wi' upokD(2)[OF p] upokD(4)[OF p] tyu _ _ nu]
    have l: "\<not> loose_bvar t 0" "\<not> loose_bvar u 0" using upokD(7,8)[OF p] by simp_all
    have cl: "closed t'" "closed u'" using nt'(2)[OF l(1)] nu'(2)[OF l(2)] by (simp_all add: closed_def)
    have "\<forall>e'. e' \<turnstile> t' : T \<and> e' \<turnstile> u' : T"
      using typing_closed[OF nt'(1)[OF l(1)] cl(1)] typing_closed[OF nu'(1)[OF l(2)] cl(2)] by blast
    moreover have "vars t \<union> vars u \<subseteq> dvars (tdps tps)" using tu by (auto simp: dvars_def)
    then have "vimg ?\<theta> (vars t \<union> evars env') \<subseteq> vimg ?\<theta> S0" "vimg ?\<theta> (vars u \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      using SV by (intro vimg_mono; blast)+
    ultimately show ?thesis using cl nt'(3,4)[OF l(1)] nu'(3,4)[OF l(2)] by blast
  qed
  text \<open>Further pairs:\<close>
  have gQ: "closed Z' \<and> (\<forall>e. e \<turnstile> Z' : tsubst (tsol0 ?\<theta>) T0) \<and> ?good Z'"
    if cl0: "closed Z" and tZ: "\<And>e. e \<turnstile> Z : T0" and vZ: "vars Z \<subseteq> ?X" and aZ: "ttvars Z \<subseteq> ?A"
      and nZ: "ok (norm_term env' Z) Z'" for Z Z' T0
  proof -
    have ty: "(\<lambda>_. propT) \<turnstile> inst (tsol0 ?\<theta>) Z : tsubst (tsol0 ?\<theta>) T0"
      using typing_closed[OF typing_inst[OF tZ cert_inst_inst_ok[OF c'(1)]]] cl0 by (simp add: closed_def)
    have "ttvars Z \<subseteq> tvars_env ?\<theta> \<union> A'" using aZ AA by blast
    note n = norm_term_props[OF ei' wY' _ this ty _ _ nZ]
    have "vars Z \<subseteq> ?X \<union> evars env'" using vZ by blast
    note n = n[OF this, of 0]
    have cl: "\<not> loose_bvar Z 0" using cl0 by (simp add: closed_def)
    have c: "closed Z'" using n(2)[OF cl] by (simp add: closed_def)
    have "\<forall>e. e \<turnstile> Z' : tsubst (tsol0 ?\<theta>) T0" using typing_closed[OF n(1)[OF cl] c] by blast
    moreover have "vimg ?\<theta> (vars Z \<union> evars env') \<subseteq> vimg ?\<theta> S0"
      by (rule vimg_mono) (use vZ SV in blast)
    ultimately show ?thesis using c n(3,4)[OF cl] by blast
  qed
  have hyps: "\<forall>h\<in>set hs. wtp h \<and> vars h = {} \<and> ttvars h = {}" using ws by (auto simp: wt_thm_def)
  have fin: "thm_inv (maxidx env') hs ntps' P''"
    if C': "wtp P'' \<and> ?good P''"
      and nt: "\<forall>(t, u)\<in>set ntps'. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
    for P'' ntps'
  proof -
    have vt: "vars_thm ntps' P'' \<subseteq> vimg ?\<theta> S0"
      using C' nt by (fastforce simp: vars_thm_def)
    have tt: "tvars_thm ntps' P'' \<subseteq> tvars_env ?\<theta> \<union> A'"
      using C' nt by (fastforce simp: tvars_thm_def)
    have "wt_thm (maxidx env') hs ntps' P''"
      unfolding wt_thm_def using C' gib[of P''] hyps nt gib by fastforce
    moreover have "-1 \<le> maxidx env'" using sm mx' by simp
    moreover have "scons (tvars_thm ntps' P'')"
      using scA tt unfolding scons_def by blast
    moreover have "lvtcons (vars_thm ntps' P'')"
      using vtS vt unfolding lvtcons_def by blast
    moreover have "\<forall>v\<in>vars_thm ntps' P''. 0 \<le> snd (fst v)"
    proof
      fix v assume "v \<in> vars_thm ntps' P''"
      with vt have "fst v \<in> fst ` S0" by (metis fst_vimg image_eqI subsetD)
      then obtain U where "(fst v, U) \<in> S0" by force
      then show "0 \<le> snd (fst v)" by (rule nnS0)
    qed
    moreover have "\<forall>v\<in>tvars_thm ntps' P''. 0 \<le> snd (fst v)"
      using tt nnA by blast
    ultimately show ?thesis by (simp add: thm_inv_def)
  qed
  have ei: "env_inv env'"
    unfolding env_inv_def
  proof (intro conjI)
    show "closed_env env'" "tacyc ?\<theta>" "tcons_env ?\<theta>"
      using e'(4,6,7) by simp_all
    show "\<forall>(x, T)\<in>evars env'. 0 \<le> snd x" using nnS0 SV(2) by blast
    show "\<forall>p\<in>tvars_env ?\<theta>. 0 \<le> snd (fst p)" using nnA by blast
    show "\<forall>x U u. vt_lookup (tenv env') x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p))"
      using nnA e'(1) unfolding tvinv_def by blast
  qed
  from new have "thm_inv (maxidx env') hs ntps P'"
  proof (elim disjE conjE exE)
    assume em0: "env_is_empty env'" and nt: "ntps = tps" and P': "P' = P"
    have em: "vt_is_empty (tenv env')" "vt_is_empty ?\<theta>" using em0 by (simp_all add: env_is_empty_def)
    have unb: "unb env' Z" for Z by (simp add: unb_def em vt_is_empty_lookup)
    have "wtp P \<and> ?good P"
    proof -
      have "vars P \<subseteq> S0" using ZP(2) SV by blast
      then have "vars P \<subseteq> vimg ?\<theta> S0" by (rule vimg_unb[OF ac' unb])
      moreover have "ttvars P \<subseteq> tvars_env ?\<theta> \<union> A'" using ZP(3) AA by blast
      ultimately show ?thesis using ZP(1) by blast
    qed
    moreover have "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set tps"
      from tpok tu have p: "upok A' env' [] X' t u" by blast
      from upokD(9)[OF p c'(2,1)] obtain e T where "e \<turnstile> inst (tsol0 ?\<theta>) t : T" "e \<turnstile> inst (tsol0 ?\<theta>) u : T"
        by auto
      then have ty: "e \<turnstile> t : T" "e \<turnstile> u : T" using inst_tsol0_unb[OF unb] by simp_all
      have cl: "closed t" "closed u" using upokD(7,8)[OF p] by (simp_all add: closed_def)
      have "vars t \<union> vars u \<subseteq> S0" using tu SV by (auto simp: dvars_def)
      then have "vars t \<subseteq> vimg ?\<theta> S0" "vars u \<subseteq> vimg ?\<theta> S0" using vimg_unb[OF ac' unb] by blast+
      moreover have "ttvars t \<subseteq> tvars_env ?\<theta> \<union> A'" "ttvars u \<subseteq> tvars_env ?\<theta> \<union> A'"
        using upokD(3,4)[OF p] by simp_all
      moreover have "\<forall>e'. e' \<turnstile> t : T \<and> e' \<turnstile> u : T" using typing_closed ty cl by blast
      ultimately show "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and> ?good t \<and> ?good u"
        using cl by blast
    qed
    ultimately show ?thesis using fin nt P' by blast
  next
    fix ntps0 assume l: "list_all2 (\<lambda>tu tu'. ok (norm_term env' (fst tu)) (fst tu') \<and> ok (norm_term env' (snd tu)) (snd tu'))
        (tps @ qs) ntps0"
      and sub: "set ntps \<subseteq> set ntps0" and nP: "ok (norm_term env' P) P'"
    have "\<forall>(t', u')\<in>set ntps. closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and>
        ?good t' \<and> ?good u'"
    proof (intro ballI, clarify)
      fix t' u' assume "(t', u') \<in> set ntps"
      with sub have "(t', u') \<in> set ntps0" by blast
      from list_all2_ex2[OF l this] obtain tu where tu: "tu \<in> set (tps @ qs)"
        and nt: "ok (norm_term env' (fst tu)) t'" and nu: "ok (norm_term env' (snd tu)) u'" by auto
      obtain t u where tue: "tu = (t, u)" by (cases tu)
      from tu[unfolded tue set_append]
      show "closed t' \<and> closed u' \<and> (\<exists>T. \<forall>e. e \<turnstile> t' : T \<and> e \<turnstile> u' : T) \<and> ?good t' \<and> ?good u'"
      proof (rule UnE)
        assume 1: "(t, u) \<in> set tps"
        from gT[OF 1 nt[unfolded tue fst_conv] nu[unfolded tue snd_conv]] show ?thesis .
      next
        assume 2: "(t, u) \<in> set qs"
        have q0: "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and>
            vars t \<union> vars u \<subseteq> ?X \<and> ttvars t \<union> ttvars u \<subseteq> ?A"
          using bspec[OF qs 2] by simp
        then obtain T0 where ty: "\<And>e. e \<turnstile> t : T0" "\<And>e. e \<turnstile> u : T0" by blast
        have q: "closed t" "closed u" "vars t \<subseteq> ?X" "vars u \<subseteq> ?X" "ttvars t \<subseteq> ?A" "ttvars u \<subseteq> ?A"
          using q0 by simp_all
        note gt = gQ[OF q(1) ty(1) q(3,5) nt[unfolded tue fst_conv]]
          and gu = gQ[OF q(2) ty(2) q(4,6) nu[unfolded tue snd_conv]]
        show ?thesis using gt gu by blast
      qed
    qed
    with fin gN[OF nP] show ?thesis by blast
  qed
  with ei show ?thesis by blast
qed

end

context pure_sig_gen
begin

lemma okT_newth:
  assumes "okT (newth ctx n (env, tps)) r"
  shows "ar_env r = env \<and> ar_n r = n \<and> th_maxidx (ar_thm r) = maxidx env \<and>
    (env_is_empty env \<and> th_tpairs (ar_thm r) = tps \<and> th_prop (ar_thm r) = list_implies (ac_Bs ctx) (ac_C ctx) \<or>
     list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps (th_tpairs (ar_thm r)) \<and>
     ok (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx))) (th_prop (ar_thm r)))"
proof (cases "env_is_empty env")
  case True
  with assms show ?thesis by (auto simp: newth_def returnW_def)
next
  case False
  with assms obtain ntps P' where n: "ok (mapM (norm_tpair env) tps) ntps"
    "ok (norm_term env (list_implies (ac_Bs ctx) (ac_C ctx))) P'"
    and r: "r = ARes env n \<lparr>th_maxidx = maxidx env, th_tpairs = ntps, th_prop = P'\<rparr>"
    by (auto simp: newth_def)
  have "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
    using n(1) unfolding ok_mapM by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
  with r n(2) show ?thesis by simp
qed

text \<open>The results of \<^const>\<open>assumption\<close> of a theorem are theorems:\<close>

theorem assumption_thm_inv:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "thm_inv (maxidx (ar_env r)) hs (th_tpairs (ar_thm r)) (th_prop (ar_thm r)) \<and> env_inv (ar_env r)"
proof -
  let ?m = "th_maxidx state" and ?A = "tvars_thm (th_tpairs state) (th_prop state)"
    and ?X = "vars_thm (th_tpairs state) (th_prop state)"
  obtain tpairs Bs Bi C params asms concl l env tps where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    and ur: "ures (empty_env ?m) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx ?m tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and si: "sinv ?A ?A ?X (empty_env ?m) (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have urs: "uresult ?A (empty_env ?m) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    by (rule uresD[OF ur _ _ si]) simp_all
  from uresultD(3)[OF urs] obtain A' K' X' where AA: "?A \<subseteq> A'" and tn: "tnew ?A (empty_env ?m) A' env"
    and ff: "ffres A' K' X' env tps" by blast
  have tA: "tvars_env (tyenv env) \<union> A' \<subseteq> ?A \<union> {p. ?m < snd (fst p)}"
    using tn by (simp add: tnew_def)
  note ds = uresultD(1)[OF urs]
  have ei': "einv A' K' env" and wi': "winv env X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env [] X' t u"
    using ff by (simp_all add: ffres_def)
  note dsd = okT_dest_state[OF d]
  have wS: "wtp (th_prop state)" using st by (simp add: thm_inv_def wt_thm_def)
  have P: "th_prop state = list_implies (Bs @ [Bi]) C"
    using list_implies_strip_prems[OF dsd(2) wtpD(2)[OF wS, of "\<lambda>_. propT"]] by simp
  have ZP: "wtp (list_implies Bs C)" "vars (list_implies Bs C) \<subseteq> ?X" "ttvars (list_implies Bs C) \<subseteq> ?A"
  proof -
    show "wtp (list_implies Bs C)" using wtp_list_implies_butlast(1) wS P by simp
    show "vars (list_implies Bs C) \<subseteq> ?X" using P by (auto simp: vars_thm_def vars_list_implies)
    have "ttvars Z \<subseteq> ttvars (list_implies (Bs @ [Bi]) C)" if "Z \<in> insert C (set Bs)" for Z
      using that ttvars_list_implies(1)[of Z "Bs @ [Bi]" C] ttvars_list_implies(2)[of C "Bs @ [Bi]"] by auto
    then show "ttvars (list_implies Bs C) \<subseteq> ?A"
      using ttvars_list_implies_sub[of Bs C] P by (fastforce simp: tvars_thm_def)
  qed
  note n = okT_newth[OF nt]
  have new: "env_is_empty env \<and> th_tpairs (ar_thm r) = tps \<and> th_prop (ar_thm r) = list_implies Bs C \<or>
      (\<exists>ntps0. list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
        (tps @ []) ntps0 \<and> set (th_tpairs (ar_thm r)) \<subseteq> set ntps0) \<and> ok (norm_term env (list_implies Bs C)) (th_prop (ar_thm r))"
    using n by auto
  from unif_thm_inv[OF st si ds einv_einvw[OF ei' wi'] wi' tpok AA tA ZP _ new l0] n show ?thesis by simp
qed

end

context pure_sig_gen
begin

text \<open>The data of a result of \<^const>\<open>assumption\<close> that its soundness theorems need:\<close>

lemma assumption_data:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
  obtains tpairs Bs Bi C params asms concl l env tps A K X where
    "okT (dest_state state i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    "pwf (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "ar_env r = env" "einv A K env" "winv env X"
    "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
proof -
  let ?A = "tvars_thm (th_tpairs state) (th_prop state)" and ?X = "vars_thm (th_tpairs state) (th_prop state)"
  obtain tpairs Bs Bi C params asms concl l env tps where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and s0: "s0 = AQ_Try (ACtx (th_maxidx state) tpairs Bs Bi C params concl) asms 1" and l: "l < length asms"
    and ur: "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and si: "sinv ?A ?A ?X (empty_env (th_maxidx state)) (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have pw: "pwf (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    using si unfolding pwf_def by (intro exI[of _ ?A] exI[of _ ?X] conjI finite_vars_thm finite_tvars_thm)
  from ures_inv[OF ur pw] obtain A K X where ei: "einv A K env" and wi: "winv env X"
    and tp: "\<forall>(t, u)\<in>set tps. upok A env [] X t u" by blast
  have tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
  proof (intro ballI, clarify)
    fix t u assume "(t, u) \<in> set tps"
    with tp have p: "upok A env [] X t u" by blast
    have "\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T" if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using upokD(9)[OF p that] by blast
    then show "closed t \<and> closed u \<and> (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
      using upokD(7,8)[OF p] by (simp add: closed_def)
  qed
  have re: "ar_env r = env" using okT_newth[OF nt] by simp
  show thesis by (rule that[OF d ap s0 l ur pw nt re ei wi tw])
qed

end

context pure_model_gen
begin

text \<open>The results of \<^const>\<open>assumption\<close> of a valid theorem are valid:\<close>

theorem assumption_valid:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and v: "valid Sh hs (th_tpairs state) (th_prop state)"
  shows "valid (Sh \<union> tyenv_sorts (tyenv (ar_env r))) hs (th_tpairs (ar_thm r)) (th_prop (ar_thm r))"
proof -
  obtain tpairs Bs Bi C params asms concl l env tps A K X where
    d: "okT (dest_state state i) (tpairs, Bs, Bi, C)" and ap: "assum_problems (-1) Bi = (params, asms, concl)"
    and l: "l < length asms"
    and ur: "ures (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and pw: "pwf (empty_env (th_maxidx state)) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs)"
    and nt: "okT (newth (ACtx (th_maxidx state) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    and re: "ar_env r = env" and ei: "einv A K env" and wi: "winv env X"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T))"
    by (rule assumption_data[OF a res cfg st]) blast
  have wt: "wt_thm (th_maxidx state) hs (th_tpairs state) (th_prop state)" using st by (simp add: thm_inv_def)
  have "valid (Sh \<union> tyenv_sorts (tyenv env)) hs (th_tpairs (ar_thm r)) (th_prop (ar_thm r))"
  proof (rule assumption_result_valid[OF d ap _ nt v wt ei wi tw])
    show "asms ! l \<in> set asms" using l by simp
    fix \<rho>' \<sigma>' \<eta> \<xi> assume sol: "gsolution \<rho>' \<sigma>' env" and ci: "cert_inst \<rho>'" and g: "good \<eta> \<xi>"
      and ts: "\<forall>(t, u)\<in>set tps. eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
    show "\<forall>(t, u)\<in>set ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs).
        eq_at \<eta> \<xi> (ap \<rho>' \<sigma>' t) (ap \<rho>' \<sigma>' u)"
      by (rule ures_solves_eq[OF ur pw sol ci g ts])
  qed
  with re show ?thesis by simp
qed

end

context pure_sig
begin

text \<open>Without loose names:\<close>

lemma dstep_fresh:
  assumes ds: "dstep env (tdps tus) env' (tdps tps)" and ei': "einvw A' K' env'" and si: "sinv A K X env (tdps tus)"
    and v: "v \<notin> fst ` (evars env \<union> dvars (tdps tus))" "snd v \<le> maxidx env"
  shows "v \<notin> fst ` (evars env' \<union> dvars (tdps tps))"
  by (rule dstep_fresh[OF ds ei' si v]) simp

theorem unif_thm_inv:
  assumes st: "thm_inv m hs tps0 P0"
    and si: "sinv (tvars_thm tps0 P0) K0 (vars_thm tps0 P0) (empty_env m) (tdps tus)"
    and ds: "dstep (empty_env m) (tdps tus) env' (tdps tps)"
    and ei': "einvw A' K' env'" and wi': "winv env' X'" and tpok: "\<forall>(t, u)\<in>set tps. upok A' env' [] X' t u"
    and AA: "tvars_thm tps0 P0 \<subseteq> A'"
    and tA: "tvars_env (tyenv env') \<union> A' \<subseteq> tvars_thm tps0 P0 \<union> {p. m < snd (fst p)}"
    and ZP: "wtp P" "vars P \<subseteq> vars_thm tps0 P0" "ttvars P \<subseteq> tvars_thm tps0 P0"
    and qs: "\<forall>(t, u)\<in>set qs. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and>
      vars t \<union> vars u \<subseteq> vars_thm tps0 P0 \<and> ttvars t \<union> ttvars u \<subseteq> tvars_thm tps0 P0"
    and new: "env_is_empty env' \<and> ntps = tps \<and> P' = P \<or>
      (\<exists>ntps0. list_all2 (\<lambda>tu tu'. ok (norm_term env' (fst tu)) (fst tu') \<and> ok (norm_term env' (snd tu)) (snd tu'))
        (tps @ qs) ntps0 \<and> set ntps \<subseteq> set ntps0) \<and> ok (norm_term env' P) P'"
  shows "thm_inv (maxidx env') hs ntps P' \<and> env_inv env'"
  by (rule unif_thm_inv[OF st si ds ei' wi' tpok AA tA ZP qs new]) simp

theorem assumption_thm_inv:
  assumes a: "okT (assumption i state) s0" and res: "aresult (unify_ops cfg vl) s0 r"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
  shows "thm_inv (maxidx (ar_env r)) hs (th_tpairs (ar_thm r)) (th_prop (ar_thm r)) \<and> env_inv (ar_env r)"
  by (rule assumption_thm_inv[OF a res cfg st]) simp

end

subsection \<open>Flex-flex pairs\<close>

text \<open>
  The results of \<^const>\<open>flexflex_rule\<close>, and the evaluation of its result sequence to a list. The
  flex-flex pairs of each unifier are smashed, as \<open>Unify.smash_unifiers\<close> does.
\<close>

inductive fresult :: "'u bops \<Rightarrow> (env \<times> (pterm \<times> pterm) list \<Rightarrow> env T) \<Rightarrow> thm_rep \<Rightarrow> 'u fseq \<Rightarrow>
    env \<times> thm_rep \<Rightarrow> bool" for ops sm th where
  First: "okT (fpull ops sm th s) (Some (x, s')) \<Longrightarrow> fresult ops sm th s x"
| Next: "okT (fpull ops sm th s) (Some (x', s')) \<Longrightarrow> fresult ops sm th s' x \<Longrightarrow> fresult ops sm th s x"

inductive fevals :: "'u bops \<Rightarrow> (env \<times> (pterm \<times> pterm) list \<Rightarrow> env T) \<Rightarrow> thm_rep \<Rightarrow> 'u fseq \<Rightarrow>
    (env \<times> thm_rep) list \<Rightarrow> bool" for ops sm th where
  Nil: "okT (fpull ops sm th s) None \<Longrightarrow> fevals ops sm th s []"
| Cons: "okT (fpull ops sm th s) (Some (x, s')) \<Longrightarrow> fevals ops sm th s' xs \<Longrightarrow> fevals ops sm th s (x # xs)"

lemma fevals_fresult: "fevals ops sm th s xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> fresult ops sm th s x"
  by (induction rule: fevals.induct) (auto intro: fresult.First fresult.Next)

text \<open>The smashing of the flex-flex pairs of a unifier (\<open>Unify.smash_flexflex\<close>):\<close>

definition smashT :: "env \<times> (pterm \<times> pterm) list \<Rightarrow> env T" where
  "smashT et = liftWT (smash_flexflex et)"

context pure_sig_gen
begin

lemma wt_thm_pair:
  assumes w: "wt_thm m hs tps P" and tu: "(t, u) \<in> set tps"
  shows "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and>
    vars t \<union> vars u \<subseteq> vars_thm tps P \<and> ttvars t \<union> ttvars u \<subseteq> tvars_thm tps P"
proof -
  have "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> ibelow m t \<and> ibelow m u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using w by (simp add: wt_thm_def)
  then have "closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)" using tu by blast
  with vars_tvars_thm(3,4)[OF tu] show ?thesis by blast
qed

lemma flexflex_sinv:
  assumes st: "thm_inv m hs tps P"
  shows "sinv (tvars_thm tps P) (tvars_thm tps P) (vars_thm tps P) (empty_env m) (tdps tps)"
proof -
  let ?A = "tvars_thm tps P" and ?X = "vars_thm tps P"
  have ws: "wt_thm m hs tps P" using st by (simp add: thm_inv_def)
  have tA: "tcert alg ?A"
  proof -
    have tc: "\<forall>p\<in>ttvars t. sort_ok alg (snd p)" if "\<exists>T. \<forall>e. e \<turnstile> t : T" for t
      using that tcert_ttvars unfolding tcert_def by blast
    have "sort_ok alg (snd p)" if p: "p \<in> ?A" for p
    proof -
      from p consider "p \<in> ttvars P" | t u where "(t, u) \<in> set tps" "p \<in> ttvars t \<union> ttvars u"
        unfolding tvars_thm_def by blast
      then show ?thesis
      proof cases
        case 1
        with tc[of P] ws show ?thesis by (auto simp: wt_thm_def wtp_def)
      next
        case 2
        then obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" using ws unfolding wt_thm_def by blast
        with 2(2) tc[of t] tc[of u] show ?thesis by blast
      qed
    qed
    then show ?thesis unfolding tcert_def by blast
  qed
  have ei: "einv ?A ?A (empty_env m)"
    by (rule einv_empty_env) (use st wt_thm_below[OF ws] tA in \<open>auto simp: thm_inv_def\<close>)
  show ?thesis
  proof (rule sinv_intro[OF ei])
    show "vt_is_empty (tenv (empty_env m))" by simp
    show "finite ?X" by simp
    show "below (maxidx (empty_env m)) ?X" using wt_thm_below(1)[OF ws] by (auto simp: below_def)
    show "vtvars ?X \<subseteq> tvars_env (tyenv (empty_env m)) \<union> ?A"
      by (auto simp: vtvars_def vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
    show "vcons \<rho> ?X" for \<rho> using st by (auto simp: thm_inv_def lvtcons_def vcons_def)
    show "\<forall>(t, u)\<in>set tps. vars t \<union> vars u \<subseteq> ?X \<and> ttvars t \<union> ttvars u \<subseteq> ?A \<and> closed t \<and> closed u \<and>
        (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
      using wt_thm_pair[OF ws] by blast
  qed
qed

text \<open>The results of \<^const>\<open>flexflex_rule\<close>: new theorems of the smashed unifiers of the flex-flex pairs.\<close>

lemma fresult_char:
  assumes "fresult (unify_ops cfg vl) smashT th s x" "s = FQ us" "cfin cfg us (ures env0 tus)"
  shows "\<exists>env' tps. ures env0 tus (El_R env' tps) \<and> okW (smash_flexflex (env', tps)) (fst x) \<and>
    ok (fnewth th (fst x)) (snd x)"
  using assms
proof (induction arbitrary: us rule: fresult.induct)
  case (First s x s')
  from First.hyps First.prems(1) obtain et us' env th' where
    p: "okT (upull cfg us) (Some (et, us'))" and sm: "okW (smash_flexflex et) env"
    and n: "ok (fnewth th env) th'" and x: "x = (env, th')"
    by (auto simp: fpull_def unify_ops_def smashT_def split: option.splits)
  obtain env' tps where et: "et = (env', tps)" by (cases et)
  from upull_fin[OF First.prems(2) p[unfolded et]] sm n x et show ?case by auto
next
  case (Next s x' s' x)
  from Next.hyps(1) Next.prems(1) obtain et us' where
    p: "okT (upull cfg us) (Some (et, us'))" and s': "s' = FQ us'"
    by (auto simp: fpull_def unify_ops_def smashT_def split: option.splits)
  obtain env' tps where et: "et = (env', tps)" by (cases et)
  from upull_fin[OF Next.prems(2) p[unfolded et]] have "cfin cfg us' (ures env0 tus)" by blast
  from Next.IH[OF s' this] show ?case .
qed

theorem flexflex_result:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 x"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
  obtains env' tps where "ures (empty_env (th_maxidx th)) (th_tpairs th) (El_R env' tps)"
    "okW (smash_flexflex (env', tps)) (fst x)" "ok (fnewth th (fst x)) (snd x)"
    "sinv (tvars_thm (th_tpairs th) (th_prop th)) (tvars_thm (th_tpairs th) (th_prop th))
      (vars_thm (th_tpairs th) (th_prop th)) (empty_env (th_maxidx th)) (tdps (th_tpairs th))"
proof -
  note si = flexflex_sinv[OF st]
  from a obtain us where us: "okT (bo_unifiers (unify_ops cfg vl) (empty_env (th_maxidx th)) (th_tpairs th)) us"
    and s0: "s0 = FQ us"
    by (auto simp: flexflex_rule_def)
  have pw: "pwf (empty_env (th_maxidx th)) (th_tpairs th)"
    using si unfolding pwf_def
    by (intro exI[of _ "tvars_thm (th_tpairs th) (th_prop th)"] exI[of _ "vars_thm (th_tpairs th) (th_prop th)"]
        conjI finite_vars_thm finite_tvars_thm)
  from fresult_char[OF res s0 unifiers_ures[OF cfg pw us]] si show thesis using that by blast
qed

text \<open>The data of a result of \<^const>\<open>flexflex_rule\<close> that its soundness theorems need:\<close>

lemma flexflex_data:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
  obtains A' K' X' where "ok (fnewth th env) th'" "einvw A' K' env" "winv env X'"
    "dstep (empty_env (th_maxidx th)) (tdps (th_tpairs th)) env (tdps [])"
    "tvars_thm (th_tpairs th) (th_prop th) \<subseteq> A'"
    "tvars_env (tyenv env) \<union> A' \<subseteq> tvars_thm (th_tpairs th) (th_prop th) \<union> {p. th_maxidx th < snd (fst p)}"
    "sinv (tvars_thm (th_tpairs th) (th_prop th)) (tvars_thm (th_tpairs th) (th_prop th))
      (vars_thm (th_tpairs th) (th_prop th)) (empty_env (th_maxidx th)) (tdps (th_tpairs th))"
proof -
  let ?A = "tvars_thm (th_tpairs th) (th_prop th)" and ?X = "vars_thm (th_tpairs th) (th_prop th)"
  obtain env' tps where ur: "ures (empty_env (th_maxidx th)) (th_tpairs th) (El_R env' tps)"
    and sm: "okW (smash_flexflex (env', tps)) env" and n: "ok (fnewth th env) th'"
    and si: "sinv ?A ?A ?X (empty_env (th_maxidx th)) (tdps (th_tpairs th))"
    using flexflex_result[OF a res cfg st] by auto
  have urs: "uresult ?A (empty_env (th_maxidx th)) (th_tpairs th) (El_R env' tps)"
    by (rule uresD[OF ur _ _ si]) simp_all
  from uresultD(3)[OF urs] obtain A' K' X' e0 where AA: "?A \<subseteq> A'" and tn: "tnew ?A (empty_env (th_maxidx th)) A' env'"
    and ff: "ffres A' K' X' env' tps" and fl: "fflex A' K' e0 env' tps" by blast
  note smi = smash_flexflex_invw[OF ff sm]
  have "dstep (empty_env (th_maxidx th)) (tdps (th_tpairs th)) env (tdps [])"
    using dstep_trans[OF uresultD(1)[OF urs] smi(1)] by simp
  moreover note smi(2)
  moreover have "tvars_env (tyenv env) \<union> A' \<subseteq> ?A \<union> {p. th_maxidx th < snd (fst p)}"
    using tn smi(4) by (simp add: tnew_def)
  ultimately show thesis using that n smi(3) AA si by blast
qed

text \<open>The invariant of theorems for another bound of the indices:\<close>

lemma thm_inv_reidx:
  assumes "thm_inv m hs tps P" "ibelow m' P" "\<forall>(t, u)\<in>set tps. ibelow m' t \<and> ibelow m' u" "-1 \<le> m'"
  shows "thm_inv m' hs tps P"
  using assms unfolding thm_inv_def wt_thm_def by fast

text \<open>The results of \<^const>\<open>flexflex_rule\<close> of a theorem are theorems:\<close>

theorem flexflex_thm_inv:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and l0: "\<forall>x\<in>loose. 0 \<le> snd x"
  shows "thm_inv (th_maxidx th') hs (th_tpairs th') (th_prop th') \<and> env_inv env"
proof -
  obtain A' K' X' where n: "ok (fnewth th env) th'" and ei: "einvw A' K' env" and wi: "winv env X'"
    and ds: "dstep (empty_env (th_maxidx th)) (tdps (th_tpairs th)) env (tdps [])"
    and AA: "tvars_thm (th_tpairs th) (th_prop th) \<subseteq> A'"
    and tA: "tvars_env (tyenv env) \<union> A' \<subseteq> tvars_thm (th_tpairs th) (th_prop th) \<union> {p. th_maxidx th < snd (fst p)}"
    and si: "sinv (tvars_thm (th_tpairs th) (th_prop th)) (tvars_thm (th_tpairs th) (th_prop th))
      (vars_thm (th_tpairs th) (th_prop th)) (empty_env (th_maxidx th)) (tdps (th_tpairs th))"
    by (rule flexflex_data[OF a res cfg st])
  have wS: "wtp (th_prop th)" using st by (simp add: thm_inv_def wt_thm_def)
  have ZP: "wtp (th_prop th)" "vars (th_prop th) \<subseteq> vars_thm (th_tpairs th) (th_prop th)"
    "ttvars (th_prop th) \<subseteq> tvars_thm (th_tpairs th) (th_prop th)"
    using wS by (auto simp: vars_thm_def tvars_thm_def)
  have tp: "\<forall>(t, u)\<in>set []. upok A' env [] X' t u" by simp
  have ws: "wt_thm (th_maxidx th) hs (th_tpairs th) (th_prop th)" using st by (simp add: thm_inv_def)
  have qs: "\<forall>(t, u)\<in>set (th_tpairs th). closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T) \<and>
      vars t \<union> vars u \<subseteq> vars_thm (th_tpairs th) (th_prop th) \<and>
      ttvars t \<union> ttvars u \<subseteq> tvars_thm (th_tpairs th) (th_prop th)"
    using wt_thm_pair[OF ws] by blast
  show ?thesis
  proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs th). aconv_term t u)")
    case True
    with n have "th' = th" by (simp add: fnewth_def)
    moreover have "thm_inv (maxidx env) hs [] (th_prop th) \<and> env_inv env"
      by (rule unif_thm_inv[OF st si ds ei wi tp AA tA ZP qs _ l0]) (use True in simp)
    ultimately show ?thesis using st by simp
  next
    case False
    from fnewth_ok[OF n False] obtain ntps P where l: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and>
        ok (norm_term env (snd tu)) (snd tu')) (th_tpairs th) ntps"
      and nP: "ok (norm_term env (th_prop th)) P"
      and th': "th_tpairs th' = filter (\<lambda>(t, u). \<not> aconv_term t u) ntps" "th_prop th' = P" by blast
    have mx: "th_maxidx th' = maxidx_tpairs (th_tpairs th') (maxidx_of_term (th_prop th'))"
      using n unfolding fnewth_def if_not_P[OF False] by (auto simp: Let_def)
    have "thm_inv (maxidx env) hs (th_tpairs th') (th_prop th') \<and> env_inv env"
    proof (rule unif_thm_inv[OF st si ds ei wi tp AA tA ZP qs _ l0])
      show "env_is_empty env \<and> th_tpairs th' = [] \<and> th_prop th' = th_prop th \<or>
          (\<exists>ntps0. list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu'))
            ([] @ th_tpairs th) ntps0 \<and> set (th_tpairs th') \<subseteq> set ntps0) \<and> ok (norm_term env (th_prop th)) (th_prop th')"
        using l nP th' by auto
    qed
    then have w: "thm_inv (maxidx env) hs (th_tpairs th') (th_prop th')" and ev: "env_inv env"
      by simp_all
    let ?k = "maxidx_tpairs (th_tpairs th') (maxidx_of_term (th_prop th'))"
    have S: "pure_sig alg ar" using pure_sig_gen_axioms by (simp add: pure_sig_def)
    have k1: "maxidx_of_term (th_prop th') \<le> ?k" by (rule maxidx_tpairs_ge)
    have "thm_inv ?k hs (th_tpairs th') (th_prop th')"
    proof (rule thm_inv_reidx[OF w])
      show "ibelow ?k (th_prop th')" by (rule ibelow_mono[OF pure_sig.maxidx_of_term_ibelow[OF S] k1])
      show "\<forall>(t, u)\<in>set (th_tpairs th'). ibelow ?k t \<and> ibelow ?k u"
        using pure_sig.maxidx_tpairs_mem[OF S] by blast
      show "-1 \<le> ?k" using k1 maxidx_term_ge[of "-1" "th_prop th'"] by (simp add: maxidx_of_term_def)
    qed
    with ev mx show ?thesis by simp
  qed
qed

end

context pure_model_gen
begin

theorem flexflex_valid:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
    and v: "valid Sh hs (th_tpairs th) (th_prop th)"
  shows "valid (Sh \<union> tyenv_sorts (tyenv env)) hs (th_tpairs th') (th_prop th')"
proof -
  obtain A' K' X' where n: "ok (fnewth th env) th'" and ei: "einvw A' K' env" and wi: "winv env X'"
    by (rule flexflex_data[OF a res cfg st])
  have wt: "wt_thm (th_maxidx th) hs (th_tpairs th) (th_prop th)" using st by (simp add: thm_inv_def)
  show ?thesis by (rule fnewth_valid[OF n v wt ei wi])
qed

end

context pure_sig
begin

text \<open>Without loose names:\<close>

lemma fresult_char:
  assumes "fresult (unify_ops cfg vl) smashT th s x" "s = FQ us" "fin cfg us (ures env0 tus)"
  shows "\<exists>env' tps. ures env0 tus (El_R env' tps) \<and> okW (smash_flexflex (env', tps)) (fst x) \<and>
    ok (fnewth th (fst x)) (snd x)"
  using fresult_char[OF assms(1,2)] assms(3) by (simp add: cfin_strict)

theorem flexflex_thm_inv:
  assumes a: "okT (flexflex_rule (unify_ops cfg vl) th) s0" and res: "fresult (unify_ops cfg vl) smashT th s0 (env, th')"
    and cfg: "cfg_alg cfg = alg" and st: "thm_inv (th_maxidx th) hs (th_tpairs th) (th_prop th)"
  shows "thm_inv (th_maxidx th') hs (th_tpairs th') (th_prop th') \<and> env_inv env"
  by (rule flexflex_thm_inv[OF a res cfg st]) simp

end

subsection \<open>Names with two types\<close>

text \<open>
  The names of the variables of a set that occur in it with two types. The general forms of the
  rules that unify take them as the loose names of the locale; the environment of a result may
  bind them.
\<close>

definition vclash :: "(indexname \<times> ptyp) set \<Rightarrow> indexname set" where
  "vclash X = {x. \<exists>T U. (x, T) \<in> X \<and> (x, U) \<in> X \<and> T \<noteq> U}"

lemma (in pure_sig_gen) lvtcons_vclash: "vclash X \<subseteq> loose \<Longrightarrow> lvtcons X"
  unfolding lvtcons_def vclash_def by blast

subsection \<open>The rules on theorems\<close>

text \<open>
  The new theorem of a result \<open>r\<close> of \<^const>\<open>assumption\<close> (\<open>Thm.assumption\<close>): the sort hypotheses
  of the proof state and of the environment (\<open>Envir.insert_sorts\<close>), its hypotheses, and the proofs
  of \<^const>\<open>ares_proof\<close> and \<^const>\<open>ares_zproof\<close>.
\<close>

definition thm_of_ares :: "'u pure_thm \<Rightarrow> actx \<Rightarrow> ares \<Rightarrow> thm_data" where
  "thm_of_ares state ctx r = with_cons (cons_of state \<union> env_constraints (ar_env r))
    (mk_thm (ar_thm r) (shyps_of state \<union> env_sorts (ar_env r)) (hyps_of state) (sign_of state)
      (bindW (proof_of state) (ares_proof ctx r))
      (bindM (zproof_of state) (ares_zproof (pure_sig_gen.ztargs (sg_consts (sign_of state))) (rep_of state) ctx r)))"

text \<open>
  The new theorem of a result satisfies the invariant of the theorems, also if names of variables
  occur at two types in the theorem; the environment of the result may bind such names. These
  are the loose names of the proofs:
\<close>

definition ares_clash :: "'u pure_thm \<Rightarrow> indexname set" where
  "ares_clash state = vclash (pure_sig_gen.vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"

lemma cons_ok_thm_of_ares:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
  shows "cons_ok (sign_of (state :: 'u pure_thm)) (cons_of state \<union> env_constraints (ar_env r))"
proof -
  let ?c = "sign_of state"
  let ?L = "ares_clash state"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  have "\<exists>env A K. ar_env r = env \<and> einv A K env" by (rule assumption_data[OF a res cfg st]) blast
  then have "tsorted (sg_alg ?c) (tyenv (ar_env r))" using einvD(12) by blast
  then show ?thesis by (simp add: cons_ok_env)
qed

lemma sorts_ok_thm_of_ares:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
  shows "\<forall>S\<in>env_sorts (ar_env r). sort_ok (sg_alg (sign_of (state :: 'u pure_thm))) S"
proof -
  let ?c = "sign_of state"
  let ?L = "ares_clash state"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  have "\<exists>env A K. ar_env r = env \<and> einv A K env" by (rule assumption_data[OF a res cfg st]) blast
  then have "scert (sg_alg ?c) (tyenv (ar_env r))" using einvD(9) by blast
  then show ?thesis using scert_env_sorts by blast
qed

lemma thm_sem_thm_of_ares:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)"
    and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    and a: "okT (assumption i (rep_of state)) s0" and res: "aresult (unify_ops cfg vl) s0 r"
  shows "thm_sem TYPE('u) (thm_of_ares (state :: 'u pure_thm) (aseq_ctx s0) r)"
proof -
  let ?c = "sign_of state" and ?th = "thm_of_ares state (aseq_ctx s0) r"
  let ?L = "ares_clash state"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = assumption_thm_inv[OF a res cfg st l0]
  obtain tpairs Bs Bi C params asms concl l env tps where
    "okT (dest_state (rep_of state) i) (tpairs, Bs, Bi, C)" "assum_problems (-1) Bi = (params, asms, concl)"
    "s0 = AQ_Try (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) asms 1" "l < length asms"
    "ures (empty_env (th_maxidx (rep_of state))) ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs) (El_R env tps)"
    and nt: "okT (newth (ACtx (th_maxidx (rep_of state)) tpairs Bs Bi C params concl) (integer_of_nat l + 1) (env, tps)) r"
    "sinv (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (tvars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state)))
      (vars_thm (th_tpairs (rep_of state)) (th_prop (rep_of state))) (empty_env (th_maxidx (rep_of state)))
      (tdps ((rlist_abs params (asms ! l), rlist_abs params concl) # tpairs))"
    by (rule assumption_result[OF a res cfg st])
  have mx: "th_maxidx (ar_thm r) = maxidx (ar_env r)" using okT_newth[OF nt(1)] by simp
  have ws: "wt_thm (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using st by (simp add: thm_inv_def)
  have "valid_in ?c M (shyps_of state \<union> env_sorts (ar_env r)) (hyps_of state) (th_tpairs (ar_thm r)) (th_prop (ar_thm r))"
    if M: "is_model ?c M" for M :: "'u model"
  proof -
    interpret pure_model_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule pure_model_gen_of[OF is_modelD[OF M]])
    have vs: "valid (shyps_of state) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
      using pure_thm_valid[OF M] by (simp add: valid_in_def)
    from assumption_valid[OF a res cfg st vs]
    show ?thesis unfolding valid_in_def by (rule valid_mono) (auto simp: env_sorts_def)
  qed
  then show ?thesis using ti mx by (simp add: thm_sem_def thm_of_ares_def pure_sig.thm_inv0_wf[OF ps] thm_inv_iff)
qed

text \<open>
  The new theorem of a result \<open>(env, r)\<close> of \<^const>\<open>flexflex_rule\<close> (\<open>Thm.flexflex_rule\<close>): the
  theorem itself if the environment is empty and it has no trivial flex-flex pairs; otherwise with
  the sort hypotheses of the environment and the normalized proofs. The rule applies it to
  the theorem with its constraints solved (\<open>Thm.solve_constraints\<close>); the new theorem has the
  constraints of the environment.
\<close>

definition thm_of_fres :: "'u pure_thm \<Rightarrow> env \<Rightarrow> thm_rep \<Rightarrow> thm_data" where
  "thm_of_fres th env r =
    (if env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs (rep_of th)). aconv_term t u) then rep_thm th
     else with_cons (env_constraints env) (mk_thm r (shyps_of th \<union> env_sorts env) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (norm_proof_remove_types env))
      (bindM (zproof_of th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (rep_of th) env))))"

lemma thm_of_fres_sign [simp]: "th_sign (thm_of_fres th env r) = sign_of th"
  by (simp add: thm_of_fres_def)

text \<open>The same without the condition on the names of the variables:\<close>

lemma cons_ok_thm_of_fres:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
  shows "cons_ok (sign_of (th :: 'u pure_thm)) (th_constraints (thm_of_fres th env r))"
proof -
  let ?c = "sign_of th"
  let ?L = "ares_clash th"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  have "\<exists>A K. einvw A K env" by (rule flexflex_data[OF a res cfg st]) blast
  then have "tsorted (sg_alg ?c) (tyenv env)" using einvwD(12) by blast
  then show ?thesis by (simp add: thm_of_fres_def cons_ok_env)
qed

lemma sorts_ok_thm_of_fres:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
  shows "\<forall>S\<in>env_sorts env. sort_ok (sg_alg (sign_of (th :: 'u pure_thm))) S"
proof -
  let ?c = "sign_of th"
  let ?L = "ares_clash th"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  have "\<exists>A K. einvw A K env" by (rule flexflex_data[OF a res cfg st]) blast
  then have "scert (sg_alg ?c) (tyenv env)" using einvwD(9) by blast
  then show ?thesis using scert_env_sorts by blast
qed

lemma thm_sem_thm_of_fres:
  assumes ps: "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of th)" and sc: "scons (pure_sig_gen.tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    and a: "okT (flexflex_rule (unify_ops cfg vl) (rep_of th)) s0"
    and res: "fresult (unify_ops cfg vl) smashT (rep_of th) s0 (env, r)"
  shows "thm_sem TYPE('u) (thm_of_fres (th :: 'u pure_thm) env r)"
proof (cases "env_is_empty env \<and> \<not> (\<exists>(t, u)\<in>set (th_tpairs (rep_of th)). aconv_term t u)")
  case True
  then show ?thesis using thm_sem_rep[of th] by (simp add: thm_of_fres_def)
next
  case False
  let ?c = "sign_of th" and ?th = "thm_of_fres th env r"
  have eq: "?th = with_cons (env_constraints env) (mk_thm r (shyps_of th \<union> env_sorts env) (hyps_of th) (sign_of th)
      (bindW (proof_of th) (norm_proof_remove_types env))
      (bindM (zproof_of th) (flexflex_zproof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (rep_of th) env)))"
    unfolding thm_of_fres_def if_not_P[OF False] ..
  let ?L = "ares_clash th"
  interpret pure_sig_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L using ps unfolding pure_sig_def .
  have st0: "thm_inv0 (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_inv0[OF ps] sc by simp
  have l0: "\<forall>x\<in>?L. 0 \<le> snd x" using st0 by (fastforce simp: thm_inv0_def vclash_def ares_clash_def)
  have lv: "lvtcons (vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)))"
    by (rule lvtcons_vclash) (simp add: ares_clash_def)
  have st: "thm_inv (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule iffD2[OF thm_inv_iff, OF conjI[OF st0 lv]])
  note ti = flexflex_thm_inv[OF a res cfg st l0]
  have ws: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using st by (simp add: thm_inv_def)
  have "valid_in ?c M (shyps_of th \<union> env_sorts env) (hyps_of th) (th_tpairs r) (th_prop r)"
    if M: "is_model ?c M" for M :: "'u model"
  proof -
    interpret pure_model_gen "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" ?L "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule pure_model_gen_of[OF is_modelD[OF M]])
    have vs: "valid (shyps_of th) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
      using pure_thm_valid[OF M] by (simp add: valid_in_def)
    from flexflex_valid[OF a res cfg st vs]
    show ?thesis unfolding valid_in_def by (rule valid_mono) (auto simp: env_sorts_def)
  qed
  then show ?thesis using ti
    by (simp add: thm_sem_def eq pure_sig.thm_inv0_wf[OF ps] thm_inv_iff)
qed

end
