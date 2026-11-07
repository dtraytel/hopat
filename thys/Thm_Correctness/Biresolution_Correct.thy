section \<open>Correctness of \<open>biresolution\<close>\<close>

theory Biresolution_Correct
  imports Lift_Rule
begin

text \<open>
  \<open>biresolution\<close> lifts each rule over the subgoal (\<^const>\<open>lift_rule\<close>) and composes it with the
  proof state by \<^const>\<open>bicompose_aux\<close>. By the theorems on lifting, the theorems on
  \<^const>\<open>bicompose_aux\<close> carry over: the results of \<open>biresolution\<close> are valid, the evaluation of
  its sequence of results terminates, and it enumerates all results of the compositions of the
  rules that pass its quick test.
\<close>

context pure_sig
begin

subsection \<open>The subgoal\<close>

lemma okT_handleT_raises: "okT (handleT m h) y \<Longrightarrow> (\<And>e. \<not> okT (h e) y) \<Longrightarrow> okT m y"
  by (auto simp: okT_handleT)

lemma okT_of_snd: "m = Some r \<Longrightarrow> snd r = TOk x \<Longrightarrow> okT m x"
  by (cases r) auto

lemma okT_dest_state:
  assumes "okT (dest_state state i) (stpairs, Bs, Bi, C)"
  shows "stpairs = th_tpairs state" "ok (strip_prems i [] (th_prop state)) (Bi # rev Bs, C)"
proof -
  have "okT (do {
      (rBs, C) \<leftarrow> liftMT (strip_prems i [] (th_prop state));
      (case rBs of
        B # rBs' \<Rightarrow> returnT (th_tpairs state, rev rBs', B, C)
      | [] \<Rightarrow> raiseT (THM (STR ''dest_state'') i State))}) (stpairs, Bs, Bi, C)"
    by (rule okT_handleT_raises[OF assms[unfolded dest_state_def]])
      (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)
  then show "stpairs = th_tpairs state" "ok (strip_prems i [] (th_prop state)) (Bi # rev Bs, C)"
    by (auto simp: neq_Nil_conv split: list.splits)
qed

lemma strip_prems_length:
  "ok (strip_prems i As B) (rAs, B') \<Longrightarrow> length rAs = nat_of_integer i + length As"
  using strip_prems_ok[of i As B rAs B'] by auto

lemma nth_prem_strip_prems:
  assumes "ok (strip_prems i As P) (rAs, C)" "length As < length rAs"
  shows "ok (nth_prem i P) (hd rAs)"
  using assms
proof (induction i As P rule: strip_prems.induct)
  case (1 i As P)
  show ?case
  proof (cases "i = 0")
    case True
    with "1.prems" show ?thesis by (subst (asm) strip_prems.simps) simp
  next
    case False
    with "1.prems"(1) obtain A B where AB: "dest_imp P = Some (A, B)"
      and r: "ok (strip_prems (i - 1) (A # As) B) (rAs, C)"
      by (subst (asm) strip_prems.simps) (auto split: option.splits)
    show ?thesis
    proof (cases "i = 1")
      case True
      with r have "rAs = A # As" by (subst (asm) strip_prems.simps) simp
      with AB True show ?thesis by (subst nth_prem.simps) simp
    next
      case i1: False
      from strip_prems_ok[OF r] have "0 \<le> i - 1" by blast
      with strip_prems_length[OF r] False i1 have "length (A # As) < length rAs"
        by (simp add: integer_reps)
      from "1.IH"[OF False AB refl r this] AB i1 show ?thesis by (subst nth_prem.simps) simp
    qed
  qed
qed

lemma okT_cprem_of: "okT (cprem_of th i) goal \<Longrightarrow> ok (nth_prem i (th_prop th)) goal"
  unfolding cprem_of_def
  by (drule okT_handleT_raises) (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)

text \<open>The subgoal of a proof state, and the proof state as composed with the rules.\<close>

lemma dest_state_cprem_of:
  assumes "okT (dest_state state i) (stpairs, Bs, Bi, C)" "okT (cprem_of state i) goal"
    "e \<turnstile> th_prop state : T"
  shows "goal = Bi" "stpairs = th_tpairs state" "th_prop state = list_implies (Bs @ [Bi]) C"
proof -
  note d = okT_dest_state[OF assms(1)]
  from nth_prem_strip_prems[OF d(2)] okT_cprem_of[OF assms(2)] show "goal = Bi" by simp
  show "stpairs = th_tpairs state" by (rule d(1))
  from list_implies_strip_prems[OF d(2) assms(3)] show "th_prop state = list_implies (Bs @ [Bi]) C"
    by simp
qed

lemma okT_biresolution:
  assumes "okT (biresolution trace match_flg rep brules i state) s0"
  obtains stpairs Bs Bi C goal where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal"
    "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi) (test_hyps Bi)) brules"
  using assms by (auto simp: biresolution_def)


subsection \<open>The result sequence\<close>

text \<open>The sequences of results of a call of \<^const>\<open>bicompose_aux\<close> reached by pulling.\<close>

inductive breach :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> 'u bseq \<Rightarrow> bool" for ops where
  Refl: "breach ops s s"
| Step: "breach ops s0 s \<Longrightarrow> okT (bpull ops s) (Some (r, s')) \<Longrightarrow> breach ops s0 s'"

lemma breach_bresult: "breach ops s0 s \<Longrightarrow> bresult ops s r \<Longrightarrow> bresult ops s0 r"
  by (induction rule: breach.induct) (auto intro: bresult.Next)

text \<open>
  The invariant of the result sequence of \<^const>\<open>biresolution\<close> for the call context \<open>ctx\<close> and
  the rules \<open>brules0\<close>: the closures are those of rules of \<open>brules0\<close>, and the sequences of results
  are reached from the results of the composition of a rule with the proof state.
\<close>

inductive rinv :: "'u bops \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> (bool \<times> 'r) list \<Rightarrow>
    ('u, 'r) rseq \<Rightarrow> bool" for ops rep ctx brules0 where
  Empty: "rinv ops rep ctx brules0 RQ_Empty"
| Make: "set (r # brules) \<subseteq> set brules0 \<Longrightarrow> rinv ops rep ctx brules0 (RQ_Make ctx r brules)"
| App: "r \<in> set brules0 \<Longrightarrow> okT (compose ops alg ctx (fst r) (rep (snd r))) xq0 \<Longrightarrow> breach ops xq0 xq \<Longrightarrow>
    rinv ops rep ctx brules0 xqq \<Longrightarrow> rinv ops rep ctx brules0 (RQ_App r xq xqq)"

lemma res_rinv: "set brules \<subseteq> set brules0 \<Longrightarrow> rinv ops rep ctx brules0 (res rep ctx brules)"
  by (induction rep ctx brules rule: res.induct) (simp_all add: rinv.Empty rinv.Make)

definition rchar_br :: "'u bops \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> (bool \<times> 'r) list \<Rightarrow>
    bres \<times> (bool \<times> 'r) \<Rightarrow> bool" where
  "rchar_br ops rep ctx brules0 xr \<longleftrightarrow> (case xr of (x, r) \<Rightarrow> r \<in> set brules0 \<and>
    (\<exists>xq0. okT (compose ops alg ctx (fst r) (rep (snd r))) xq0 \<and> bresult ops xq0 x))"

lemma brstep_rinv:
  assumes "rinv ops rep ctx brules0 s" "okT (brstep ops alg rep s) st"
  shows "case st of
      RS_Done \<Rightarrow> True
    | RS_Skip s' \<Rightarrow> rinv ops rep ctx brules0 s'
    | RS_Result xr s' \<Rightarrow> rinv ops rep ctx brules0 s' \<and> rchar_br ops rep ctx brules0 xr"
  using assms(1)
proof cases
  case Empty
  with assms(2) show ?thesis by simp
next
  case (Make r brules)
  obtain e rule where r: "r = (e, rule)" by (cases r)
  from assms(2) Make r obtain xq where xq: "okT (compose ops alg ctx e (rep rule)) xq"
    and st: "st = RS_Skip (RQ_App (e, rule) xq (res rep ctx brules))"
    by auto
  have "rinv ops rep ctx brules0 (RQ_App (e, rule) xq (res rep ctx brules))"
    by (rule rinv.App[OF _ _ breach.Refl res_rinv]) (use Make r xq in auto)
  with st show ?thesis by simp
next
  case (App r xq0 xq xqq)
  from assms(2) App obtain x where p: "okT (bpull ops xq) x"
    and st: "okT (case x of None \<Rightarrow> returnT (RS_Skip xqq)
      | Some (th, xq') \<Rightarrow> returnT (RS_Result (th, r) (RQ_App r xq' xqq))) st"
    by auto
  show ?thesis
  proof (cases x)
    case None
    with st App show ?thesis by simp
  next
    case (Some y)
    then obtain th xq' where y: "x = Some (th, xq')" by (cases y) auto
    with st have st': "st = RS_Result (th, r) (RQ_App r xq' xqq)" by simp
    have "rinv ops rep ctx brules0 (RQ_App r xq' xqq)"
      by (rule rinv.App[OF App(2,3) breach.Step[OF App(4)] App(5)]) (use p y in simp)
    moreover have "bresult ops xq0 th"
      by (rule breach_bresult[OF App(4) bresult.First]) (use p y in simp)
    ultimately show ?thesis using st' App(2,3) by (auto simp: rchar_br_def)
  qed
qed

lemma brpull_rinv_aux:
  "brpull ops a rep s = Some r0 \<Longrightarrow> a = alg \<Longrightarrow> snd r0 = TOk (Some (xr, s')) \<Longrightarrow>
    rinv ops rep ctx brules0 s \<Longrightarrow> rchar_br ops rep ctx brules0 xr \<and> rinv ops rep ctx brules0 s'"
proof (induction ops a rep s r0 arbitrary: xr s' rule: brpull.raw_induct[rotated, consumes 1])
  case (1 P ops a rep s r0)
  note hyps = okT_of_snd[OF "1.hyps" "1.prems"(2)]
  from hyps obtain st where st: "okT (brstep ops a rep s) st"
    and cont: "okT (case st of
        RS_Done \<Rightarrow> returnT None
      | RS_Skip s' \<Rightarrow> P ops a rep s'
      | RS_Result x s' \<Rightarrow> returnT (Some (x, s'))) (Some (xr, s'))"
    by auto
  note inv = brstep_rinv[OF "1.prems"(3) st[unfolded "1.prems"(1)]]
  show ?case
  proof (cases st)
    case RS_Done
    with cont show ?thesis by simp
  next
    case (RS_Skip s1)
    with cont obtain evs where "P ops a rep s1 = Some (evs, TOk (Some (xr, s')))" by auto
    from "1.IH"[OF this "1.prems"(1) _] inv RS_Skip show ?thesis by simp
  next
    case (RS_Result x s1)
    with cont inv show ?thesis by simp
  qed
qed

lemma brpull_rinv:
  "brpull ops alg rep s = Some r0 \<Longrightarrow> snd r0 = TOk (Some (xr, s')) \<Longrightarrow> rinv ops rep ctx brules0 s \<Longrightarrow>
    rchar_br ops rep ctx brules0 xr \<and> rinv ops rep ctx brules0 s'"
  using brpull_rinv_aux by blast

text \<open>The results of the sequence of \<^const>\<open>biresolution\<close>, as for \<^const>\<open>bicompose_aux\<close>.\<close>

inductive brresult :: "'u bops \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow> bres \<times> (bool \<times> 'r) \<Rightarrow> bool"
  for ops rep where
  First: "okT (brpull ops alg rep s) (Some (xr, s')) \<Longrightarrow> brresult ops rep s xr"
| Next: "okT (brpull ops alg rep s) (Some (xr', s')) \<Longrightarrow> brresult ops rep s' xr \<Longrightarrow> brresult ops rep s xr"

lemma brresult_rchar:
  assumes "brresult ops rep s xr" "rinv ops rep ctx brules0 s"
  shows "rchar_br ops rep ctx brules0 xr"
  using assms
proof (induction rule: brresult.induct)
  case (First s xr s')
  then obtain evs where "brpull ops alg rep s = Some (evs, TOk (Some (xr, s')))" by blast
  from brpull_rinv[OF this _ First.prems] show ?case by simp
next
  case (Next s xr' s' xr)
  then obtain evs where "brpull ops alg rep s = Some (evs, TOk (Some (xr', s')))" by blast
  from brpull_rinv[OF this _ Next.prems] Next.IH show ?case by simp
qed

text \<open>
  A result of \<^const>\<open>biresolution\<close> is a result of the composition of one of the rules, lifted
  over the subgoal, with the proof state.
\<close>

lemma biresolution_result:
  assumes "okT (biresolution trace match_flg rep brules i state) s0"
    and "brresult ops rep s0 (x, (eres_flg, rule))"
  obtains stpairs Bs Bi C goal where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "(eres_flg, rule) \<in> set brules"
    "\<exists>xq0. okT (bicompose_aux ops alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C) True
      eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq0 \<and>
      bresult ops xq0 x"
proof -
  from assms(1) obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal"
    and s0: "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi) (test_hyps Bi)) brules"
    by (rule okT_biresolution)
  let ?ctx = "BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi) (test_hyps Bi)"
  have "rinv ops rep ?ctx brules s0" unfolding s0 by (rule res_rinv) simp
  from brresult_rchar[OF assms(2) this] show thesis
    by (intro that[OF d g]) (auto simp: rchar_br_def compose_def)
qed



text \<open>The state and the rule lifted over its subgoal \<open>G\<close> are consistent:\<close>

lemma lift_rule_cons:
  assumes sp: "lsplit G = (p, G0)" and ws: "wt_thm smax hs stpairs S"
    and G: "vars G \<subseteq> vars_thm stpairs S" "ttvars G \<subseteq> tvars_thm stpairs S"
    and cs: "scons (tvars_thm stpairs S)" "vtcons (vars_thm stpairs S)"
    and r: "thm_inv (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
  defines "lr \<equiv> lift_rule G smax rule"
  shows "scons (tvars_thm stpairs S \<union> tvars_thm (th_tpairs lr) (th_prop lr))"
    "vtcons (vars_thm stpairs S \<union> vars_thm (th_tpairs lr) (th_prop lr))"
proof -
  let ?inc = "smax + 1"
  have P: "e \<turnstile> th_prop rule : propT" for e using r by (simp add: thm_inv_def wt_thm_def wtpD(2))
  have rc: "scons (tvars_thm (th_tpairs rule) (th_prop rule))" "vtcons (vars_thm (th_tpairs rule) (th_prop rule))"
    and rn: "\<forall>v\<in>vars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
      "\<forall>v\<in>tvars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
    using r by (simp_all add: thm_inv_def)
  have tv: "((a, i), U) \<in> tvars_thm stpairs S \<and> i \<le> smax \<or>
      ((a, i - ?inc), U) \<in> tvars_thm (th_tpairs rule) (th_prop rule) \<and> smax < i"
    if "((a, i), U) \<in> tvars_thm stpairs S \<union> tvars_thm (th_tpairs lr) (th_prop lr)" for a i U
  proof -
    from that consider "((a, i), U) \<in> tvars_thm stpairs S"
      | "((a, i - ?inc), U) \<in> tvars_thm (th_tpairs rule) (th_prop rule)"
      using lift_rule_tvars[OF sp P, of a i U smax] G(2) unfolding lr_def by blast
    then show ?thesis
    proof cases
      case 1
      with wt_thm_below(2)[OF ws 1] show ?thesis by simp
    next
      case 2
      with rn(2) have "0 \<le> i - ?inc" by force
      with 2 show ?thesis by simp
    qed
  qed
  show "scons (tvars_thm stpairs S \<union> tvars_thm (th_tpairs lr) (th_prop lr))"
    unfolding scons_def
  proof (intro allI impI)
    fix v U U'
    assume h: "(v, U) \<in> tvars_thm stpairs S \<union> tvars_thm (th_tpairs lr) (th_prop lr)"
      "(v, U') \<in> tvars_thm stpairs S \<union> tvars_thm (th_tpairs lr) (th_prop lr)"
    obtain a i where v: "v = (a, i)" by (cases v)
    from tv[OF h(1)[unfolded v]] tv[OF h(2)[unfolded v]] cs(1) rc(1) show "U = U'" unfolding scons_def by auto
  qed
  have vv: "((x, i), T) \<in> vars_thm stpairs S \<and> i \<le> smax \<or>
      (\<exists>T0. ((x, i - ?inc), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule) \<and>
        T = foldr fun_type (ptys p) (incr_tvar ?inc T0) \<and> smax < i)"
    if "((x, i), T) \<in> vars_thm stpairs S \<union> vars_thm (th_tpairs lr) (th_prop lr)" for x i T
  proof -
    from that consider "((x, i), T) \<in> vars_thm stpairs S"
      | T0 where "((x, i - ?inc), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule)"
          "T = foldr fun_type (ptys p) (incr_tvar ?inc T0)"
      using lift_rule_vars[OF sp, of x i T smax rule] G(1) unfolding lr_def by blast
    then show ?thesis
    proof cases
      case 1
      with wt_thm_below(1)[OF ws 1] show ?thesis by simp
    next
      case (2 T0)
      with rn(1) have "0 \<le> i - ?inc" by force
      with 2 show ?thesis by auto
    qed
  qed
  show "vtcons (vars_thm stpairs S \<union> vars_thm (th_tpairs lr) (th_prop lr))"
    unfolding vtcons_def
  proof (intro allI impI)
    fix v T T'
    assume h: "(v, T) \<in> vars_thm stpairs S \<union> vars_thm (th_tpairs lr) (th_prop lr)"
      "(v, T') \<in> vars_thm stpairs S \<union> vars_thm (th_tpairs lr) (th_prop lr)"
    obtain x i where v: "v = (x, i)" by (cases v)
    from vv[OF h(1)[unfolded v]] vv[OF h(2)[unfolded v]] cs(2) rc(2) show "T = T'" unfolding vtcons_def by (metis (no_types, lifting) not_less)
  qed
qed

text \<open>The conditions of the composition of a rule with the proof state:\<close>

lemma compose_cond:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rule: "thm_inv (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
  defines "lr \<equiv> lift_rule goal (th_maxidx state) rule"
  shows "goal = Bi" "stpairs = th_tpairs state" "th_prop state = list_implies (Bs @ [Bi]) C"
    "wt_thm (th_maxidx state) hs stpairs (list_implies (Bs @ [Bi]) C)" "wtp Bi"
    "wt_thm (th_maxidx lr) hr (th_tpairs lr) (th_prop lr)"
    "lifted_over (th_maxidx state) Bi (th_prop lr) (nprems_of rule)"
    "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm (th_tpairs lr) (th_prop lr))"
    "vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs lr) (th_prop lr))"
proof -
  let ?smax = "th_maxidx state" and ?S = "list_implies (Bs @ [Bi]) C"
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and rm: "-1 \<le> th_maxidx rule" and rn: "\<forall>v\<in>vars (th_prop rule). 0 \<le> snd (fst v)"
    using rule by (auto simp: thm_inv_def vars_thm_def)
  have ws0: "wt_thm ?smax hs (th_tpairs state) (th_prop state)" using state by (simp add: thm_inv_def)
  note ds = dest_state_cprem_of[OF d g wtpD(2)[OF conjunct1[OF ws0[unfolded wt_thm_def]], of "\<lambda>_. propT"]]
  show "goal = Bi" "stpairs = th_tpairs state" "th_prop state = ?S" by (rule ds)+
  show ws: "wt_thm ?smax hs stpairs ?S" using ws0 ds by simp
  have wB: "wtp Bi" "ibelow ?smax Bi"
    using ws wtp_list_implies[of "Bs @ [Bi]" "Bs @ [Bi]" C C] by (simp_all add: wt_thm_def)
  then show "wtp Bi" by simp
  have GS: "vars Bi \<subseteq> vars_thm stpairs ?S" "ttvars Bi \<subseteq> tvars_thm stpairs ?S"
    using ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C]
    by (auto simp: vars_thm_def tvars_thm_def vars_list_implies)
  have cS: "scons (tvars_thm stpairs ?S)" "vtcons (vars_thm stpairs ?S)"
    using state ds by (simp_all add: thm_inv_def)
  obtain p G0 where sp: "lsplit Bi = (p, G0)" by (cases "lsplit Bi")
  show "wt_thm (th_maxidx lr) hr (th_tpairs lr) (th_prop lr)"
    unfolding lr_def ds(1) by (rule lift_rule_wt_thm[OF wr wB rm])
  show "lifted_over ?smax Bi (th_prop lr) (nprems_of rule)"
    unfolding lr_def ds(1) by (rule lift_rule_lifted_over[OF rn])
  show "scons (tvars_thm stpairs ?S \<union> tvars_thm (th_tpairs lr) (th_prop lr))"
    "vtcons (vars_thm stpairs ?S \<union> vars_thm (th_tpairs lr) (th_prop lr))"
    unfolding lr_def ds(1) by (rule lift_rule_cons[OF sp ws GS cS rule])+
qed

text \<open>The rule lifted over a subgoal of a theorem is a theorem:\<close>

lemma lift_rule_thm_inv:
  assumes G: "wtp G" "ibelow smax G" and sm: "-1 \<le> smax"
    and rule: "thm_inv (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and cs: "scons (tvars_thm stpairs S \<union> tvars_thm (th_tpairs (lift_rule G smax rule)) (th_prop (lift_rule G smax rule)))"
      "vtcons (vars_thm stpairs S \<union> vars_thm (th_tpairs (lift_rule G smax rule)) (th_prop (lift_rule G smax rule)))"
    and nnG: "\<forall>v\<in>vars G. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars G. 0 \<le> snd (fst v)"
  shows "thm_inv (th_maxidx (lift_rule G smax rule)) hr (th_tpairs (lift_rule G smax rule))
    (th_prop (lift_rule G smax rule))"
proof -
  let ?lr = "lift_rule G smax rule"
  obtain p G0 where sp: "lsplit G = (p, G0)" by (cases "lsplit G")
  have wr: "wt_thm (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)" and rm: "-1 \<le> th_maxidx rule"
    and nn: "\<forall>v\<in>vars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
      "\<forall>v\<in>tvars_thm (th_tpairs rule) (th_prop rule). 0 \<le> snd (fst v)"
    using rule by (simp_all add: thm_inv_def)
  have P: "e \<turnstile> th_prop rule : propT" for e using wr by (simp add: wt_thm_def wtpD(2))
  have "wt_thm (th_maxidx ?lr) hr (th_tpairs ?lr) (th_prop ?lr)" by (rule lift_rule_wt_thm[OF wr G rm])
  moreover have "-1 \<le> th_maxidx ?lr" using rm sm by (simp add: lift_rule_maxidx)
  moreover have "scons (tvars_thm (th_tpairs ?lr) (th_prop ?lr))" using cs(1) unfolding scons_def by blast
  moreover have "vtcons (vars_thm (th_tpairs ?lr) (th_prop ?lr))" using cs(2) unfolding vtcons_def by blast
  moreover have "\<forall>v\<in>vars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd (fst v)"
  proof
    fix v assume v: "v \<in> vars_thm (th_tpairs ?lr) (th_prop ?lr)"
    obtain x i T where vT: "v = ((x, i), T)" by (cases v) auto
    from lift_rule_vars[OF sp v[unfolded vT]] show "0 \<le> snd (fst v)"
    proof
      assume "((x, i), T) \<in> vars G"
      with nnG(1) show ?thesis by (force simp: vT)
    next
      assume "\<exists>T0. ((x, i - (smax + 1)), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule) \<and>
        T = foldr fun_type (ptys p) (incr_tvar (smax + 1) T0)"
      then obtain T0 where "((x, i - (smax + 1)), T0) \<in> vars_thm (th_tpairs rule) (th_prop rule)" by blast
      with nn(1) have "0 \<le> i - (smax + 1)" by force
      with sm show ?thesis by (simp add: vT)
    qed
  qed
  moreover have "\<forall>v\<in>tvars_thm (th_tpairs ?lr) (th_prop ?lr). 0 \<le> snd (fst v)"
  proof
    fix v assume v: "v \<in> tvars_thm (th_tpairs ?lr) (th_prop ?lr)"
    obtain a i S where vS: "v = ((a, i), S)" by (cases v) auto
    from lift_rule_tvars[OF sp P v[unfolded vS]] show "0 \<le> snd (fst v)"
    proof
      assume "((a, i), S) \<in> ttvars G"
      with nnG(2) show ?thesis by (force simp: vS)
    next
      assume "((a, i - (smax + 1)), S) \<in> tvars_thm (th_tpairs rule) (th_prop rule)"
      with nn(2) have "0 \<le> i - (smax + 1)" by force
      with sm show ?thesis by (simp add: vS)
    qed
  qed
  ultimately show ?thesis by (simp add: thm_inv_def)
qed

text \<open>The results of \<^const>\<open>biresolution\<close> of theorems are theorems (and their indices are not negative):\<close>

theorem biresolution_thm_inv:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
  shows "thm_inv (maxidx (br_env x)) (hs @ hyps rule) (br_tpairs x) (br_prop x) \<and> bres_inv x"
proof -
  from br res obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs, Bs, Bi, C) True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  note ir = rules[OF r]
  note c = compose_cond[OF d g state ir]
  let ?lr = "lift_rule goal (th_maxidx state) (rep rule)" and ?S = "list_implies (Bs @ [Bi]) C"
  have sS: "thm_inv (th_maxidx state) hs stpairs ?S" using state c(2,3) by simp
  have sm: "-1 \<le> th_maxidx state" using state by (simp add: thm_inv_def)
  have iB: "ibelow (th_maxidx state) Bi" using c(4) by (simp add: wt_thm_def)
  have nnB: "\<forall>v\<in>vars Bi. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars Bi. 0 \<le> snd (fst v)"
    using sS ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C]
    by (auto simp: thm_inv_def vars_thm_def tvars_thm_def vars_list_implies)
  have cs: "scons (tvars_thm stpairs ?S \<union> tvars_thm (th_tpairs ?lr) (th_prop ?lr))"
    "vtcons (vars_thm stpairs ?S \<union> vars_thm (th_tpairs ?lr) (th_prop ?lr))"
    using c(8,9) by (simp_all add: c(1))
  have lr: "thm_inv (th_maxidx ?lr) (hyps rule) (th_tpairs ?lr) (th_prop ?lr)"
    unfolding c(1) by (rule lift_rule_thm_inv[OF c(5) iB sm ir cs[unfolded c(1)] nnB])
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, ?S) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of (rep rule))) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using c(2,3) by (auto simp: pthm_of_def)
  show ?thesis
    by (rule bicompose_aux_thm_inv[OF ok rx cfg sS lr _ c(8,9) vl]) (use c(7) in simp)
qed

end


subsection \<open>Soundness\<close>

context pure_model
begin

text \<open>The results of \<^const>\<open>biresolution\<close> of valid theorems are valid.\<close>

theorem biresolution_valid:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "valid hs (th_tpairs state) (th_prop state)"
      "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> valid (hyps r) (th_tpairs (rep r)) (th_prop (rep r)) \<and>
      thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
  shows "valid (hs @ hyps rule) (br_tpairs x) (br_prop x)"
proof -
  from br res obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs, Bs, Bi, C) True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  from rules[OF r] have vr: "valid (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    and ir: "thm_inv (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))" by auto
  have wr: "wt_thm (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    using ir by (simp add: thm_inv_def)
  note c = compose_cond[OF d g state(2) ir]
  let ?lr = "lift_rule goal (th_maxidx state) (rep rule)"
  have vS: "valid hs stpairs (list_implies (Bs @ [Bi]) C)" using state(1) c(2,3) by simp
  have vl': "valid (hyps rule) (th_tpairs ?lr) (th_prop ?lr)"
    unfolding c(1) by (rule lift_rule_valid[OF vr wr c(5)])
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of (rep rule))) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using c(2,3) by (auto simp: pthm_of_def)
  show ?thesis
    by (rule bicompose_aux_valid[OF ok rx cfg vS c(4) vl' c(6) _ c(8) _ vl]) (use c(7,9) in simp_all)
qed

end


subsection \<open>Termination\<close>

context pure_sig
begin

text \<open>The evaluation of the result sequence of \<^const>\<open>biresolution\<close> to the list of its results.\<close>

inductive brevals :: "'u bops \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> ('u, 'r) rseq \<Rightarrow>
    (bres \<times> (bool \<times> 'r)) list \<Rightarrow> bool" for ops rep where
  Nil: "okT (brpull ops alg rep s) None \<Longrightarrow> brevals ops rep s []"
| Cons: "okT (brpull ops alg rep s) (Some (xr, s')) \<Longrightarrow> brevals ops rep s' xs \<Longrightarrow>
    brevals ops rep s (xr # xs)"

lemma brevals_skip:
  assumes "okT (brstep ops alg rep s) (RS_Skip s')" "brevals ops rep s' xs"
  shows "brevals ops rep s xs"
proof -
  have p: "okT (brpull ops alg rep s) y" if "okT (brpull ops alg rep s') y" for y
    using assms(1) that by (subst brpull.simps) force
  from assms(2) show ?thesis
  proof cases
    case Nil
    with p show ?thesis by (blast intro: brevals.Nil)
  next
    case (Cons xr s'' xs')
    with p show ?thesis by (blast intro: brevals.Cons)
  qed
qed

lemma brevals_App:
  assumes "bevals ops xq rs" "brevals ops rep xqq xs"
  shows "brevals ops rep (RQ_App r xq xqq) (map (\<lambda>x. (x, r)) rs @ xs)"
  using assms(1)
proof (induction rule: bevals.induct)
  case (Nil s)
  have "okT (brstep ops alg rep (RQ_App r s xqq)) (RS_Skip xqq)" using Nil by force
  from brevals_skip[OF this assms(2)] show ?case by simp
next
  case (Cons s r' s' rs)
  have "okT (brpull ops alg rep (RQ_App r s xqq)) (Some ((r', r), RQ_App r s' xqq))"
    using Cons(1) by (subst brpull.simps) force
  from brevals.Cons[OF this Cons.IH] show ?case by simp
qed

lemma brevals_det: "brevals ops rep s xs \<Longrightarrow> brevals ops rep s ys \<Longrightarrow> xs = ys"
proof (induction arbitrary: ys rule: brevals.induct)
  case (Nil s)
  from Nil.prems show ?case by cases (use Nil.hyps okT_det in force)+
next
  case (Cons s xr s' xs)
  from Cons.prems show ?case
  proof cases
    case Nil
    with Cons.hyps(1) okT_det show ?thesis by force
  next
    case (Cons xr' s'' ys')
    with Cons.hyps(1) okT_det have "xr' = xr" "s'' = s'" by force+
    with Cons Cons.IH show ?thesis by simp
  qed
qed

lemma brevals_brresult: "brevals ops rep s xs \<Longrightarrow> xr \<in> set xs \<Longrightarrow> brresult ops rep s xr"
  by (induction rule: brevals.induct) (auto intro: brresult.First brresult.Next)

text \<open>
  The results of the rules that pass the quick test are those of their compositions with the
  proof state, in order.
\<close>

definition brres :: "'u bops \<Rightarrow> ('r \<Rightarrow> thm_rep) \<Rightarrow> brctx \<Rightarrow> bool \<times> 'r \<Rightarrow>
    (bres \<times> (bool \<times> 'r)) list \<Rightarrow> bool" where
  "brres ops rep ctx r xs \<longleftrightarrow> (\<exists>xq rs. okT (compose ops alg ctx (fst r) (rep (snd r))) xq \<and>
    bevals ops xq rs \<and> map (\<lambda>x. (x, r)) rs = xs)"

lemma brevals_res:
  assumes "\<And>r. r \<in> set brules \<Longrightarrow> \<exists>xq rs. okT (compose ops alg ctx (fst r) (rep (snd r))) xq \<and> bevals ops xq rs"
  shows "\<exists>xs. brevals ops rep (res rep ctx brules) xs \<and>
    (\<forall>r\<in>set brules. brc_trace ctx \<or> could_bires (brc_test_hyps ctx) (brc_Hs ctx) (brc_B ctx) (fst r) (rep (snd r)) \<longrightarrow>
      (\<exists>ys. brres ops rep ctx r ys \<and> set ys \<subseteq> set xs))"
  using assms
proof (induction brules)
  case Nil
  have "okT (brpull ops alg rep RQ_Empty) None" by (subst brpull.simps) simp
  then show ?case by (auto intro: brevals.Nil)
next
  case (Cons r brules)
  obtain e rule where r: "r = (e, rule)" by (cases r)
  from Cons.IH Cons.prems obtain xs where xs: "brevals ops rep (res rep ctx brules) xs"
    and al: "\<forall>r\<in>set brules. brc_trace ctx \<or> could_bires (brc_test_hyps ctx) (brc_Hs ctx) (brc_B ctx) (fst r) (rep (snd r)) \<longrightarrow>
      (\<exists>ys. brres ops rep ctx r ys \<and> set ys \<subseteq> set xs)"
    by auto
  show ?case
  proof (cases "brc_trace ctx \<or> could_bires (brc_test_hyps ctx) (brc_Hs ctx) (brc_B ctx) e (rep rule)")
    case True
    from Cons.prems[of r] r obtain xq rs where c: "okT (compose ops alg ctx e (rep rule)) xq"
      and b: "bevals ops xq rs" by auto
    have "okT (brstep ops alg rep (RQ_Make ctx (e, rule) brules))
        (RS_Skip (RQ_App (e, rule) xq (res rep ctx brules)))"
      using c by simp
    from brevals_skip[OF this brevals_App[OF b xs]]
    have "brevals ops rep (res rep ctx (r # brules)) (map (\<lambda>x. (x, (e, rule))) rs @ xs)"
      using True r by simp
    moreover have "brres ops rep ctx r (map (\<lambda>x. (x, (e, rule))) rs)"
      using c b r by (auto simp: brres_def)
    ultimately show ?thesis using al r by (intro exI[of _ "map (\<lambda>x. (x, (e, rule))) rs @ xs"]) fastforce
  next
    case False
    with xs al r show ?thesis by (intro exI[of _ xs]) auto
  qed
qed

lemma count_prems_list_implies: "count_prems (list_implies Xs Y) = ilength Xs + count_prems Y"
proof (induction Xs)
  case (Cons X Xs)
  then show ?case by (subst count_prems.simps) (simp add: implies_def)
qed simp

lemma nprems_lift_rule: "nprems_of rule \<le> count_prems (th_prop (lift_rule G smax rule))"
proof -
  have "count_prems (th_prop (lift_rule G smax rule)) = ilength (strip_imp_prems (th_prop rule)) +
      count_prems (lift_all (smax + 1) G (strip_imp_concl (th_prop rule)))"
    by (simp add: lift_rule_def Let_def count_prems_list_implies ilength_eq)
  moreover have "nprems_of rule = ilength (strip_imp_prems (th_prop rule))"
    by (simp add: nprems_of_def count_prems_strip_imp)
  ultimately show ?thesis
    using count_prems_nonneg[of "lift_all (smax + 1) G (strip_imp_concl (th_prop rule))"] by simp
qed

text \<open>The composition of a rule with the proof state terminates with a finite sequence of results.\<close>

lemma compose_terminates:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rule: "thm_inv (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and er: "eres_flg \<Longrightarrow> 0 < nprems_of rule"
  shows "\<exists>xq rs. okT (compose (unify_ops cfg vl) alg
      (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal B Hs th) eres_flg rule) xq \<and>
    bevals (unify_ops cfg vl) xq rs"
proof -
  let ?lr = "lift_rule goal (th_maxidx state) rule"
  note c = compose_cond[OF d g state rule]
  have ns: "0 \<le> nprems_of rule" "nprems_of rule \<le> count_prems (th_prop ?lr)"
    using count_prems_nonneg nprems_lift_rule by (auto simp: nprems_of_def)
  have "\<exists>s rs. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of rule)) s \<and> bevals (unify_ops cfg vl) s rs"
    by (rule bicompose_aux_terminates[OF cfg c(4) c(6) _ c(8) _ ns er _ vl]) (use c(7,9) in simp_all)
  then show ?thesis by (simp add: compose_def pthm_of_def c(2,3))
qed

text \<open>
  The evaluation of the result sequence of \<^const>\<open>biresolution\<close> terminates, unless
  elim-resolution is requested for a rule without premises; the results of each rule that passes
  the quick test are those of its composition with the proof state.
\<close>

theorem biresolution_terminates:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow>
      thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r)) \<and> (e \<longrightarrow> 0 < nprems_of (rep r))"
  obtains stpairs Bs Bi C goal xs where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "brevals (unify_ops cfg vl) rep s0 xs"
    "\<And>r. r \<in> set brules \<Longrightarrow> trace \<or> could_bires (test_hyps Bi) (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<Longrightarrow>
      \<exists>ys. brres (unify_ops cfg vl) rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal
        (strip_assums_concl Bi) (strip_assums_hyp Bi) (test_hyps Bi)) r ys \<and> set ys \<subseteq> set xs"
proof -
  from br obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal"
    and s0: "s0 = res rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi)
      (strip_assums_hyp Bi) (test_hyps Bi)) brules"
    by (rule okT_biresolution)
  let ?ctx = "BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi) (strip_assums_hyp Bi) (test_hyps Bi)"
  have "\<exists>xs. brevals (unify_ops cfg vl) rep (res rep ?ctx brules) xs \<and>
      (\<forall>r\<in>set brules. brc_trace ?ctx \<or> could_bires (brc_test_hyps ?ctx) (brc_Hs ?ctx) (brc_B ?ctx) (fst r) (rep (snd r)) \<longrightarrow>
        (\<exists>ys. brres (unify_ops cfg vl) rep ?ctx r ys \<and> set ys \<subseteq> set xs))"
  proof (rule brevals_res)
    fix r assume r: "r \<in> set brules"
    obtain e rl where r': "r = (e, rl)" by (cases r)
    from rules[of e rl] r r' have "thm_inv (th_maxidx (rep rl)) (hyps rl) (th_tpairs (rep rl)) (th_prop (rep rl))"
      "e \<Longrightarrow> 0 < nprems_of (rep rl)" by auto
    from compose_terminates[OF d g cfg vl state this] r'
    show "\<exists>xq rs. okT (compose (unify_ops cfg vl) alg ?ctx (fst r) (rep (snd r))) xq \<and> bevals (unify_ops cfg vl) xq rs"
      by simp
  qed
  then obtain xs where xs: "brevals (unify_ops cfg vl) rep s0 xs"
    and al: "\<forall>r\<in>set brules. trace \<or> could_bires (test_hyps Bi) (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<longrightarrow>
        (\<exists>ys. brres (unify_ops cfg vl) rep ?ctx r ys \<and> set ys \<subseteq> set xs)"
    by (simp only: s0 brctx.sel) blast
  show thesis by (rule that[OF d g xs]) (use al in blast)
qed

end


subsection \<open>Every result passes the quick test\<close>

text \<open>
  With the fix \<open>thm-quick-eres\<close>, the quick test of \<^const>\<open>biresolution\<close> skips only rules
  without results: the instances of the problems of a result under a ground solution are equal,
  so that \<^const>\<open>could_unify\<close> holds for the conclusions and, for elim-resolution, for the
  first premise and the assumption that it is unified with.
\<close>

lemma head_of_incr_idx:
  "(\<And>x T. head_of t \<noteq> Var x T) \<Longrightarrow> head_of (incr_idx Ts inc lev t) = incr_idx Ts inc lev (head_of t)"
  by (induction t) auto

lemma could_unify_head_Const: "head_of t = Const a T \<Longrightarrow> could_unify t u \<longleftrightarrow>
    (case head_of u of Var _ _ \<Rightarrow> True | Abs _ _ _ \<Rightarrow> True | Const b _ \<Rightarrow> a = b \<and> matchrands t u | _ \<Rightarrow> False)"
  by (subst could_unify.simps) (simp split: pterm.split)

lemma could_unify_head_Free: "head_of t = Free a T \<Longrightarrow> could_unify t u \<longleftrightarrow>
    (case head_of u of Var _ _ \<Rightarrow> True | Abs _ _ _ \<Rightarrow> True | Free b _ \<Rightarrow> a = b \<and> matchrands t u | _ \<Rightarrow> False)"
  by (subst could_unify.simps) (simp split: pterm.split)

lemma could_unify_head_Bound: "head_of t = Bound i \<Longrightarrow> could_unify t u \<longleftrightarrow>
    (case head_of u of Var _ _ \<Rightarrow> True | Abs _ _ _ \<Rightarrow> True | Bound j \<Rightarrow> i = j \<and> matchrands t u | _ \<Rightarrow> False)"
  by (subst could_unify.simps) (simp split: pterm.split)

lemma could_unify_head_flex: "head_of t = Var x T \<or> head_of t = Abs a T b \<Longrightarrow> could_unify t u"
  by (subst could_unify.simps) (auto split: pterm.split)

text \<open>The quick test on a term whose indices are incremented holds for the term itself.\<close>

lemma could_unify_incr_idx:
  "could_unify (incr_idx Ts inc lev t) u \<Longrightarrow> could_unify t u"
  "matchrands (incr_idx Ts inc lev t) u \<Longrightarrow> matchrands t u"
proof (induction t u and t u rule: could_unify_matchrands.induct)
  case (1 t u)
  note p = "1.prems"
  show ?case
  proof (cases "head_of t")
    case (Const a T)
    then have h: "head_of (incr_idx Ts inc lev t) = Const a (incr_tvar inc T)"
      using head_of_incr_idx[of t Ts inc lev] by simp
    show ?thesis
    proof (cases "head_of u")
      case (Const b U)
      from p h Const have "matchrands (incr_idx Ts inc lev t) u" "a = b"
        by (simp_all add: could_unify_head_Const)
      with "1.IH"(1)[OF refl \<open>head_of t = Const a T\<close> Const] \<open>head_of t = Const a T\<close> Const
      show ?thesis by (simp add: could_unify_head_Const)
    qed (use p h Const in \<open>simp_all add: could_unify_head_Const\<close>)
  next
    case (Free a T)
    then have h: "head_of (incr_idx Ts inc lev t) = Free a (incr_tvar inc T)"
      using head_of_incr_idx[of t Ts inc lev] by simp
    show ?thesis
    proof (cases "head_of u")
      case (Free b U)
      from p h Free have "matchrands (incr_idx Ts inc lev t) u" "a = b"
        by (simp_all add: could_unify_head_Free)
      with "1.IH"(2)[OF refl \<open>head_of t = Free a T\<close> Free] \<open>head_of t = Free a T\<close> Free
      show ?thesis by (simp add: could_unify_head_Free)
    qed (use p h Free in \<open>simp_all add: could_unify_head_Free\<close>)
  next
    case (Bound i)
    then have h: "head_of (incr_idx Ts inc lev t) = Bound i"
      using head_of_incr_idx[of t Ts inc lev] by simp
    show ?thesis
    proof (cases "head_of u")
      case (Bound j)
      from p h Bound have "matchrands (incr_idx Ts inc lev t) u" "i = j"
        by (simp_all add: could_unify_head_Bound)
      with "1.IH"(3)[OF refl \<open>head_of t = Bound i\<close> Bound] \<open>head_of t = Bound i\<close> Bound
      show ?thesis by (simp add: could_unify_head_Bound)
    qed (use p h Bound in \<open>simp_all add: could_unify_head_Bound\<close>)
  next
    case (App f v)
    moreover have "head_of t \<noteq> f $ v" by (induction t) auto
    ultimately show ?thesis by blast
  qed (auto intro: could_unify_head_flex)
next
  case (2 f t g u)
  then show ?case by simp
qed simp_all


context pure_sig
begin

subsection \<open>Implications and quantifications at the top\<close>

lemma q_simps:
  "strip_assums_concl (Const STR ''Pure.imp'' U $ H $ B) = strip_assums_concl B"
  "strip_assums_concl (Const STR ''Pure.all'' U $ Abs a T b) = strip_assums_concl b"
  "strip_imp_concl (Const STR ''Pure.imp'' U $ H $ B) = strip_imp_concl B"
  "strip_imp_concl (Const STR ''Pure.all'' U $ Abs a T b) = Const STR ''Pure.all'' U $ Abs a T b"
  "strip_all_body (Const STR ''Pure.imp'' U $ H $ B) = Const STR ''Pure.imp'' U $ H $ B"
  "strip_all_body (Const STR ''Pure.all'' U $ Abs a T b) = strip_all_body b"
  "strip_assums_all params (Const STR ''Pure.all'' U $ Abs a T b) = strip_assums_all ((a, T) # params) b"
  "strip_assums_hyp_aux Hs (Const STR ''Pure.imp'' U $ H $ B) = strip_assums_hyp_aux (H # Hs) B"
  "strip_assums_hyp_aux Hs (Const STR ''Pure.all'' U $ Abs a T b) = strip_assums_hyp_aux (map (incr_boundvars 1) Hs) b"
  "count_prems (Const STR ''Pure.imp'' U $ H $ B) = 1 + count_prems B"
  "n \<noteq> 0 \<Longrightarrow> strip_assums_imp n Hs (Const STR ''Pure.imp'' U $ H $ B) = strip_assums_imp (n - 1) (H # Hs) B"
  by (subst strip_assums_concl.simps strip_imp_concl.simps strip_all_body.simps strip_assums_all.simps
      strip_assums_hyp_aux.simps count_prems.simps strip_assums_imp.simps; simp)+

lemma atomic_simps:
  "atomic t \<Longrightarrow> strip_assums_concl t = t"
  "atomic t \<Longrightarrow> strip_imp_concl t = t"
  "atomic t \<Longrightarrow> strip_all_body t = t"
  "atomic t \<Longrightarrow> strip_assums_hyp_aux Hs t = rev Hs"
  "atomic t \<Longrightarrow> count_prems t = 0"
  by (subst strip_assums_concl.simps strip_imp_concl.simps strip_all_body.simps
      strip_assums_hyp_aux.simps count_prems.simps; simp add: atomic_def)+


subsection \<open>The assumptions and conclusion of a subgoal with prefix \<open>p\<close>\<close>

lemma strip_assums_concl_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic t \<Longrightarrow> strip_assums_concl (lift_pre p t) = t"
proof (induction p)
  case (Cons i p)
  then show ?case by (cases i) (auto simp: q_simps)
qed (simp add: atomic_simps)

definition alls :: "litem list \<Rightarrow> bool" where
  "alls p \<longleftrightarrow> (\<forall>i\<in>set p. \<exists>c a T. i = LAll c a T)"

definition imps :: "litem list \<Rightarrow> bool" where
  "imps p \<longleftrightarrow> (\<forall>i\<in>set p. \<exists>c H. i = LImp c H)"

lemma imps_strip_imp_concl:
  "\<forall>i\<in>set q. litem_ok i \<Longrightarrow> dest_all (strip_imp_concl (lift_pre q t)) = None \<Longrightarrow> imps q"
proof (induction q)
  case (Cons i q)
  then show ?case by (cases i) (auto simp: q_simps imps_def)
qed (simp add: imps_def)

text \<open>The prefix of a subgoal that passes \<^const>\<open>test_hyps\<close>: no parameters after assumptions.\<close>

lemma test_hyps_split:
  assumes "lsplit Bi = (p, Bi0)" "test_hyps Bi"
  obtains ps hs where "p = ps @ hs" "alls ps" "imps hs"
proof -
  from lsplit_ok[OF assms(1)] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
    and at: "atomic Bi0" by blast+
  have "\<exists>ps hs. p = ps @ hs \<and> alls ps \<and> imps hs"
    if "\<forall>i\<in>set p. litem_ok i" "dest_all (strip_imp_concl (strip_all_body (lift_pre p Bi0))) = None" for p
    using that
  proof (induction p)
    case Nil
    then show ?case by (simp add: alls_def imps_def)
  next
    case (Cons i q)
    show ?case
    proof (cases i)
      case (LImp c H)
      with Cons.prems have "dest_all (strip_imp_concl (lift_pre (i # q) Bi0)) = None"
        by (auto simp: q_simps)
      from imps_strip_imp_concl[OF Cons.prems(1) this] have "imps (i # q)" .
      moreover have "alls []" by (simp add: alls_def)
      ultimately show ?thesis by (metis append_Nil)
    next
      case (LAll c a T)
      with Cons.prems have "dest_all (strip_imp_concl (strip_all_body (lift_pre q Bi0))) = None"
        by (auto simp: q_simps)
      with Cons.IH Cons.prems(1) obtain ps hs where "q = ps @ hs" "alls ps" "imps hs" by auto
      with LAll show ?thesis by (intro exI[of _ "i # ps"] exI[of _ hs]) (simp add: alls_def)
    qed
  qed
  then have "\<exists>ps hs. p = ps @ hs \<and> alls ps \<and> imps hs" using ok assms(2) Bi by (simp add: test_hyps_def)
  with that show thesis by blast
qed

lemma strip_all_body_alls:
  "alls ps \<Longrightarrow> \<forall>i\<in>set ps. litem_ok i \<Longrightarrow> dest_all t = None \<Longrightarrow> strip_all_body (lift_pre ps t) = t"
proof (induction ps)
  case Nil
  then show ?case by (subst strip_all_body.simps) simp
next
  case (Cons i ps)
  then show ?case by (cases i) (auto simp: q_simps alls_def)
qed

lemma strip_assums_all_alls:
  "alls ps \<Longrightarrow> \<forall>i\<in>set ps. litem_ok i \<Longrightarrow> dest_all t = None \<Longrightarrow>
    \<exists>params'. strip_assums_all params (lift_pre ps t) = (params', t)"
proof (induction ps arbitrary: params)
  case Nil
  then show ?case by (subst strip_assums_all.simps) simp
next
  case (Cons i ps)
  then show ?case by (cases i) (auto simp: q_simps alls_def)
qed

lemma strip_assums_hyp_aux_alls:
  "alls ps \<Longrightarrow> \<forall>i\<in>set ps. litem_ok i \<Longrightarrow> strip_assums_hyp_aux [] (lift_pre ps t) = strip_assums_hyp_aux [] t"
proof (induction ps)
  case (Cons i ps)
  then show ?case by (cases i) (auto simp: q_simps alls_def)
qed simp

lemma strip_assums_hyp_aux_imps:
  "imps hs \<Longrightarrow> \<forall>i\<in>set hs. litem_ok i \<Longrightarrow> atomic t \<Longrightarrow>
    strip_assums_hyp_aux acc (lift_pre hs t) = rev acc @ phyps hs"
proof (induction hs arbitrary: acc)
  case (Cons i hs)
  then show ?case by (cases i) (auto simp: q_simps imps_def)
qed (simp add: atomic_simps)

lemma count_prems_imps:
  "imps hs \<Longrightarrow> \<forall>i\<in>set hs. litem_ok i \<Longrightarrow> atomic t \<Longrightarrow> count_prems (lift_pre hs t) = of_nat (length hs)"
proof (induction hs)
  case (Cons i hs)
  then show ?case by (cases i) (auto simp: q_simps imps_def)
qed (simp add: atomic_simps)

lemma strip_assums_imp_imps:
  "imps hs \<Longrightarrow> \<forall>i\<in>set hs. litem_ok i \<Longrightarrow>
    strip_assums_imp (of_nat (length hs)) acc (lift_pre hs X) = (rev (phyps hs) @ acc, X)"
proof (induction hs arbitrary: acc)
  case Nil
  then show ?case by (subst strip_assums_imp.simps) simp
next
  case (Cons i hs)
  have "(of_nat (length (i # hs)) :: integer) \<noteq> 0" by (simp add: integer_eq_iff)
  with Cons show ?case by (cases i) (auto simp: q_simps imps_def)
qed

text \<open>
  For a subgoal that passes \<^const>\<open>test_hyps\<close>, elim-resolution with a premise lifted over it
  tries the assumptions of the subgoal with the unlifted premise.
\<close>

lemma assum_problems_test_hyps:
  assumes "lsplit Bi = (p, Bi0)" "test_hyps Bi" "0 < count_prems (strip_all_body Bi)"
    "assum_problems (count_prems (strip_all_body Bi)) (lift_pre p X) = (params, asms, concl)"
  shows "concl = X" "asms = strip_assums_hyp Bi"
proof -
  from lsplit_ok[OF assms(1)] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
    and at: "atomic Bi0" by blast+
  from test_hyps_split[OF assms(1,2)] obtain ps hs where p: "p = ps @ hs" "alls ps" "imps hs" .
  have okp: "\<forall>i\<in>set ps. litem_ok i" "\<forall>i\<in>set hs. litem_ok i" using ok p(1) by auto
  have hs: "hs \<noteq> []"
  proof
    assume "hs = []"
    with p okp at have "strip_all_body Bi = Bi0"
      using strip_all_body_alls[of ps Bi0] by (simp add: Bi atomic_def)
    with assms(3) at show False by (simp add: atomic_simps)
  qed
  then obtain c H hs' where hsc: "hs = LImp c H # hs'" using p(3) by (cases hs) (auto simp: imps_def)
  have da: "dest_all (lift_pre hs Y) = None" for Y using okp(2) hsc by auto
  have sab: "strip_all_body Bi = lift_pre hs Bi0"
    using strip_all_body_alls[OF p(2) okp(1) da] by (simp add: Bi p(1) lift_pre_append)
  have cp: "count_prems (strip_all_body Bi) = of_nat (length hs)"
    using count_prems_imps[OF p(3) okp(2) at] sab by simp
  from strip_assums_all_alls[OF p(2) okp(1) da, of "[]" X] obtain params' where
    sa: "strip_assums_all [] (lift_pre p X) = (params', lift_pre hs X)"
    by (auto simp: p(1) lift_pre_append)
  have "assum_problems (count_prems (strip_all_body Bi)) (lift_pre p X) = (params', phyps hs, X)"
    unfolding assum_problems_def cp sa using strip_assums_imp_imps[OF p(3) okp(2), of "[]" X] by simp
  with assms(4) have c: "concl = X" "asms = phyps hs" by simp_all
  have "strip_assums_hyp Bi = phyps hs"
    unfolding strip_assums_hyp_def Bi p(1) lift_pre_append
    using strip_assums_hyp_aux_alls[OF p(2) okp(1)] strip_assums_hyp_aux_imps[OF p(3) okp(2) at, of "[]"]
    by simp
  with c show "concl = X" "asms = strip_assums_hyp Bi" by simp_all
qed

end


subsection \<open>Completeness\<close>

context pure_sig
begin

text \<open>
  A result of the unification of a well-formed problem has a ground solution: its flex-flex
  pairs are smashed, and the canonical solution of the resulting environment solves the problem.
\<close>

lemma uresult_ground:
  assumes r: "uresult A env tus (El_R env' tps)" and si: "sinv A K X env (tdps tus)"
  obtains \<rho> \<sigma> where "cert_inst \<rho>" "wt_subst \<sigma>"
    "\<And>t u. (t, u) \<in> set tus \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<and> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T)"
proof -
  from uresultD(3)[OF r] obtain A' K' X' e0 where ff: "ffres A' K' X' env' tps" and fl: "fflex A' K' e0 env' tps"
    by blast
  from smash_flexflex_term[OF ff fl] obtain env'' where ds': "dstep env' (tdps tps) env'' []"
    and fv: "finv A' K' e0 env''" and wi'': "winv env'' X'" by blast
  have ds: "dstep env (tdps tus) env'' []" by (rule dstep_trans[OF uresultD(1)[OF r] ds'])
  have "ffres A' K' X' env'' []" using fv wi'' by (simp add: ffres_def finv_def)
  then have ei'': "einv A' K' env''" by (simp add: ffres_def)
  note c = canonical_solution[OF ei'' wi'']
  let ?\<rho> = "tsol0 (tyenv env'')" and ?\<sigma> = "esol (tsol0 (tyenv env'')) env''"
  have ext: "extends env env''" by (rule dstepD(1)[OF ds])
  have wi: "winv env X" and p: "\<forall>(rb, t, u)\<in>set (tdps tus). pok A env rb X t u"
    using si by (auto simp: sinv_def)
  have \<rho>0: "tsol (tyenv env) ?\<rho>" by (rule extends_tsol[OF c(5) ext])
  have w: "wt_env ?\<rho> env" "vinv ?\<rho> env X" using winvD[OF wi \<rho>0 c(4)] by blast+
  have dt: "dtyped ?\<rho> (tdps tus)" by (rule sinv_dtyped[OF si \<rho>0 c(4)])
  have vi: "vinv ?\<rho> env (X \<union> dvars (tdps tus))" by (rule ur_vinv_sub[OF w(2)]) (use sinv_dvars[OF si] in blast)
  note D = dstepD(2)[OF ds c(5) extends_refl w(1) dt vi]
  have "dsolved ?\<rho> ?\<sigma> (tdps tus)" using D c(1) by simp
  then have eq: "ap ?\<rho> ?\<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap ?\<rho> ?\<sigma> u" if "(t, u) \<in> set tus" for t u
    using that unfolding dsolved_tdps by blast
  have ty: "\<exists>e T. e \<turnstile> inst ?\<rho> t : T \<and> e \<turnstile> inst ?\<rho> u : T" if "(t, u) \<in> set tus" for t u
  proof -
    have "pok A env [] X t u" using p that by auto
    from pokD(9)[OF this \<rho>0 c(4)] show ?thesis by blast
  qed
  show thesis by (rule that[OF c(4) solutionD(3)[OF c(1)]]) (use eq ty in blast)
qed

text \<open>A ground solution of the closures of two terms over the parameters of a prefix:\<close>

lemma could_unify_abs_pre:
  assumes ok: "\<forall>i\<in>set p. litem_ok i" and wX: "wtp (lift_pre p X)" and wY: "wtp (lift_pre p Y)"
    and \<rho>: "cert_inst \<rho>" and \<sigma>: "wt_subst \<sigma>"
    and eq: "ap \<rho> \<sigma> (abs_pre p X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p Y)"
  shows "could_unify X Y"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (lparams p)" and ?e = "\<lambda>_::integer. propT"
  let ?T = "tsubst \<rho> (ptys p \<Rrightarrow> propT)"
  have ty: "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> inst \<rho> (abs_pre p Z) : ?T" if "wtp (lift_pre p Z)" for Z
    by (rule typing_inst[OF closure_typed(2)[OF ok that] cert_inst_inst_ok[OF \<rho>]])
  have i: "inst \<rho> (abs_pre p Z) = abs_list ?bs (inst \<rho> Z)" for Z
    by (simp add: abs_pre_abs_list inst_abs_list)
  have a: "ap \<rho> \<sigma> (abs_pre p Z) = abs_list ?bs (ap \<rho> \<sigma> Z)" for Z
    by (simp add: abs_pre_abs_list ap_abs_list)
  have eq': "ap \<rho> \<sigma> X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> Y"
  proof (rule conv_abs_list_inv)
    show "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> abs_list ?bs (ap \<rho> \<sigma> X) : ?T"
      using typing_ap[OF ty[OF wX] \<sigma>] a by simp
    show "(\<lambda>j. tsubst \<rho> (?e j)) \<turnstile> abs_list ?bs (ap \<rho> \<sigma> Y) : ?T"
      using typing_ap[OF ty[OF wY] \<sigma>] a by simp
    show "abs_list ?bs (ap \<rho> \<sigma> X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (ap \<rho> \<sigma> Y)" using eq a by simp
  qed
  from ty[OF wX] i obtain V where "pushes (\<lambda>j. tsubst \<rho> (?e j)) (map snd ?bs) \<turnstile> inst \<rho> X : V"
    by (auto elim: typing_abs_listE)
  with eq' show ?thesis by (intro could_unify_complete[OF \<sigma>])
qed

lemma bevals_det: "bevals ops s rs \<Longrightarrow> bevals ops s rs' \<Longrightarrow> rs = rs'"
proof (induction arbitrary: rs' rule: bevals.induct)
  case (Nil s)
  from Nil.prems show ?case
  proof cases
    case (Cons r2 s2 rs2)
    with Nil.hyps show ?thesis by auto
  qed simp
next
  case (Cons s r s' rs)
  note hyp = Cons.hyps(1) and IH = Cons.IH
  from Cons.prems show ?case
  proof cases
    case Nil
    with hyp show ?thesis by auto
  next
    case (Cons r2 s2 rs2)
    with hyp have "r2 = r" "s2 = s'" by auto
    with Cons IH show ?thesis by simp
  qed
qed

text \<open>
  Every result of the composition of a rule with the proof state passes the quick test of
  biresolution with \<^const>\<open>test_hyps\<close> (fix \<open>thm-quick-eres\<close>).
\<close>

lemma compose_result_could_bires:
  assumes d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rule: "thm_inv (th_maxidx rule) hr (th_tpairs rule) (th_prop rule)"
    and ok: "okT (compose (unify_ops cfg vl) alg
      (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal B' Hs th) e rule) xq"
    and bv: "bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
  shows "could_bires (test_hyps Bi) (strip_assums_hyp Bi) (strip_assums_concl Bi) e rule"
proof -
  note c = compose_cond[OF d g state rule]
  let ?lr = "lift_rule goal (th_maxidx state) rule"
  have ok': "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (th_maxidx state, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) True e
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of rule)) xq"
    using ok c(2,3) by (simp add: compose_def pthm_of_def)
  have l: "True \<Longrightarrow> lifted_over (th_maxidx state) Bi (th_prop ?lr) (nprems_of rule)" using c(7) by simp
  have v: "True \<Longrightarrow> vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm (th_tpairs ?lr) (th_prop ?lr))"
    using c(9) by simp
  obtain rAs B env where sp: "ok (strip_prems (nprems_of rule) [] (th_prop ?lr)) (rAs, B)"
    and pa: "pinv_all (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True e (th_tpairs ?lr) rAs B)"
    and rc: "rchar (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True e (th_tpairs ?lr) rAs B) x"
    using bicompose_aux_rchar[OF ok' bevals_results[OF bv x] cfg c(4) c(6) l c(8) v] by blast
  let ?sp = "call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True e (th_tpairs ?lr) rAs B"
  have sel: "sp_env ?sp = env" "sp_eres ?sp = e" "sp_rAs ?sp = rAs"
    "bc_dpairs (sp_ctx ?sp) = strip_assums2 B Bi # th_tpairs ?lr @ stpairs"
    "bc_nlift (sp_ctx ?sp) = count_prems (strip_all_body Bi) + (if e then -1 else 0)"
    by (simp_all add: call_spec_def Let_def)
  from rc obtain A na tus env' tps where its: "itsok ?sp A na tus"
    and ur: "ures (sp_env ?sp) tus (El_R env' tps)" by (auto simp: rchar_def)
  from itsok_pwf[OF its pa] obtain A0 K X where "finite X" "finite K" "sinv A0 K X (sp_env ?sp) (tdps tus)"
    by (auto simp: pwf_def)
  with uresD[OF ur] obtain \<rho> \<sigma> where \<rho>: "cert_inst \<rho>" and \<sigma>: "wt_subst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tus \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    by (metis uresult_ground)
  text \<open>The lifted rule.\<close>
  obtain p Bi0 where ls: "lsplit Bi = (p, Bi0)" by (cases "lsplit Bi")
  from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and pok: "\<forall>i\<in>set p. litem_ok i"
    and at: "atomic Bi0" by blast+
  let ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  let ?f = "incr_idx (ptys p) (th_maxidx state + 1) 0"
  have P: "th_prop ?lr = list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B))"
    unfolding c(1) by (rule lift_rule_prop[OF ls])
  have np: "nprems_of rule = ilength (map (lift_pre p) (map ?f ?As))"
    by (simp add: nprems_of_def count_prems_strip_imp ilength_eq)
  from sp have rAs: "rAs = rev (map (lift_pre p) (map ?f ?As))" and B: "B = lift_pre p (?f ?B)"
    unfolding P np strip_prems_list_implies by (simp_all add: return_def)
  have wl: "(\<forall>A\<in>set (map (lift_pre p) (map ?f ?As)). wtp A) \<and> wtp (lift_pre p (?f ?B))"
    using c(6) wtp_list_implies[of "map (lift_pre p) (map ?f ?As)" "map (lift_pre p) (map ?f ?As)"
        "lift_pre p (?f ?B)" "lift_pre p (?f ?B)"]
    unfolding P by (simp add: wt_thm_def)
  have BBi: "strip_assums2 B Bi = (abs_pre p (?f ?B), abs_pre p Bi0)"
    unfolding B Bi by (rule strip_assums2_lift_pre[OF pok at])
  have BBi_in: "set (bc_dpairs (sp_ctx ?sp)) \<subseteq> set tus"
    using its by (auto simp: itsok_def eres_prob_def)
  text \<open>The conclusions.\<close>
  have "(abs_pre p (?f ?B), abs_pre p Bi0) \<in> set tus" using BBi_in BBi sel(4) by force
  from sol[OF this] have "could_unify (?f ?B) Bi0"
    by (rule could_unify_abs_pre[OF pok conjunct2[OF wl] c(5)[unfolded Bi] \<rho> \<sigma>, rotated])
  then have cB: "could_unify (concl_of rule) (strip_assums_concl Bi)"
    using could_unify_incr_idx(1) strip_assums_concl_lift_pre[OF pok at] by (simp add: concl_of_def Bi)
  text \<open>The premise for elim-resolution.\<close>
  have "could_reshyp (test_hyps Bi) (strip_assums_hyp Bi) (prems_of rule)" if e: e
  proof -
    have "sp_eres ?sp" using e sel(2) by simp
    with its obtain n asm where n: "1 \<le> n" "nat_of_integer n \<le> length (asms_of ?sp)"
      and asm: "asm = asms_of ?sp ! (nat_of_integer n - 1)" and tus: "tus = eres_prob ?sp asm"
      unfolding itsok_def by blast
    have n1: "1 \<le> nat_of_integer n" using n(1) by (simp add: integer_reps)
    have asm_in: "asm \<in> set (asms_of ?sp)" using n(2) n1 asm by simp
    then have "rev (sp_rAs ?sp) \<noteq> []" by (auto simp: asms_of_def)
    then have "?As \<noteq> []" using sel(3) rAs by simp
    then obtain A1r As' where As: "?As = A1r # As'" by (cases ?As) auto
    show ?thesis
    proof (cases "test_hyps Bi")
      case False
      then show ?thesis using As by (simp add: prems_of_def)
    next
      case th: True
      obtain params asms concl where ap: "assum_problems (count_prems (strip_all_body Bi))
          (lift_pre p (?f A1r)) = (params, asms, concl)"
        by (cases "assum_problems (count_prems (strip_all_body Bi)) (lift_pre p (?f A1r))")
      have r: "rev (sp_rAs ?sp) = lift_pre p (?f A1r) # map (lift_pre p) (map ?f As')"
        using sel(3) rAs As by simp
      have nl: "bc_nlift (sp_ctx ?sp) + 1 = count_prems (strip_all_body Bi)" using sel(5) e by simp
      have aso: "asms_of ?sp = asms" unfolding asms_of_def r nl using ap by simp
      have ero: "eres_of ?sp = ER env params concl (rlist_abs params concl)
          (lift_pre p (?f A1r)) (map (lift_pre p) (map ?f As'))"
        unfolding eres_of_def r nl using ap sel(1) by simp
      have "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
      from assum_problems_length[OF ap this] have "ilength asms \<le> count_prems (strip_all_body Bi)" .
      moreover have "0 < ilength asms" using asm_in aso
        by (cases asms) (auto simp: ilength_eq integer_less_iff integer_of_nat.rep_eq)
      ultimately have "0 < count_prems (strip_all_body Bi)" by simp
      note apt = assum_problems_test_hyps[OF ls th this ap[unfolded Bi[symmetric]]]
      have "(rlist_abs params asm, rlist_abs params concl) \<in> set tus"
        using tus ero by (simp add: eres_prob_def)
      moreover have "wtp (lift_pre p (?f A1r))" using wl As by simp
      moreover have "asm \<in> set asms" using asm_in aso by simp
      ultimately have "could_unify concl asm"
        using could_unify_closure(2)[OF ap _ _ \<rho> \<sigma> sol] by blast
      then have "could_unify A1r asm" using apt(1) could_unify_incr_idx(1) by simp
      moreover have "asm \<in> set (strip_assums_hyp Bi)" using asm_in aso apt(2) by simp
      ultimately show ?thesis using As th by (auto simp: prems_of_def list_ex_iff)
    qed
  qed
  with cB show ?thesis by (auto simp: could_bires_def)
qed

text \<open>
  \<^const>\<open>biresolution\<close> enumerates all results of the composition of each rule with the proof
  state, by \<^const>\<open>bicompose_aux\<close> for the rule lifted over the subgoal: the rules that the quick
  test skips have none (@{thm [source] compose_result_could_bires}).
\<close>

theorem biresolution_complete:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and state: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow>
      thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r)) \<and> (e \<longrightarrow> 0 < nprems_of (rep r))"
  obtains stpairs Bs Bi C goal xs where "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of state i) goal" "brevals (unify_ops cfg vl) rep s0 xs"
    "\<And>e rule xq rs x. (e, rule) \<in> set brules \<Longrightarrow>
      okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C)
        True e (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq \<Longrightarrow>
      bevals (unify_ops cfg vl) xq rs \<Longrightarrow> x \<in> set rs \<Longrightarrow> (x, (e, rule)) \<in> set xs"
proof -
  from biresolution_terminates[OF assms] obtain stpairs Bs Bi C goal xs
    where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of state i) goal"
      and xs: "brevals (unify_ops cfg vl) rep s0 xs"
      and al: "\<And>r. r \<in> set brules \<Longrightarrow> trace \<or> could_bires (test_hyps Bi) (strip_assums_hyp Bi) (strip_assums_concl Bi) (fst r) (rep (snd r)) \<Longrightarrow>
        \<exists>ys. brres (unify_ops cfg vl) rep (BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal
          (strip_assums_concl Bi) (strip_assums_hyp Bi) (test_hyps Bi)) r ys \<and> set ys \<subseteq> set xs"
    by blast
  show thesis
  proof (rule that[OF d g xs])
    fix e rule xq rs x
    assume r: "(e, rule) \<in> set brules"
      and ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state) (stpairs, Bs, Bi, C)
        True e (pthm_of (lift_rule goal (th_maxidx state) (rep rule))) (nprems_of (rep rule))) xq"
      and bv: "bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
    from rules[OF r] have ru: "thm_inv (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
      by auto
    let ?ctx = "BRCtx trace match_flg state (stpairs, Bs, Bi, C) goal (strip_assums_concl Bi) (strip_assums_hyp Bi) (test_hyps Bi)"
    have okc: "okT (compose (unify_ops cfg vl) alg ?ctx e (rep rule)) xq" using ok by (simp add: compose_def)
    have t: "could_bires (test_hyps Bi) (strip_assums_hyp Bi) (strip_assums_concl Bi) e (rep rule)"
      by (rule compose_result_could_bires[OF d g cfg vl state ru okc bv x])
    from al[of "(e, rule)"] r t obtain ys xq' rs' where
      c: "okT (compose (unify_ops cfg vl) alg ?ctx e (rep rule)) xq'"
      and bv': "bevals (unify_ops cfg vl) xq' rs'" and ys: "map (\<lambda>x. (x, (e, rule))) rs' = ys"
      and sub: "set ys \<subseteq> set xs"
      by (auto simp: brres_def)
    from c okc have "xq' = xq" by auto
    with bv bv' have "rs' = rs" using bevals_det by blast
    with x ys sub show "(x, (e, rule)) \<in> set xs" by auto
  qed
qed

end

end
