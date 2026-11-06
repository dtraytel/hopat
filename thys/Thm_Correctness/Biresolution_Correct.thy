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



subsection \<open>Theorems\<close>

text \<open>
  The invariant of theorems with maximal index \<open>m\<close>: they are well-typed, type variables and
  variables with the same name have the same sort and type, and indices are nonnegative.
\<close>

definition thm_inv :: "integer \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "thm_inv m hs tps P \<longleftrightarrow> wt_thm m hs tps P \<and> -1 \<le> m \<and> scons (tvars_thm tps P) \<and> vtcons (vars_thm tps P) \<and>
    (\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v))"

lemma wt_thm_below:
  assumes "wt_thm m hs tps P"
  shows "v \<in> vars_thm tps P \<Longrightarrow> snd (fst v) \<le> m" "w \<in> tvars_thm tps P \<Longrightarrow> snd (fst w) \<le> m"
  using assms by (fastforce simp: wt_thm_def vars_thm_def tvars_thm_def ibelow_def)+

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
  let ?smax = "th_maxidx state" and ?S = "list_implies (Bs @ [Bi]) C"
  from rules[OF r] have vr: "valid (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    and ir: "thm_inv (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))" by auto
  have wr: "wt_thm (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    and rm: "-1 \<le> th_maxidx (rep rule)" and rn: "\<forall>v\<in>vars (th_prop (rep rule)). 0 \<le> snd (fst v)"
    using ir by (auto simp: thm_inv_def vars_thm_def)
  have ws0: "wt_thm ?smax hs (th_tpairs state) (th_prop state)" using state(2) by (simp add: thm_inv_def)
  note ds = dest_state_cprem_of[OF d g wtpD(2)[OF conjunct1[OF ws0[unfolded wt_thm_def]], of "\<lambda>_. propT"]]
  have ws: "wt_thm ?smax hs stpairs ?S" and vS: "valid hs stpairs ?S"
    using ws0 state(1) ds by simp_all
  have wB: "wtp Bi" "ibelow ?smax Bi"
    using ws wtp_list_implies[of "Bs @ [Bi]" "Bs @ [Bi]" C C] by (simp_all add: wt_thm_def)
  have GS: "vars Bi \<subseteq> vars_thm stpairs ?S" "ttvars Bi \<subseteq> tvars_thm stpairs ?S"
    using ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C]
    by (auto simp: vars_thm_def tvars_thm_def vars_list_implies)
  have cS: "scons (tvars_thm stpairs ?S)" "vtcons (vars_thm stpairs ?S)"
    using state(2) ds by (simp_all add: thm_inv_def)
  let ?lr = "lift_rule Bi ?smax (rep rule)"
  obtain p G0 where sp: "lsplit Bi = (p, G0)" by (cases "lsplit Bi")
  note cons = lift_rule_cons[OF sp ws GS cS ir]
  have vl': "valid (hyps rule) (th_tpairs ?lr) (th_prop ?lr)" by (rule lift_rule_valid[OF vr wr wB(1)])
  have wl: "wt_thm (th_maxidx ?lr) (hyps rule) (th_tpairs ?lr) (th_prop ?lr)"
    by (rule lift_rule_wt_thm[OF wr wB rm])
  have lov: "lifted_over ?smax Bi (th_prop ?lr) (nprems_of (rep rule))" by (rule lift_rule_lifted_over[OF rn])
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (?smax, stpairs, ?S) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of (rep rule))) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using ds by (auto simp: pthm_of_def)
  show ?thesis
    by (rule bicompose_aux_valid[OF ok rx cfg vS ws vl' wl _ cons vl]) (use lov in simp_all)
qed

end

end
