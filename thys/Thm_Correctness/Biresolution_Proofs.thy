section \<open>Biresolution of theorems with proofs\<close>

theory Biresolution_Proofs
  imports ZProof_Syntax
begin

text \<open>
  The proofs of the results of \<^const>\<open>biresolution\<close>, classic (\<^const>\<open>bres_proof\<close>) and tight
  (\<^const>\<open>bres_zproof\<close>), from the lifted proofs of the rule (\<^const>\<open>lift_rule_proof\<close>,
  \<^const>\<open>lift_rule_zproof\<close>) and the proof of the proof state, are valid and satisfy the
  invariants of the proofs of theorems again: the classic ones have non-negative indices
  (\<^const>\<open>prf_idx\<close>), the tight ones have no proof constants and non-negative indices
  (\<^const>\<open>zinv\<close>).
\<close>

subsection \<open>The proofs of the new theorems\<close>

text \<open>
  The classic and the tight proof of the new theorem of a result \<open>x\<close> of biresolution of the
  proof state \<open>st\<close> at subgoal \<open>i\<close> with the rule \<open>ru\<close>, from the proofs \<open>rp\<close> of the rule and
  \<open>sp\<close> of the proof state (\<open>Thm.bicompose_aux\<close> with the lifting of \<open>Thm.biresolution\<close>).
\<close>

definition bires_proof :: "thm_rep \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> thm_rep \<Rightarrow> bres \<Rightarrow> prf \<Rightarrow> prf \<Rightarrow> prf P" where
  "bires_proof st i e ru x rp sp = (case SOME d. okT (dest_state st i) d of (stpairs, Bs, Bi, C) \<Rightarrow>
    bres_proof st Bs (bres_nlift Bi e) True x (lift_rule_proof Bi (th_maxidx st) ru rp) sp)"

definition bires_zproof :: "ztypargs \<Rightarrow> thm_rep \<Rightarrow> integer \<Rightarrow> bool \<Rightarrow> thm_rep \<Rightarrow> bres \<Rightarrow> zproof \<Rightarrow> zproof \<Rightarrow>
    zproof Z" where
  "bires_zproof ta st i e ru x rp sp = (case SOME d. okT (dest_state st i) d of (stpairs, Bs, Bi, C) \<Rightarrow> do {
    lrp \<leftarrow> lift_rule_zproof ta Bi (th_maxidx st) ru rp;
    bres_zproof ta st Bs (bres_nlift Bi e) True (lift_rule Bi (th_maxidx st) ru) x lrp sp})"


subsection \<open>Preliminaries\<close>

context prf_sig
begin

lemma bres_proof_sel:
  "bres_proof st Bs nlift flatten x rprf sprf =
    bicompose_proof (br_env x) (th_maxidx st) flatten Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (nlift + 1) (ren_prf (na_ren (br_newas x)) rprf) sprf"
proof (cases x)
  case (BRes env tps P A na)
  then show ?thesis by (cases na) (simp add: bres_proof_def ren_prf_def)
qed

lemma bres_zproof_sel:
  "bres_zproof ta st Bs nlift flatten orule x rprf sprf = do {
     rprf' \<leftarrow> (case na_ren (br_newas x) of None \<Rightarrow> return rprf | Some r \<Rightarrow> zren_proof r (th_maxidx st) rprf);
     visible \<leftarrow> liftMZ (mapM (\<lambda>th. full_prop_of (th_tpairs th) (th_prop th)) [st, orule]);
     zbicompose_proof ta (br_env x) (th_maxidx st) flatten Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
       (na_n (br_newas x)) (nlift + 1) visible rprf' sprf}"
proof (cases x)
  case (BRes env tps P A na)
  then show ?thesis by (cases na) (simp add: bres_zproof_def)
qed

lemma zterm_of_zdec_pnn: "e \<turnstile> t : T \<Longrightarrow> pnn t \<Longrightarrow> \<exists>z. zterm_of ztargs t = return z \<and> zdec z = t"
  by (rule zterm_of_zdec) (fastforce simp: pnn_def tnn_def)+

text \<open>The subgoal of a theorem can be lifted over:\<close>

lemma zlift_ok_typed: "e \<turnstile> G : V \<Longrightarrow> pnn G \<Longrightarrow> zlift_ok G"
proof (induction G arbitrary: e V rule: zlift_ok.induct)
  case (1 c U A B)
  from "1.prems"(1) obtain TA TB where tA: "e \<turnstile> A : TA" and tB: "e \<turnstile> B : TB" by blast
  have p: "pnn A" "pnn B" using "1.prems"(2) by simp_all
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    from "1.IH"[OF True tB p(2)] zterm_of_zdec_pnn[OF tA p(1)] show ?thesis by simp
  qed simp
next
  case (2 c U a T t)
  from "2.prems"(1) obtain Tt where tt: "e\<langle>0:T\<rangle> \<turnstile> t : Tt" by blast
  have p: "tnn T" "pnn t" using "2.prems"(2) by simp_all
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    from "2.IH"[OF True tt p(2)] p(1) show ?thesis by (simp add: tnn_typ_of_ztyp_of ztyp_ok_ztyp_of)
  qed simp
qed simp_all

end


text \<open>Non-negative indices:\<close>

context prf_sig
begin

lemma pnn_Const [simp]: "pnn (Const c T) \<longleftrightarrow> tnn T"
  by (simp add: pnn_def)

lemma pnn_list_implies: "pnn (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. pnn A) \<and> pnn B"
  by (induction As) (auto simp: implies_def propT_def)

lemma pnn_noneg: "pnn t \<Longrightarrow> noneg t"
  by (fastforce simp: pnn_def tnn_def noneg_iff)

lemma pnn_iff: "pnn t \<longleftrightarrow> (\<forall>v\<in>vars t. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars t. 0 \<le> snd (fst v))"
  by (fastforce simp: pnn_def tnn_def ttvars_def)

lemma thm_inv_pnn:
  assumes "thm_inv m hs tps P"
  shows "pnn P" "\<forall>(t, u)\<in>set tps. pnn t \<and> pnn u"
  using assms by (auto simp: thm_inv_def vars_thm_def tvars_thm_def pnn_iff)

lemma set_term_vars [simp]: "set (term_vars t) = vars t"
  by (induction t) auto

lemma set_term_types [simp]: "set (term_types t) = typs t"
  by (induction t) auto

lemma tnn_typing: "e \<turnstile> t : T \<Longrightarrow> (\<forall>i. tnn (e i)) \<Longrightarrow> \<forall>U\<in>typs t. tnn U \<Longrightarrow> tnn T"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  have "\<forall>i. tnn ((e\<langle>0:T\<rangle>) i)" using Abs.prems(1) Abs.prems(2) by (simp add: shift_def)
  with Abs show ?case by simp
qed auto

text \<open>The visible propositions of the tight proofs:\<close>

lemma full_prop_of_pnn:
  assumes fp: "ok (full_prop_of tps P) p" and P: "pnn P"
    and tps: "\<forall>(t, u)\<in>set tps. pnn t \<and> pnn u \<and> closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)"
  shows "pnn p" "tvars_thm tps P \<subseteq> ttvars p"
proof -
  from fp obtain eqs where l: "list_all2 (\<lambda>tu eq. ok (mk_equals tu) eq) tps eqs" and p: "p = list_implies eqs P"
    by (auto simp: full_prop_of_def ok_mapM)
  have eq: "pnn eq \<and> ttvars t \<union> ttvars u \<subseteq> ttvars eq" if "(t, u) \<in> set tps" "ok (mk_equals (t, u)) eq" for t u eq
  proof -
    from tps that(1) obtain T where pt: "pnn t" "pnn u" and cl: "closed t" and ty: "\<forall>e. e \<turnstile> t : T" by blast
    have "fastype_of t = return T" by (rule fastype_of_closed[OF spec[OF ty] cl])
    with that(2) have e: "eq = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u"
      by (simp add: mk_equals_def return_def)
    have "tnn T" by (rule tnn_typing[OF spec[OF ty, of "\<lambda>_. propT"]]) (use pt(1) in \<open>simp_all add: propT_def pnn_def\<close>)
    with pt show ?thesis by (auto simp: e propT_def ttvars_def)
  qed
  have pe: "\<forall>A\<in>set eqs. pnn A"
  proof
    fix A assume "A \<in> set eqs"
    from list_all2_ex2[OF l this] obtain tu where "tu \<in> set tps" "ok (mk_equals tu) A" by blast
    with eq show "pnn A" by (cases tu) blast
  qed
  show "pnn p" using pe P by (simp add: p pnn_list_implies)
  show "tvars_thm tps P \<subseteq> ttvars p"
  proof
    fix v assume "v \<in> tvars_thm tps P"
    then consider "v \<in> ttvars P" | t u where "(t, u) \<in> set tps" "v \<in> ttvars t \<union> ttvars u"
      by (auto simp: tvars_thm_def)
    then show "v \<in> ttvars p"
    proof cases
      case 1
      then show ?thesis using ttvars_list_implies(2)[of P eqs] by (auto simp: p)
    next
      case 2
      from list_all2_ex1[OF l 2(1)] obtain A where "A \<in> set eqs" "ok (mk_equals (t, u)) A" by blast
      with eq[OF 2(1)] 2(2) ttvars_list_implies(1)[of A eqs P] show ?thesis by (auto simp: p)
    qed
  qed
qed

text \<open>The data of a result of biresolution:\<close>

lemma bres_inv_props:
  assumes "bres_inv r"
  shows "zenv_nn (br_env r)" "eneg (br_env r)" "tacyc (tyenv (br_env r))"
    "acyc (br_env r)" "closed_env (br_env r)" "\<forall>w\<in>evars (br_env r). 0 \<le> snd (fst w)"
    "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)). pnn A"
proof -
  let ?E = "br_env r"
  have b: "acyc ?E" "closed_env ?E" "tacyc (tyenv ?E)" "\<forall>(x, T)\<in>evars ?E. 0 \<le> snd x"
    "\<forall>p\<in>tvars_env (tyenv ?E). 0 \<le> snd (fst p)"
    "\<forall>x U u. vt_lookup (tenv ?E) x = Some (U, u) \<longrightarrow> (\<forall>p\<in>tvars U \<union> ttvars u. 0 \<le> snd (fst p))"
    "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)).
      (\<forall>v\<in>vars A. 0 \<le> snd (fst v)) \<and> (\<forall>p\<in>ttvars A. 0 \<le> snd (fst p))"
    using assms unfolding bres_inv_def by blast+
  show "acyc ?E" by (fact b(1))
  show "closed_env ?E" by (fact b(2))
  show "tacyc (tyenv ?E)" by (fact b(3))
  show ev: "\<forall>w\<in>evars ?E. 0 \<le> snd (fst w)" using b(4) by (simp add: case_prod_beta)
  have bn: "(x, U, u) \<in> bnds ?E" if "vt_lookup (tenv ?E) x = Some (U, u)" for x U u
    using that by (simp add: bnds_def)
  have val: "pnn u" if "vt_lookup (tenv ?E) x = Some (U, u)" for x U u
  proof -
    have "vars u \<subseteq> evars ?E" using bn[OF that] unfolding evars_def by blast
    with ev have "\<forall>v\<in>vars u. 0 \<le> snd (fst v)" by blast
    moreover have "\<forall>p\<in>ttvars u. 0 \<le> snd (fst p)" using b(6) that by blast
    ultimately show ?thesis by (simp add: pnn_iff)
  qed
  show "zenv_nn ?E" unfolding zenv_nn_def using b(5) val by (auto simp: pnn_def)
  have x: "0 \<le> snd x" if "vt_lookup (tenv ?E) x = Some (U, u)" for x U u
  proof -
    have "(x, U) \<in> evars ?E" using bn[OF that] unfolding evars_def by blast
    with ev show ?thesis by force
  qed
  show "eneg ?E" unfolding eneg_def
    using tyenv_ok_nn[OF b(5)] val x pnn_noneg integer_nonneg_ne_m1 by blast
  show "\<forall>A\<in>set (na_As (br_newas r) @ na_oldAs (br_newas r)). pnn A" using b(7) by (simp add: pnn_iff)
qed

lemma biresolution_setup:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
  obtains stpairs Bs Bi C rAs B env where
    "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)" "(eres_flg, rule) \<in> set brules"
    "stpairs = th_tpairs state" "th_prop state = list_implies (Bs @ [Bi]) C"
    "wt_thm (th_maxidx state) hs stpairs (list_implies (Bs @ [Bi]) C)" "pnn Bi"
    "thm_inv (th_maxidx (lift_rule Bi (th_maxidx state) (rep rule))) (hyps rule)
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) (th_prop (lift_rule Bi (th_maxidx state) (rep rule)))"
    "th_prop (lift_rule Bi (th_maxidx state) (rep rule)) = list_implies (rev rAs) B"
    "pinv_all (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B)"
    "rchar (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B) x"
    "lifted_rule (th_maxidx state) Bi (rev rAs) B"
    "bres_inv x" "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
proof -
  from br res obtain stpairs Bs Bi C goal where d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs, Bs, Bi, C) True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  have some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)"
    using d by (blast intro: okT_det)
  note ir = rules[OF r]
  note c = compose_cond[OF d g st ir]
  let ?lr = "lift_rule goal (th_maxidx state) (rep rule)" and ?S = "list_implies (Bs @ [Bi]) C"
  let ?smax = "th_maxidx state"
  have sS: "thm_inv ?smax hs stpairs ?S" using st c(2,3) by simp
  have sm: "-1 \<le> ?smax" using st by (simp add: thm_inv_def)
  have iB: "ibelow ?smax Bi" using c(4) by (simp add: wt_thm_def)
  have nnB: "\<forall>v\<in>vars Bi. 0 \<le> snd (fst v)" "\<forall>v\<in>ttvars Bi. 0 \<le> snd (fst v)"
    using sS ttvars_list_implies(1)[of Bi "Bs @ [Bi]" C]
    by (auto simp: thm_inv_def vars_thm_def tvars_thm_def vars_list_implies)
  have cs: "scons (tvars_thm stpairs ?S \<union> tvars_thm (th_tpairs ?lr) (th_prop ?lr))"
    "vtcons (vars_thm stpairs ?S \<union> vars_thm (th_tpairs ?lr) (th_prop ?lr))"
    using c(8,9) by (simp_all add: c(1))
  have lri: "thm_inv (th_maxidx ?lr) (hyps rule) (th_tpairs ?lr) (th_prop ?lr)"
    unfolding c(1) by (rule lift_rule_thm_inv[OF c(5) iB sm ir cs[unfolded c(1)] nnB])
  from xq obtain xq0 where ok: "okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True
      (?smax, stpairs, ?S) (stpairs, Bs, Bi, C) True eres_flg
      (th_maxidx ?lr, th_tpairs ?lr, th_prop ?lr) (nprems_of (rep rule))) xq0"
    and rx: "bresult (unify_ops cfg vl) xq0 x"
    using c(2,3) by (auto simp: pthm_of_def)
  have "thm_inv (maxidx (br_env x)) (hs @ hyps rule) (br_tpairs x) (br_prop x) \<and> bres_inv x"
    by (rule biresolution_thm_inv[OF br res cfg vl st]) (rule rules)
  then have bi: "bres_inv x" by blast
  obtain rAs B env where P: "th_prop ?lr = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env True match_flg ?smax stpairs Bs Bi C True eres_flg (th_tpairs ?lr) rAs B)"
    and rc: "rchar (call_spec cfg vl env True match_flg ?smax stpairs Bs Bi C True eres_flg (th_tpairs ?lr) rAs B) x"
    and lrl: "lifted_rule ?smax Bi (rev rAs) B"
    by (rule bicompose_aux_rchar[OF ok rx cfg c(4) c(6) c(7) c(8) c(9)]) blast
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = strip_assums2 B Bi"
  define ctx where "ctx = BCtx True match_flg True ?smax Bs Bi C (th_tpairs ?lr) nlift BBi (BBi # th_tpairs ?lr @ stpairs)"
  have sp': "call_spec cfg vl env True match_flg ?smax stpairs Bs Bi C True eres_flg (th_tpairs ?lr) rAs B =
      BSpec cfg vl env ctx rAs eres_flg"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  obtain A1o na tus env' tps Pre As0 n dps tps1 where its: "itsok (call_spec cfg vl env True match_flg ?smax stpairs Bs Bi C True eres_flg (th_tpairs ?lr) rAs B) A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth ctx A1o na (env', tps)) x"
    and rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps" and tus: "set (BBi # th_tpairs ?lr @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> True then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "Pre = [] \<and> A1o = None \<and> n = 0 \<or> (\<exists>A1. Pre = [A1] \<and> A1o = Some A1 \<and> 1 \<le> n)"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl asm. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
      nat_of_integer n \<le> length asms \<and> asm = asms ! (nat_of_integer n - 1) \<and>
      (rlist_abs params concl, rlist_abs params asm) \<in> set dps \<and>
      (rlist_abs params asm, rlist_abs params concl) \<in> set tus"
    by (rule rchar_data[OF sp' ctx_def nlift_def rc]) blast
  have "br_A x = A1o" using ad by (cases rule: addth_cases) auto
  with A1o rAs have bA: "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)" by auto
  have pB: "pnn Bi" using nnB by (simp add: pnn_iff)
  show thesis
    by (rule that[OF some r c(2,3) c(4)[unfolded c(2)[symmetric]] pB lri[unfolded c(1)] P[unfolded c(1)]
      pa[unfolded c(1)] rc[unfolded c(1)] lrl bi bA])
qed

lemma wtp_list_implies_mem: "wtp (list_implies As B) \<Longrightarrow> A \<in> set As \<Longrightarrow> wtp A"
  using wtp_list_implies[of As As B B] by simp


subsection \<open>Validity of the proofs\<close>

theorem biresolution_proof_valid:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
    and sp: "prf_valid ax (set hs) (th_tpairs state) sprf (th_prop state)" "prf_idx (\<lambda>i. 0 \<le> i) sprf"
    and rp: "prf_valid ax (set (hyps rule)) (th_tpairs (rep rule)) rprf (th_prop (rep rule))" "prf_idx (\<lambda>i. 0 \<le> i) rprf"
    and p: "bires_proof state i eres_flg (rep rule) x rprf sprf = returnW p"
  shows "prf_valid ax (set (hs @ hyps rule)) (br_tpairs x) p (br_prop x) \<and> prf_idx (\<lambda>i. 0 \<le> i) p"
proof -
  obtain stpairs Bs Bi C rAs B env where some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)"
    and r: "(eres_flg, rule) \<in> set brules" and tp: "stpairs = th_tpairs state"
    and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and ws: "wt_thm (th_maxidx state) hs stpairs (list_implies (Bs @ [Bi]) C)" and pB: "pnn Bi"
    and lri: "thm_inv (th_maxidx (lift_rule Bi (th_maxidx state) (rep rule))) (hyps rule)
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) (th_prop (lift_rule Bi (th_maxidx state) (rep rule)))"
    and P: "th_prop (lift_rule Bi (th_maxidx state) (rep rule)) = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B)"
    and rc: "rchar (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B) x"
    and lrl: "lifted_rule (th_maxidx state) Bi (rev rAs) B" and bi: "bres_inv x"
    by (rule biresolution_setup[OF br res cfg vl st rules])
  let ?smax = "th_maxidx state" and ?lr = "lift_rule Bi (th_maxidx state) (rep rule)"
  let ?rprf = "lift_rule_proof Bi ?smax (rep rule) rprf"
  have wr: "wt_thm (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    using rules[OF r] by (simp add: thm_inv_def)
  have wB: "wtp Bi" using ws wtp_list_implies_mem[of "Bs @ [Bi]" C Bi] by (simp add: wt_thm_def)
  have sm: "-1 \<le> ?smax" using st by (simp add: thm_inv_def)
  have lv: "prf_valid ax (set (hyps rule)) (th_tpairs ?lr) ?rprf (th_prop ?lr)"
    unfolding lift_rule_proof_def lift_rule_prems_def by (rule prf_valid_lift_proof[OF rp(1) wr wB])
  have la: "prf_above ?smax ?rprf" unfolding lift_rule_proof_def by (rule prf_above_lift_proof[OF rp(2)])
  have li: "prf_idx (\<lambda>i. 0 \<le> i) ?rprf" unfolding lift_rule_proof_def by (rule prf_nonneg_lift_proof[OF rp(2) sm])
  have p': "bicompose_proof (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas x)) ?rprf) sprf = returnW p"
    using p by (simp add: bires_proof_def some bres_proof_sel bres_nlift_def)
  have "prf_valid ax (set (hs @ hyps rule)) (br_tpairs x) p (br_prop x)"
  proof (rule bicompose_proof_valid[OF HOL.refl rc pa _ _ _ _ _ _ _ _ vl p'])
    show "prf_valid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" using sp(1) tp SP by simp
    show "wtp (list_implies (Bs @ [Bi]) C)" "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
      "\<forall>(t, u)\<in>set stpairs. ibelow ?smax t \<and> ibelow ?smax u"
      using ws by (auto simp: wt_thm_def)
    show "prf_valid ax (set (hyps rule)) (th_tpairs ?lr) ?rprf (list_implies (rev rAs) B)" using lv P by simp
    show "wtp (list_implies (rev rAs) B)" using lri P by (simp add: thm_inv_def wt_thm_def)
    show "True \<Longrightarrow> lifted_rule ?smax Bi (rev rAs) B" using lrl .
    show "True \<Longrightarrow> prf_above ?smax ?rprf" using la .
  qed
  moreover have "prf_idx (\<lambda>i. 0 \<le> i) p"
    by (rule prf_idx_bicompose_proof[OF p' _ sp(2)])
      (use li bres_inv_props[OF bi] in \<open>simp_all add: prf_idx_ren_prf\<close>)
  ultimately show ?thesis by blast
qed

text \<open>The visible propositions of the tight proofs:\<close>

lemma thm_inv_full_prop_of:
  assumes "thm_inv m hs tps P" "ok (full_prop_of tps P) fp"
  shows "pnn fp" "tvars_thm tps P \<subseteq> ttvars fp"
proof -
  have "\<forall>(t, u)\<in>set tps. pnn t \<and> pnn u \<and> closed t \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T)"
    using thm_inv_pnn(2)[OF assms(1)] assms(1) by (fastforce simp: thm_inv_def wt_thm_def)
  from full_prop_of_pnn[OF assms(2) thm_inv_pnn(1)[OF assms(1)] this] show "pnn fp" "tvars_thm tps P \<subseteq> ttvars fp"
    by blast+
qed

lemma visible_pnn:
  assumes "\<forall>t\<in>set vis. pnn t"
  shows "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T" "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
    "set (visible_tvars vis) = (\<Union>t\<in>set vis. ttvars t)"
proof -
  show "set (visible_tvars vis) = (\<Union>t\<in>set vis. ttvars t)" by (auto simp: visible_tvars_def ttvars_def)
  show "\<forall>(x, T)\<in>set (visible_vars vis). 0 \<le> snd x \<and> tnn T"
    using assms by (fastforce simp: visible_vars_def pnn_def dest: vars_typs)
  show "\<forall>(v, S)\<in>set (visible_tvars vis). 0 \<le> snd v"
    using assms by (fastforce simp: visible_tvars_def pnn_def tnn_def)
qed

theorem biresolution_zproof_valid:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and st: "thm_inv (th_maxidx state) hs (th_tpairs state) (th_prop state)"
    and rules: "\<And>e r. (e, r) \<in> set brules \<Longrightarrow> thm_inv (th_maxidx (rep r)) (hyps r) (th_tpairs (rep r)) (th_prop (rep r))"
    and sp: "zvalid ax (set hs) (th_tpairs state) sprf (th_prop state)" "zinv sprf"
    and rp: "zvalid ax (set (hyps rule)) (th_tpairs (rep rule)) rprf (th_prop (rep rule))" "zinv rprf"
    and p: "bires_zproof ztargs state i eres_flg (rep rule) x rprf sprf = return p"
  shows "zvalid ax (set (hs @ hyps rule)) (br_tpairs x) p (br_prop x) \<and> zinv p"
proof -
  obtain stpairs Bs Bi C rAs B env where some: "(SOME d. okT (dest_state state i) d) = (stpairs, Bs, Bi, C)"
    and r: "(eres_flg, rule) \<in> set brules" and tp: "stpairs = th_tpairs state"
    and SP: "th_prop state = list_implies (Bs @ [Bi]) C"
    and ws: "wt_thm (th_maxidx state) hs stpairs (list_implies (Bs @ [Bi]) C)" and pB: "pnn Bi"
    and lri: "thm_inv (th_maxidx (lift_rule Bi (th_maxidx state) (rep rule))) (hyps rule)
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) (th_prop (lift_rule Bi (th_maxidx state) (rep rule)))"
    and P: "th_prop (lift_rule Bi (th_maxidx state) (rep rule)) = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B)"
    and rc: "rchar (call_spec cfg vl env True match_flg (th_maxidx state) stpairs Bs Bi C True eres_flg
      (th_tpairs (lift_rule Bi (th_maxidx state) (rep rule))) rAs B) x"
    and lrl: "lifted_rule (th_maxidx state) Bi (rev rAs) B" and bi: "bres_inv x"
    and bA: "\<forall>C'. br_A x = Some C' \<longrightarrow> C' \<in> set (rev rAs)"
    by (rule biresolution_setup[OF br res cfg vl st rules])
  let ?smax = "th_maxidx state" and ?lr = "lift_rule Bi (th_maxidx state) (rep rule)"
  let ?prems = "map (lift_all (?smax + 1) Bi) (strip_imp_prems (th_prop (rep rule)))"
  note bp = bres_inv_props[OF bi]
  have ir: "thm_inv (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))" by (rule rules[OF r])
  have wr: "wt_thm (th_maxidx (rep rule)) (hyps rule) (th_tpairs (rep rule)) (th_prop (rep rule))"
    using ir by (simp add: thm_inv_def)
  have wB: "wtp Bi" using ws wtp_list_implies_mem[of "Bs @ [Bi]" C Bi] by (simp add: wt_thm_def)
  have sm: "-1 \<le> ?smax" using st by (simp add: thm_inv_def)
  from p obtain lrp where lz: "lift_rule_zproof ztargs Bi ?smax (rep rule) rprf = return lrp"
    and bz: "bres_zproof ztargs state Bs (bres_nlift Bi eres_flg) True ?lr x lrp sprf = return p"
    by (auto simp: bires_zproof_def some bindZ_eq_returnZ)
  from bz obtain rprf' vis
    where rr: "(case na_ren (br_newas x) of None \<Rightarrow> return lrp | Some r \<Rightarrow> zren_proof r ?smax lrp) = return rprf'"
    and vz: "liftMZ (mapM (\<lambda>th. full_prop_of (th_tpairs th) (th_prop th)) [state, ?lr]) = return vis"
    and zb: "zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
      (na_n (br_newas x)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) vis rprf' sprf = return p"
    by (auto simp: bres_zproof_sel bindZ_eq_returnZ bres_nlift_def)
  text \<open>The lifted proof of the rule:\<close>
  have zl: "zlift_proof ztargs Bi (?smax + 1) ?prems rprf = return lrp"
    using lz by (simp add: lift_rule_zproof_def lift_rule_prems_def)
  have lrP: "th_prop ?lr = list_implies ?prems (lift_all (?smax + 1) Bi (strip_imp_concl (th_prop (rep rule))))"
    by (simp add: lift_rule_def Let_def)
  have wP: "wtp (th_prop ?lr)" and pP: "pnn (th_prop ?lr)" using lri thm_inv_pnn(1)[OF lri] by (simp_all add: thm_inv_def wt_thm_def)
  have prem: "wtp A \<and> pnn A" if "A \<in> set ?prems" for A
    using wtp_list_implies_mem[OF wP[unfolded lrP] that] pP[unfolded lrP pnn_list_implies] that by blast
  have zlv: "zvalid ax (set (hyps rule)) (th_tpairs ?lr) lrp (th_prop ?lr)"
  proof (rule zvalid_zlift_proof[OF rp(1) wr wB _ _ _ _ _ zl])
    show "zconst_free rprf" "zprf_all zterm_ok ztyp_ok rprf" using rp(2) by (simp_all add: zinv_def)
    show "0 \<le> ?smax + 1" using sm by simp
    show "zlift_ok Bi" by (rule zlift_ok_typed[OF wtpD(2)[OF wB] pB])
    show "\<forall>A\<in>set ?prems. \<exists>z. zterm_of ztargs A = return z \<and> zdec z = A"
      using prem zterm_of_zdec_pnn wtpD(2) by blast
  qed
  have zli: "zinv lrp" by (rule zinv_zlift_proof[OF zl rp(2) _ pB]) (use sm prem in auto)
  have rren: "case na_ren (br_newas x) of None \<Rightarrow> rprf' = lrp | Some rn \<Rightarrow> zren_proof rn ?smax lrp = return rprf'"
    using rr by (cases "na_ren (br_newas x)") auto
  have zri: "zinv rprf'" using rren zli by (cases "na_ren (br_newas x)") (auto intro: zinv_zren_proof)
  text \<open>The visible propositions:\<close>
  from vz obtain fs fl where vis: "vis = [fs, fl]" and fs: "ok (full_prop_of (th_tpairs state) (th_prop state)) fs"
    and fl: "ok (full_prop_of (th_tpairs ?lr) (th_prop ?lr)) fl"
    by (auto simp: liftMZ_eq_returnZ ok_mapM list_all2_Cons1)
  note fS = thm_inv_full_prop_of[OF st fs] and fL = thm_inv_full_prop_of[OF lri fl]
  have pv: "\<forall>t\<in>set vis. pnn t" using fS(1) fL(1) by (simp add: vis)
  note vp = visible_pnn[OF pv]
  have tvis: "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm (th_tpairs ?lr) (list_implies (rev rAs) B)
      \<subseteq> set (visible_tvars vis)"
  proof -
    have "set (visible_tvars vis) = ttvars fs \<union> ttvars fl" using vp(3) by (simp add: vis)
    with fS(2) fL(2) tp SP P show ?thesis by auto
  qed
  text \<open>Composition:\<close>
  have pS: "pnn (list_implies (Bs @ [Bi]) C)" using thm_inv_pnn(1)[OF st] SP by simp
  have "zvalid ax (set (hs @ hyps rule)) (br_tpairs x) p (br_prop x)"
  proof (rule zbicompose_proof_valid[OF HOL.refl rc pa _ _ _ _ _ _ _ _ _ _ vl _ rren _ _ _ _ bp(2) _ zb])
    show "zvalid ax (set hs) stpairs sprf (list_implies (Bs @ [Bi]) C)" using sp(1) tp SP by simp
    show "wtp (list_implies (Bs @ [Bi]) C)" "ibelow ?smax (list_implies (Bs @ [Bi]) C)"
      "\<forall>(t, u)\<in>set stpairs. ibelow ?smax t \<and> ibelow ?smax u"
      using ws by (auto simp: wt_thm_def)
    show "zvalid ax (set (hyps rule)) (th_tpairs ?lr) lrp (list_implies (rev rAs) B)" using zlv P by simp
    show "wtp (list_implies (rev rAs) B)" using wP P by simp
    show "True \<Longrightarrow> lifted_rule ?smax Bi (rev rAs) B" using lrl .
    show "noneg (list_implies (rev rAs) B)" using pP P by (simp add: pnn_noneg)
    show "noneg (list_implies (Bs @ [Bi]) C)" using pS by (simp add: pnn_noneg)
    show "\<forall>A\<in>set (na_As (br_newas x) @ na_oldAs (br_newas x)). noneg A" using bp(7) by (simp add: pnn_noneg)
    show "-1 \<le> ?smax" by (rule sm)
    show "vis \<noteq> []" by (simp add: vis)
    show "\<forall>(x, T)\<in>set (visible_vars vis). snd x \<noteq> -1" using vp(1) by (fastforce simp: integer_nonneg_ne_m1)
    show "\<forall>(v, S)\<in>set (visible_tvars vis). snd v \<noteq> -1" using vp(2) by (fastforce simp: integer_nonneg_ne_m1)
    show "tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm (th_tpairs ?lr) (list_implies (rev rAs) B)
        \<subseteq> set (visible_tvars vis)" by (rule tvis)
    show "\<forall>h\<in>set (hs @ hyps rule). closed h" using ws wr by (auto simp: wt_thm_def dest: wtpD(1))
  qed
  moreover have "zinv p"
  proof (rule zinv_zbicompose_proof[OF zb zri sp(2) bp(3) bp(1) vp(1,2)])
    show "\<forall>t\<in>set (Bs @ na_As (br_newas x) @ na_oldAs (br_newas x)). pnn t"
      using bp(7) pS by (auto simp: pnn_list_implies)
    show "\<forall>C'. br_A x = Some C' \<longrightarrow> pnn C'" using bA pP P by (auto simp: pnn_list_implies)
  qed
  ultimately show ?thesis by blast
qed

end

end
