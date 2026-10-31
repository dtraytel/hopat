section \<open>Correctness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Correct
  imports Bicompose_Sound Bicompose_Typing
begin

context csig
begin

text \<open>
  The results of \<open>bicompose_aux\<close> are the theorems obtained by pulling its lazy sequence
  (\<^const>\<open>bpull\<close>), one after the other.
\<close>

inductive bresult :: "'u bops \<Rightarrow> 'u bseq \<Rightarrow> bres \<Rightarrow> bool" for ops where
  First: "okT (bpull ops s) (Some (r, s')) \<Longrightarrow> bresult ops s r"
| Next: "okT (bpull ops s) (Some (r', s')) \<Longrightarrow> bresult ops s' r \<Longrightarrow> bresult ops s r"


subsection \<open>Rules\<close>

lemma strip_prems_list_implies:
  "strip_prems (ilength As) Hs (list_implies As B) = return (rev As @ Hs, B)"
proof (induction As arbitrary: Hs)
  case Nil
  then show ?case by (subst strip_prems.simps) simp
next
  case (Cons A As)
  have "ilength (A # As) \<noteq> 0" by (simp add: ilength_eq integer_eq_iff integer_of_nat.rep_eq)
  with Cons show ?case
    by (subst strip_prems.simps) (simp add: ilength_Cons implies_imp_type mk_implies_def)
qed

text \<open>
  A rule lifted over the subgoal \<open>Bi\<close> of a proof state with maximal index \<open>m\<close>
  (\<open>Thm.lift_rule\<close>): its \<open>n\<close> premises and its conclusion are lifted over the parameters and
  assumptions of \<open>Bi\<close>, and its variables have been incremented above \<open>m\<close>.
\<close>

definition lifted_over :: "integer \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> bool" where
  "lifted_over m Bi P n \<longleftrightarrow> (\<exists>p Bi0 As0 B0. lsplit Bi = (p, Bi0) \<and>
    P = list_implies (map (lift_pre p) As0) (lift_pre p B0) \<and> n = ilength As0 \<and>
    (\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x))"

lemma lifted_over_lifted_rule:
  assumes "lifted_over m Bi P n" "ok (strip_prems n [] P) (rAs, B)"
  shows "lifted_rule m Bi (rev rAs) B"
proof -
  from assms(1) obtain p Bi0 As0 B0 where ls: "lsplit Bi = (p, Bi0)"
    and P: "P = list_implies (map (lift_pre p) As0) (lift_pre p B0)" and n: "n = ilength As0"
    and v: "\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x"
    unfolding lifted_over_def by blast
  have "strip_prems n [] P = return (rev (map (lift_pre p) As0), lift_pre p B0)"
    using strip_prems_list_implies[of "map (lift_pre p) As0" "[]" "lift_pre p B0"] by (simp add: P n ilength_eq)
  with assms(2) have "rAs = rev (map (lift_pre p) As0)" "B = lift_pre p B0"
    by (simp_all add: return_def)
  with ls v show ?thesis unfolding lifted_rule_def by auto
qed


subsection \<open>Soundness\<close>

end

context wf_csig
begin

lemma bresult_rchar:
  assumes "bresult (unify_ops (bs_cfg sp) (bs_vl sp)) s r" "binv sp s"
    "cfg_alg (bs_cfg sp) = alg" "finite (bs_A sp)" "pinv_all sp"
  shows "rchar sp r"
  using assms(1,2)
proof (induction rule: bresult.induct)
  case (First s r s')
  then obtain r0 where "bpull (unify_ops (bs_cfg sp) (bs_vl sp)) s = Some r0" "snd r0 = TOk (Some (r, s'))"
    by (cases "bpull (unify_ops (bs_cfg sp) (bs_vl sp)) s") auto
  from bpull_binv[OF assms(3-5) this(1) refl this(2) First.prems] show ?case by simp
next
  case (Next s r' s' r)
  then obtain r0 where "bpull (unify_ops (bs_cfg sp) (bs_vl sp)) s = Some r0" "snd r0 = TOk (Some (r', s'))"
    by (cases "bpull (unify_ops (bs_cfg sp) (bs_vl sp)) s") auto
  from bpull_binv[OF assms(3-5) this(1) refl this(2) Next.prems] Next.IH show ?case by simp
qed

end

context bicompose_sem
begin

text \<open>
  The results of \<open>bicompose_aux\<close> for a valid proof state \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> and a valid rule
  are valid, if the problems of unification are well-typed.
\<close>

lemma bicompose_aux_valid_pinv:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "valid stpairs (list_implies (Bs @ [Bi]) C)" "wfp ar (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "valid rtpairs rprop" "wfp ar rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and typed: "\<And>env rAs B. ok (strip_prems nsubgoal [] rprop) (rAs, B) \<Longrightarrow>
      (incremented \<Longrightarrow> env = empty_env (max rmax smax)) \<Longrightarrow>
      (\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
        (empty_env (max rmax smax))) (Some env)) \<Longrightarrow>
      pinv_all (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
  shows "valid (br_tpairs r) (br_prop r)"
  using ok cfg finA
proof (cases rule: bicompose_aux_binv)
  case empty
  have "bpull (unify_ops cfg vl) BS_Empty = returnT None" by (subst bpull.simps) simp
  with res empty show ?thesis by (cases rule: bresult.cases) auto
next
  case (spec rAs B env)
  let ?sp = "call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have pa: "pinv_all ?sp" by (rule typed[OF spec(1-3)])
  have sel: "bs_cfg ?sp = cfg" "bs_vl ?sp = vl" "bs_A ?sp = A" by (simp_all add: call_spec_def Let_def)
  have "rchar ?sp r"
    by (rule bresult_rchar[of ?sp]) (use res spec(4)[OF pa] cfg finA pa sel in simp_all)
  moreover have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF spec(1)]) (use rule(2) in \<open>simp add: wfp_def\<close>)
  ultimately show ?thesis
    using rchar_valid[OF refl _ state] rule vl lifted_over_lifted_rule[OF _ spec(1)] by simp
qed

lemma wt_thm_wfp: "wt_thm ar A W m tps P \<Longrightarrow> wfp ar P"
  by (simp add: wt_thm_def wt_term_def wfp_def swf_tm_def)

lemma wt_thm_cong:
  assumes "wt_thm ar A W m tps P" "\<forall>x\<in>vars_thm tps P. W' x = W x"
  shows "wt_thm ar A W' m tps P"
proof -
  have c: "wt_term ar A W' m t T" if "wt_term ar A W m t T" "vars t \<subseteq> vars_thm tps P" for t T
    using that assms(2) has_type_vars[of W "[]" t T W'] by (auto simp: wt_term_def)
  from assms(1) have P: "wt_term ar A W m P propT" "cok P"
    and tps: "\<forall>(t, u)\<in>set tps. \<exists>T. wt_term ar A W m t T \<and> wt_term ar A W m u T"
    by (simp_all add: wt_thm_def)
  have "wt_term ar A W' m P propT" by (rule c[OF P(1)]) (auto simp: vars_thm_def)
  moreover have "\<forall>(t, u)\<in>set tps. \<exists>T. wt_term ar A W' m t T \<and> wt_term ar A W' m u T"
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    with tps obtain T where "wt_term ar A W m t T" "wt_term ar A W m u T" by blast
    moreover have "vars t \<subseteq> vars_thm tps P" "vars u \<subseteq> vars_thm tps P"
      using tu by (auto simp: vars_thm_def)
    ultimately show "\<exists>T. wt_term ar A W' m t T \<and> wt_term ar A W' m u T" using c by blast
  qed
  ultimately show ?thesis using P(2) by (simp add: wt_thm_def)
qed

text \<open>
  The main theorem: the results of \<open>bicompose_aux\<close> for a valid, well-typed proof state
  \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> with flex-flex pairs \<open>stpairs\<close> and maximal index \<open>smax\<close>, and a valid,
  well-typed rule with maximal index \<open>rmax\<close> and flex-flex pairs \<open>rtpairs\<close>, lifted over \<open>Bi\<close> if
  \<open>lifted\<close>, are valid. The proof state and the rule are typed by \<open>Ws\<close> and \<open>Wr\<close>, which agree on
  common variables if the rule is incremented (otherwise \<open>bicompose_aux\<close> unifies the types of
  common variables). The type variables of both are among \<open>A\<close>.
\<close>

theorem bicompose_aux_valid:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "valid stpairs (list_implies (Bs @ [Bi]) C)" "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "valid rtpairs rprop" "wt_thm ar A Wr rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
      "tcert alg A"
    and inc: "incremented \<Longrightarrow>
      \<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<inter> vars_thm rtpairs rprop. Ws x = Wr x"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "valid (br_tpairs r) (br_prop r)"
proof (rule bicompose_aux_valid_pinv[OF ok res cfg finA state(1) wt_thm_wfp[OF state(2)] state(3)
    rule(1) wt_thm_wfp[OF rule(2)] rule(3) vl])
  fix env rAs B
  assume sp: "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
    and e1: "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
    and e2: "\<not> incremented \<Longrightarrow> okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
      (empty_env (max rmax smax))) (Some env)"
  have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
    using lifted_over_lifted_rule[OF rule(3)[OF that] sp] by (auto simp: lifted_rule_def)
  show "pinv_all (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
  proof (cases incremented)
    case True
    let ?VS = "vars_thm stpairs (list_implies (Bs @ [Bi]) C)"
    define W where "W x = (if x \<in> ?VS then Ws x else Wr x)" for x
    have "wt_thm ar A W smax stpairs (list_implies (Bs @ [Bi]) C)"
      by (rule wt_thm_cong[OF state(2)]) (simp add: W_def)
    moreover have "wt_thm ar A W rmax rtpairs rprop"
      by (rule wt_thm_cong[OF rule(2)]) (use inc[OF True] in \<open>auto simp: W_def\<close>)
    moreover have "\<forall>x. tyA ar A (W x)" using A(3,4) by (simp add: W_def)
    ultimately show ?thesis
      using pinv_all_empty_env[OF _ _ sp lift A(1,2)] e1[OF True] A(5) by blast
  next
    case False
    show ?thesis by (rule pinv_all_unify_var_types[OF state(2) rule(2) sp lift A e2[OF False]])
  qed
qed

end

end
