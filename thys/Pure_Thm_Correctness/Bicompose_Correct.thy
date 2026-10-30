section \<open>Correctness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Correct
  imports Bicompose_Sound Bicompose_Typing
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

context bicompose_sem
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

text \<open>
  The results of \<open>bicompose_aux\<close> for a valid proof state \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> and a valid rule
  are valid, if the problems of unification are well-typed.
\<close>

theorem bicompose_aux_valid:
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
  have pa: "pinv_all ?sp" by (rule typed[OF spec(1)])
  have sel: "bs_cfg ?sp = cfg" "bs_vl ?sp = vl" "bs_A ?sp = A" by (simp_all add: call_spec_def Let_def)
  have "rchar ?sp r"
    by (rule bresult_rchar[of ?sp]) (use res spec(4)[OF pa] cfg finA pa sel in simp_all)
  moreover have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF spec(1)]) (use rule(2) in \<open>simp add: wfp_def\<close>)
  ultimately show ?thesis
    using rchar_valid[OF refl _ state] rule vl lifted_over_lifted_rule[OF _ spec(1)] by simp
qed

end

end
