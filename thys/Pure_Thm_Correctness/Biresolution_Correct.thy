section \<open>Correctness of \<open>biresolution\<close>\<close>

theory Biresolution_Correct
  imports Bicompose_Complete "Pure_Thm.Pure_Biresolution"
begin

text \<open>
  \<open>biresolution\<close> lifts each rule over the subgoal (\<^const>\<open>lift_rule\<close>) and composes it with the
  proof state by \<^const>\<open>bicompose_aux\<close>. The lifted rule has the shape that the theorems on
  \<^const>\<open>bicompose_aux\<close> assume (\<^const>\<open>lifted_over\<close>), its variables are those of the rule with
  their indices incremented above the proof state, and it is valid and well-typed if the rule
  is.
\<close>


subsection \<open>The syntax of lifted rules\<close>

lemma lift_all_aux_atomic: "atomic G \<Longrightarrow> lift_all_aux inc Ts G t = incr_indexes (rev Ts) inc t"
  by (cases "(inc, Ts, G, t)" rule: lift_all_aux.cases) (auto simp: atomic_def)

lemma lift_abs_aux_atomic: "atomic G \<Longrightarrow> lift_abs_aux inc Ts G t = incr_indexes (rev Ts) inc t"
  by (cases "(inc, Ts, G, t)" rule: lift_abs_aux.cases) (auto simp: atomic_def)

lemma lift_all_aux_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic G0 \<Longrightarrow>
    lift_all_aux inc Ts (lift_pre p G0) t = lift_pre p (incr_indexes (rev Ts @ ptys p) inc t)"
proof (induction p arbitrary: Ts)
  case Nil
  then show ?case by (simp add: lift_all_aux_atomic)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with Cons LImp show ?thesis by simp
  next
    case (LAll c a T)
    with Cons.prems obtain U where "c = Const STR ''Pure.all'' U" by auto
    with Cons LAll show ?thesis by simp
  qed
qed

lemma lift_abs_aux_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic G0 \<Longrightarrow>
    lift_abs_aux inc Ts (lift_pre p G0) t = abs_pre p (incr_indexes (rev Ts @ ptys p) inc t)"
proof (induction p arbitrary: Ts)
  case Nil
  then show ?case by (simp add: lift_abs_aux_atomic)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with Cons LImp show ?thesis by simp
  next
    case (LAll c a T)
    with Cons.prems obtain U where "c = Const STR ''Pure.all'' U" by auto
    with Cons LAll show ?thesis by simp
  qed
qed

lemma lift_all_lsplit:
  "lsplit G = (p, G0) \<Longrightarrow> lift_all inc G t = lift_pre p (incr_indexes (ptys p) inc t)"
  using lift_all_aux_lift_pre[of p G0 inc "[]" t] by (simp add: lift_all_def lsplit_lift_pre_iff)

lemma lift_abs_lsplit:
  "lsplit G = (p, G0) \<Longrightarrow> lift_abs inc G t = abs_pre p (incr_indexes (ptys p) inc t)"
  using lift_abs_aux_lift_pre[of p G0 inc "[]" t] by (simp add: lift_abs_def lsplit_lift_pre_iff)

lemma vars_incr_idx: "vars (incr_idx Ts inc lev t) = (\<lambda>(x, i). (x, i + inc)) ` vars t"
proof (induction Ts inc lev t rule: incr_idx.induct)
  case (1 Ts inc lev x i T)
  have "vars (combound u n k) = vars u" for u n k
    by (induction u n k rule: combound.induct) simp_all
  then show ?case by simp
qed auto

lemma vars_incr_indexes: "vars (incr_indexes Ts inc t) = (\<lambda>(x, i). (x, i + inc)) ` vars t"
  by (auto simp: incr_indexes_def vars_incr_idx)

lemma strip_imp_list_implies:
  "strip_imp_prems (list_implies As B) = As @ strip_imp_prems B"
  "strip_imp_concl (list_implies As B) = strip_imp_concl B"
  by (induction As) (subst strip_imp_prems.simps strip_imp_concl.simps; simp add: implies_def)+

lemma list_implies_strip_imp: "t = list_implies (strip_imp_prems t) (strip_imp_concl t)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    then obtain U where t: "t = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: dest_imp_Some)
    from less.IH[of B] AB show ?thesis
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps) (auto simp: t implies_def dest_size)
  next
    case None
    then show ?thesis
      by (subst strip_imp_prems.simps, subst strip_imp_concl.simps) simp
  qed
qed

lemma count_prems_strip_imp: "count_prems t = ilength (strip_imp_prems t)"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "dest_imp t")
    case (Some AB)
    then obtain A B where AB: "dest_imp t = Some (A, B)" by (cases AB) auto
    from less.IH[of B] AB dest_imp_size[OF AB] show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) (simp add: ilength_Cons)
  next
    case None
    then show ?thesis
      by (subst count_prems.simps, subst strip_imp_prems.simps) (simp add: ilength_eq)
  qed
qed

text \<open>A rule lifted over a subgoal of a proof state is lifted over it (\<^const>\<open>lifted_over\<close>).\<close>

lemma lift_rule_lifted_over:
  assumes "\<forall>x\<in>vars (th_prop rule). 0 \<le> snd x" "0 \<le> smax"
  shows "lifted_over smax G (th_prop (lift_rule G smax rule)) (nprems_of rule)"
proof -
  obtain p G0 where ls: "lsplit G = (p, G0)" by (cases "lsplit G")
  let ?inc = "smax + 1" and ?As = "strip_imp_prems (th_prop rule)" and ?B = "strip_imp_concl (th_prop rule)"
  let ?f = "incr_indexes (ptys p) ?inc"
  have P: "th_prop (lift_rule G smax rule) = list_implies (map (lift_pre p) (map ?f ?As)) (lift_pre p (?f ?B))"
    by (simp add: lift_rule_def Let_def lift_all_lsplit[OF ls] comp_def)
  have v: "\<forall>x\<in>vars X. 0 \<le> snd x" if "X \<in> insert ?B (set ?As)" for X
  proof -
    have "vars X \<subseteq> vars (th_prop rule)"
    proof -
      have "vars (list_implies As B) = (\<Union>A\<in>set As. vars A) \<union> vars B" for As B
        by (induction As) (auto simp: implies_def)
      with list_implies_strip_imp[of "th_prop rule"] that show ?thesis by (metis UnCI UN_I insert_iff subsetI)
    qed
    with assms(1) show ?thesis by blast
  qed
  have "\<forall>x\<in>vars (?f X). smax < snd x" if "X \<in> insert ?B (set ?As)" for X
    using v[OF that] by (auto simp: vars_incr_indexes)
  then have "\<forall>X\<in>insert (?f ?B) (set (map ?f ?As)). \<forall>x\<in>vars X. smax < snd x" by auto
  moreover have "nprems_of rule = ilength (map ?f ?As)"
    by (simp add: nprems_of_def count_prems_strip_imp ilength_eq)
  ultimately show ?thesis unfolding lifted_over_def using ls P by blast
qed

end
