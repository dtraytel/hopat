section \<open>Termination and Completeness of \<open>biresolution\<close>\<close>

theory Biresolution_Complete
  imports "Thm_Soundness.Biresolution_Sound" Bicompose_Complete
begin

text \<open>
  The evaluation of the sequence of results of \<open>biresolution\<close> terminates, and it enumerates all
  results of the compositions of the rules that pass its quick test, for theorems whose
  variables have one type for each name.
\<close>

subsection \<open>Termination\<close>

context pure_sig_gen
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

end

context pure_sig
begin

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
  proof -
    interpret bc: bicompose_call alg ar ctab cfg vl True match_flg True "th_maxidx state" stpairs Bs Bi C
      True eres_flg "th_maxidx ?lr" "th_tpairs ?lr" "th_prop ?lr" "nprems_of rule" hs hr
      by unfold_locales (use cfg c(4,6-9) vl in simp_all)
    show ?thesis by (rule bc.bicompose_aux_terminates[OF ns er]) simp
  qed
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


context pure_sig_gen
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
  assumes r: "uresult_flex A env tus (El_R env' tps)" and si: "sinv A K X env (tdps tus)"
  obtains \<rho> \<sigma> where "cert_inst \<rho>" "wt_subst \<sigma>"
    "\<And>t u. (t, u) \<in> set tus \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u \<and> (\<exists>e T. e \<turnstile> inst \<rho> t : T \<and> e \<turnstile> inst \<rho> u : T)"
proof -
  from uresult_flexD(3)[OF r] obtain A' K' X' e0 where ff: "ffres A' K' X' env' tps" and fl: "fflex A' K' e0 env' tps"
    by blast
  from smash_flexflex_term[OF ff fl] obtain env'' where ds': "dstep env' (tdps tps) env'' []"
    and fv: "finv A' K' e0 env''" and wi'': "winv env'' X'" by blast
  have ds: "dstep env (tdps tus) env'' []" by (rule dstep_trans[OF uresult_flexD(1)[OF r] ds'])
  have "ffres A' K' X' env'' []" using fv wi'' by (simp add: ffres_def finv_def)
  then have ei'': "einv A' K' env''" by (simp add: ffres_def)
  note c = canonical_solution[OF ei'' wi'']
  let ?\<rho> = "tsol0 (tyenv env'')" and ?\<sigma> = "esol (tsol0 (tyenv env'')) env''"
  have ext: "extends env env''" by (rule dstepD(1)[OF ds])
  have wi: "winv env X" and p: "\<forall>(rb, t, u)\<in>set (tdps tus). upok A env rb X t u"
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
    have "upok A env [] X t u" using p that by auto
    from upokD(9)[OF this \<rho>0 c(4)] show ?thesis by blast
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
  with ures_flex[OF ur] obtain \<rho> \<sigma> where \<rho>: "cert_inst \<rho>" and \<sigma>: "wt_subst \<sigma>"
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
