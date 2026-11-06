section \<open>Soundness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Sound
  imports Bicompose_Norm
begin

text \<open>
  The theorems produced by \<open>bicompose_aux\<close> from a valid proof state and a valid rule are
  valid. An instance of a result is extended to a solution of the environment of the unifier;
  at this solution, the instances of the proof state and of the renamed rule hold, the
  conclusion of the rule implies the subgoal, and the new premises imply the renamed premises
  of the rule.
\<close>

subsection \<open>Well-typed propositions\<close>


context pure_sig
begin

definition wtp :: "pterm \<Rightarrow> bool" where
  "wtp A \<longleftrightarrow> closed A \<and> (\<forall>e. e \<turnstile> A : propT)"

lemma wtpI: "closed A \<Longrightarrow> e \<turnstile> A : propT \<Longrightarrow> wtp A"
  unfolding wtp_def using typing_closed by blast

lemma wtpD: "wtp A \<Longrightarrow> closed A" "wtp A \<Longrightarrow> e \<turnstile> A : propT"
  unfolding wtp_def by blast+

lemma gterm_ap_wtp: "wtp A \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> gterm (ap \<rho> \<sigma> A) propT"
  using gterm_ap[of \<rho> \<sigma> A _ propT] by (simp add: wtp_def)

lemma wtp_list_implies:
  "wtp (list_implies As B) \<Longrightarrow> (\<forall>A\<in>set As. wtp A) \<and> wtp B"
  using typing_list_impliesD[of _ As B]
  by (auto simp: wtp_def closed_def loose_bvar_list_implies)

lemma wtp_list_impliesI:
  "\<forall>A\<in>set As. wtp A \<Longrightarrow> wtp B \<Longrightarrow> (As \<noteq> [] \<longrightarrow> cert_typ alg ar imp_type) \<Longrightarrow> wtp (list_implies As B)"
  by (auto simp: wtp_def closed_def loose_bvar_list_implies intro!: typing_list_impliesI)

lemma ibelow_simps:
  "ibelow m (s $ t) \<longleftrightarrow> ibelow m s \<and> ibelow m t"
  "ibelow m (Abs a T t) \<longleftrightarrow> (\<forall>p\<in>tvars T. snd (fst p) \<le> m) \<and> ibelow m t"
  by (auto simp: ibelow_def)

lemma ibelow_list_implies [simp]:
  "ibelow m (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. ibelow m A) \<and> ibelow m B"
  by (induction As) (auto simp: ibelow_def implies_imp_type imp_type_def propT_def)

lemma ibelow_spine_hyps: "ibelow m t \<Longrightarrow> H \<in> set (spine_hyps t) \<Longrightarrow> ibelow m H"
proof (induction t rule: spine_hyps.induct)
  case (1 t)
  show ?case
  proof (cases "dest_imp t")
    case (Some HB)
    then obtain H' B where HB: "dest_imp t = Some (H', B)" by (cases HB) auto
    with "1.prems" "1.IH"(2)[OF HB refl] show ?thesis
      by (subst (asm) spine_hyps.simps) (auto simp: dest_imp_Some ibelow_simps)
  next
    case None
    show ?thesis
    proof (cases "dest_all t")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases aTb) auto
      with "1.prems" "1.IH"(1)[OF None aTb refl refl] None show ?thesis
        by (subst (asm) spine_hyps.simps) (auto simp: dest_all_Some ibelow_simps)
    next
      case None': None
      with "1.prems" None show ?thesis by (subst (asm) spine_hyps.simps) simp
    qed
  qed
qed

lemma ibelow_lift_pre: "ibelow m (lift_pre p X) \<Longrightarrow> ibelow m X"
  by (induction p X rule: lift_pre.induct) (auto simp: ibelow_simps)

lemma ibelow_phyps:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> ibelow m (lift_pre p X) \<Longrightarrow> H \<in> set (phyps p) \<Longrightarrow> ibelow m H"
  using ibelow_spine_hyps[of m "lift_pre p X" H] by (simp add: spine_hyps_lift_pre)


subsection \<open>Lifted rules\<close>

text \<open>
  The premises of a rule lifted over the subgoal \<open>Bi\<close> of a proof state with maximal index \<open>m\<close>:
  the variables of the rule have been incremented above \<open>m\<close>.
\<close>

definition lifted_rule :: "integer \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "lifted_rule m Bi As B \<longleftrightarrow> (\<exists>p Bi0 As0 B0. lsplit Bi = (p, Bi0) \<and> As = map (lift_pre p) As0 \<and>
    B = lift_pre p B0 \<and> (\<forall>X\<in>insert B0 (set As0). \<forall>v\<in>vars X. m < snd (fst v)))"

lemma lifted_rule_Cons:
  assumes "lifted_rule m Bi (A # As) B"
  shows "lifted_rule m Bi As B"
proof -
  from assms obtain p Bi0 As0 B0 where "lsplit Bi = (p, Bi0)" "A # As = map (lift_pre p) As0"
    "B = lift_pre p B0" "\<forall>X\<in>insert B0 (set As0). \<forall>v\<in>vars X. m < snd (fst v)"
    unfolding lifted_rule_def by (elim exE conjE) simp
  then show ?thesis
    unfolding lifted_rule_def by (intro exI[of _ p] exI[of _ Bi0] exI[of _ "tl As0"] exI[of _ B0]) (cases As0; auto)
qed

lemma lifted_rule_lift_pre:
  assumes "lifted_rule m Bi As0 B"
  obtains p Bi0 As0' B0 where "Bi = lift_pre p Bi0" "\<forall>i\<in>set p. litem_ok i" "atomic Bi0"
    "As0 = map (lift_pre p) As0'" "B = lift_pre p B0"
    "\<forall>X\<in>insert B0 (set As0'). \<forall>v\<in>vars X. m < snd (fst v)"
  using assms lsplit_ok unfolding lifted_rule_def by blast

text \<open>Renaming the variables of a lifted premise:\<close>

lemma rsubst_Nil [simp]: "rsubst m [] \<sigma> = \<sigma>"
  by (auto simp: rsubst_def ren_name_def fun_eq_iff)

lemma ap_rsubst_id:
  "\<forall>v\<in>vars t. snd (fst v) \<le> m \<or> ren_name tab (fst (fst v)) = fst (fst v) \<Longrightarrow>
    ap \<rho> (rsubst m tab \<sigma>) t = ap \<rho> \<sigma> t"
  unfolding ap_def by (rule vsubst_rsubst_id) (auto simp: vars_inst)

lemma aconv_lift_pre_ren:
  assumes "\<forall>v\<in>pvars p. snd (fst v) \<le> m" "\<forall>v\<in>vars X. m < snd (fst v)"
  shows "aconv_term (ap \<rho> \<sigma> (lift_pre p (ren_term r X))) (ap \<rho> (rsubst m (fst r) \<sigma>) (lift_pre p X))"
  using assms(1)
proof (induction p)
  case Nil
  have "aconv_term (vsubst \<sigma> (ren_term r (inst \<rho> X))) (vsubst (rsubst m (fst r) \<sigma>) (inst \<rho> X))"
    by (rule aconv_ren_term) (use assms(2) in \<open>auto simp: vars_inst\<close>)
  then show ?case by (simp add: ap_def inst_ren_term)
next
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    have "ap \<rho> (rsubst m (fst r) \<sigma>) c = ap \<rho> \<sigma> c" "ap \<rho> (rsubst m (fst r) \<sigma>) H = ap \<rho> \<sigma> H"
      using Cons.prems LImp by (auto intro!: ap_rsubst_id)
    with Cons LImp show ?thesis by simp
  next
    case (LAll c a T)
    have "ap \<rho> (rsubst m (fst r) \<sigma>) c = ap \<rho> \<sigma> c"
      using Cons.prems LAll by (auto intro!: ap_rsubst_id)
    with Cons LAll show ?thesis by simp
  qed
qed

lemma loose_bvar_lift_pre_ren [simp]:
  "loose_bvar (lift_pre p (ren_term r X)) k \<longleftrightarrow> loose_bvar (lift_pre p X) k"
  by (induction p X arbitrary: k rule: lift_pre.induct) auto

lemma typing_lift_pre_ren [simp]: "e \<turnstile> lift_pre p (ren_term r X) : T \<longleftrightarrow> e \<turnstile> lift_pre p X : T"
  by (induction p X arbitrary: e T rule: lift_pre.induct) auto

lemma wtp_lift_pre_ren: "wtp (lift_pre p (ren_term r X)) \<longleftrightarrow> wtp (lift_pre p X)"
  by (simp add: wtp_def closed_def)

end


subsection \<open>The new premises\<close>

context pure_valuation
begin

text \<open>
  The new premises before flattening (\<^const>\<open>na_oldAs\<close>) are the original ones or, if the rule
  is lifted, their renamings. The schematic variables renamed by \<open>tab\<close> occur neither on the left
  of the disagreement pairs nor in the flex-flex pairs.
\<close>

lemma newAs_ren:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
  obtains tab r2 where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
proof -
  have h: "\<not> okT (case e of UExn (PExn (Term_Error _ _)) \<Rightarrow> raiseT (THM (STR ''bicompose: 1st premise'') 0 Orule)
        | _ \<Rightarrow> raiseT e) y" for e and y :: newas
    by (auto simp: raiseT_def split: texn.splits uexn.splits exn.splits)
  from assms have flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    and old: "na_oldAs na = As0 \<or> (\<exists>r. bc_lifted ctx \<and>
      rename_bvars dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0 = Some r \<and>
      na_oldAs na = map (strip_apply (ren_term r) (bc_Bi ctx)) As0)"
    unfolding newAs_def
    by (auto simp: okT_handleT h ok_mapM list.rel_eq split: if_splits option.splits)
  from old show thesis
  proof (elim disjE exE conjE)
    assume "na_oldAs na = As0"
    with that[of "[]", OF _ _ flat] show thesis by (simp add: ren_name_def)
  next
    fix r assume "bc_lifted ctx" and r: "rename_bvars dps (bc_rtpairs ctx @ tps1) (bc_Bi ctx) As0 = Some r"
      and "na_oldAs na = map (strip_apply (ren_term r) (bc_Bi ctx)) As0"
    then show thesis using rename_bvars_unknowns[OF r] flat by (intro that[of "fst r" "snd r"]) auto
  qed
qed

text \<open>
  The new premises are well-typed, and each of them implies the instance of the corresponding
  premise of the rule, renamed by \<open>tab\<close>.
\<close>

lemma newAs_holds:
  assumes na: "okT (newAs vl ctx As0 n dps tps1) na"
    and lr: "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    and ib: "ibelow (bc_smax ctx) (bc_Bi ctx)" and wf: "\<forall>A\<in>set As0. wtp A"
    and vl: "\<And>xs. length (vl xs) = length xs"
  obtains tab where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    "\<not> bc_lifted ctx \<Longrightarrow> tab = []"
    "\<And>\<rho> \<sigma>. cert_inst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
      list_all2 (\<lambda>A' A. holds (ap \<rho> \<sigma> A') \<longrightarrow> holds (ap \<rho> (rsubst (bc_smax ctx) tab \<sigma>) A)) (na_As na) As0"
    "\<forall>A\<in>set (na_As na). wtp A"
proof -
  let ?m = "bc_smax ctx"
  obtain tab r2 where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
    and old: "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    by (rule newAs_ren[OF na]) (rule that)
  text \<open>The renamed premises are well-typed and have the instances of the original ones.\<close>
  have oldAs: "list_all2 (\<lambda>A1 A. wtp A1 \<and> wtp A \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> A1) (ap \<rho> (rsubst ?m tab \<sigma>) A)))
    (na_oldAs na) As0"
    using old
  proof (elim disjE conjE)
    assume "na_oldAs na = As0" "tab = []"
    then show ?thesis
      using wf by (auto intro!: list.rel_refl_strong)
  next
    assume lf: "bc_lifted ctx"
      and o: "na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    from lr[OF lf] obtain p Bi0 As0' B0 where Bi: "bc_Bi ctx = lift_pre p Bi0"
      and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
      and above: "\<forall>X\<in>insert B0 (set As0'). \<forall>v\<in>vars X. ?m < snd (fst v)"
      by (rule lifted_rule_lift_pre)
    have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> ?m"
      using ib Bi by (auto simp: ibelow_def vars_lift_pre)
    have "na_oldAs na = map (\<lambda>X. lift_pre p (ren_term (tab, r2) X)) As0'"
      using o As0 Bi strip_apply_lift_pre[OF ok at] by simp
    then show ?thesis
      using As0 wf pv above aconv_lift_pre_ren[OF pv, of _ _ _ "(tab, r2)"]
      by (auto simp: list_all2_map1 list_all2_map2 wtp_lift_pre_ren intro!: list.rel_refl_strong)
  qed
  have step: "wtp A' \<and> (\<forall>\<rho> \<sigma>. cert_inst \<rho> \<longrightarrow> gsubst \<sigma> \<longrightarrow>
      holds (ap \<rho> \<sigma> A') \<longrightarrow> holds (ap \<rho> (rsubst ?m tab \<sigma>) A))"
    if f: "if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A'"
      and o: "wtp A1 \<and> wtp A \<and> (\<forall>\<rho> \<sigma>. aconv_term (ap \<rho> \<sigma> A1) (ap \<rho> (rsubst ?m tab \<sigma>) A))"
      for A' A1 A
  proof -
    have wA: "wtp A" using o by blast
    have l: "length (vl (map fst (strip_params A1))) = length (strip_params A1)"
      using vl[of "map fst (strip_params A1)"] by simp
    have w1: "wtp A1" using o by blast
    have "wtp A'"
    proof (cases "bc_flatten ctx")
      case True
      with f have fp: "ok (flatten_params vl n A1) A'" by simp
      show ?thesis
        by (rule wtpI[OF _ flatten_params_typing[OF fp l wtpD(2)[OF w1]]])
          (use flatten_params_loose[OF fp l] wtpD(1)[OF w1] in \<open>simp add: closed_def\<close>)
    next
      case False
      with f w1 show ?thesis by simp
    qed
    moreover have "holds (ap \<rho> (rsubst ?m tab \<sigma>) A)"
      if \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and h: "holds (ap \<rho> \<sigma> A')" for \<rho> \<sigma>
    proof -
      have "holds (ap \<rho> \<sigma> A1)"
      proof (cases "bc_flatten ctx")
        case True
        with f have "ok (flatten_params vl n A1) A'" by simp
        from flatten_params_holds[OF this l \<rho> \<sigma> wtpD(2)[OF w1] wtpD(1)[OF w1] h] show ?thesis .
      next
        case False
        with f h show ?thesis by simp
      qed
      moreover have "gsubst (rsubst ?m tab \<sigma>)"
        using \<sigma> wt_subst_rsubst by (auto simp: gsubst_def rsubst_def)
      ultimately show ?thesis
        using holds_conv[OF gterm_ap_wtp[OF w1 \<rho> \<sigma>] gterm_ap_wtp[OF wA \<rho>] aconv_term_conv] o by blast
    qed
    ultimately show ?thesis by blast
  qed
  have flat': "list_all2 (\<lambda>A' A1. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
    (na_As na) (na_oldAs na)"
    using flat by (simp add: list_all2_conv_all_nth)
  have r: "list_all2 (\<lambda>A' A. wtp A' \<and> (\<forall>\<rho> \<sigma>. cert_inst \<rho> \<longrightarrow> gsubst \<sigma> \<longrightarrow>
      holds (ap \<rho> \<sigma> A') \<longrightarrow> holds (ap \<rho> (rsubst ?m tab \<sigma>) A))) (na_As na) As0"
    by (rule list_all2_trans[OF step flat' oldAs])
  show thesis
  proof (rule that[OF ren])
    show "\<not> bc_lifted ctx \<Longrightarrow> tab = []" using old by blast
    show "list_all2 (\<lambda>A' A. holds (ap \<rho> \<sigma> A') \<longrightarrow> holds (ap \<rho> (rsubst ?m tab \<sigma>) A)) (na_As na) As0"
      if "cert_inst \<rho>" "gsubst \<sigma>" for \<rho> \<sigma>
      using r that by (auto elim: list_all2_mono)
    show "\<forall>A\<in>set (na_As na). wtp A"
      using r by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  qed
qed


text \<open>
  If the rule is lifted, the first assumptions of the new premises are lifted assumptions of
  the subgoal (up to renumbering bound variables).
\<close>

lemma newAs_skip:
  assumes "okT (newAs vl ctx As0 n dps tps1) na" "bc_lifted ctx"
    "lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" "\<And>xs. length (vl xs) = length xs"
    "0 \<le> k" "k + (if 0 < n \<and> bc_flatten ctx then 1 else 0) \<le> count_prems (strip_all_body (bc_Bi ctx))"
  shows "\<forall>A\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer k) (spine_hyps A)).
    \<exists>H0\<in>set (spine_hyps (bc_Bi ctx)). vars H = vars H0 \<and> typs H = typs H0"
proof -
  let ?K = "nat_of_integer k" and ?d = "if 0 < n \<and> bc_flatten ctx then 1 else 0 :: nat"
  obtain tab r2 where
    old: "na_oldAs na = As0 \<and> tab = [] \<or>
      bc_lifted ctx \<and> na_oldAs na = map (strip_apply (ren_term (tab, r2)) (bc_Bi ctx)) As0"
    and flat: "list_all2 (\<lambda>A1 A'. if bc_flatten ctx then ok (flatten_params vl n A1) A' else A1 = A')
      (na_oldAs na) (na_As na)"
    by (rule newAs_ren[OF assms(1)]) (rule that)
  from assms(3) obtain p Bi0 As0' where Bi: "bc_Bi ctx = lift_pre p Bi0"
    and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0" and As0: "As0 = map (lift_pre p) As0'"
    by (rule lifted_rule_lift_pre) blast
  have sBi: "spine_hyps (bc_Bi ctx) = phyps p"
    by (simp add: Bi spine_hyps_lift_pre[OF ok] spine_hyps_atomic[OF at])
  have "k + (if 0 < n \<and> bc_flatten ctx then 1 else 0) \<le> ilength (phyps p)"
    using order_trans[OF assms(6)[unfolded Bi] count_prems_lift_pre[OF ok at]] .
  then have len: "?K + ?d \<le> length (phyps p)"
    using assms(5)
    by (auto simp: ilength_eq integer_reps nat_le_iff Suc_le_eq
        nat_less_iff split: if_splits)
  text \<open>The first \<open>k\<close> hypotheses of a new premise are lifted ones.\<close>
  have step: "\<exists>H0\<in>set (phyps p). vars H = vars H0 \<and> typs H = typs H0"
    if f: "if bc_flatten ctx then ok (flatten_params vl n A1) A else A1 = A"
      and A1: "A1 = lift_pre p Z" and H: "H \<in> set (take ?K (spine_hyps A))" for A1 A Z H
  proof -
    have "\<exists>H1\<in>set (take (?K + ?d) (spine_hyps A1)). vars H = vars H1 \<and> typs H = typs H1"
    proof (cases "bc_flatten ctx")
      case True
      with f have fp: "ok (flatten_params vl n A1) A" by simp
      have l: "length (vl (map fst (strip_params A1))) = length (strip_params A1)"
        using assms(4)[of "map fst (strip_params A1)"] by simp
      obtain A'' where r: "ok (remove_params (ilength (strip_params A1)) n A1) A''"
        and A: "A = list_forall (zip (vl (map fst (strip_params A1))) (map snd (strip_params A1))) A''"
        by (rule flatten_params_ok[OF fp l])
      from H have "H \<in> set (take ?K (spine_hyps A''))" by (simp add: A spine_hyps_list_forall)
      from remove_params_spine_hyps[OF r this] True show ?thesis by simp
    next
      case False
      with f H show ?thesis by auto
    qed
    moreover have "take (?K + ?d) (spine_hyps A1) = take (?K + ?d) (phyps p)"
      using len by (simp add: A1 spine_hyps_lift_pre[OF ok])
    ultimately show ?thesis using set_take_subset by fastforce
  qed
  have "list_all2 (\<lambda>A1 A. (\<exists>Z. A1 = lift_pre p Z) \<longrightarrow> (\<forall>H\<in>set (take ?K (spine_hyps A)).
      \<exists>H0\<in>set (phyps p). vars H = vars H0 \<and> typs H = typs H0)) (na_oldAs na) (na_As na)"
    using flat by (rule list_all2_mono) (blast intro: step)
  moreover have "\<forall>A1\<in>set (na_oldAs na). \<exists>Z. A1 = lift_pre p Z"
    using old assms(2) by (auto simp: As0 Bi strip_apply_lift_pre[OF ok at])
  ultimately show ?thesis unfolding sBi by (rule list_all2_imp_all')
qed

end


subsection \<open>The new theorem\<close>

text \<open>The cases of \<^const>\<open>addth\<close>.\<close>

lemma addth_cases:
  assumes "okT (addth ctx A na (env, tps)) r"
  obtains (empty) "env_is_empty env" "r = BRes env tps (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)) A na"
  | (norm) ntps Hs C' where "\<not> env_is_empty env" "r = BRes env ntps (list_implies Hs C') A na"
      "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
      "above env (bc_smax ctx) \<and> bc_lifted ctx \<and> C' = bc_C ctx \<and>
        (\<exists>As'. Hs = bc_Bs ctx @ As' \<and> list_all2 (\<lambda>X X'. okT (norm_term_skip env (bc_nlift ctx) X) X') (na_As na) As') \<or>
       above env (bc_smax ctx) \<and> \<not> bc_lifted ctx \<and> C' = bc_C ctx \<and>
        (\<exists>As'. Hs = bc_Bs ctx @ As' \<and> list_all2 (\<lambda>X X'. ok (norm_term env X) X') (na_As na) As') \<or>
       \<not> above env (bc_smax ctx) \<and> list_all2 (\<lambda>X X'. ok (norm_term env X) X') (bc_Bs ctx @ na_As na) Hs \<and>
        ok (norm_term env (bc_C ctx)) C'"
proof (cases "env_is_empty env")
  case True
  with assms show thesis by (intro empty) (auto simp: addth_def)
next
  case False
  from assms False obtain ntps where nt: "ok (mapM (norm_tpair env) tps) ntps"
    and rest: "okT (do {
          (ntpairs, Hs, C') \<leftarrow>
            if above env (bc_smax ctx) then
              if bc_lifted ctx then do {
                As' \<leftarrow> mapT (norm_term_skip env (bc_nlift ctx)) (na_As na);
                returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
              else do {
                As' \<leftarrow> liftMT (mapM (norm_term env) (na_As na));
                returnT (ntps, bc_Bs ctx @ As', bc_C ctx)}
            else if bc_match ctx then raiseT COMPOSE
            else do {
              Hs \<leftarrow> liftMT (mapM (norm_term env) (bc_Bs ctx @ na_As na));
              C' \<leftarrow> liftMT (norm_term env (bc_C ctx));
              returnT (ntps, Hs, C')};
          returnT (BRes env ntpairs (list_implies Hs C') A na)}) r"
    by (auto simp: addth_def)
  have l: "list_all2 (\<lambda>tu tu'. ok (norm_term env (fst tu)) (fst tu') \<and> ok (norm_term env (snd tu)) (snd tu')) tps ntps"
    using nt unfolding ok_mapM
    by (rule list_all2_mono) (auto simp: norm_tpair_def split: prod.splits)
  show thesis
  proof (cases "above env (bc_smax ctx)")
    case True
    show thesis
    proof (cases "bc_lifted ctx")
      case lf: True
      with True rest obtain As' where "list_all2 (\<lambda>X X'. okT (norm_term_skip env (bc_nlift ctx) X) X') (na_As na) As'"
        "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: okT_mapT)
      with False l True lf show thesis by (intro norm) auto
    next
      case lf: False
      with True rest obtain As' where "list_all2 (\<lambda>X X'. ok (norm_term env X) X') (na_As na) As'"
        "r = BRes env ntps (list_implies (bc_Bs ctx @ As') (bc_C ctx)) A na"
        by (auto simp: ok_mapM)
      with False l True lf show thesis by (intro norm) auto
    qed
  next
    case na: False
    with rest obtain Hs C' where "list_all2 (\<lambda>X X'. ok (norm_term env X) X') (bc_Bs ctx @ na_As na) Hs"
      "ok (norm_term env (bc_C ctx)) C'" "r = BRes env ntps (list_implies Hs C') A na"
      by (auto simp: ok_mapM split: if_splits)
    with False l na show thesis by (intro norm) auto
  qed
qed

context pure_sig
begin

lemma norm_term_skip_loose:
  "okT (norm_term_skip env n t) t' \<Longrightarrow> tsol (tyenv env) \<rho> \<Longrightarrow> wt_env \<rho> env \<Longrightarrow> 0 \<le> k \<Longrightarrow>
    \<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar t' k"
proof (induction env n t arbitrary: t' k rule: norm_term_skip.induct)
  case (1 env n t)
  show ?case
  proof (cases "n = 0")
    case True
    with "1.prems"(1) have "ok (norm_term env t) t'" by (simp add: norm_term_skip.simps)
    from nsoundD(2)[OF norm_term_sound[OF this "1.prems"(2,3)] "1.prems"(4,5)] show ?thesis .
  next
    case n: False
    show ?thesis
    proof (cases "dest_all t")
      case (Some x)
      then obtain a T b where aTb: "dest_all t = Some (a, T, b)" by (cases x) auto
      then obtain U where t: "t = Const STR ''Pure.all'' U $ Abs a T b" by (auto simp: dest_all_Some)
      from "1.prems"(1) n aTb obtain T' b' where T': "ok (norm_type (tyenv env) T) T'"
        and b': "okT (norm_term_skip env n b) b'" and t': "t' = all_const T' $ Abs a T' b'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from T' have T'': "okT (liftMT (norm_type (tyenv env) T)) T'" by simp
      from "1.IH"(2)[OF n aTb refl refl T'' b' "1.prems"(2,3), of "k + 1"] "1.prems"(4,5) t
      show ?thesis by (simp add: t' all_const_def)
    next
      case None
      with "1.prems"(1) n obtain A B where AB: "dest_imp t = Some (A, B)"
        by (auto simp: norm_term_skip.simps[of env n t] split: option.splits)
      with "1.prems"(1) n None obtain B' where B': "okT (norm_term_skip env (n - 1) B) B'"
        and t': "t' = mk_implies A B'"
        by (auto simp: norm_term_skip.simps[of env n t])
      from AB obtain U where t: "t = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: dest_imp_Some)
      from "1.IH"(1)[OF n None AB refl B' "1.prems"(2,3,4)] "1.prems"(5) t
      show ?thesis by (simp add: t' mk_implies_def implies_def)
    qed
  qed
qed

lemma gterm_apI: "gsubst \<sigma> \<Longrightarrow> closed t \<Longrightarrow> e \<turnstile> inst \<rho> t : T \<Longrightarrow> gterm (ap \<rho> \<sigma> t) T"
  by (rule gtermI[OF _ typing_ap]) (auto simp: closed_def gsubstD)

text \<open>The flex-flex pairs of the new theorem are the normalizations of those of the unifier.\<close>

lemma addth_tpairs:
  assumes "okT (addth ctx A na (env', tps)) r" "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
    "\<forall>(t, u)\<in>set tps. \<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T"
    "\<forall>(t, u)\<in>set (br_tpairs r). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "\<forall>(t, u)\<in>set tps. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
  using assms(1)
proof (cases rule: addth_cases)
  case empty
  have "ap \<rho>' \<sigma>' t = ap \<rho> \<sigma> t" for t by (rule iext_unb[OF assms(2) unb_empty[OF empty(1)]])
  with assms(4) empty(2) show ?thesis by auto
next
  case (norm ntps Hs C')
  show ?thesis
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    from list_all2_ex1[OF norm(3) tu] obtain tu' where tu': "tu' \<in> set ntps"
      and n: "ok (norm_term env' t) (fst tu')" "ok (norm_term env' u) (snd tu')"
      by auto
    obtain t' u' where tu'': "tu' = (t', u')" by (cases tu')
    note tu' = tu'[unfolded tu''] and n = n[unfolded tu'' fst_conv snd_conv]
    from assms(3) tu obtain e T where ty: "e \<turnstile> inst \<rho>' t : T" "e \<turnstile> inst \<rho>' u : T" by blast
    have "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" by (rule conv_sym[OF iext_norm_term(1)[OF assms(2) n(1) ty(1)]])
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'" using assms(4) tu' norm(2) by auto
    also have "\<dots> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" by (rule iext_norm_term(1)[OF assms(2) n(2) ty(2)])
    finally show "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" .
  qed
qed

end

context pure_valuation
begin

lemma holds_list_implies_conv:
  assumes "gterm (list_implies Xs C) propT" "list_all2 (\<lambda>X Y. gterm Y propT \<and> Y \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> X) Xs Ys"
    "gterm C' propT" "C' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> C" "holds (list_implies Xs C)"
  shows "holds (list_implies Ys C')"
  using assms(2,1,5)
proof (induction rule: list_all2_induct)
  case Nil
  then show ?case using holds_conv[OF _ assms(3) conv_sym[OF assms(4)]] by simp
next
  case (Cons X Xs Y Ys)
  have gX: "gterm X propT" and gXs: "gterm (list_implies Xs C) propT" and ci: "cert_typ alg ar imp_type"
    using Cons.prems(1) typing_implies by (auto simp: gterm_def closed_def implies_def)
  have hX: "holds X \<longrightarrow> holds (list_implies Xs C)"
    using Cons.prems(2) holds_imp[OF gX gXs] by simp
  have gYs: "gterm (list_implies Ys C') propT"
  proof -
    have "\<forall>Z\<in>set Ys. gterm Z propT" using Cons.hyps(2) by (induction rule: list_all2_induct) auto
    with assms(3) ci show ?thesis
      by (auto simp: gterm_def closed_def loose_bvar_list_implies vars_list_implies intro!: typing_list_impliesI)
  qed
  have "holds Y \<Longrightarrow> holds X" using holds_conv[OF _ gX] Cons.hyps(1) by blast
  with hX Cons.IH[OF gXs] have "holds Y \<longrightarrow> holds (list_implies Ys C')" by blast
  with holds_imp[OF _ gYs] Cons.hyps(1) show ?case by simp
qed

text \<open>The proposition of the new theorem holds if its unnormalized instance holds.\<close>

lemma addth_holds:
  assumes ad: "okT (addth ctx A na (env', tps)) r" and ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" and \<sigma>: "gsubst \<sigma>"
    and wS: "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtp X \<and> ibelow (bc_smax ctx) X"
    and wN: "\<forall>X\<in>set (na_As na). wtp X"
    and sk: "bc_lifted ctx \<Longrightarrow> 0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
    and h: "holds (ap \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
    and ci: "cert_typ alg ar imp_type"
  shows "holds (ap \<rho> \<sigma> (br_prop r))"
proof -
  let ?Bs = "bc_Bs ctx" and ?As = "na_As na" and ?C = "bc_C ctx"
  let ?rel = "\<lambda>X Y. gterm (ap \<rho> \<sigma> Y) propT \<and> ap \<rho> \<sigma> Y \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' X"
  note i = iextD[OF ie]
  have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
  have wX: "wtp X" if "X \<in> set (?Bs @ ?As) \<or> X = ?C" for X using that wS wN by auto
  have gX: "gterm (ap \<rho>' \<sigma>' X) propT" if "wtp X" for X by (rule gterm_ap_wtp[OF that ci' i(2)])
  have gl: "gterm (ap \<rho>' \<sigma>' (list_implies (?Bs @ ?As) ?C)) propT"
    by (rule gterm_ap_wtp[OF wtp_list_impliesI ci' i(2)]) (use wX ci in auto)
  have tr: "holds (ap \<rho> \<sigma> (list_implies Hs C'))"
    if "list_all2 ?rel (?Bs @ ?As) Hs" "?rel ?C C'" for Hs C'
  proof -
    have "list_all2 (\<lambda>X Y. gterm Y propT \<and> Y \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> X) (map (ap \<rho>' \<sigma>') (?Bs @ ?As)) (map (ap \<rho> \<sigma>) Hs)"
      using that(1) by (simp only: list_all2_map1 list_all2_map2)
    from holds_list_implies_conv[OF gl[unfolded ap_list_implies] this _ _ h[unfolded ap_list_implies]] that(2)
    show ?thesis by (simp add: ap_list_implies)
  qed
  have rel_unb: "?rel X X" if "wtp X" "unb env' X" for X
    using gX[OF that(1)] iext_unb[OF ie that(2)] by simp
  have rel_norm: "?rel X Y" if "wtp X" "ok (norm_term env' X) Y" for X Y
  proof -
    have ty: "(\<lambda>_. propT) \<turnstile> inst \<rho>' X : propT"
      using typing_closed[OF typing_inst[OF wtpD(2)[OF that(1)] cert_inst_inst_ok[OF ci']]] wtpD(1)[OF that(1)]
      by (simp add: closed_def)
    note n = iext_norm_term[OF ie that(2) ty]
    have "closed Y"
      using nsoundD(2)[OF norm_term_sound[OF that(2) i(5,4)], of 0] wtpD(1)[OF that(1)]
      by (simp add: closed_def)
    with n show ?thesis using gterm_apI[OF \<sigma>] by blast
  qed
  have rel_skip: "?rel X Y" if "wtp X" "skip_unb env' (bc_nlift ctx) X" "okT (norm_term_skip env' (bc_nlift ctx) X) Y" for X Y
  proof -
    note n = iext_norm_term_skip[OF that(3) ie \<sigma> wtpD(2)[OF that(1)] that(2), of "\<lambda>_. propT"]
    have "closed Y"
      using norm_term_skip_loose[OF that(3) i(5,4), of 0] wtpD(1)[OF that(1)] by (simp add: closed_def)
    with n show ?thesis using gterm_apI[OF \<sigma>] by blast
  qed
  have unbS: "\<forall>X\<in>set ?Bs. unb env' X" "unb env' ?C" if "above env' (bc_smax ctx)"
    using wS above_unb[OF that] by auto
  show ?thesis
    using ad
  proof (cases rule: addth_cases)
    case empty
    have "list_all2 ?rel (?Bs @ ?As) (?Bs @ ?As)"
      by (rule list.rel_refl_strong) (use wX rel_unb unb_empty[OF empty(1)] in auto)
    moreover have "?rel ?C ?C" using wS rel_unb unb_empty[OF empty(1)] by auto
    ultimately show ?thesis using tr empty(2) by simp
  next
    case (norm ntps Hs C')
    from norm(4) consider
      (lifted) As' where "above env' (bc_smax ctx)" "bc_lifted ctx" "C' = ?C" "Hs = ?Bs @ As'"
        "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X') ?As As'"
    | (above) As' where "above env' (bc_smax ctx)" "C' = ?C" "Hs = ?Bs @ As'"
        "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') ?As As'"
    | (all) "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (?Bs @ ?As) Hs" "ok (norm_term env' ?C) C'"
      by blast
    then have "list_all2 ?rel (?Bs @ ?As) Hs \<and> ?rel ?C C'"
    proof cases
      case lifted
      from sk[OF lifted(2)] have n: "0 \<le> bc_nlift ctx"
        and hh: "\<forall>X\<in>set ?As. \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H"
        by auto
      have sk': "skip_unb env' (bc_nlift ctx) X" if "X \<in> set ?As" for X
        by (rule skip_unb_take[OF n]) (use hh that above_unb[OF lifted(1)] in blast)
      have "list_all2 (\<lambda>X X'. okT (norm_term_skip env' (bc_nlift ctx) X) X' \<and> X \<in> set ?As) ?As As'"
        using lifted(5) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
      then have "list_all2 ?rel ?As As'"
        by (rule list_all2_mono) (use wN sk' rel_skip in blast)
      moreover have "list_all2 ?rel ?Bs ?Bs"
        by (rule list.rel_refl_strong) (use wS unbS[OF lifted(1)] rel_unb in auto)
      ultimately show ?thesis
        using lifted rel_unb[of ?C] wS unbS(2)[OF lifted(1)] by (simp add: list_all2_appendI)
    next
      case above
      have "list_all2 (\<lambda>X X'. ok (norm_term env' X) X' \<and> X \<in> set ?As) ?As As'"
        using above(4) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
      then have "list_all2 ?rel ?As As'"
        by (rule list_all2_mono) (use wN rel_norm in blast)
      moreover have "list_all2 ?rel ?Bs ?Bs"
        by (rule list.rel_refl_strong) (use wS unbS[OF above(1)] rel_unb in auto)
      ultimately show ?thesis
        using above rel_unb[of ?C] wS unbS(2)[OF above(1)] by (simp add: list_all2_appendI)
    next
      case all
      have "list_all2 (\<lambda>X X'. ok (norm_term env' X) X' \<and> X \<in> set (?Bs @ ?As)) (?Bs @ ?As) Hs"
        using all(1) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
      then have "list_all2 ?rel (?Bs @ ?As) Hs"
        by (rule list_all2_mono) (use wX rel_norm in blast)
      with rel_norm[OF _ all(2)] wS show ?thesis by simp
    qed
    with tr norm(2) show ?thesis by simp
  qed
qed


end


subsection \<open>Composition\<close>

context pure_sig
begin

text \<open>The invariants of a unifier and its soundness:\<close>

lemma ures_inv:
  assumes "ures env tus (El_R env' tps)" "pwf env tus"
  obtains A K X where "einv A K env'" "winv env' X" "\<forall>(t, u)\<in>set tps. pok A env' [] X t u"
proof -
  from ures_pwf[OF assms] obtain A0 where "uresult A0 env tus (El_R env' tps)" .
  from uresultD(3)[OF this] obtain A K X where "ffres A K X env' tps" by blast
  then show thesis unfolding ffres_def by (blast intro: that)
qed

lemma ures_solves:
  assumes ur: "ures env tus (El_R env' tps)" and pw: "pwf env tus"
    and sol: "solution \<rho> \<sigma> env'" and ci: "cert_inst \<rho>"
    and ts: "\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  shows "\<forall>(t, u)\<in>set tus. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
proof -
  from ures_pwf[OF ur pw] obtain A where "uresult A env tus (El_R env' tps)" .
  then have ds: "dstep env (tdps tus) env' (tdps tps)" by (rule uresultD(1))
  from pw obtain A0 K X where si: "sinv A0 K X env (tdps tus)" by (auto simp: pwf_def)
  have t': "tsol (tyenv env') \<rho>" by (rule solutionD(2)[OF sol])
  have t: "tsol (tyenv env) \<rho>" by (rule extends_tsol[OF t' dstepD(1)[OF ds]])
  from winvD[OF _ t ci] si have w: "wt_env \<rho> env" "vinv \<rho> env X" by (auto simp: sinv_def)
  have v: "vinv \<rho> env ({} \<union> dvars (tdps tus))"
    using ur_vinv_sub[OF w(2)] sinv_dvars[OF si] by simp
  have "dsolved \<rho> \<sigma> (tdps tps)" using ts by (simp only: dsolved_tdps)
  with dstepD(2)[OF ds t' extends_refl w(1) sinv_dtyped[OF si t ci] v] sol
  have "dsolved \<rho> \<sigma> (tdps tus)" by blast
  then show ?thesis by (simp only: dsolved_tdps)
qed

text \<open>The problems of a closure are well-formed:\<close>

lemma itsok_pwf: "itsok sp A na tus \<Longrightarrow> pinv_all sp \<Longrightarrow> pwf (sp_env sp) tus"
proof (unfold itsok_def, elim disjE exE conjE)
  assume "\<not> sp_eres sp" "tus = bc_dpairs (sp_ctx sp)" "pinv_all sp"
  then show "pwf (sp_env sp) tus" by (simp add: pinv_all_def)
next
  fix n asm assume er: "sp_eres sp" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
    "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm" "pinv_all sp"
  have "nat_of_integer n - 1 < length (asms_of sp)" using er(2,3) by (simp add: integer_reps)
  then have "asm \<in> set (asms_of sp)" using er(4) by simp
  with er show "pwf (sp_env sp) tus" by (simp add: pinv_all_def)
qed

text \<open>
  The instance argument: an instance \<open>(\<rho>, \<sigma>)\<close> of a result whose flex-flex pairs are solved
  extends to a solution \<open>(\<rho>', \<sigma>')\<close> of the environment of the unifier, which agrees with
  \<open>(\<rho>, \<sigma>)\<close> on unbound variables and solves the problem of unification. The validity of the
  result (theorem \<open>rchar_valid\<close> below) follows from it.
\<close>

lemma bresult_inst:
  assumes its: "itsok sp A na tus" and pa: "pinv_all sp" and ur: "ures (sp_env sp) tus (El_R env' tps)"
    and ad: "okT (addth (sp_ctx sp) A na (env', tps)) r"
    and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<forall>(t, u)\<in>set (br_tpairs r). ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  obtains \<rho>' \<sigma>' where "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
proof -
  from ures_inv[OF ur itsok_pwf[OF its pa]] obtain A' K' X' where ei': "einv A' K' env'" and wi': "winv env' X'"
    and tpok: "\<forall>(t, u)\<in>set tps. pok A' env' [] X' t u" by blast
  obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" by (rule iext_exists[OF ei' wi' \<rho> \<sigma>])
  note i = iextD[OF ie]
  have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
  have "\<forall>(t, u)\<in>set tps. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
  proof (rule addth_tpairs[OF ad ie _ sol])
    show "\<forall>(t, u)\<in>set tps. \<exists>e T. e \<turnstile> inst \<rho>' t : T \<and> e \<turnstile> inst \<rho>' u : T"
      using tpok pokD(9)[OF _ i(5) ci'] by fast
  qed
  from ures_solves[OF ur itsok_pwf[OF its pa] i(3) ci' this] ie show thesis by (rule that[rotated])
qed

end

context pure_model
begin


text \<open>
  The results of a call of \<open>bicompose_aux\<close> for a valid proof state \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> with
  hypotheses \<open>hs\<close>, flex-flex pairs \<open>stpairs\<close> and maximal index \<open>smax\<close>, and a valid rule
  \<open>\<lbrakk>As\<rbrakk> \<Longrightarrow> B\<close> with hypotheses \<open>hr\<close> and flex-flex pairs \<open>rtpairs\<close>, lifted over \<open>Bi\<close> if
  \<open>lifted\<close>, are valid, with the hypotheses of both.
\<close>

theorem rchar_valid:
  assumes sp: "sp = call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and r: "rchar sp r" and pa: "pinv_all sp"
    and state: "valid hs stpairs (list_implies (Bs @ [Bi]) C)" "wtp (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "valid hr rtpairs (list_implies (rev rAs) B)" "wtp (list_implies (rev rAs) B)"
      "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and hyps: "\<forall>h\<in>set (hs @ hr). vars h = {} \<and> ttvars h = {}"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "valid (hs @ hr) (br_tpairs r) (br_prop r)"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "sp_eres sp = eres_flg" "sp_ctx sp = ctx" "sp_vl sp = vl" "sp_rAs sp = rAs" "sp_env sp = env"
    by (simp_all add: sp')
  from r obtain A1o na tus env' tps where its: "itsok sp A1o na tus"
    and ur: "ures env tus (El_R env' tps)" and ad: "okT (addth ctx A1o na (env', tps)) r"
    by (auto simp: rchar_def sp')
  have wS: "\<forall>X\<in>set Bs. wtp X" "wtp Bi" "wtp C" using wtp_list_implies[OF state(2)] by simp_all
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using state(3) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wtp X" "wtp B" using wtp_list_implies[OF rule(2)] by simp_all
  have ci: "cert_typ alg ar imp_type"
  proof -
    obtain X Xs where "Bs @ [Bi] = X # Xs" by (cases "Bs @ [Bi]") auto
    with wtpD(2)[OF state(2), of "\<lambda>_. propT"] show ?thesis by (simp add: typing_implies)
  qed
  text \<open>The problem and the new premises: the premises \<open>Pre\<close> of the rule that are proved
    (none, or the first by an assumption), the other premises \<open>As0\<close>, and the further
    disagreement pairs \<open>dps\<close> given to \<^const>\<open>newAs\<close>.\<close>
  obtain Pre As0 n dps tps1 where
    rAs: "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps"
    and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl asm. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> asm \<in> set asms \<and>
      (rlist_abs params concl, rlist_abs params asm) \<in> set dps \<and>
      (rlist_abs params asm, rlist_abs params concl) \<in> set tus"
  proof -
    from its consider (res) tps1 where "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
        "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      | (eres) n asm tps1 where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
        "okT (newAs vl ctx (er_As (eres_of sp)) n
          [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      using its unfolding itsok_def sp_sel ctx_sel by blast
    then show thesis
    proof cases
      case res
      have "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
      then show thesis using res
        by (intro that[of "[]" "rev rAs" 0 "[BBi]" tps1]) (simp_all add: nlift_def)
    next
      case eres
      have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
      obtain A1 As where rA: "rev rAs = A1 # As"
        using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
      obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
        by (cases "assum_problems (nlift + 1) A1")
      have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
        using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
      have asm: "asm \<in> set asms" using eres(2-4) er(2) by (simp add: integer_reps)
      have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
      have "ilength asms \<le> nlift + 1"
        by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
      moreover have "n \<le> ilength asms" using eres(2,3) er(2)
        by (simp add: ilength_eq integer_reps)
      ultimately have nle: "n \<le> nlift + 1" by simp
      show thesis
      proof (rule that[of "[A1]" As n "[BBi, (rlist_abs params concl, rlist_abs params asm)]" tps1])
        show "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
          using eres(6) er by simp
        show "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
          using eres(5) er by (auto simp: eres_prob_def sp' ctx_sel)
        show "\<exists>params' asms' concl' asm'. eres_flg \<and> [A1] = [A1'] \<and>
            assum_problems (nlift + 1) A1' = (params', asms', concl') \<and> asm' \<in> set asms' \<and>
            (rlist_abs params' concl', rlist_abs params' asm') \<in> set [BBi, (rlist_abs params concl, rlist_abs params asm)] \<and>
            (rlist_abs params' asm', rlist_abs params' concl') \<in> set tus"
          if "A1' \<in> set [A1]" for A1'
          using that eres(1,5) ap asm er by (auto simp: eres_prob_def)
      qed (use rA eres(2) nle cnt in auto)
    qed
  qed
  have wP: "\<forall>X\<in>set Pre. wtp X" "\<forall>X\<in>set As0. wtp X" using wR(1) rAs by auto
  have lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (Pre @ As0) B" using rule(3) rAs by simp
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    using lr0 by (induction Pre) (auto dest: lifted_rule_Cons)
  have pv: "\<forall>v\<in>pvars p. snd (fst v) \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
    using iS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
  show ?thesis
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (br_tpairs r) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
      and hh: "\<And>h. h \<in> set (hs @ hr) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    interpret pure_valuation alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval \<eta> \<xi>
      by unfold_locales (rule g)
    obtain tab where
      ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> vnames t) \<and>
        (\<forall>(t, u)\<in>set (rtpairs @ tps1). x \<notin> vnames t \<and> x \<notin> vnames u)"
      and nlt: "\<not> lifted \<Longrightarrow> tab = []"
      and nah: "\<And>\<rho> \<sigma>. cert_inst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow>
        list_all2 (\<lambda>A' A. holds (ap \<rho> \<sigma> A') \<longrightarrow> holds (ap \<rho> (rsubst smax tab \<sigma>) A)) (na_As na) As0"
      and wN: "\<forall>A\<in>set (na_As na). wtp A"
      using newAs_holds[OF na, of B] lr iS(2) wP(2) vl by (auto simp: ctx_sel)
    text \<open>The variables that are not renamed.\<close>
    have keep: "ap \<rho> (rsubst smax tab \<sigma>) t = ap \<rho> \<sigma> t"
      if "\<And>v. v \<in> vars t \<Longrightarrow> snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)" for \<rho> \<sigma> t
      using that by (intro ap_rsubst_id) blast
    obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'"
      and dsol0: "\<forall>(t, u)\<in>set tus. ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u"
      by (rule bresult_inst[OF its pa ur[folded sp_sel(5)] ad[folded sp_sel(2)] \<rho> \<sigma>]) (use sol in auto)
    note i = iextD[OF ie]
    have ci': "cert_inst \<rho>'" by (rule cinstD(2)[OF i(1)])
    let ?\<sigma>r = "rsubst smax tab \<sigma>'"
    have gr: "gsubst ?\<sigma>r" using i(2) wt_subst_rsubst by (auto simp: gsubst_def rsubst_def)
    have dsol: "ap \<rho>' \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
      using dsol0 that by blast
    have hyp: "holds (ap \<rho>' \<sigma>' h) \<and> holds (ap \<rho>' ?\<sigma>r h)" if "h \<in> set (hs @ hr)" for h
    proof -
      have u: "unb env' h" using hyps that by (simp add: unb_def)
      have "ap \<rho>' ?\<sigma>r h = ap \<rho>' \<sigma>' h" by (rule keep) (use hyps that in simp)
      with iext_unb[OF ie u] hh[OF that] show ?thesis by simp
    qed
    text \<open>The instances of the proof state and of the rule.\<close>
    have hS: "holds (ap \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule validD[OF state(1) g i(1,2)]) (use dsol tus hyp in auto)
    have hR: "holds (ap \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
    proof (rule validD[OF rule(1) g i(1) gr])
      fix t u assume tu: "(t, u) \<in> set rtpairs"
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars t \<union> vars u" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from bspec[OF conjunct2[OF ren[OF this]], of "(t, u)"] tu
        have "fst (fst v) \<notin> vnames t \<and> fst (fst v) \<notin> vnames u" by simp
        moreover have "fst (fst v) \<in> vnames t \<union> vnames u" using that by blast
        ultimately show False by blast
      qed
      have "ap \<rho>' ?\<sigma>r t = ap \<rho>' \<sigma>' t" "ap \<rho>' ?\<sigma>r u = ap \<rho>' \<sigma>' u"
        by (rule keep; simp add: nr)+
      with dsol[of t u] tus tu show "ap \<rho>' ?\<sigma>r t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' ?\<sigma>r u" by auto
    qed (use hyp in auto)
    text \<open>The conclusion of the rule implies the subgoal.\<close>
    have BBi_sol: "ap \<rho>' \<sigma>' (fst BBi) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' (snd BBi)"
      using dsol[of "fst BBi" "snd BBi"] tus by simp
    have hBi: "holds (ap \<rho>' \<sigma>' Bi)" if hB: "holds (ap \<rho>' ?\<sigma>r B)"
    proof (cases lifted)
      case True
      from lr0[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      have nr: "ren_name tab (fst (fst v)) = fst (fst v)" if "v \<in> vars B0" for v
      proof (rule ccontr)
        assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
        from ren[OF this] dps have "case BBi of (t, u) \<Rightarrow> fst (fst v) \<notin> vnames t" by blast
        with that BBi show False by auto
      qed
      have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B"
        by (rule keep) (use pv[OF ls] nr in \<open>auto simp: B vars_lift_pre\<close>)
      with hB have "holds (ap \<rho>' \<sigma>' (lift_pre p B0))" by (simp add: B)
      from holds_lift_pre_conv[OF ci' i(2) ok _ _ _ _ _ this] wR(2) wS(2) BBi_sol BBi B Bi
      show ?thesis by (simp add: wtp_def)
    next
      case False
      then have "ap \<rho>' ?\<sigma>r B = ap \<rho>' \<sigma>' B" by (simp add: nlt)
      moreover have "BBi = (B, Bi)" using False by (simp add: BBi_def)
      ultimately show ?thesis
        using hB BBi_sol holds_conv[OF gterm_ap_wtp[OF wR(2) ci' i(2)] gterm_ap_wtp[OF wS(2) ci' i(2)]]
        by simp
    qed
    text \<open>The premise proved by an assumption.\<close>
    have hPre: "holds (ap \<rho>' ?\<sigma>r A1)" if A1: "A1 \<in> set Pre" for A1
    proof -
      from pre[OF A1] obtain params asms concl asm where er: "eres_flg" "Pre = [A1]"
        and ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and asm: "asm \<in> set asms"
        and cd: "(rlist_abs params concl, rlist_abs params asm) \<in> set dps"
        and ac: "(rlist_abs params asm, rlist_abs params concl) \<in> set tus"
        by blast
      have wA1: "wtp A1" using wP(1) A1 by blast
      have e: "ap \<rho>' \<sigma>' (rlist_abs params asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho>' \<sigma>' (rlist_abs params concl)" by (rule dsol[OF ac])
      have c: "ap \<rho>' ?\<sigma>r (rlist_abs params concl) = ap \<rho>' \<sigma>' (rlist_abs params concl)"
      proof (rule keep)
        fix v assume v: "v \<in> vars (rlist_abs params concl)"
        show "snd (fst v) \<le> smax \<or> ren_name tab (fst (fst v)) = fst (fst v)"
        proof (rule disjI2, rule ccontr)
          assume "ren_name tab (fst (fst v)) \<noteq> fst (fst v)"
          from bspec[OF conjunct1[OF ren[OF this]] cd]
          have "fst (fst v) \<notin> vnames (rlist_abs params concl)" by simp
          moreover have "fst (fst v) \<in> vnames (rlist_abs params concl)" using v by blast
          ultimately show False by blast
        qed
      qed
      have a: "ap \<rho>' ?\<sigma>r (rlist_abs params asm) = ap \<rho>' \<sigma>' (rlist_abs params asm)"
      proof (cases lifted)
        case True
        from lr0[OF True] obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
          and As: "Pre @ As0 = map (lift_pre p) As0'" by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        from As er(2) obtain X1 where A1': "A1 = lift_pre p X1" by (cases As0') auto
        have "nlift + 1 = count_prems (strip_all_body Bi)" using er(1) by (simp add: nlift_def)
        then have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ ap[unfolded A1']] Bi n(4) by simp
        with asm have "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        with pv[OF ls] show ?thesis by (intro keep) auto
      next
        case False
        then show ?thesis by (simp add: nlt)
      qed
      show ?thesis
        by (rule eres_holds[OF ap asm _ ci' gr wtpD(2)[OF wA1] wtpD(1)[OF wA1]]) (use e a c in simp)
    qed
    text \<open>The instance of the composed theorem.\<close>
    have gS: "gterm (ap \<rho>' \<sigma>' X) propT" if "wtp X" for X by (rule gterm_ap_wtp[OF that ci' i(2)])
    have gR: "gterm (ap \<rho>' ?\<sigma>r X) propT" if "wtp X" for X by (rule gterm_ap_wtp[OF that ci' gr])
    have hS': "holds (ap \<rho>' \<sigma>' C)"
      if "\<forall>X\<in>set Bs. holds (ap \<rho>' \<sigma>' X)" "holds (ap \<rho>' \<sigma>' Bi)"
    proof (rule holds_list_impliesD[OF _ hS[unfolded ap_list_implies]])
      show "gterm (list_implies (map (ap \<rho>' \<sigma>') (Bs @ [Bi])) (ap \<rho>' \<sigma>' C)) propT"
        using gS[OF state(2)] by (simp add: ap_list_implies)
    qed (use that in auto)
    have hR': "holds (ap \<rho>' ?\<sigma>r B)" if "\<forall>X\<in>set (Pre @ As0). holds (ap \<rho>' ?\<sigma>r X)"
    proof (rule holds_list_impliesD[OF _ hR[unfolded ap_list_implies]])
      show "gterm (list_implies (map (ap \<rho>' ?\<sigma>r) (rev rAs)) (ap \<rho>' ?\<sigma>r B)) propT"
        using gR[OF rule(2)] by (simp add: ap_list_implies)
    qed (use that rAs in auto)
    have hN: "holds (ap \<rho>' \<sigma>' (list_implies (Bs @ na_As na) C))"
    proof (simp only: ap_list_implies, rule holds_list_impliesI)
      have w: "wtp (list_implies (Bs @ na_As na) C)" by (rule wtp_list_impliesI) (use wS wN ci in auto)
      show "gterm (list_implies (map (ap \<rho>' \<sigma>') (Bs @ na_As na)) (ap \<rho>' \<sigma>' C)) propT"
        using gS[OF w] by (simp add: ap_list_implies)
      assume H: "\<And>X. X \<in> set (map (ap \<rho>' \<sigma>') (Bs @ na_As na)) \<Longrightarrow> holds X"
      have "\<forall>X\<in>set As0. holds (ap \<rho>' ?\<sigma>r X)"
        using list_all2_imp_all'[OF nah[OF ci' i(2)]] H by simp
      with hPre have "holds (ap \<rho>' ?\<sigma>r B)" by (intro hR') auto
      then have "holds (ap \<rho>' \<sigma>' Bi)" by (rule hBi)
      with H show "holds (ap \<rho>' \<sigma>' C)" by (intro hS') auto
    qed
    text \<open>The new theorem.\<close>
    show "holds (ap \<rho> \<sigma> (br_prop r))"
    proof (rule addth_holds[OF ad ie \<sigma> _ wN _ _ ci])
      show "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wtp X \<and> ibelow (bc_smax ctx) X"
        using wS iS by (simp add: ctx_sel)
      show "holds (ap \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
        using hN by (simp add: ctx_sel)
      assume "bc_lifted ctx"
      then have lf: lifted by (simp add: ctx_sel)
      have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> typs H = typs H0"
        using newAs_skip[OF na _ _ vl n(4)] lf lr n(3) by (simp add: ctx_sel)
      then show "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
          \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
        using ibelow_spine_hyps[OF iS(2)] n(4) by (fastforce simp: ctx_sel ibelow_def ttvars_def)
    qed
  qed
qed

end

end
