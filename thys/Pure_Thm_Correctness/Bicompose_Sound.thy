section \<open>Soundness of \<open>bicompose_aux\<close>\<close>

theory Bicompose_Sound
  imports Bicompose_Norm
begin

text \<open>
  A theorem with flex-flex pairs \<open>tps\<close> and proposition \<open>P\<close> is valid if every ground instance
  of \<open>P\<close> holds whose instance of \<open>tps\<close> is solved. The theorems produced by \<open>bicompose_aux\<close> from
  a valid proof state and a valid rule are valid.
\<close>

subsection \<open>Prefixes\<close>

fun nall :: "litem list \<Rightarrow> nat" where
  "nall [] = 0"
| "nall (LImp c H # p) = nall p"
| "nall (LAll c a T # p) = Suc (nall p)"

fun pvars :: "litem list \<Rightarrow> indexname set" where
  "pvars [] = {}"
| "pvars (LImp c H # p) = vars c \<union> vars H \<union> pvars p"
| "pvars (LAll c a T # p) = vars c \<union> pvars p"

lemma vars_lift_pre: "vars (lift_pre p X) = pvars p \<union> vars X"
  by (induction p X rule: lift_pre.induct) auto

lemma vars_abs_pre: "vars (abs_pre p X) = vars X"
  by (induction p X rule: abs_pre.induct) auto

lemma sm_abs_pre: "sm \<rho> \<sigma> (abs_pre p X) = Abs_m (nall p) (sm \<rho> \<sigma> X)"
  sorry

context pure_sem
begin

text \<open>
  If the closures of \<open>X\<close> and \<open>Y\<close> over the parameters of a prefix are equal, then \<open>Y\<close> under the
  prefix holds if \<open>X\<close> does.
\<close>

lemma holds_lift_pre_transfer:
  assumes "rigid_subst \<sigma>" "closed_on UNIV \<sigma>" "\<forall>i\<in>set p. litem_ok i"
    "cok (lift_pre p X)" "cok (lift_pre p Y)"
    "no_loose_bound (tr (lift_pre p X)) 0" "no_loose_bound (tr (lift_pre p Y)) 0"
    "sm \<rho> \<sigma> (abs_pre p X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (abs_pre p Y)"
    "holds (sm \<rho> \<sigma> (lift_pre p X))"
  shows "holds (sm \<rho> \<sigma> (lift_pre p Y))"
  sorry

end


subsection \<open>Renaming lifted premises\<close>

lemma sm_lift_pre_ren:
  assumes "\<forall>x\<in>pvars p. snd x \<le> m" "\<forall>x\<in>vars X. m < snd x"
  shows "sm \<rho> \<sigma> (lift_pre p (ren_term r X)) = sm \<rho> (\<sigma> \<circ>\<^sub>s rsub m (fst r)) (lift_pre p X)"
  sorry


subsection \<open>The hypotheses along the spine\<close>

function spine_hyps :: "pterm \<Rightarrow> pterm list" where
  "spine_hyps t =
    (case dest_imp t of
      Some (H, B) \<Rightarrow> H # spine_hyps B
    | None \<Rightarrow> (case dest_all t of Some (_, _, b) \<Rightarrow> spine_hyps b | None \<Rightarrow> []))"
  by auto
termination by (relation "measure size") (auto dest: dest_size)

declare spine_hyps.simps[simp del]

fun phyps :: "litem list \<Rightarrow> pterm list" where
  "phyps [] = []"
| "phyps (LImp c H # p) = H # phyps p"
| "phyps (LAll c a T # p) = phyps p"

lemma vars_phyps: "H \<in> set (phyps p) \<Longrightarrow> vars H \<subseteq> pvars p"
  by (induction p rule: phyps.induct) auto

lemma spine_hyps_lift_pre: "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> spine_hyps (lift_pre p X) = phyps p @ spine_hyps X"
  sorry

lemma count_prems_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> atomic Y \<Longrightarrow> count_prems (strip_all_body (lift_pre p Y)) \<le> ilength (phyps p)"
  sorry

lemma skip_unb_take:
  "0 \<le> n \<Longrightarrow> \<forall>H\<in>set (take (nat_of_integer n) (spine_hyps t)). unb env H \<Longrightarrow> skip_unb env n t"
  sorry

text \<open>Elim-resolution with a lifted rule uses lifted assumptions.\<close>

lemma assum_problems_lift_pre:
  assumes "\<forall>i\<in>set p. litem_ok i" "atomic Y" "k \<le> count_prems (strip_all_body (lift_pre p Y))"
    "assum_problems k (lift_pre p X) = (params, asms, concl)"
  shows "set asms \<subseteq> set (phyps p)"
  sorry


subsection \<open>The new premises\<close>

text \<open>Well-formed propositions.\<close>

definition wfp :: "(name \<Rightarrow> nat) \<Rightarrow> pterm \<Rightarrow> bool" where
  "wfp ar t \<longleftrightarrow> cok t \<and> proper t \<and> twft ar t \<and> no_loose_bound (tr t) 0"

text \<open>
  The premises of a rule lifted over the subgoal \<open>Bi\<close> of a proof state with maximal index \<open>m\<close>:
  the variables of the rule have been incremented above \<open>m\<close>.
\<close>

definition lifted_rule :: "integer \<Rightarrow> pterm \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "lifted_rule m Bi As B \<longleftrightarrow> (\<exists>p Bi0 As0 B0. lsplit Bi = (p, Bi0) \<and> As = map (lift_pre p) As0 \<and>
    B = lift_pre p B0 \<and> (\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x))"

lemma list_all2_imp_all: "list_all2 (\<lambda>a b. P a \<longrightarrow> Q b) xs ys \<Longrightarrow> \<forall>x\<in>set xs. P x \<Longrightarrow> \<forall>y\<in>set ys. Q y"
  by (induction rule: list_all2_induct) auto

lemma wfp_list_impliesD: "wfp ar (list_implies As B) \<Longrightarrow> (\<forall>A\<in>set As. wfp ar A) \<and> wfp ar B"
  sorry

lemma ibelow_list_implies[simp]: "ibelow m (list_implies As B) \<longleftrightarrow> (\<forall>A\<in>set As. ibelow m A) \<and> ibelow m B"
  sorry

lemma lifted_rule_Cons:
  assumes "lifted_rule m Bi (A # As) B"
  shows "lifted_rule m Bi As B"
proof -
  from assms obtain p Bi0 As0 B0 where "lsplit Bi = (p, Bi0)" "A # As = map (lift_pre p) As0"
    "B = lift_pre p B0" "\<forall>X\<in>insert B0 (set As0). \<forall>x\<in>vars X. m < snd x"
    unfolding lifted_rule_def by (elim exE conjE) simp
  then show ?thesis
    unfolding lifted_rule_def by (intro exI[of _ p] exI[of _ Bi0] exI[of _ "tl As0"] exI[of _ B0]) (cases As0; auto)
qed

lemma ptpok_swf: "ptpok ar A W env e0 (t, u) \<Longrightarrow> swf_tm ar [] t \<and> swf_tm ar [] u"
  sorry

lemma ibelow_spine_hyps: "ibelow m t \<Longrightarrow> H \<in> set (spine_hyps t) \<Longrightarrow> ibelow m H"
  sorry

lemma assum_problems_length: "assum_problems k A = (params, asms, concl) \<Longrightarrow> 0 \<le> k \<Longrightarrow> ilength asms \<le> k"
  sorry

lemma count_prems_nonneg: "0 \<le> count_prems t"
proof (induction t rule: measure_induct_rule[of size])
  case (less t)
  then show ?case by (subst count_prems.simps) (auto split: option.splits dest: dest_size)
qed

lemma newAs_ren:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
  obtains tab where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    "\<not> bc_lifted ctx \<Longrightarrow> tab = []"
    "na_oldAs na = (if bc_lifted ctx then map (strip_apply (ren_term (tab, snd (the (na_ren na)))) (bc_Bi ctx)) As0 else As0)"
  sorry

context pure_sem
begin

lemma newAs_holds:
  assumes "okT (newAs vl ctx As0 n dps tps1) na"
    "bc_lifted ctx \<Longrightarrow> lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B"
    "ibelow (bc_smax ctx) (bc_Bi ctx)" "\<forall>A\<in>set As0. wfp ar A" "\<And>xs. length (vl xs) = length xs"
  obtains tab where
    "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (bc_rtpairs ctx @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    "\<not> bc_lifted ctx \<Longrightarrow> tab = []"
    "\<And>\<rho> \<sigma>. rigid_subst \<sigma> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow>
      list_all2 (\<lambda>A' A. holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub (bc_smax ctx) tab) A)) (na_As na) As0"
  sorry

end

lemma newAs_wfp:
  assumes "okT (newAs vl ctx As0 n dps tps1) na" "\<forall>A\<in>set As0. wfp ar A" "\<And>xs. length (vl xs) = length xs"
  shows "\<forall>A\<in>set (na_As na). wfp ar A"
  sorry

lemma newAs_skip:
  assumes "okT (newAs vl ctx As0 n dps tps1) na" "bc_lifted ctx"
    "lifted_rule (bc_smax ctx) (bc_Bi ctx) As0 B" "\<forall>A\<in>set As0. wfp ar A" "\<And>xs. length (vl xs) = length xs"
    "0 \<le> k" "k + (if 0 < n \<and> bc_flatten ctx then 1 else 0) \<le> count_prems (strip_all_body (bc_Bi ctx))"
    "n \<le> count_prems (strip_all_body (bc_Bi ctx))"
  shows "\<forall>A\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer k) (spine_hyps A)).
    \<exists>H0\<in>set (spine_hyps (bc_Bi ctx)). vars H = vars H0 \<and> tys H = tys H0"
  sorry


subsection \<open>The new theorem\<close>

locale bicompose_sem = wf_algebra alg ar + pure_sem holds inhab
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and holds :: "dB \<Rightarrow> bool" and inhab :: "ptyp \<Rightarrow> dB \<Rightarrow> bool"
begin

definition valid :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid tps P \<longleftrightarrow> (\<forall>\<rho> \<sigma>. gtinst \<rho> \<longrightarrow> closed_on UNIV \<sigma> \<longrightarrow> rigid_subst \<sigma> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<longrightarrow> holds (sm \<rho> \<sigma> P))"

lemma validD:
  "valid tps P \<Longrightarrow> gtinst \<rho> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<Longrightarrow> holds (sm \<rho> \<sigma> P)"
  unfolding valid_def by blast

lemma validI:
  "(\<And>\<rho> \<sigma>. gtinst \<rho> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<Longrightarrow> holds (sm \<rho> \<sigma> P)) \<Longrightarrow> valid tps P"
  unfolding valid_def by blast

text \<open>
  The new theorem of \<^const>\<open>addth\<close>: its flex-flex pairs and its proposition are the
  normalizations of those of the unifier and of \<open>\<lbrakk>Bs; As\<rbrakk> \<Longrightarrow> C\<close>.
\<close>

lemma addth_tpairs:
  assumes "okT (addth ctx A na (env', tps)) r" "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>"
    "swf_env ar env'" "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u"
    "\<forall>(t, u)\<in>set (br_tpairs r). sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
  shows "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
  sorry

lemma addth_holds:
  assumes "okT (addth ctx A na (env', tps)) r" "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" "rigid_subst \<sigma>" "closed_on UNIV \<sigma>"
    "swf_env ar env'" "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wfp ar X \<and> ibelow (bc_smax ctx) X"
    "\<forall>X\<in>set (na_As na). wfp ar X"
    "bc_lifted ctx \<Longrightarrow> 0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
    "holds (sm \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
  shows "holds (sm \<rho> \<sigma> (br_prop r))"
  sorry


subsection \<open>Composition\<close>

text \<open>
  The results of a call of \<open>bicompose_aux\<close> for a valid proof state \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> with
  flex-flex pairs \<open>stpairs\<close> and maximal index \<open>smax\<close>, and a valid rule \<open>\<lbrakk>As\<rbrakk> \<Longrightarrow> B\<close> with
  flex-flex pairs \<open>rtpairs\<close>, lifted over \<open>Bi\<close> if \<open>lifted\<close>, are valid.
\<close>

theorem rchar_valid:
  assumes sp: "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
    and r: "rchar sp r"
    and state: "valid stpairs (list_implies (Bs @ [Bi]) C)" "wfp ar (list_implies (Bs @ [Bi]) C)"
      "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "valid rtpairs (list_implies (rev rAs) B)" "wfp ar (list_implies (rev rAs) B)"
      "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "valid (br_tpairs r) (br_prop r)"
proof -
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    using sp by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs"
    by (simp_all add: ctx_def)
  have sp_sel: "bs_eres sp = eres_flg" "bs_ctx sp = ctx" "bs_vl sp = vl" "bs_rAs sp = rAs" "bs_env sp = env"
    "bs_A sp = A"
    by (simp_all add: sp')
  from r obtain A1o na tus env' tps where its: "itsok sp A1o na tus"
    and pu: "punifier env (dps_of tus) env' tps" and pr: "prres alg ar A env' tps"
    and ad: "okT (addth ctx A1o na (env', tps)) r"
    by (auto simp: rchar_def sp')
  from pr obtain W e0 where pi: "pinv alg ar A W env' []" and tpok: "\<forall>ab\<in>set tps. ptpok ar A W env' e0 ab"
    by (auto simp: prres_def)
  have pe: "penv_inv alg ar W env'" by (rule pinvD(1)[OF pi])
  have swf: "swf_env ar env'" by (rule penv_inv_swf_env[OF pe])
  have tps_wf: "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u"
    using tpok ptpok_swf by fast
  have wS: "\<forall>X\<in>set Bs. wfp ar X" "wfp ar Bi" "wfp ar C" using wfp_list_impliesD[OF state(2)] by simp_all
  have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax Bi" "ibelow smax C" using state(3) by simp_all
  have wR: "\<forall>X\<in>set (rev rAs). wfp ar X" "wfp ar B" using wfp_list_impliesD[OF rule(2)] by simp_all
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
      with res show thesis
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
        by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
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
  have wP: "\<forall>X\<in>set Pre. wfp ar X" "\<forall>X\<in>set As0. wfp ar X" using wR(1) rAs by auto
  have lr0: "lifted \<Longrightarrow> lifted_rule smax Bi (Pre @ As0) B" using rule(3) rAs by simp
  have lr: "lifted \<Longrightarrow> lifted_rule smax Bi As0 B"
    using lr0 by (induction Pre) (auto dest: lifted_rule_Cons)
  obtain tab where
    ren: "\<And>x. ren_name tab x \<noteq> x \<Longrightarrow> (\<forall>(t, u)\<in>set dps. x \<notin> fst ` vars t) \<and>
      (\<forall>(t, u)\<in>set (rtpairs @ tps1). x \<notin> fst ` vars t \<and> x \<notin> fst ` vars u)"
    and nlt: "\<not> lifted \<Longrightarrow> tab = []"
    and nah: "\<And>\<rho> \<sigma>. rigid_subst \<sigma> \<Longrightarrow> closed_on UNIV \<sigma> \<Longrightarrow>
      list_all2 (\<lambda>A' A. holds (sm \<rho> \<sigma> A') \<longrightarrow> holds (sm \<rho> (\<sigma> \<circ>\<^sub>s rsub smax tab) A)) (na_As na) As0"
    using newAs_holds[OF na, of B ar] lr iS(2) wP(2) vl by (auto simp: ctx_sel)
  have wN: "\<forall>X\<in>set (na_As na). wfp ar X" by (rule newAs_wfp[OF na wP(2) vl])
  text \<open>The variables that are not renamed.\<close>
  have keep: "sm \<rho> (\<sigma> \<circ>\<^sub>s rsub smax tab) t = sm \<rho> \<sigma> t"
    if "\<And>x. x \<in> vars t \<Longrightarrow> snd x \<le> smax \<or> ren_name tab (fst x) = fst x" for \<rho> \<sigma> t
    using that by (intro sm_rsub_id) blast
  show ?thesis
  proof (rule validI)
    fix \<rho> \<sigma> assume g: "gtinst \<rho>" and cl: "closed_on UNIV \<sigma>" and rg: "rigid_subst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set (br_tpairs r) \<Longrightarrow> sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
    obtain \<rho>' \<sigma>' where ie: "iext env' \<rho> \<sigma> \<rho>' \<sigma>'" by (rule iext_exists[OF pe g cl rg])
    from ie have gs: "gsol alg ar (tyenv env') \<rho>'" and cl': "closed_on UNIV \<sigma>'"
      and rg': "rigid_subst \<sigma>'" and ps: "psat (\<sigma>' \<circ> cren \<rho>') env'"
      by (simp_all add: iext_def)
    have g': "gtinst \<rho>'" by (rule gtinst_gsol[OF gs])
    let ?\<sigma>r = "\<sigma>' \<circ>\<^sub>s rsub smax tab"
    have clr: "closed_on UNIV ?\<sigma>r" by (rule closed_comp_rsub[OF cl'])
    have rgr: "rigid_subst ?\<sigma>r" by (rule rigid_subst_comp_rsub[OF rg'])
    have tsol: "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
      by (rule addth_tpairs[OF ad ie rg swf tps_wf]) (use sol in auto)
    have dsol: "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
    proof -
      have "\<forall>(t, u)\<in>set tps. mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma>' \<circ> cren \<rho>') (tr u)"
        using tsol by (simp add: sm_def mk_subst_inst)
      with pu ps have "dsolved_all (\<sigma>' \<circ> cren \<rho>') (dps_of tus)" by (auto simp: punifier_def)
      with that have "dsolved (\<sigma>' \<circ> cren \<rho>') ([], t, u)" by fastforce
      then show ?thesis by (simp add: dsolved_Nil unifies_def sm_def mk_subst_inst)
    qed
    text \<open>The instances of the proof state and of the rule.\<close>
    have hS: "holds (sm \<rho>' \<sigma>' (list_implies (Bs @ [Bi]) C))"
      by (rule validD[OF state(1) g' cl' rg']) (use dsol tus in auto)
    have hR: "holds (sm \<rho>' ?\<sigma>r (list_implies (rev rAs) B))"
    proof (rule validD[OF rule(1) g' clr rgr])
      fix t u assume tu: "(t, u) \<in> set rtpairs"
      have nr: "ren_name tab (fst x) = fst x" if "x \<in> vars t \<union> vars u" for x
      proof (rule ccontr)
        assume "ren_name tab (fst x) \<noteq> fst x"
        from ren[OF this] have "\<forall>(t, u)\<in>set rtpairs. fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u"
          by simp
        with tu have "fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u" by blast
        with that show False by blast
      qed
      have "sm \<rho>' ?\<sigma>r t = sm \<rho>' \<sigma>' t" "sm \<rho>' ?\<sigma>r u = sm \<rho>' \<sigma>' u"
        by (rule keep; simp add: nr)+
      with dsol[of t u] tus tu show "sm \<rho>' ?\<sigma>r t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' ?\<sigma>r u" by auto
    qed
    text \<open>The conclusion of the rule implies the subgoal.\<close>
    have BBi_sol: "sm \<rho>' \<sigma>' (fst BBi) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' (snd BBi)"
      using dsol[of "fst BBi" "snd BBi"] tus by simp
    have pv: "\<forall>x\<in>pvars p. snd x \<le> smax" if "lsplit Bi = (p, Bi0)" for p Bi0
      using iS(2) lsplit_ok[OF that] by (auto simp: ibelow_def vars_lift_pre)
    have hBi: "holds (sm \<rho>' \<sigma>' Bi)" if hB: "holds (sm \<rho>' ?\<sigma>r B)"
    proof (cases lifted)
      case True
      from lr0[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
        and at: "atomic Bi0" by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      have nr: "ren_name tab (fst x) = fst x" if "x \<in> vars B0" for x
      proof (rule ccontr)
        assume "ren_name tab (fst x) \<noteq> fst x"
        from ren[OF this] dps have "case BBi of (t, u) \<Rightarrow> fst x \<notin> fst ` vars t" by blast
        with that BBi show False by (simp add: vars_abs_pre)
      qed
      have "sm \<rho>' ?\<sigma>r B = sm \<rho>' \<sigma>' B"
        by (rule keep) (use pv[OF ls] nr in \<open>auto simp: B vars_lift_pre\<close>)
      with hB have "holds (sm \<rho>' \<sigma>' (lift_pre p B0))" by (simp add: B)
      from holds_lift_pre_transfer[OF rg' cl' ok _ _ _ _ _ this] wR(2) wS(2) BBi_sol BBi B Bi
      show ?thesis by (simp add: wfp_def)
    next
      case False
      then have "sm \<rho>' ?\<sigma>r B = sm \<rho>' \<sigma>' B" by (intro keep) (simp add: nlt ren_name_def)
      moreover have "BBi = (B, Bi)" using False by (simp add: BBi_def)
      ultimately show ?thesis using hB BBi_sol wR(2) wS(2)
        by (intro holds_equiv[of "sm \<rho>' \<sigma>' B" "sm \<rho>' \<sigma>' Bi"]) (auto simp: wfp_def no_loose_bound_sm[OF cl'])
    qed
    text \<open>The premise proved by an assumption.\<close>
    have hPre: "holds (sm \<rho>' ?\<sigma>r A1)" if A1: "A1 \<in> set Pre" for A1
    proof -
      from pre[OF A1] obtain params asms concl asm where er: "eres_flg" "Pre = [A1]"
        and ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and asm: "asm \<in> set asms"
        and cd: "(rlist_abs params concl, rlist_abs params asm) \<in> set dps"
        and ac: "(rlist_abs params asm, rlist_abs params concl) \<in> set tus"
        by blast
      have wA1: "wfp ar A1" using wP(1) A1 by blast
      have e: "sm \<rho>' \<sigma>' (rlist_abs params asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' (rlist_abs params concl)" by (rule dsol[OF ac])
      have c: "sm \<rho>' ?\<sigma>r (rlist_abs params concl) = sm \<rho>' \<sigma>' (rlist_abs params concl)"
      proof (rule keep)
        fix x assume x: "x \<in> vars (rlist_abs params concl)"
        show "snd x \<le> smax \<or> ren_name tab (fst x) = fst x"
        proof (rule disjI2, rule ccontr)
          assume "ren_name tab (fst x) \<noteq> fst x"
          from ren[OF this] cd have "fst x \<notin> fst ` vars (rlist_abs params concl)" by auto
          with x show False by blast
        qed
      qed
      have a: "sm \<rho>' ?\<sigma>r (rlist_abs params asm) = sm \<rho>' \<sigma>' (rlist_abs params asm)"
      proof (cases lifted)
        case True
        from lr0[OF True] obtain p Bi0 As0' where ls: "lsplit Bi = (p, Bi0)"
          and As: "Pre @ As0 = map (lift_pre p) As0'" by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
          and at: "atomic Bi0" by auto
        from As er(2) obtain X1 where A1': "A1 = lift_pre p X1" by (cases As0') auto
        have "nlift + 1 = count_prems (strip_all_body Bi)" using er(1) by (simp add: nlift_def)
        then have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ ap[unfolded A1']] Bi by simp
        with asm have "vars asm \<subseteq> pvars p" by (auto dest: vars_phyps)
        with pv[OF ls] show ?thesis by (intro keep) (auto simp: vars_rlist_abs)
      next
        case False
        then show ?thesis by (intro keep) (simp add: nlt ren_name_def)
      qed
      show ?thesis
        by (rule eres_holds[OF ap asm _ rgr clr]) (use e a c wA1 in \<open>simp_all add: wfp_def\<close>)
    qed
    text \<open>The instance of the composed theorem.\<close>
    have clX: "closed (sm \<rho>' \<sigma>' X)" if "wfp ar X" for X
      using that cl' by (simp add: wfp_def no_loose_bound_sm)
    have clXr: "closed (sm \<rho>' ?\<sigma>r X)" if "wfp ar X" for X
      using that clr by (simp add: wfp_def no_loose_bound_sm)
    have hS': "holds (sm \<rho>' \<sigma>' C)"
      if "\<forall>X\<in>set Bs. holds (sm \<rho>' \<sigma>' X)" "holds (sm \<rho>' \<sigma>' Bi)"
    proof -
      have "\<forall>A\<in>set (map (sm \<rho>' \<sigma>') (Bs @ [Bi])). closed A" using wS clX by auto
      from holds_foldr_dIMP[OF this clX[OF wS(3)]] hS that show ?thesis
        by (simp add: sm_list_implies[OF rg'] del: map_append foldr_append)
    qed
    have hR': "holds (sm \<rho>' ?\<sigma>r B)" if "\<forall>X\<in>set (Pre @ As0). holds (sm \<rho>' ?\<sigma>r X)"
    proof -
      have "\<forall>A\<in>set (map (sm \<rho>' ?\<sigma>r) (Pre @ As0)). closed A" using wP clXr by auto
      from holds_foldr_dIMP[OF this clXr[OF wR(2)]] hR that rAs show ?thesis
        by (simp add: sm_list_implies[OF rgr] del: map_append foldr_append)
    qed
    have hN: "holds (sm \<rho>' \<sigma>' (list_implies (Bs @ na_As na) C))"
    proof -
      have "holds (sm \<rho>' \<sigma>' C)" if H: "\<forall>X\<in>set (Bs @ na_As na). holds (sm \<rho>' \<sigma>' X)"
      proof -
        have "\<forall>X\<in>set As0. holds (sm \<rho>' ?\<sigma>r X)"
          using list_all2_imp_all[OF nah[OF rg' cl', of \<rho>']] H by simp
        with hPre have "holds (sm \<rho>' ?\<sigma>r B)" by (intro hR') auto
        then have "holds (sm \<rho>' \<sigma>' Bi)" by (rule hBi)
        with H show ?thesis by (intro hS') auto
      qed
      moreover have "\<forall>A\<in>set (map (sm \<rho>' \<sigma>') (Bs @ na_As na)). closed A" using wS wN clX by auto
      ultimately show ?thesis using holds_foldr_dIMP[OF _ clX[OF wS(3)]]
        by (simp add: sm_list_implies[OF rg'] del: map_append foldr_append)
    qed
    text \<open>The new theorem.\<close>
    show "holds (sm \<rho> \<sigma> (br_prop r))"
    proof (rule addth_holds[OF ad ie rg cl swf])
      show "\<forall>X\<in>insert (bc_C ctx) (set (bc_Bs ctx)). wfp ar X \<and> ibelow (bc_smax ctx) X"
        using wS iS by (simp add: ctx_sel)
      show "\<forall>X\<in>set (na_As na). wfp ar X" by (rule wN)
      show "holds (sm \<rho>' \<sigma>' (list_implies (bc_Bs ctx @ na_As na) (bc_C ctx)))"
        using hN by (simp add: ctx_sel)
      assume "bc_lifted ctx"
      then have lf: lifted by (simp add: ctx_sel)
      have "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)).
          \<exists>H0\<in>set (spine_hyps Bi). vars H = vars H0 \<and> tys H = tys H0"
        using newAs_skip[OF na _ _ wP(2) vl n(4)] lf lr n(2,3) by (simp add: ctx_sel)
      then show "0 \<le> bc_nlift ctx \<and> (\<forall>X\<in>set (na_As na).
          \<forall>H\<in>set (take (nat_of_integer (bc_nlift ctx)) (spine_hyps X)). ibelow (bc_smax ctx) H)"
        using ibelow_spine_hyps[OF iS(2)] n(4) by (fastforce simp: ctx_sel ibelow_def)
    qed
  qed
qed

end

end
