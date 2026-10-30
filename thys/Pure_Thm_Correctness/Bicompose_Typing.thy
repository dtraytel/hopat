section \<open>Well-Typed Problems of Unification\<close>

theory Bicompose_Typing
  imports Bicompose_Seq
begin

text \<open>
  The unifiers that \<open>bicompose_aux\<close> enumerates are characterized for well-typed problems
  (\<^const>\<open>wf_algebra.pinv_all\<close>). The problems are well-typed if the proof state and the rule are.
\<close>

subsection \<open>Types of propositions\<close>

lemma has_type_implies:
  "has_type W Ts (implies $ A $ B) T \<longleftrightarrow> T = propT \<and> has_type W Ts A propT \<and> has_type W Ts B propT"
  by (auto elim!: has_type_elims intro!: has_type.App has_type.Const simp: implies_imp_type imp_type_def)

lemma has_type_list_impliesD:
  "has_type W Ts (list_implies As B) propT \<Longrightarrow> (\<forall>A\<in>set As. has_type W Ts A propT) \<and> has_type W Ts B propT"
  by (induction As) (auto simp: mk_implies_def has_type_implies)

lemma has_type_all_const:
  "has_type W Ts (all_const T $ Abs a T B) U \<longleftrightarrow> U = propT \<and> has_type W (T # Ts) B propT"
  by (auto elim!: has_type_elims intro!: has_type.App has_type.Const has_type.Abs
      simp: all_const_all_type all_type_def)

lemma has_type_list_forallD:
  "has_type W Ts (list_forall ps B) propT \<Longrightarrow> has_type W (rev (map snd ps) @ Ts) B propT"
  by (induction ps B arbitrary: Ts rule: list_forall.induct) (auto simp: has_type_all_const)

lemma tys_list_forall: "tys (list_forall ps B) = (\<Union>(a, T)\<in>set ps. {all_type T, T}) \<union> tys B"
  by (induction ps B rule: list_forall.induct) (auto simp: all_const_all_type)

lemma vars_list_forall: "vars (list_forall ps B) = vars B"
  by (induction ps B rule: list_forall.induct) (auto simp: all_const_def)

lemma tys_list_implies: "tys (list_implies As B) = (if As = [] then {} else {imp_type}) \<union> (\<Union>A\<in>set As. tys A) \<union> tys B"
  by (induction As) (auto simp: mk_implies_def implies_imp_type)

lemma vars_list_implies: "vars (list_implies As B) = (\<Union>A\<in>set As. vars A) \<union> vars B"
  by (induction As) (auto simp: mk_implies_def implies_def)

text \<open>The types of the parameters of a prefix, outermost first.\<close>

fun ptys :: "litem list \<Rightarrow> ptyp list" where
  "ptys [] = []"
| "ptys (LImp c H # p) = ptys p"
| "ptys (LAll c a T # p) = T # ptys p"

lemma has_type_abs_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> cok (lift_pre p X) \<Longrightarrow> has_type W Ts (lift_pre p X) propT \<Longrightarrow>
    has_type W Ts (abs_pre p X) (foldr fun_type (ptys p) propT)"
proof (induction p arbitrary: Ts)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.imp'' U" by auto
    have "U = imp_type \<and> cok H \<and> cok (lift_pre p X)"
      by (rule cok_imp) (use Cons.prems(2) LImp c in simp_all)
    with Cons LImp c show ?thesis by (simp add: implies_imp_type[symmetric] has_type_implies)
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where c: "c = Const STR ''Pure.all'' U" by auto
    with Cons.prems(2) LAll have "U = all_type T" "cok (lift_pre p X)" by auto
    with Cons LAll c show ?thesis
      by (auto simp: all_const_all_type[symmetric] has_type_all_const intro: has_type.Abs)
  qed
qed simp

lemma has_type_assum_problems:
  assumes "assum_problems k A = (params, asms, concl)" "cok A" "has_type W [] A propT" "asm \<in> set asms"
  shows "has_type W [] (rlist_abs params asm) (foldr fun_type (rev (map snd params)) propT)"
    "has_type W [] (rlist_abs params concl) (foldr fun_type (rev (map snd params)) propT)"
proof -
  from assum_problems_struct[OF assms(1,2)]
  have A: "A = list_forall (rev params) (list_implies asms concl)" by blast
  from has_type_list_forallD[of W "[]" "rev params"] assms(3) A
  have "has_type W (map snd params) (list_implies asms concl) propT" by (simp add: rev_map)
  from has_type_list_impliesD[OF this] assms(4)
  have "has_type W (map snd params @ []) asm propT" "has_type W (map snd params @ []) concl propT" by auto
  then show "has_type W [] (rlist_abs params asm) (foldr fun_type (rev (map snd params)) propT)"
    "has_type W [] (rlist_abs params concl) (foldr fun_type (rev (map snd params)) propT)"
    by (auto intro: has_type_rlist_abs)
qed

lemma swf_abs_pre_gen: "swf_tm ar rb (lift_pre p X) \<Longrightarrow> swf_tm ar rb (abs_pre p X)"
proof (induction p arbitrary: rb)
  case (Cons i p)
  then show ?case
  proof (cases i)
    case (LAll c a T)
    with Cons.prems have "swf_tm ar ((a, T) # rb) (lift_pre p X)" "wft ar T"
      by (simp_all add: swf_tm_def)
    from Cons.IH[OF this(1)] this(2) LAll show ?thesis by (simp add: swf_tm_def)
  next
    case (LImp c H)
    with Cons.prems have "swf_tm ar rb (lift_pre p X)" by (simp add: swf_tm_def)
    from Cons.IH[OF this] LImp show ?thesis by simp
  qed
qed simp

lemma swf_abs_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> swf_tm ar [] (lift_pre p X) \<Longrightarrow> swf_tm ar [] (abs_pre p X)"
  by (rule swf_abs_pre_gen)

lemma swf_assum_problems:
  assumes "assum_problems k A = (params, asms, concl)" "cok A" "swf_tm ar [] A" "asm \<in> set asms"
  shows "swf_tm ar [] (rlist_abs params asm)" "swf_tm ar [] (rlist_abs params concl)"
proof -
  from assum_problems_struct[OF assms(1,2)]
  have A: "A = list_forall (rev params) (list_implies asms concl)" by blast
  have sb: "sbinders ar params" and tw: "twft ar (list_implies asms concl)"
    using assms(3) A by (auto simp: swf_tm_def sbinders_def twft_tys tys_list_forall)
  have "swf_tm ar params X" if "X \<in> insert concl (set asms)" for X
    using assms(3) A that tw by (auto simp: swf_tm_def no_loose_bound_list_forall
      no_loose_bound_list_implies twft_tys tys_list_implies)
  then show "swf_tm ar [] (rlist_abs params asm)" "swf_tm ar [] (rlist_abs params concl)"
    using assms(4) sb by (auto simp: swf_tm_def proper_rlist_abs twft_rlist_abs tr_rlist_abs)
qed

lemma tys_vars_abs_pre: "tys (abs_pre p X) \<subseteq> tys (lift_pre p X) \<and> vars (abs_pre p X) \<subseteq> vars (lift_pre p X)"
  by (induction p X rule: abs_pre.induct) auto

lemma tys_vars_assum_problems:
  assumes "assum_problems k A = (params, asms, concl)" "cok A" "asm \<in> set asms"
  shows "tys (rlist_abs params asm) \<subseteq> tys A" "vars (rlist_abs params asm) \<subseteq> vars A"
    "tys (rlist_abs params concl) \<subseteq> tys A" "vars (rlist_abs params concl) \<subseteq> vars A"
proof -
  from assum_problems_struct[OF assms(1,2)]
  have A: "A = list_forall (rev params) (list_implies asms concl)" by blast
  show "tys (rlist_abs params asm) \<subseteq> tys A" "vars (rlist_abs params asm) \<subseteq> vars A"
    "tys (rlist_abs params concl) \<subseteq> tys A" "vars (rlist_abs params concl) \<subseteq> vars A"
    using assms(3) by (auto simp: A tys_rlist_abs vars_rlist_abs tys_list_forall vars_list_forall
      tys_list_implies vars_list_implies)
qed


text \<open>The premises stripped from a rule:\<close>

lemma lift_pre_limp:
  "\<forall>it\<in>set p. is_limp it \<and> litem_ok it \<Longrightarrow> cok (lift_pre p B) \<Longrightarrow>
    lift_pre p B = list_implies (map lhyp p) B"
proof (induction p)
  case (Cons it p)
  have "is_limp it \<and> litem_ok it" using Cons.prems(1) by simp
  then obtain U H where it: "it = LImp (Const STR ''Pure.imp'' U) H" by (cases it) auto
  have "U = imp_type \<and> cok H \<and> cok (lift_pre p B)"
    by (rule cok_imp) (use Cons.prems(2) it in simp_all)
  with Cons it show ?case by (simp add: implies_imp_type mk_implies_def)
qed simp

lemma list_implies_strip_prems:
  assumes "ok (strip_prems i [] P) (rAs, B)" "cok P"
  shows "P = list_implies (rev rAs) B"
proof -
  from strip_prems_ok[OF assms(1)] obtain p where p: "P = lift_pre p B"
    "\<forall>it\<in>set p. is_limp it \<and> litem_ok it" "rAs = rev (map lhyp p)"
    by auto
  with lift_pre_limp[OF p(2)] assms(2) show ?thesis by simp
qed


subsection \<open>Well-typed theorems\<close>

text \<open>
  Types are well-formed and their type variables are among \<open>A\<close>. A term of a theorem with
  maximal index \<open>m\<close> is well-typed under the typing \<open>W\<close> of its variables, well-formed, and
  its variables have indices of at most \<open>m\<close>.
\<close>

definition tyA :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tyA ar A T \<longleftrightarrow> tvars T \<subseteq> A \<and> wft ar T"

definition wt_term :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow>
    pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "wt_term ar A W m t T \<longleftrightarrow> has_type W [] t T \<and> swf_tm ar [] t \<and> below m t \<and> (\<forall>U\<in>tys t. tyA ar A U)"

definition wt_thm :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow>
    (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "wt_thm ar A W m tps P \<longleftrightarrow> wt_term ar A W m P propT \<and> cok P \<and>
    (\<forall>(t, u)\<in>set tps. \<exists>T. wt_term ar A W m t T \<and> wt_term ar A W m u T)"

lemma empty_env_simps[simp]:
  "maxidx (empty_env m) = m" "tenv (empty_env m) = vt_empty" "tyenv (empty_env m) = vt_empty"
  "etys (empty_env m) = {}" "etvars (empty_env m) = {}"
  by (simp_all add: empty_env_def etys_def etvars_def)

lemma tinv_empty_env: "scons A \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> m \<Longrightarrow> tinv ar m vt_empty A"
  by (simp add: tinv_def tacyc_empty tvars_env_def)

lemma tyw_empty: "tyA ar A T \<Longrightarrow> tyw ar vt_empty A T"
  by (auto simp: tyA_def tyw_def tvars_env_def uvars_def uvarsA_def tnorm_empty)

lemma wt_term_mono: "wt_term ar A W m t T \<Longrightarrow> m \<le> m' \<Longrightarrow> wt_term ar A W m' t T"
  by (auto simp: wt_term_def intro: below_mono)

lemma wt_term_list_implies:
  assumes "wt_term ar A W m (list_implies As B) propT"
  shows "\<forall>X\<in>set As. wt_term ar A W m X propT" "wt_term ar A W m B propT"
  using assms has_type_list_impliesD[of W "[]" As B]
  by (auto simp: wt_term_def swf_tm_def twft_tys tys_list_implies no_loose_bound_list_implies
      below_def vars_list_implies)

lemma wt_term_sub:
  "wt_term ar A W m t U \<Longrightarrow> has_type W [] t' T \<Longrightarrow> swf_tm ar [] t' \<Longrightarrow> tys t' \<subseteq> tys t \<Longrightarrow>
    vars t' \<subseteq> vars t \<Longrightarrow> wt_term ar A W m t' T"
  by (auto simp: wt_term_def below_def)

context wf_algebra
begin

lemma penv_inv_empty_env: "penv_inv alg ar W (empty_env m)"
  by (simp add: penv_inv_def pwf_env_def wt_env_def fresh_env_def nacyc_def ndep_def acyclic_def
      tsorted_empty tinv_empty_env scons_def)

lemma pinv_empty_env:
  assumes "scons A" "\<forall>p\<in>A. snd (fst p) \<le> m" "\<forall>x. tyA ar A (W x)"
    "\<forall>(t, u)\<in>set tus. \<exists>T. wt_term ar A W m t T \<and> wt_term ar A W m u T"
  shows "pinv alg ar A W (empty_env m) (dps_of tus)"
proof -
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar vt_empty A T) \<and> ptyped (empty_env m) W dp \<and> dp_below m dp"
    if "dp \<in> set (dps_of tus)" for dp
  proof -
    from that obtain t u where dp: "dp = ([], t, u)" and tu: "(t, u) \<in> set tus" by auto
    from assms(4) tu obtain T where "wt_term ar A W m t T" "wt_term ar A W m u T" by blast
    then show ?thesis
      by (auto simp: dp wt_term_def sbinders_def typed_empty vtyp_def[abs_def] dp_below_def intro: tyw_empty)
  qed
  then show ?thesis
    using assms(1-3) by (simp add: pinv_def penv_inv_empty_env tinv_empty_env wcons_def tyw_empty)
qed

text \<open>The problems of a call are well-typed if the types of the variables need not be unified.\<close>

theorem pinv_all_empty_env:
  assumes state: "wt_thm ar A W smax stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A W rmax rtpairs rprop" "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (W x)"
  shows "pinv_all (call_spec cfg A vl (empty_env (max rmax smax)) flatten match_flg smax stpairs Bs Bi C
    lifted eres_flg rtpairs rAs B)"
proof -
  let ?m = "max rmax smax"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  let ?sp = "BSpec cfg A vl (empty_env ?m) ctx rAs eres_flg"
  have sp: "call_spec cfg A vl (empty_env ?m) flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B = ?sp"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have mono: "wt_term ar A W ?m t T" if "wt_term ar A W smax t T \<or> wt_term ar A W rmax t T" for t T
    using that wt_term_mono[of ar A W smax t T ?m] wt_term_mono[of ar A W rmax t T ?m] by auto
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF rule(2)]) (use rule(1) in \<open>simp add: wt_thm_def\<close>)
  have wS: "\<forall>X\<in>set Bs. wt_term ar A W ?m X propT" "wt_term ar A W ?m Bi propT"
    using wt_term_list_implies[of ar A W smax "Bs @ [Bi]" C] state mono by (auto simp: wt_thm_def)
  have wR: "\<forall>X\<in>set (rev rAs). wt_term ar A W ?m X propT" "wt_term ar A W ?m B propT"
    using wt_term_list_implies[of ar A W rmax "rev rAs" B] rule(1) P mono by (auto simp: wt_thm_def)
  have cS: "cok Bi" using state by (simp add: wt_thm_def)
  have cR: "\<forall>X\<in>set (rev rAs). cok X" "cok B" using rule(1) P by (simp_all add: wt_thm_def)
  text \<open>The disagreement pairs.\<close>
  have tps: "\<exists>T. wt_term ar A W ?m t T \<and> wt_term ar A W ?m u T" if "(t, u) \<in> set (rtpairs @ stpairs)" for t u
  proof -
    from that consider "(t, u) \<in> set rtpairs" | "(t, u) \<in> set stpairs" by auto
    then show ?thesis
    proof cases
      case 1
      with rule(1) obtain T where "wt_term ar A W rmax t T" "wt_term ar A W rmax u T"
        unfolding wt_thm_def by blast
      with mono show ?thesis by blast
    next
      case 2
      with state obtain T where "wt_term ar A W smax t T" "wt_term ar A W smax u T"
        unfolding wt_thm_def by blast
      with mono show ?thesis by blast
    qed
  qed
  have BBi: "\<exists>T. wt_term ar A W ?m (fst BBi) T \<and> wt_term ar A W ?m (snd BBi) T"
  proof (cases lifted)
    case True
    from lift[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0" by blast
    from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" by auto
    have BBi': "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    have "wt_term ar A W ?m (abs_pre p X) (foldr fun_type (ptys p) propT)"
      if "wt_term ar A W ?m (lift_pre p X) propT" "cok (lift_pre p X)" for X
      using wt_term_sub[OF that(1) has_type_abs_pre[OF ok that(2)] swf_abs_pre[OF ok]] that(1)
        tys_vars_abs_pre[of p X]
      by (simp add: wt_term_def)
    with wS(2) wR(2) cS cR(2) B Bi BBi' show ?thesis by auto
  next
    case False
    with wS(2) wR(2) show ?thesis by (auto simp: BBi_def)
  qed
  have dps: "\<forall>(t, u)\<in>set (BBi # rtpairs @ stpairs). \<exists>T. wt_term ar A W ?m t T \<and> wt_term ar A W ?m u T"
    using tps BBi by (auto simp: case_prod_unfold)
  have pi: "pinv alg ar A W (empty_env ?m) (dps_of tus)"
    if "\<forall>(t, u)\<in>set tus. \<exists>T. wt_term ar A W ?m t T \<and> wt_term ar A W ?m u T" for tus
    by (rule pinv_empty_env[OF A that])
  have "pinv_all ?sp"
    unfolding pinv_all_def
  proof (intro conjI impI ballI)
    assume "\<not> bs_eres ?sp"
    show "\<exists>W. pinv alg ar (bs_A ?sp) W (bs_env ?sp) (dps_of (bc_dpairs (bs_ctx ?sp)))"
      using pi[OF dps] by (auto simp: ctx_def)
  next
    fix asm assume er: "bs_eres ?sp" and asm: "asm \<in> set (asms_of ?sp)"
    then obtain A1 As where rA: "rev rAs = A1 # As" by (cases "rev rAs") (auto simp: asms_of_def)
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_prob ?sp asm = (rlist_abs params asm, rlist_abs params concl) # bc_dpairs ctx"
      "asm \<in> set asms"
      using rA ap asm by (simp_all add: eres_prob_def eres_of_def asms_of_def ctx_def)
    have wA1: "wt_term ar A W ?m A1 propT" "cok A1" using wR(1) cR(1) rA by auto
    have "wt_term ar A W ?m (rlist_abs params X) (foldr fun_type (rev (map snd params)) propT)"
      if "X \<in> {asm, concl}" for X
    proof (rule wt_term_sub[OF wA1(1)])
      show "has_type W [] (rlist_abs params X) (foldr fun_type (rev (map snd params)) propT)"
        "swf_tm ar [] (rlist_abs params X)" "tys (rlist_abs params X) \<subseteq> tys A1"
        "vars (rlist_abs params X) \<subseteq> vars A1"
        using that has_type_assum_problems[OF ap wA1(2) _ e(2)] swf_assum_problems[OF ap wA1(2) _ e(2)]
          tys_vars_assum_problems[OF ap wA1(2) e(2)] wA1(1)
        by (auto simp: wt_term_def)
    qed
    then have h: "\<exists>T. wt_term ar A W ?m (rlist_abs params asm) T \<and> wt_term ar A W ?m (rlist_abs params concl) T"
      by blast
    have st: "set (eres_prob ?sp asm) =
        insert (rlist_abs params asm, rlist_abs params concl) (set (BBi # rtpairs @ stpairs))"
      using e(1) by (simp add: ctx_def)
    have "\<forall>(t, u)\<in>set (eres_prob ?sp asm). \<exists>T. wt_term ar A W ?m t T \<and> wt_term ar A W ?m u T"
      unfolding st using h dps by (simp only: set_simps ball_simps prod.case) blast
    from pi[OF this] show "\<exists>W. pinv alg ar (bs_A ?sp) W (bs_env ?sp) (dps_of (eres_prob ?sp asm))"
      by auto
  qed
  then show ?thesis by (simp only: sp)
qed

end

end
