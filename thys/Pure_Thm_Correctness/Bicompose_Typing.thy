section \<open>Well-Typed Problems of Unification\<close>

theory Bicompose_Typing
  imports Bicompose_Seq
begin

context csig
begin

text \<open>
  The unifiers that \<open>bicompose_aux\<close> enumerates are characterized for well-typed problems
  (\<^const>\<open>wf_csig.pinv_all\<close>). The problems are well-typed if the proof state and the rule are.
\<close>

subsection \<open>Types of propositions\<close>

lemma const_typ_ok_imp_type[simp]: "const_typ_ok STR ''Pure.imp'' imp_type"
  and const_typ_ok_all_type[simp]: "const_typ_ok STR ''Pure.all'' (all_type T)"
  by (auto simp: const_typ_ok_def imp_type_def all_type_def propT_def)

lemma has_type_implies:
  "has_type W Ts (implies $ A $ B) T \<longleftrightarrow> T = propT \<and> has_type W Ts A propT \<and> has_type W Ts B propT"
  by (auto elim!: has_type_elims intro!: has_type.App has_type.Const
      simp: implies_def const_typ_ok_def propT_def)

lemma has_type_list_impliesD:
  "has_type W Ts (list_implies As B) propT \<Longrightarrow> (\<forall>A\<in>set As. has_type W Ts A propT) \<and> has_type W Ts B propT"
  by (induction As) (auto simp: mk_implies_def has_type_implies)

lemma has_type_all_const:
  "has_type W Ts (all_const T $ Abs a T B) U \<longleftrightarrow> U = propT \<and> has_type W (T # Ts) B propT"
  by (auto elim!: has_type_elims intro!: has_type.App has_type.Const has_type.Abs
      simp: all_const_all_type all_type_def const_typ_ok_def propT_def)

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

definition vars_thm :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> indexname set" where
  "vars_thm tps P = vars P \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u)"

text \<open>
  Typing modulo a type environment \<open>\<theta>\<close>: a term of a theorem typed by \<open>Wt\<close> is typed by \<open>W\<close>
  modulo \<open>\<theta>\<close> if \<open>Wt\<close> and \<open>W\<close> agree modulo \<open>\<theta>\<close> on its variables.
\<close>

definition wt_mod :: "(name \<Rightarrow> nat) \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> tyenv \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow>
    (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "wt_mod ar A \<theta> W Wt m t T \<longleftrightarrow> wt_term ar A Wt m t T \<and> (\<forall>x\<in>vars t. tnorm \<theta> (Wt x) = tnorm \<theta> (W x))"

lemma wt_modI:
  "wt_term ar A Wt m t T \<Longrightarrow> m \<le> m' \<Longrightarrow> vars t \<subseteq> V \<Longrightarrow> \<forall>x\<in>V. tnorm \<theta> (Wt x) = tnorm \<theta> (W x) \<Longrightarrow>
    wt_mod ar A \<theta> W Wt m' t T"
  by (auto simp: wt_mod_def intro: wt_term_mono)

end

context wf_csig
begin

text \<open>
  The environments of a call before the search for unifiers: the types of the variables are
  unified (\<open>unify_var_types\<close>), the term environment is empty.
\<close>

definition tvinv :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> env \<Rightarrow> bool" where
  "tvinv A m env \<longleftrightarrow> vt_is_empty (tenv env) \<and> m \<le> maxidx env \<and> tinv ar (maxidx env) (tyenv env) A \<and>
    tsorted alg (tyenv env) \<and> tcert alg A \<and> tcert alg (tvars_env (tyenv env))"

lemma tvinv_empty_env: "scons A \<Longrightarrow> \<forall>p\<in>A. snd (fst p) \<le> m \<Longrightarrow> tcert alg A \<Longrightarrow> tvinv A m (empty_env m)"
  by (simp add: tvinv_def tinv_empty_env tsorted_empty tvars_env_def)

lemma tinv_subset: "tinv ar n \<theta> A \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> tinv ar n \<theta> A'"
  unfolding tinv_def scons_def by blast

lemma penv_inv_tvinv: "tvinv A m env \<Longrightarrow> penv_inv alg ar W env"
  by (auto simp: tvinv_def penv_inv_def pwf_env_def wt_env_def fresh_env_def nacyc_def ndep_def acyclic_def
      vt_is_empty_lookup etvars_def etys_def intro: tinv_subset)

lemma pinv_tvinv:
  assumes "tvinv A m env" "\<forall>x. tyA ar A (W x)"
    "\<forall>(t, u)\<in>set tus. \<exists>T Wt Wu. wt_mod ar A (tyenv env) W Wt m t T \<and> wt_mod ar A (tyenv env) W Wu m u T"
  shows "pinv alg ar A W env (dps_of tus)"
proof -
  let ?\<theta> = "tyenv env"
  from assms(1) have te: "vt_is_empty (tenv env)" and mx: "m \<le> maxidx env"
    and ti: "tinv ar (maxidx env) ?\<theta> A"
    by (simp_all add: tvinv_def)
  have ac: "tacyc ?\<theta>" by (rule tinv_tacyc[OF ti])
  have tw: "tyw ar ?\<theta> A T" if "tyA ar A T" for T
    by (rule tyw_textends[OF ac _ tyw_empty[OF that]]) (simp add: textends_def)
  have tyd: "typed env W [] t T" if "wt_mod ar A ?\<theta> W Wt m t T" for t T Wt
  proof -
    from that have h: "has_type Wt [] t T" and ag: "\<forall>x\<in>vars t. tnorm ?\<theta> (Wt x) = tnorm ?\<theta> (W x)"
      by (simp_all add: wt_mod_def wt_term_def)
    from has_type_tnormt[OF h] have "has_type (\<lambda>x. tnorm ?\<theta> (Wt x)) [] (tnormt ?\<theta> t) (tnorm ?\<theta> T)"
      by simp
    then have "has_type (tctx env W) [] (tnormt ?\<theta> t) (tnorm ?\<theta> T)"
      by (rule has_type_vars) (use ag te in \<open>simp add: vtyp_def vt_is_empty_lookup\<close>)
    then show ?thesis by (simp add: typed_def)
  qed
  have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar ?\<theta> A T) \<and> ptyped env W dp \<and> dp_below (maxidx env) dp"
    if "dp \<in> set (dps_of tus)" for dp
  proof -
    from that obtain t u where dp: "dp = ([], t, u)" and tu: "(t, u) \<in> set tus" by auto
    from assms(3) tu obtain T Wt Wu where t: "wt_mod ar A ?\<theta> W Wt m t T" and u: "wt_mod ar A ?\<theta> W Wu m u T"
      by blast
    from tyd[OF t] tyd[OF u] have "ptyped env W dp" by (auto simp: dp)
    moreover have "swf_dp ar dp \<and> (\<forall>T\<in>dtys dp. tyw ar ?\<theta> A T) \<and> dp_below (maxidx env) dp"
      using t u mx by (auto simp: dp wt_mod_def wt_term_def sbinders_def dp_below_def intro: tw below_mono)
    ultimately show ?thesis by blast
  qed
  moreover have "etys env = {}" using te by (simp add: etys_def vt_is_empty_lookup)
  moreover have "wcons W env" using te by (simp add: wcons_def vt_is_empty_lookup)
  ultimately show ?thesis
    using assms(1,2) ti tw by (simp add: pinv_def penv_inv_tvinv) (simp add: tvinv_def)
qed

text \<open>
  The problems of a call are well-typed if the proof state and the rule are, and if their
  typings agree modulo the type environment with a common typing \<open>W\<close>.
\<close>

theorem pinv_all_tvinv:
  assumes state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop" "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and env: "tvinv A (max rmax smax) env" "\<forall>x. tyA ar A (W x)"
    and agS: "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C). tnorm (tyenv env) (Ws x) = tnorm (tyenv env) (W x)"
    and agR: "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
  shows "pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) W"
proof -
  let ?m = "max rmax smax" and ?\<theta> = "tyenv env"
  let ?VS = "vars_thm stpairs (list_implies (Bs @ [Bi]) C)" and ?VR = "vars_thm rtpairs rprop"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  let ?sp = "BSpec cfg A vl env ctx rAs eres_flg"
  have sp: "call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B = ?sp"
    by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have mS: "wt_mod ar A ?\<theta> W Ws ?m t T" if "wt_term ar A Ws smax t T" "vars t \<subseteq> ?VS" for t T
    using wt_modI[OF that(1) _ that(2) agS] by simp
  have mR: "wt_mod ar A ?\<theta> W Wr ?m t T" if "wt_term ar A Wr rmax t T" "vars t \<subseteq> ?VR" for t T
    using wt_modI[OF that(1) _ that(2) agR] by simp
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF rule(2)]) (use rule(1) in \<open>simp add: wt_thm_def\<close>)
  have wS: "wt_term ar A Ws smax Bi propT"
    using wt_term_list_implies[of ar A Ws smax "Bs @ [Bi]" C] state by (auto simp: wt_thm_def)
  have wR: "\<forall>X\<in>set (rev rAs). wt_term ar A Wr rmax X propT" "wt_term ar A Wr rmax B propT"
    using wt_term_list_implies[of ar A Wr rmax "rev rAs" B] rule(1) P by (auto simp: wt_thm_def)
  have vS: "vars Bi \<subseteq> ?VS" by (auto simp: vars_thm_def vars_list_implies)
  have vR: "\<forall>X\<in>set (rev rAs). vars X \<subseteq> ?VR" "vars B \<subseteq> ?VR"
    using P by (auto simp: vars_thm_def vars_list_implies)
  have cS: "cok Bi" using state by (simp add: wt_thm_def)
  have cR: "\<forall>X\<in>set (rev rAs). cok X" "cok B" using rule(1) P by (simp_all add: wt_thm_def)
  text \<open>The disagreement pairs.\<close>
  have tps: "\<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m t T \<and> wt_mod ar A ?\<theta> W Wu ?m u T"
    if "(t, u) \<in> set (rtpairs @ stpairs)" for t u
  proof -
    from that consider "(t, u) \<in> set rtpairs" | "(t, u) \<in> set stpairs" by auto
    then show ?thesis
    proof cases
      case 1
      with rule(1) obtain T where "wt_term ar A Wr rmax t T" "wt_term ar A Wr rmax u T"
        unfolding wt_thm_def by blast
      moreover have "vars t \<subseteq> ?VR" "vars u \<subseteq> ?VR" using 1 by (auto simp: vars_thm_def)
      ultimately show ?thesis using mR by blast
    next
      case 2
      with state obtain T where "wt_term ar A Ws smax t T" "wt_term ar A Ws smax u T"
        unfolding wt_thm_def by blast
      moreover have "vars t \<subseteq> ?VS" "vars u \<subseteq> ?VS" using 2 by (auto simp: vars_thm_def)
      ultimately show ?thesis using mS by blast
    qed
  qed
  have BBi: "\<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m (fst BBi) T \<and> wt_mod ar A ?\<theta> W Wu ?m (snd BBi) T"
  proof (cases lifted)
    case True
    from lift[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0" by blast
    from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i"
      and at: "atomic Bi0" by auto
    have BBi': "BBi = (abs_pre p B0, abs_pre p Bi0)"
      using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
    have ab: "wt_term ar A Wt m (abs_pre p X) (foldr fun_type (ptys p) propT) \<and>
        vars (abs_pre p X) \<subseteq> vars (lift_pre p X)"
      if "wt_term ar A Wt m (lift_pre p X) propT" "cok (lift_pre p X)" for Wt m X
      using wt_term_sub[OF that(1) has_type_abs_pre[OF ok that(2)] swf_abs_pre[OF ok]] that(1)
        tys_vars_abs_pre[of p X]
      by (simp add: wt_term_def)
    from ab[of Wr rmax B0] ab[of Ws smax Bi0] wS wR(2) cS cR(2) B Bi vS vR(2)
    have "wt_mod ar A ?\<theta> W Wr ?m (abs_pre p B0) (foldr fun_type (ptys p) propT)"
      "wt_mod ar A ?\<theta> W Ws ?m (abs_pre p Bi0) (foldr fun_type (ptys p) propT)"
      by (auto intro!: mR mS)
    with BBi' show ?thesis by auto
  next
    case False
    have "wt_mod ar A ?\<theta> W Wr ?m B propT" "wt_mod ar A ?\<theta> W Ws ?m Bi propT"
      using mR[OF wR(2) vR(2)] mS[OF wS vS] .
    with False show ?thesis by (auto simp: BBi_def)
  qed
  have dps: "\<forall>(t, u)\<in>set (BBi # rtpairs @ stpairs).
      \<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m t T \<and> wt_mod ar A ?\<theta> W Wu ?m u T"
    using tps BBi by (auto simp: case_prod_unfold)
  have pi: "pinv alg ar A W env (dps_of tus)"
    if "\<forall>(t, u)\<in>set tus. \<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m t T \<and> wt_mod ar A ?\<theta> W Wu ?m u T" for tus
    by (rule pinv_tvinv[OF env that])
  have "pinv_allW ?sp W"
    unfolding pinv_allW_def
  proof (intro conjI impI ballI)
    assume "\<not> bs_eres ?sp"
    show "pinv alg ar (bs_A ?sp) W (bs_env ?sp) (dps_of (bc_dpairs (bs_ctx ?sp)))"
      using pi[OF dps] by (auto simp: ctx_def)
  next
    fix asm assume er: "bs_eres ?sp" and asm: "asm \<in> set (asms_of ?sp)"
    then obtain A1 As where rA: "rev rAs = A1 # As" by (cases "rev rAs") (auto simp: asms_of_def)
    obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
      by (cases "assum_problems (nlift + 1) A1")
    have e: "eres_prob ?sp asm = (rlist_abs params asm, rlist_abs params concl) # bc_dpairs ctx"
      "asm \<in> set asms"
      using rA ap asm by (simp_all add: eres_prob_def eres_of_def asms_of_def ctx_def)
    have wA1: "wt_term ar A Wr rmax A1 propT" "cok A1" "vars A1 \<subseteq> ?VR" using wR(1) cR(1) vR(1) rA by auto
    have "wt_mod ar A ?\<theta> W Wr ?m (rlist_abs params X) (foldr fun_type (rev (map snd params)) propT)"
      if "X \<in> {asm, concl}" for X
    proof (rule mR)
      show "wt_term ar A Wr rmax (rlist_abs params X) (foldr fun_type (rev (map snd params)) propT)"
      proof (rule wt_term_sub[OF wA1(1)])
        show "has_type Wr [] (rlist_abs params X) (foldr fun_type (rev (map snd params)) propT)"
          "swf_tm ar [] (rlist_abs params X)" "tys (rlist_abs params X) \<subseteq> tys A1"
          "vars (rlist_abs params X) \<subseteq> vars A1"
          using that has_type_assum_problems[OF ap wA1(2) _ e(2)] swf_assum_problems[OF ap wA1(2) _ e(2)]
            tys_vars_assum_problems[OF ap wA1(2) e(2)] wA1(1)
          by (auto simp: wt_term_def)
      qed
      show "vars (rlist_abs params X) \<subseteq> ?VR"
        using that tys_vars_assum_problems[OF ap wA1(2) e(2)] wA1(3) by auto
    qed
    then have h: "\<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m (rlist_abs params asm) T \<and>
        wt_mod ar A ?\<theta> W Wu ?m (rlist_abs params concl) T"
      by blast
    have st: "set (eres_prob ?sp asm) =
        insert (rlist_abs params asm, rlist_abs params concl) (set (BBi # rtpairs @ stpairs))"
      using e(1) by (simp add: ctx_def)
    have "\<forall>(t, u)\<in>set (eres_prob ?sp asm). \<exists>T Wt Wu. wt_mod ar A ?\<theta> W Wt ?m t T \<and> wt_mod ar A ?\<theta> W Wu ?m u T"
      unfolding st using h dps by (simp only: set_simps ball_simps prod.case) blast
    from pi[OF this] show "pinv alg ar (bs_A ?sp) W (bs_env ?sp) (dps_of (eres_prob ?sp asm))"
      by auto
  qed
  then show ?thesis by (simp only: sp)
qed

text \<open>If the rule is incremented, the types of the variables are not unified.\<close>

corollary pinv_all_empty_env:
  assumes state: "wt_thm ar A W smax stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A W rmax rtpairs rprop" "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (W x)" "tcert alg A"
  shows "pinv_all (call_spec cfg A vl (empty_env (max rmax smax)) flatten match_flg smax stpairs Bs Bi C
    lifted eres_flg rtpairs rAs B)"
  by (rule pinv_allW_pinv_all, rule pinv_all_tvinv[OF state rule lift tvinv_empty_env[OF A(1,2,4)] A(3)]) simp_all

end


context csig
begin

subsection \<open>Unification of the types of variables\<close>

text \<open>
  \<open>unify_var_types\<close> collects the types of each variable of the proof state and the rule in a
  table and unifies them.
\<close>

definition vtab :: "(indexname \<times> ptyp list) list \<Rightarrow> (indexname \<times> ptyp) set" where
  "vtab tab = {(x, T). \<exists>Ts. (x, Ts) \<in> set tab \<and> T \<in> set Ts}"

lemma vtab_simps: "vtab [] = {}" "vtab ((x, Ts) # tab) = Pair x ` set Ts \<union> vtab tab"
  by (auto simp: vtab_def)

lemma vtab_insert_list: "vtab (insert_list xT tab) = insert xT (vtab tab)"
  by (induction xT tab rule: insert_list.induct) (auto simp: vtab_simps list_ex_iff)

lemma fst_insert_list: "fst ` set (insert_list (x, T) tab) = insert x (fst ` set tab)"
  by (induction "(x, T)" tab rule: insert_list.induct) auto

lemma distinct_insert_list: "distinct (map fst tab) \<Longrightarrow> distinct (map fst (insert_list xT tab))"
proof (induction xT tab rule: insert_list.induct)
  case (2 xi T yj Ts tab)
  then show ?case using fst_insert_list[of xi T tab] by auto
qed simp

lemma vtab_add_vars: "vtab (add_vars t tab) = vps t \<union> vtab tab"
  by (induction t tab rule: add_vars.induct) (auto simp: vtab_insert_list)

lemma distinct_add_vars: "distinct (map fst tab) \<Longrightarrow> distinct (map fst (add_vars t tab))"
  by (induction t tab rule: add_vars.induct) (auto simp: distinct_insert_list)

lemma set_insert_key: "set (insert_key p qs) = insert p (set qs)"
  by (induction p qs rule: insert_key.induct) auto

lemma distinct_insert_key:
  "distinct (map fst (insert_key p qs)) \<longleftrightarrow> fst p \<notin> fst ` set qs \<and> distinct (map fst qs)"
  by (induction p qs rule: insert_key.induct) (auto simp: set_insert_key)

lemma set_sort_keys: "set (sort_keys tab) = set tab"
  by (induction tab) (simp_all add: sort_keys_def set_insert_key)

lemma distinct_sort_keys: "distinct (map fst (sort_keys tab)) \<longleftrightarrow> distinct (map fst tab)"
proof (induction tab)
  case (Cons a tab)
  then show ?case
    using set_sort_keys[of tab] by (simp add: sort_keys_def distinct_insert_key)
qed (simp add: sort_keys_def)

definition vps_thm :: "(pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vps_thm tps P = vps P \<union> (\<Union>(t, u)\<in>set tps. vps t \<union> vps u)"

lemma vps_list_implies: "vps (list_implies As B) = (\<Union>A\<in>set As. vps A) \<union> vps B"
  by (induction As) (auto simp: mk_implies_def implies_def)

lemma vps_full_prop_of: "ok (full_prop_of tps P) p \<Longrightarrow> vps p = vps_thm tps P"
proof -
  assume "ok (full_prop_of tps P) p"
  then obtain eqs where l: "list_all2 (\<lambda>tu eq. ok (mk_equals tu) eq) tps eqs" and p: "p = list_implies eqs P"
    by (auto simp: full_prop_of_def ok_mapM)
  from l have "(\<Union>A\<in>set eqs. vps A) = (\<Union>(t, u)\<in>set tps. vps t \<union> vps u)"
    by (induction rule: list_all2_induct) (auto simp: mk_equals_def)
  then show ?thesis by (simp add: p vps_list_implies vps_thm_def Un_ac)
qed

lemma has_type_vps: "has_type W Ts t T \<Longrightarrow> x \<in> vars t \<Longrightarrow> (x, W x) \<in> vps t"
  by (induction rule: has_type.induct) auto

lemma vps_tys: "(x, T) \<in> vps t \<Longrightarrow> T \<in> tys t"
  by (induction t) auto

end

context wf_csig
begin

lemma tyA_tyw: "tinv ar n \<theta> A \<Longrightarrow> tyA ar A T \<Longrightarrow> tyw ar \<theta> A T"
  by (rule tyw_textends[OF tinv_tacyc _ tyw_empty]) (simp_all add: textends_def)

lemma unify_types_tvinv:
  assumes "ok (unify_types alg T U env) env'" "tvinv A m env" "tyA ar A T" "tyA ar A U"
  shows "tvinv A m env' \<and> textends (tyenv env) (tyenv env') \<and> tnorm (tyenv env') T = tnorm (tyenv env') U"
proof -
  from assms(2) have te: "vt_is_empty (tenv env)" and mx: "m \<le> maxidx env"
    and ti: "tinv ar (maxidx env) (tyenv env) A" and ts: "tsorted alg (tyenv env)" and cA: "tcert alg A"
    and ce: "tcert alg (tvars_env (tyenv env))"
    by (simp_all add: tvinv_def)
  from unify_types_poly[OF ti ts tyA_tyw[OF ti assms(3)] tyA_tyw[OF ti assms(4)]] assms(1)
  have te': "tenv env' = tenv env" and st: "Type_Mgu.tstep alg ar A (\<lambda>\<rho>. tsubst \<rho> T = tsubst \<rho> U) (tyenv env)
      (maxidx env) (tyenv env') (maxidx env')"
    and so: "\<forall>\<rho>. tsol (tyenv env') \<rho> \<longrightarrow> tsubst \<rho> T = tsubst \<rho> U" and ts': "tsorted alg (tyenv env')"
    by auto
  note s = Type_Mgu.tstepD[OF st]
  have "tnorm (tyenv env') T = tnorm (tyenv env') U"
    by (rule tnorm_eq_tsol[OF tinv_tacyc[OF s(3)]]) (use so in blast)
  moreover have "tcert alg (tvars_env (tyenv env'))" using s(6) cA ce by simp
  ultimately show ?thesis using te te' mx s(1-3) ts' cA by (simp add: tvinv_def)
qed

lemma foldM_unify_types_tvinv:
  assumes "ok (foldM (\<lambda>U env. unify_types alg T U env) Us env) env'" "tvinv A m env" "tyA ar A T"
    "\<forall>U\<in>set Us. tyA ar A U"
  shows "tvinv A m env' \<and> textends (tyenv env) (tyenv env') \<and> (\<forall>U\<in>set Us. tnorm (tyenv env') T = tnorm (tyenv env') U)"
  using assms
proof (induction Us arbitrary: env)
  case (Cons U Us)
  from Cons.prems(1) obtain e1 where u: "ok (unify_types alg T U env) e1"
    and f: "ok (foldM (\<lambda>U env. unify_types alg T U env) Us e1) env'"
    by auto
  note s1 = unify_types_tvinv[OF u Cons.prems(2,3)] Cons.prems(4)
  from Cons.IH[OF f _ Cons.prems(3)] s1 have IH: "tvinv A m env'" "textends (tyenv e1) (tyenv env')"
    "\<forall>U\<in>set Us. tnorm (tyenv env') T = tnorm (tyenv env') U" by auto
  have ac: "tacyc (tyenv env')" using IH(1) unfolding tvinv_def by (blast intro: tinv_tacyc)
  have "tnorm (tyenv env') T = tnorm (tyenv env') U"
    using tnorm_textends[OF ac IH(2), of T] tnorm_textends[OF ac IH(2), of U] s1 by simp
  with IH s1 show ?case by (auto intro: textends_trans)
qed (simp add: return_def)

lemma unify_vars_tvinv:
  assumes "ok (unify_vars alg Ts env) env'" "tvinv A m env" "\<forall>T\<in>set Ts. tyA ar A T"
  shows "tvinv A m env' \<and> textends (tyenv env) (tyenv env') \<and>
    (\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env') T = tnorm (tyenv env') U)"
proof (cases Ts)
  case Nil
  with assms show ?thesis by simp
next
  case (Cons T Us)
  with assms foldM_unify_types_tvinv[of T Us env env' A m] show ?thesis by auto metis
qed

lemma foldM_unify_vars_tvinv:
  assumes "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab env) env'" "tvinv A m env"
    "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tyA ar A T"
  shows "tvinv A m env' \<and> textends (tyenv env) (tyenv env') \<and>
    (\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env') T = tnorm (tyenv env') U)"
  using assms
proof (induction tab arbitrary: env)
  case (Cons xTs tab)
  obtain x Ts where xTs: "xTs = (x, Ts)" by (cases xTs)
  from Cons.prems(1) xTs obtain e1 where u: "ok (unify_vars alg Ts env) e1"
    and f: "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) tab e1) env'"
    by auto
  have tT: "\<forall>T\<in>set Ts. tyA ar A T" and tt: "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. tyA ar A T"
    using Cons.prems(3) xTs by auto
  from unify_vars_tvinv[OF u Cons.prems(2) tT] have s1': "tvinv A m e1" "textends (tyenv env) (tyenv e1)"
    "\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv e1) T = tnorm (tyenv e1) U" by blast+
  from Cons.IH[OF f s1'(1) tt] have IH: "tvinv A m env'" "textends (tyenv e1) (tyenv env')"
    "\<forall>(x, Ts)\<in>set tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env') T = tnorm (tyenv env') U" by blast+
  have ac: "tacyc (tyenv env')" using IH(1) unfolding tvinv_def by (blast intro: tinv_tacyc)
  have "\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env') T = tnorm (tyenv env') U"
    using s1'(3) tnorm_textends[OF ac IH(2)] by metis
  moreover have "textends (tyenv env) (tyenv env')" by (rule textends_trans[OF s1'(2) IH(2)])
  ultimately show ?case using IH(1,3) xTs by (simp only: list.set prod.case ball_simps)
qed (simp add: return_def)

lemma unify_var_types_tvinv:
  assumes "okT (unify_var_types alg (tps1, P1) (tps2, P2) (empty_env m)) (Some env)"
    "scons A" "\<forall>p\<in>A. snd (fst p) \<le> m" "\<forall>(x, T)\<in>vps_thm tps1 P1 \<union> vps_thm tps2 P2. tyA ar A T"
    "tcert alg A"
  shows "tvinv A m env"
    "(x, T) \<in> vps_thm tps1 P1 \<union> vps_thm tps2 P2 \<Longrightarrow> (x, U) \<in> vps_thm tps1 P1 \<union> vps_thm tps2 P2 \<Longrightarrow>
      tnorm (tyenv env) T = tnorm (tyenv env) U"
proof -
  let ?V = "vps_thm tps1 P1 \<union> vps_thm tps2 P2"
  let ?f = "do {
      p1 \<leftarrow> full_prop_of tps1 P1;
      p2 \<leftarrow> full_prop_of tps2 P2;
      let vars = sort_keys (add_vars p2 (add_vars p1 []));
      foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) vars (empty_env m)}"
  obtain f where f: "f = ?f" by simp
  have "ok f env"
    using assms(1) unfolding unify_var_types_def fst_conv snd_conv f[symmetric]
    by (cases f) (simp_all split: res.splits exn.splits)
  then have "ok ?f env" by (simp only: f)
  then obtain p1 p2 where p1: "ok (full_prop_of tps1 P1) p1" and p2: "ok (full_prop_of tps2 P2) p2"
    and f: "ok (foldM (\<lambda>(_, Ts) env. unify_vars alg Ts env) (sort_keys (add_vars p2 (add_vars p1 [])))
      (empty_env m)) env"
    by (auto simp: Let_def)
  let ?tab = "sort_keys (add_vars p2 (add_vars p1 []))"
  have vt: "vtab ?tab = ?V"
    using vps_full_prop_of[OF p1] vps_full_prop_of[OF p2]
    by (auto simp: vtab_def set_sort_keys vtab_add_vars[unfolded vtab_def] split: prod.splits)
  have ds: "distinct (map fst ?tab)" by (simp add: distinct_sort_keys distinct_add_vars)
  have "\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. tyA ar A T"
    using vt assms(4) by (auto simp: vtab_def)
  from foldM_unify_vars_tvinv[OF f tvinv_empty_env[OF assms(2,3,5)] this]
  have r: "tvinv A m env"
    "\<forall>(x, Ts)\<in>set ?tab. \<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env) T = tnorm (tyenv env) U"
    by auto
  show "tvinv A m env" by (rule r(1))
  assume "(x, T) \<in> ?V" "(x, U) \<in> ?V"
  then have "(x, T) \<in> vtab ?tab" "(x, U) \<in> vtab ?tab" by (simp_all add: vt)
  then obtain Ts Us where Ts: "(x, Ts) \<in> set ?tab" "T \<in> set Ts" and Us: "(x, Us) \<in> set ?tab" "U \<in> set Us"
    unfolding vtab_def by blast
  have "Ts = Us" by (rule eq_key_imp_eq_value[OF ds Ts(1) Us(1)])
  from bspec[OF r(2) Ts(1)] have "\<forall>T\<in>set Ts. \<forall>U\<in>set Ts. tnorm (tyenv env) T = tnorm (tyenv env) U"
    by (simp only: prod.case)
  with Ts(2) Us(2) \<open>Ts = Us\<close> show "tnorm (tyenv env) T = tnorm (tyenv env) U" by blast
qed

text \<open>The problems of a call are well-typed if the proof state and the rule are.\<close>

theorem pinv_all_unify_var_types:
  assumes state: "wt_thm ar A Ws smax stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A Wr rmax rtpairs rprop" "ok (strip_prems nsubgoal [] rprop) (rAs, B)"
    and lift: "lifted \<Longrightarrow> \<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (Ws x)" "\<forall>x. tyA ar A (Wr x)"
      "tcert alg A"
    and u: "okT (unify_var_types alg (stpairs, list_implies (Bs @ [Bi]) C) (rtpairs, rprop)
      (empty_env (max rmax smax))) (Some env)"
  shows "pinv_all (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C"
  let ?VS = "vars_thm stpairs ?S"
  define W where "W x = (if x \<in> ?VS then Ws x else Wr x)" for x
  have vps: "(x, Wt x) \<in> vps_thm tps P" if "wt_thm ar A Wt m tps P" "x \<in> vars_thm tps P" for Wt m tps P x
  proof -
    from that(2) consider "x \<in> vars P" | t u where "(t, u) \<in> set tps" "x \<in> vars t \<union> vars u"
      by (auto simp: vars_thm_def)
    then show ?thesis
    proof cases
      case 1
      with that(1) show ?thesis by (auto simp: wt_thm_def wt_term_def vps_thm_def dest: has_type_vps)
    next
      case 2
      with that(1) obtain T where "has_type Wt [] t T" "has_type Wt [] u T"
        by (auto simp: wt_thm_def wt_term_def)
      with 2 show ?thesis by (auto simp: vps_thm_def dest: has_type_vps)
    qed
  qed
  have tyv: "tyA ar A T" if "wt_thm ar A Wt m tps P" "(x, T) \<in> vps_thm tps P" for Wt m tps P x T
  proof -
    from that(2) consider "(x, T) \<in> vps P" | t u where "(t, u) \<in> set tps" "(x, T) \<in> vps t \<union> vps u"
      by (auto simp: vps_thm_def)
    then show ?thesis
    proof cases
      case 1
      with that(1) show ?thesis by (auto simp: wt_thm_def wt_term_def dest: vps_tys)
    next
      case 2
      with that(1) obtain T' where "wt_term ar A Wt m t T'" "wt_term ar A Wt m u T'"
        unfolding wt_thm_def by blast
      with 2 show ?thesis by (auto simp: wt_term_def dest: vps_tys)
    qed
  qed
  have "\<forall>(x, T)\<in>vps_thm stpairs ?S \<union> vps_thm rtpairs rprop. tyA ar A T"
    using tyv[OF state] tyv[OF rule(1)] by blast
  note uv = unify_var_types_tvinv[OF u A(1,2) this A(5)]
  show ?thesis
  proof (rule pinv_allW_pinv_all, rule pinv_all_tvinv[OF state rule lift uv(1)])
    show "\<forall>x. tyA ar A (W x)" using A(3,4) by (simp add: W_def)
    show "\<forall>x\<in>?VS. tnorm (tyenv env) (Ws x) = tnorm (tyenv env) (W x)" by (simp add: W_def)
    show "\<forall>x\<in>vars_thm rtpairs rprop. tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
    proof
      fix x assume x: "x \<in> vars_thm rtpairs rprop"
      show "tnorm (tyenv env) (Wr x) = tnorm (tyenv env) (W x)"
      proof (cases "x \<in> ?VS")
        case True
        from uv(2)[of x "Wr x" "Ws x"] vps[OF rule(1) x] vps[OF state True] show ?thesis
          by (simp add: W_def True)
      qed (simp add: W_def)
    qed
  qed
qed

end

end
