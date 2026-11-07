section \<open>Soundness of \<open>bicompose_aux\<close>: the Main Theorem\<close>

theory Bicompose_Correct
  imports Bicompose_Typing
begin

context pure_sig
begin

subsection \<open>Rules\<close>

lemma lift_pre_limp:
  "\<forall>it\<in>set p. is_limp it \<and> litem_ok it \<Longrightarrow> e \<turnstile> lift_pre p B : T \<Longrightarrow>
    lift_pre p B = list_implies (map lhyp p) B"
proof (induction p arbitrary: T)
  case (Cons it p)
  have "is_limp it \<and> litem_ok it" using Cons.prems(1) by simp
  then obtain U H where it: "it = LImp (Const STR ''Pure.imp'' U) H" by (cases it) auto
  then have d: "dest_imp (lift_pre (it # p) B) = Some (H, lift_pre p B)" by simp
  note ty = typing_dest_imp[OF Cons.prems(2) d]
  from Cons.IH[OF _ ty(5)] Cons.prems(1) ty(1) it show ?case by simp
qed simp

lemma list_implies_strip_prems:
  assumes "ok (strip_prems i [] P) (rAs, B)" "e \<turnstile> P : T"
  shows "P = list_implies (rev rAs) B"
proof -
  from strip_prems_ok[OF assms(1)] obtain p where p: "P = lift_pre p B"
    "\<forall>it\<in>set p. is_limp it \<and> litem_ok it" "rAs = rev (map lhyp p)"
    by auto
  with lift_pre_limp[OF p(2)] assms(2) show ?thesis by simp
qed

text \<open>
  A rule lifted over the subgoal \<open>Bi\<close> of a proof state with maximal index \<open>m\<close>
  (\<open>Thm.lift_rule\<close>): its \<open>n\<close> premises and its conclusion are lifted over the parameters and
  assumptions of \<open>Bi\<close>, and its variables have been incremented above \<open>m\<close>.
\<close>

definition lifted_over :: "integer \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> integer \<Rightarrow> bool" where
  "lifted_over m Bi P n \<longleftrightarrow> (\<exists>p Bi0 As0 B0. lsplit Bi = (p, Bi0) \<and>
    P = list_implies (map (lift_pre p) As0) (lift_pre p B0) \<and> n = ilength As0 \<and>
    (\<forall>X\<in>insert B0 (set As0). \<forall>v\<in>vars X. m < snd (fst v)))"

lemma lifted_over_lifted_rule:
  assumes "lifted_over m Bi P n" "ok (strip_prems n [] P) (rAs, B)"
  shows "lifted_rule m Bi (rev rAs) B"
proof -
  from assms(1) obtain p Bi0 As0 B0 where ls: "lsplit Bi = (p, Bi0)"
    and P: "P = list_implies (map (lift_pre p) As0) (lift_pre p B0)" and n: "n = ilength As0"
    and v: "\<forall>X\<in>insert B0 (set As0). \<forall>v\<in>vars X. m < snd (fst v)"
    unfolding lifted_over_def by blast
  have "strip_prems n [] P = return (rev (map (lift_pre p) As0), lift_pre p B0)"
    using strip_prems_list_implies[of "map (lift_pre p) As0" "[]" "lift_pre p B0"] by (simp add: P n ilength_eq)
  with assms(2) have "rAs = rev (map (lift_pre p) As0)" "B = lift_pre p B0"
    by (simp_all add: return_def)
  with ls v show ?thesis unfolding lifted_rule_def by auto
qed

text \<open>
  The environment of a call: the type variables of the proof state and the rule are known, and
  after the unification of the types of variables (unless the rule is incremented), variables
  with the same name have the same type in every solution.
\<close>

lemma call_env0:
  assumes state: "wt_thm smax hs stpairs S" and rule: "wt_thm rmax hr rtpairs P"
    and tv: "scons (tvars_thm stpairs S \<union> tvars_thm rtpairs P)"
  shows "einv (tvars_thm stpairs S \<union> tvars_thm rtpairs P) (tvars_thm stpairs S \<union> tvars_thm rtpairs P)
      (empty_env (max rmax smax))"
    "\<forall>(x, T)\<in>vars_thm stpairs S \<union> vars_thm rtpairs P.
      tvars T \<subseteq> tvars_thm stpairs S \<union> tvars_thm rtpairs P \<and> cert_typ alg ar T"
proof -
  let ?A = "tvars_thm stpairs S \<union> tvars_thm rtpairs P" and ?m = "max rmax smax"
  let ?X = "vars_thm stpairs S \<union> vars_thm rtpairs P"
  have wS: "wtp S" and wR: "wtp P" using state rule by (simp_all add: wt_thm_def)
  have tA: "tcert alg ?A"
  proof -
    have tc: "\<forall>p\<in>ttvars t. sort_ok alg (snd p)" if "\<exists>T. \<forall>e. e \<turnstile> t : T" for t
      using that tcert_ttvars unfolding tcert_def by blast
    have "\<forall>p\<in>tvars_thm tps Q. sort_ok alg (snd p)" if "wt_thm m hs' tps Q" for m hs' tps Q
    proof
      fix p assume p: "p \<in> tvars_thm tps Q"
      have wp: "\<exists>T. \<forall>e. e \<turnstile> Q : T" using that by (auto simp: wt_thm_def wtp_def)
      have wt: "(\<exists>T. \<forall>e. e \<turnstile> t : T) \<and> (\<exists>T. \<forall>e. e \<turnstile> u : T)" if tu: "(t, u) \<in> set tps" for t u
      proof -
        have "\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T"
          using \<open>wt_thm m hs' tps Q\<close> tu unfolding wt_thm_def by auto
        then obtain T where "\<And>e. e \<turnstile> t : T" "\<And>e. e \<turnstile> u : T" by blast
        then show ?thesis by blast
      qed
      from p consider "p \<in> ttvars Q" | t u where "(t, u) \<in> set tps" "p \<in> ttvars t \<union> ttvars u"
        unfolding tvars_thm_def by blast
      then show "sort_ok alg (snd p)"
      proof cases
        case 1
        with tc[OF wp] show ?thesis by blast
      next
        case 2
        with wt[OF 2(1)] tc show ?thesis by blast
      qed
    qed
    with state rule show ?thesis unfolding tcert_def by blast
  qed
  have iA: "\<forall>p\<in>?A. snd (fst p) \<le> ?m"
    using state rule by (fastforce simp: tvars_thm_def wt_thm_def ibelow_def)
  show "einv ?A ?A (empty_env ?m)" by (rule einv_empty_env[OF tv iA tA])
  show "\<forall>(x, T)\<in>?X. tvars T \<subseteq> ?A \<and> cert_typ alg ar T"
  proof (clarify)
    fix x T assume xT: "(x, T) \<in> ?X"
    have "tvars T \<subseteq> ?A"
      using xT by (auto simp: vars_thm_def tvars_thm_def dest!: vtvars_ttvars)
    moreover have "cert_typ alg ar T"
      using xT state rule wtpD(2)[OF wS] wtpD(2)[OF wR]
      by (fastforce simp: vars_thm_def wt_thm_def dest: vars_typs_cert)
    ultimately show "tvars T \<subseteq> ?A \<and> cert_typ alg ar T" by blast
  qed
qed

lemma call_env:
  assumes state: "wt_thm smax hs stpairs S" and rule: "wt_thm rmax hr rtpairs P"
    and tv: "scons (tvars_thm stpairs S \<union> tvars_thm rtpairs P)"
    and inc: "incremented \<Longrightarrow> vtcons (vars_thm stpairs S \<union> vars_thm rtpairs P)"
    and e1: "incremented \<Longrightarrow> env = empty_env (max rmax smax)"
    and e2: "\<not> incremented \<Longrightarrow>
      okT (unify_var_types alg (stpairs, S) (rtpairs, P) (empty_env (max rmax smax))) (Some env)"
  shows "einv (tvars_thm stpairs S \<union> tvars_thm rtpairs P) (tvars_thm stpairs S \<union> tvars_thm rtpairs P) env \<and>
    vt_is_empty (tenv env) \<and> max rmax smax \<le> maxidx env \<and>
    (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> vcons \<rho> (vars_thm stpairs S \<union> vars_thm rtpairs P))"
proof (cases incremented)
  case True
  have "vcons \<rho> (vars_thm stpairs S \<union> vars_thm rtpairs P)" for \<rho>
    using inc[OF True] by (auto simp: vcons_def vtcons_def)
  then show ?thesis using e1[OF True] call_env0(1)[OF state rule tv] by simp
next
  case False
  note u = unify_var_types_einv[OF e2[OF False] call_env0(1)[OF state rule tv]
      finite_tvars_thm[THEN finite_UnI[OF _ finite_tvars_thm]] call_env0(2)[OF state rule tv]]
  have "vcons \<rho> (vars_thm stpairs S \<union> vars_thm rtpairs P)" if "tsol (tyenv env) \<rho>" for \<rho>
    unfolding vcons_def using u(4)[OF that] by blast
  then show ?thesis using u(1-3) by blast
qed

end


subsection \<open>The results\<close>

context pure_sig
begin

text \<open>
  The results of \<open>bicompose_aux\<close> for a well-typed proof state and a well-typed rule satisfy
  the characterization \<^const>\<open>rchar\<close> for the specification of the call.
\<close>

lemma bicompose_aux_rchar:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg"
    and state: "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm rmax hr rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and tv: "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs rprop)"
    and inc: "incremented \<Longrightarrow> vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
  obtains rAs B env where "ok (strip_prems nsubgoal [] rprop) (rAs, B)" "rprop = list_implies (rev rAs) B"
    "pinv_all (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
    "rchar (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) r"
    "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
  using ok cfg
proof (cases rule: bicompose_aux_binv)
  case empty
  have "bpull (unify_ops cfg vl) BS_Empty = returnT None" by (subst bpull.simps) simp
  with res empty show ?thesis by (cases rule: bresult.cases) auto
next
  case (spec rAs B env)
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  let ?A = "tvars_thm stpairs ?S \<union> tvars_thm rtpairs rprop"
  let ?X = "vars_thm stpairs ?S \<union> vars_thm rtpairs rprop"
  let ?sp = "call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  have wR: "wtp rprop" using rule(1) by (simp add: wt_thm_def)
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF spec(1) wtpD(2)[OF wR, of "\<lambda>_. propT"]])
  have env: "einv ?A ?A env \<and> vt_is_empty (tenv env) \<and> ?m \<le> maxidx env \<and>
      (\<forall>\<rho>. tsol (tyenv env) \<rho> \<longrightarrow> cert_inst \<rho> \<longrightarrow> vcons \<rho> ?X)"
    by (rule call_env[OF state rule(1) tv inc spec(2,3)])
  have lift: "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
    using lifted_over_lifted_rule[OF rule(2)[OF that] spec(1)] by (auto simp: lifted_rule_def)
  have pa: "pinv_all ?sp"
  proof (rule pinv_all_call_spec)
    show "wt_thm smax hs stpairs ?S" by (rule state)
    show "wt_thm rmax hr rtpairs (list_implies (rev rAs) B)" using rule(1) P by simp
    show "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted using lift[OF that] .
    show "einv ?A ?A env" "finite ?A" "vt_is_empty (tenv env)" "max rmax smax \<le> maxidx env"
      using env by simp_all
    show "tvars_thm stpairs ?S \<union> tvars_thm rtpairs (list_implies (rev rAs) B) \<subseteq> ?A" using P by simp
    show "vcons \<rho> (vars_thm stpairs ?S \<union> vars_thm rtpairs (list_implies (rev rAs) B))"
      if "tsol (tyenv env) \<rho>" "cert_inst \<rho>" for \<rho>
      using env that P by simp
  qed
  have sel: "sp_cfg ?sp = cfg" "sp_vl ?sp = vl" by (simp_all add: call_spec_def Let_def)
  have "rchar ?sp r"
    by (rule bresult_rchar[of ?sp]) (use res spec(4)[OF pa] cfg pa sel in simp_all)
  moreover have "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    using lifted_over_lifted_rule[OF _ spec(1)] rule(2) by blast
  ultimately show ?thesis using that spec(1) P pa by blast
qed

end


subsection \<open>Soundness\<close>

context pure_model
begin

text \<open>
  The main theorem: the results of \<open>bicompose_aux\<close> for a valid, well-typed proof state
  \<open>\<lbrakk>Bs; Bi\<rbrakk> \<Longrightarrow> C\<close> with hypotheses \<open>hs\<close>, flex-flex pairs \<open>stpairs\<close> and maximal index
  \<open>smax\<close>, and a valid, well-typed rule with hypotheses \<open>hr\<close>, flex-flex pairs \<open>rtpairs\<close> and
  maximal index \<open>rmax\<close>, lifted over \<open>Bi\<close> if \<open>lifted\<close>, are valid, with the hypotheses of both and
  the sort hypotheses of both and of the type environment of the result.
  The type variables of the proof state and the rule have unique sorts. If the rule is
  incremented, variables with the same name have the same type (\<open>Envir\<close> looks variables up by
  their names); otherwise \<open>bicompose_aux\<close> unifies their types.
\<close>

theorem bicompose_aux_valid:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg incremented
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg"
    and state: "valid Shs hs stpairs (list_implies (Bs @ [Bi]) C)" "wt_thm smax hs stpairs (list_implies (Bs @ [Bi]) C)"
    and rule: "valid Shr hr rtpairs rprop" "wt_thm rmax hr rtpairs rprop"
      "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and tv: "scons (tvars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> tvars_thm rtpairs rprop)"
    and inc: "incremented \<Longrightarrow> vtcons (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
    and vl: "\<And>xs. length (vl xs) = length xs"
  shows "valid (Shs \<union> Shr \<union> tyenv_sorts (tyenv (br_env r))) (hs @ hr) (br_tpairs r) (br_prop r)"
proof -
  have wS: "wtp (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)" and wR: "wtp rprop"
    using state(2) rule(2) by (simp_all add: wt_thm_def)
  obtain rAs B env where P: "rprop = list_implies (rev rAs) B"
    and pa: "pinv_all (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)"
    and rc: "rchar (call_spec cfg vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) r"
    and lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
    using bicompose_aux_rchar[OF ok res cfg state(2) rule(2,3) tv inc] by blast
  have "\<forall>h\<in>set (hs @ hr). vars h = {} \<and> ttvars h = {}"
    using state(2) rule(2) by (auto simp: wt_thm_def)
  then show ?thesis
    using rchar_valid[OF refl rc pa state(1) wS rule(1)[unfolded P] wR[unfolded P] lr _ vl] by blast
qed
end

end
