section \<open>The abstract type of theorems\<close>

theory Thm_Type
  imports Biresolution_Correct
begin

text \<open>
  A theorem of Isabelle (\<open>Thm.thm\<close>) carries its certificate (the theory), its maximal index, its
  hypotheses, its flex-flex pairs and its proposition. The certificate is modelled by the
  signature: the sort algebra, the arities of the type constructors and the types of the
  constants. Theorems are the records that satisfy the invariant \<^const>\<open>pure_sig.thm_inv\<close> in
  their signature and are valid in every model of it over a universe \<open>'u\<close>. Biresolution maps
  theorems to theorems; its results are those of the compositions of the rules with the proof
  state, and their enumeration terminates.
\<close>


subsection \<open>Signatures and models\<close>

record sign =
  sg_alg :: algebra
  sg_ar :: "name \<Rightarrow> nat"
  sg_consts :: "name \<Rightarrow> ptyp option"

record 'u model =
  m_mem :: "'u \<Rightarrow> 'u \<Rightarrow> bool"
  m_fun :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
  m_app :: "'u \<Rightarrow> 'u \<Rightarrow> 'u"
  m_lam :: "'u \<Rightarrow> ('u \<Rightarrow> 'u) \<Rightarrow> 'u"
  m_bool :: 'u
  m_true :: 'u
  m_false :: 'u
  m_tcon :: "name \<Rightarrow> 'u list \<Rightarrow> 'u"
  m_cls :: "pclass \<Rightarrow> 'u \<Rightarrow> bool"
  m_cval :: "name \<Rightarrow> 'u \<Rightarrow> 'u"

definition is_model :: "sign \<Rightarrow> 'u model \<Rightarrow> bool" where
  "is_model c M \<longleftrightarrow> pure_model (sg_alg c) (sg_ar c) (m_mem M) (m_fun M) (m_app M) (m_lam M)
    (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"

definition valid_in :: "sign \<Rightarrow> 'u model \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid_in c M = pure_model.valid (sg_alg c) (sg_ar c) (sg_consts c) (m_mem M) (m_fun M) (m_app M)
    (m_lam M) (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"

lemma is_modelD: "is_model c M \<Longrightarrow> pure_model (sg_alg c) (sg_ar c) (m_mem M) (m_fun M) (m_app M) (m_lam M)
    (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"
  by (simp add: is_model_def)


subsection \<open>Theorems\<close>

record thm_data = thm_rep +
  th_hyps :: "pterm list"
  th_sign :: sign

definition thm_ok :: "'u itself \<Rightarrow> thm_data \<Rightarrow> bool" where
  "thm_ok U th \<longleftrightarrow> pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<longrightarrow>
    pure_sig.thm_inv (sg_alg (th_sign th)) (sg_ar (th_sign th)) (sg_consts (th_sign th))
      (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th) \<and>
    (\<forall>M :: 'u model. is_model (th_sign th) M \<longrightarrow>
      valid_in (th_sign th) M (th_hyps th) (th_tpairs th) (th_prop th))"

text \<open>The theorem \<open>A \<Longrightarrow> A\<close> (\<open>Thm.trivial\<close>) shows that there are theorems.\<close>

definition sign0 :: sign where
  "sign0 = \<lparr>sg_alg = undefined, sg_ar = \<lambda>_. 0, sg_consts = \<lambda>_. None\<rparr>"

definition thm0 :: thm_data where
  "thm0 = \<lparr>th_maxidx = 0, th_tpairs = [],
    th_prop = implies $ Var (STR ''A'', 0) propT $ Var (STR ''A'', 0) propT, th_hyps = [], th_sign = sign0\<rparr>"

lemma thm_ok_thm0: "thm_ok TYPE('u) thm0"
proof -
  let ?alg = "sg_alg sign0" and ?ar = "sg_ar sign0" and ?ct = "sg_consts sign0"
  let ?A = "Var (STR ''A'', 0) propT"
  let ?P = "implies $ ?A $ ?A"
  have "pure_sig.thm_inv ?alg ?ar ?ct 0 [] [] ?P \<and> (\<forall>M :: 'u model. is_model sign0 M \<longrightarrow> valid_in sign0 M [] [] ?P)"
    if ps: "pure_sig ?alg ?ar"
  proof -
    interpret pure_sig ?alg ?ar ?ct by (rule ps)
    have c: "cert_typ ?alg ?ar propT" "cert_typ ?alg ?ar imp_type"
      by (simp_all add: cert_typ_def propT_def imp_type_def tarity_def sign0_def)
    have wP: "wtp ?P" by (rule wtpI[of _ "\<lambda>_. propT"]) (use c in \<open>auto simp: closed_def implies_def imp_type_def const_typ_ok_def propT_def\<close>)
    have "thm_inv 0 [] [] ?P"
      using wP by (auto simp: thm_inv_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def
        scons_def vtcons_def implies_def imp_type_def propT_def)
    moreover have "valid_in sign0 M [] [] ?P" if M: "is_model sign0 M" for M :: "'u model"
    proof -
      interpret pure_model ?alg ?ar ?ct "m_mem M" "m_fun M" "m_app M" "m_lam M" "m_bool M" "m_true M"
        "m_false M" "m_tcon M" "m_cls M" "m_cval M"
        by (rule is_modelD[OF M])
      have "valid [] [] ?P"
      proof (rule validI)
        fix \<eta> \<xi> \<rho> \<sigma> assume g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
        interpret pure_valuation ?alg ?ar ?ct "m_mem M" "m_fun M" "m_app M" "m_lam M" "m_bool M" "m_true M"
          "m_false M" "m_tcon M" "m_cls M" "m_cval M" \<eta> \<xi>
          by unfold_locales (rule g)
        have "holds (list_implies [ap \<rho> \<sigma> ?A] (ap \<rho> \<sigma> ?A))"
        proof (rule holds_list_impliesI)
          show "gterm (list_implies [ap \<rho> \<sigma> ?A] (ap \<rho> \<sigma> ?A)) propT"
            using gterm_ap_wtp[OF wP cinstD(2)[OF \<rho>] \<sigma>] by simp
        qed simp
        then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> ?P)" by simp
      qed
      then show ?thesis by (simp add: valid_in_def)
    qed
    ultimately show ?thesis by blast
  qed
  then show ?thesis by (simp add: thm_ok_def thm0_def)
qed

typedef (overloaded) 'u pure_thm = "{th. thm_ok TYPE('u) th}"
  morphisms rep_thm Abs_thm
  using thm_ok_thm0 by blast

abbreviation rep_of :: "'u pure_thm \<Rightarrow> thm_rep" where
  "rep_of th \<equiv> thm_rep.truncate (rep_thm th)"

abbreviation sign_of :: "'u pure_thm \<Rightarrow> sign" where
  "sign_of th \<equiv> th_sign (rep_thm th)"

abbreviation hyps_of :: "'u pure_thm \<Rightarrow> pterm list" where
  "hyps_of th \<equiv> th_hyps (rep_thm th)"

lemma rep_of_sel [simp]:
  "th_maxidx (rep_of th) = th_maxidx (rep_thm th)" "th_tpairs (rep_of th) = th_tpairs (rep_thm th)"
  "th_prop (rep_of th) = th_prop (rep_thm th)"
  by (simp_all add: thm_rep.truncate_def)

lemma thm_ok_rep: "thm_ok TYPE('u) (rep_thm (th :: 'u pure_thm))"
  using rep_thm by blast

text \<open>Every theorem is valid in every model of its signature:\<close>

theorem pure_thm_valid:
  fixes th :: "'u pure_thm" and M :: "'u model"
  assumes M: "is_model (sign_of th) M"
  shows "valid_in (sign_of th) M (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
proof -
  have "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    by (rule pure_model.axioms(1)[OF is_modelD[OF M]])
  with thm_ok_rep[of th] M show ?thesis unfolding thm_ok_def by blast
qed

lemma pure_thm_inv:
  "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th)) \<Longrightarrow>
    pure_sig.thm_inv (sg_alg (sign_of th)) (sg_ar (sign_of th)) (sg_consts (sign_of th))
      (th_maxidx (rep_thm th)) (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
  using thm_ok_rep[of th] by (simp add: thm_ok_def)


subsection \<open>Biresolution of theorems\<close>

text \<open>
  The new theorem of a result of \<^const>\<open>biresolution\<close> has the signature of the proof state and
  the rules, which must agree (\<open>Thm.join_certificate\<close>), and the hypotheses of both (Isabelle
  merges the ordered lists; only their set matters).
\<close>

definition thm_of_bres :: "sign \<Rightarrow> 'u pure_thm \<Rightarrow> 'u pure_thm \<Rightarrow> bres \<Rightarrow> thm_data" where
  "thm_of_bres c state rule x = \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x,
    th_hyps = hyps_of state @ hyps_of rule, th_sign = c\<rparr>"

text \<open>
  \<open>biresolution_thms cfg vl trace match brules i state\<close>: the results of \<^const>\<open>biresolution\<close>
  on theorems, each with the rule it was obtained with; \<open>None\<close> if an exception is raised, if
  the signatures of the proof state and the rules do not agree, or if the configuration does not
  belong to the signature. \<open>vl\<close> is \<open>Name.variant_list []\<close>.
\<close>

definition biresolution_thms :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<times> 'u pure_thm) list \<Rightarrow>
    integer \<Rightarrow> 'u pure_thm \<Rightarrow> ('u pure_thm \<times> (bool \<times> 'u pure_thm)) list option" where
  "biresolution_thms cfg vl trace match_flg brules i state =
    (let c = sign_of state;
      R = (\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0 \<and>
        pure_sig.brevals (sg_alg c) (unify_ops cfg vl) rep_of s0 xs)
     in if pure_sig (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          (\<forall>r\<in>set brules. sign_of (snd r) = c) \<and> (\<exists>xs. R xs)
       then Some (map (\<lambda>(x, r). (Abs_thm (thm_of_bres c state (snd r) x), r)) (THE xs. R xs))
       else None)"

text \<open>The new theorems are theorems:\<close>

lemma thm_ok_thm_of_bres:
  assumes ps: "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and cfg: "cfg_alg cfg = sg_alg (sign_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and sg: "\<forall>r\<in>set brules. sign_of (snd r) = sign_of state"
    and br: "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0"
    and res: "pure_sig.brresult (sg_alg (sign_of state)) (unify_ops cfg vl) rep_of s0 (x, (e, rule))"
  shows "thm_ok TYPE('u) (thm_of_bres (sign_of state) (state :: 'u pure_thm) rule x)"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv[OF ps] by simp
  have ru: "thm_inv (th_maxidx (rep_of r)) (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r))"
    if "(e', r) \<in> set brules" for e' r
    using pure_thm_inv[of r] sg that ps by fastforce
  have ti: "thm_inv (maxidx (br_env x)) (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)"
    by (rule conjunct1[OF biresolution_thm_inv[OF br res cfg vl st ru]])
  have "valid_in ?c M (hyps_of state @ hyps_of rule) (br_tpairs x) (br_prop x)" if M: "is_model ?c M" for M :: "'u model"
  proof -
    interpret pure_model "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "m_mem M" "m_fun M" "m_app M" "m_lam M"
      "m_bool M" "m_true M" "m_false M" "m_tcon M" "m_cls M" "m_cval M"
      by (rule is_modelD[OF M])
    have vs: "valid (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
      using pure_thm_valid[OF M] by (simp add: valid_in_def)
    have vr: "valid (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r)) \<and>
        thm_inv (th_maxidx (rep_of r)) (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r))"
      if "(e', r) \<in> set brules" for e' r
    proof -
      have "sign_of r = ?c" using sg that by fastforce
      with pure_thm_valid[of r M] M ru[OF that] show ?thesis by (simp add: valid_in_def)
    qed
    show ?thesis
      using biresolution_valid[OF br res cfg vl vs st vr] by (simp add: valid_in_def)
  qed
  with ti show ?thesis by (simp add: thm_ok_def thm_of_bres_def)
qed

text \<open>
  Soundness: the results of biresolution of theorems are the new theorems of the compositions
  of the rules, lifted over the subgoal, with the proof state.
\<close>

theorem biresolution_thms_results:
  assumes bt: "biresolution_thms cfg vl trace match_flg brules i state = Some xs"
    and th: "(th, (e, rule)) \<in> set xs"
  shows "(e, rule) \<in> set brules \<and> (\<exists>stpairs Bs Bi C goal xq x. okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C) \<and>
    okT (cprem_of (rep_of state) i) goal \<and>
    okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) True match_flg True (pthm_of (rep_of state))
      (stpairs, Bs, Bi, C) True e (pthm_of (lift_rule goal (th_maxidx (rep_of state)) (rep_of rule)))
      (nprems_of (rep_of rule))) xq \<and>
    pure_sig.bresult (unify_ops cfg vl) xq x \<and> rep_thm th = thm_of_bres (sign_of state) state rule x)"
proof -
  let ?c = "sign_of state"
  let ?R = "\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0 \<and>
    pure_sig.brevals (sg_alg ?c) (unify_ops cfg vl) rep_of s0 xs"
  from bt have g: "pure_sig (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. sign_of (snd r) = ?c" "\<exists>xs. ?R xs"
    and xs: "xs = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c state (snd r) x), r)) (THE xs. ?R xs)"
    unfolding biresolution_thms_def Let_def by (auto split: if_splits)
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule g(1))
  from g(5) obtain ys s0 where br: "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0"
    and ev: "brevals (unify_ops cfg vl) rep_of s0 ys" by blast
  have the: "(THE xs. ?R xs) = ys"
  proof (rule the_equality)
    show "?R ys" using br ev by blast
    fix zs assume "?R zs"
    then obtain s1 where "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s1"
      "brevals (unify_ops cfg vl) rep_of s1 zs" by blast
    with br ev show "zs = ys" using okT_det brevals_det by metis
  qed
  from th obtain x where x: "(x, (e, rule)) \<in> set ys" and thx: "th = Abs_thm (thm_of_bres ?c state rule x)"
    unfolding xs the by auto
  have res: "brresult (unify_ops cfg vl) rep_of s0 (x, (e, rule))" by (rule brevals_brresult[OF ev x])
  have ok: "thm_ok TYPE('a) (thm_of_bres ?c state rule x)"
    by (rule thm_ok_thm_of_bres[OF g(1,2) _ g(4) br res]) (use g(3) in blast)
  have rep: "rep_thm th = thm_of_bres ?c state rule x" using Abs_thm_inverse ok thx by blast
  obtain stpairs Bs Bi C goal where "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)"
    "okT (cprem_of (rep_of state) i) goal" "(e, rule) \<in> set brules"
    "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) True match_flg True (pthm_of (rep_of state))
      (stpairs, Bs, Bi, C) True e (pthm_of (lift_rule goal (th_maxidx (rep_of state)) (rep_of rule)))
      (nprems_of (rep_of rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result[OF br res])
  with rep show ?thesis by blast
qed

text \<open>
  Termination: on theorems, biresolution yields the finite list of its results, unless an
  exception is raised or elim-resolution is requested with a rule without premises.
\<close>

theorem biresolution_thms_terminates:
  assumes "pure_sig (sg_alg (sign_of state)) (sg_ar (sign_of state))"
    and "cfg_alg cfg = sg_alg (sign_of state)" and "\<And>xs. length (vl xs) = length xs"
    and "\<forall>r\<in>set brules. sign_of (snd r) = sign_of state"
    and br: "okT (biresolution trace match_flg rep_of brules i (rep_of state)) (s0 :: (seq, 'u pure_thm) rseq)"
    and er: "\<forall>(e, r)\<in>set brules. e \<longrightarrow> 0 < nprems_of (rep_of r)"
  shows "\<exists>xs. biresolution_thms cfg vl trace match_flg brules i (state :: 'u pure_thm) = Some xs"
proof -
  let ?c = "sign_of state"
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule assms(1))
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv[OF assms(1)] by simp
  have ru: "thm_inv (th_maxidx (rep_of r)) (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r)) \<and>
      (e \<longrightarrow> 0 < nprems_of (rep_of r))" if "(e, r) \<in> set brules" for e r
    using pure_thm_inv[of r] assms(1,4) er that by fastforce
  have "\<exists>ys. brevals (unify_ops cfg vl) rep_of s0 ys"
  proof (rule biresolution_terminates[OF br assms(2,3) st ru])
    fix stpairs Bs Bi C goal ys
    assume "brevals (unify_ops cfg vl) rep_of s0 ys"
    then show "\<exists>ys. brevals (unify_ops cfg vl) rep_of s0 ys" by blast
  qed
  with br assms show ?thesis by (auto simp: biresolution_thms_def Let_def)
qed

text \<open>
  Completeness: the results include the new theorems of all results of the compositions of the
  rules with the proof state.
\<close>

theorem biresolution_thms_complete:
  assumes bt: "biresolution_thms cfg vl trace match_flg brules i state = Some xs"
    and er: "\<forall>(e, r)\<in>set brules. e \<longrightarrow> 0 < nprems_of (rep_of r)"
    and r: "(e, rule) \<in> set brules"
    and d: "okT (dest_state (rep_of state) i) (stpairs, Bs, Bi, C)" and g: "okT (cprem_of (rep_of state) i) goal"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (sg_alg (sign_of state)) True match_flg True (pthm_of (rep_of state))
      (stpairs, Bs, Bi, C) True e (pthm_of (lift_rule goal (th_maxidx (rep_of state)) (rep_of rule)))
      (nprems_of (rep_of rule))) xq"
    and ev: "pure_sig.bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
  shows "(Abs_thm (thm_of_bres (sign_of state) state rule x), (e, rule)) \<in> set xs"
proof -
  let ?c = "sign_of state"
  let ?R = "\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0 \<and>
    pure_sig.brevals (sg_alg ?c) (unify_ops cfg vl) rep_of s0 xs"
  from bt have gd: "pure_sig (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. sign_of (snd r) = ?c" "\<exists>xs. ?R xs"
    and xs: "xs = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c state (snd r) x), r)) (THE xs. ?R xs)"
    unfolding biresolution_thms_def Let_def by (auto split: if_splits)
  interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule gd(1))
  from gd(5) obtain ys s0 where br: "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s0"
    and evs: "brevals (unify_ops cfg vl) rep_of s0 ys" by blast
  have the: "(THE xs. ?R xs) = ys"
  proof (rule the_equality)
    show "?R ys" using br evs by blast
    fix zs assume "?R zs"
    then obtain s1 where "okT (biresolution trace match_flg rep_of brules i (rep_of state)) s1"
      "brevals (unify_ops cfg vl) rep_of s1 zs" by blast
    with br evs show "zs = ys" using okT_det brevals_det by metis
  qed
  have st: "thm_inv (th_maxidx (rep_of state)) (hyps_of state) (th_tpairs (rep_of state)) (th_prop (rep_of state))"
    using pure_thm_inv[OF gd(1)] by simp
  have ru: "thm_inv (th_maxidx (rep_of r)) (hyps_of r) (th_tpairs (rep_of r)) (th_prop (rep_of r)) \<and>
      (e \<longrightarrow> 0 < nprems_of (rep_of r))" if "(e, r) \<in> set brules" for e r
    using pure_thm_inv[of r] gd(1,4) er that by fastforce
  have vl: "\<And>xs. length (vl xs) = length xs" using gd(3) by blast
  show ?thesis
  proof (rule biresolution_complete[OF br gd(2) vl st ru])
    fix stpairs' Bs' Bi' C' goal' ys'
    assume d': "okT (dest_state (rep_of state) i) (stpairs', Bs', Bi', C')"
      and g': "okT (cprem_of (rep_of state) i) goal'" and ev': "brevals (unify_ops cfg vl) rep_of s0 ys'"
      and al: "\<And>e rule xq rs x. (e, rule) \<in> set brules \<Longrightarrow>
        okT (bicompose_aux (unify_ops cfg vl) (sg_alg ?c) True match_flg True (pthm_of (rep_of state)) (stpairs', Bs', Bi', C')
          True e (pthm_of (lift_rule goal' (th_maxidx (rep_of state)) (rep_of rule))) (nprems_of (rep_of rule))) xq \<Longrightarrow>
        bevals (unify_ops cfg vl) xq rs \<Longrightarrow> x \<in> set rs \<Longrightarrow> (x, (e, rule)) \<in> set ys'"
    have "(stpairs', Bs', Bi', C') = (stpairs, Bs, Bi, C)" "goal' = goal" using d d' g g' okT_det by metis+
    then have "(x, (e, rule)) \<in> set ys'" using al[OF r _ ev x] ok by simp
    moreover have "ys' = ys" using brevals_det[OF ev' evs] .
    ultimately show ?thesis unfolding xs the by force
  qed
qed

end
