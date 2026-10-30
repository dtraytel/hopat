section \<open>The abstract type of theorems\<close>

theory Thm_Type
  imports Biresolution_Thm
begin

context csig
begin

text \<open>
  A theorem of Isabelle (\<open>Thm.thm\<close>) is a record of its certificate (the theory), its maximal
  index, its hypotheses, its flex-flex pairs and its proposition, among others. The certificate
  is modelled by the signature that the proofs need: the sort algebra and the arities of the type
  constructors.
\<close>


subsection \<open>Hypotheses\<close>

text \<open>
  The hypotheses of a theorem are well-typed propositions without schematic variables and
  schematic type variables: \<open>Thm.assume\<close> demands this, and the other rules keep it; e.g.,
  \<open>Thm.instantiate\<close> does not instantiate the hypotheses, \<open>Thm.lift_rule\<close> does not lift them, and
  \<open>Thm.generalize\<close> does not generalize variables free in them. A hypothesis therefore denotes the
  same proposition in every instance of a theorem.
\<close>

definition hyp_ok :: "(name \<Rightarrow> nat) \<Rightarrow> pterm \<Rightarrow> bool" where
  "hyp_ok ar h \<longleftrightarrow> vars h = {} \<and> wt_term ar {} (\<lambda>_. propT) (-1) h propT \<and> cok h"

lemma tsubst_no_tvars: "tvars T = {} \<Longrightarrow> tsubst \<rho> T = T"
  using tsubst_cong[of T \<rho> TVar] by simp

lemma inst_no_tvars: "\<forall>U\<in>tys t. tvars U = {} \<Longrightarrow> inst \<rho> t = t"
  by (induction t) (simp_all add: tsubst_no_tvars)

lemma mk_subst_tr_no_vars: "vars t = {} \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow> mk_subst \<sigma> (tr t) = tr t"
  by (induction t) (auto simp: rigid_substD)

lemma sm_hyp: "hyp_ok ar h \<Longrightarrow> rigid_subst \<sigma> \<Longrightarrow> sm \<rho> \<sigma> h = tr h"
  by (auto simp: hyp_ok_def wt_term_def tyA_def sm_def inst_no_tvars mk_subst_tr_no_vars)

end

context bicompose_sem
begin

text \<open>
  A theorem with hypotheses \<open>hs\<close>, flex-flex pairs \<open>tps\<close> and proposition \<open>P\<close> is valid if every
  instance of \<open>P\<close> holds whose hypotheses hold and whose flex-flex pairs are solved. Since the
  hypotheses have no schematic variables, this is the validity of \<open>tps\<close> and \<open>P\<close> if the hypotheses
  hold.
\<close>

definition valid_thm :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid_thm hs tps P \<longleftrightarrow> (\<forall>\<rho> \<sigma>. gtinst \<rho> \<longrightarrow> closed_on UNIV \<sigma> \<longrightarrow> rigid_subst \<sigma> \<longrightarrow>
    (\<forall>h\<in>set hs. holds (sm \<rho> \<sigma> h)) \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<longrightarrow> holds (sm \<rho> \<sigma> P))"

lemma valid_thm_Nil[simp]: "valid_thm [] tps P \<longleftrightarrow> valid tps P"
  by (simp add: valid_thm_def valid_def)

lemma valid_thm_iff:
  assumes "\<forall>h\<in>set hs. hyp_ok ar h"
  shows "valid_thm hs tps P \<longleftrightarrow> ((\<forall>h\<in>set hs. holds (tr h)) \<longrightarrow> valid tps P)"
proof -
  have e: "sm \<rho> \<sigma> h = tr h" if "h \<in> set hs" "rigid_subst \<sigma>" for \<rho> \<sigma> h
    using sm_hyp assms that by blast
  have "(\<forall>h\<in>set hs. holds (sm \<rho> \<sigma> h)) \<longleftrightarrow> (\<forall>h\<in>set hs. holds (tr h))" if "rigid_subst \<sigma>" for \<rho> \<sigma>
    using e[OF _ that] by auto
  then show ?thesis unfolding valid_thm_def valid_def by blast
qed

end


subsection \<open>The type of theorems\<close>

text \<open>
  The certificate of a theorem (\<open>Context.certificate\<close>, the theory) is modelled by its signature:
  the sort algebra, the arities of the type constructors and the declared types of the constants.
  The record \<^typ>\<open>thm_rep\<close> of the model is extended by the hypotheses and the certificate.
  Theorems are the records that are typed in their signature with non-negative indices
  (@{const csig.thm_typed}; in particular, their constants occur at instances of their declared
  types), whose hypotheses are well-typed and without schematic variables (@{const csig.hyp_ok}),
  and that are valid in every model of their signature.
\<close>

record sign =
  sg_alg :: algebra
  sg_ar :: "name \<Rightarrow> nat"
  sg_consts :: "name \<Rightarrow> ptyp option"

record thm_cert = thm_rep +
  th_hyps :: "pterm list"
  th_cert :: sign

definition thm_ok :: "thm_cert \<Rightarrow> bool" where
  "thm_ok th \<longleftrightarrow> (let alg = sg_alg (th_cert th); ar = sg_ar (th_cert th); ct = sg_consts (th_cert th) in
    csig.thm_typed ct ar 0 (thm_rep.truncate th) \<and> (\<forall>h\<in>set (th_hyps th). csig.hyp_ok ct ar h) \<and>
    (\<forall>holds inhab. bicompose_sem ct alg ar holds inhab \<longrightarrow>
      bicompose_sem.valid_thm alg ar holds (th_hyps th) (th_tpairs th) (th_prop th)))"

text \<open>The theorem \<open>A \<Longrightarrow> A\<close> (\<open>Thm.trivial\<close>) shows that there are theorems.\<close>

definition trivial_thm :: thm_cert where
  "trivial_thm = \<lparr>th_maxidx = 0, th_tpairs = [],
    th_prop = implies $ Var (STR ''A'', 0) propT $ Var (STR ''A'', 0) propT, th_hyps = [],
    th_cert = \<lparr>sg_alg = undefined, sg_ar = \<lambda>_. 0, sg_consts = \<lambda>_. None\<rparr>\<rparr>"

lemma thm_ok_trivial: "thm_ok trivial_thm"
proof -
  let ?A = "Var (STR ''A'', 0) propT" and ?ar = "\<lambda>_ :: name. 0 :: nat" and ?ct = "\<lambda>_ :: name. None :: ptyp option"
  interpret csig ?ct .
  have wp: "wft ?ar propT" "wft ?ar imp_type" "tvars propT = {}" "tvars imp_type = {}"
    by (simp_all add: propT_def imp_type_def tarity_def)
  have h: "has_type (\<lambda>_. propT) [] (implies $ ?A $ ?A) propT"
    by (simp add: has_type_implies has_type.Var)
  have "tys (implies $ ?A $ ?A) = {imp_type, propT}" by (auto simp: implies_imp_type)
  then have w: "wt_term ?ar {} (\<lambda>_. propT) 0 (implies $ ?A $ ?A) propT"
    using h wp by (simp add: wt_term_def swf_tm_def implies_imp_type below_def tyA_def)
  have "thm_typed ?ar 0 \<lparr>th_maxidx = 0, th_tpairs = [], th_prop = implies $ ?A $ ?A\<rparr>"
    unfolding thm_typed_def using w wp h
    by (auto simp: wt_thm_def scons_def vars_thm_def implies_imp_type tyA_def
      intro!: exI[of _ "{}"] exI[of _ "\<lambda>_. propT"] has_type_cok)
  moreover have "bicompose_sem.valid_thm undefined ?ar holds [] [] (implies $ ?A $ ?A)"
    if "bicompose_sem ?ct undefined ?ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ?ct undefined ?ar holds inhab by fact
    show ?thesis unfolding valid_thm_Nil
    proof (rule validI)
      fix \<rho> \<sigma> assume cl: "closed_on UNIV \<sigma>" and rg: "rigid_subst \<sigma>"
      have w: "wfp ?ar ?A" using wp by (simp add: wfp_def)
      have c: "closed (sm \<rho> \<sigma> ?A)" using w cl by (simp add: wfp_def no_loose_bound_sm)
      from holds_foldr_dIMP[of "[sm \<rho> \<sigma> ?A]" "sm \<rho> \<sigma> ?A"] c
      have "holds (foldr dIMP [sm \<rho> \<sigma> ?A] (sm \<rho> \<sigma> ?A))" by simp
      moreover have "sm \<rho> \<sigma> (implies $ ?A $ ?A) = foldr dIMP [sm \<rho> \<sigma> ?A] (sm \<rho> \<sigma> ?A)"
        using sm_list_implies[OF rg, of \<rho> "[?A]" ?A] by simp
      ultimately show "holds (sm \<rho> \<sigma> (implies $ ?A $ ?A))" by simp
    qed
  qed
  ultimately show ?thesis by (auto simp: thm_ok_def trivial_thm_def thm_rep.truncate_def)
qed

text \<open>The theorem \<open>A \<turnstile> A\<close> (\<open>Thm.assume\<close>) of a hypothesis \<open>A\<close>.\<close>

definition assume_thm :: "sign \<Rightarrow> pterm \<Rightarrow> thm_cert" where
  "assume_thm c A = \<lparr>th_maxidx = -1, th_tpairs = [], th_prop = A, th_hyps = [A], th_cert = c\<rparr>"

lemma thm_ok_assume: "csig.hyp_ok (sg_consts c) (sg_ar c) A \<Longrightarrow> thm_ok (assume_thm c A)"
proof -
  assume A: "csig.hyp_ok (sg_consts c) (sg_ar c) A"
  obtain alg ar ct where c: "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (cases c) auto
  interpret csig ct .
  have "wft ar propT"
    using A by (intro has_type_wft[of "\<lambda>_. propT" "[]" A]) (auto simp: c hyp_ok_def wt_term_def tyA_def)
  then have wp: "tyA ar {} propT" by (simp add: tyA_def propT_def)
  from A have "thm_typed ar 0 \<lparr>th_maxidx = -1, th_tpairs = [], th_prop = A\<rparr>"
    unfolding thm_typed_def using wp
    by (auto simp: c hyp_ok_def wt_thm_def scons_def vars_thm_def
      intro!: exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
  moreover have "bicompose_sem.valid_thm alg ar holds [A] [] A"
    if "bicompose_sem ct alg ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ct alg ar holds inhab by fact
    show ?thesis by (simp add: valid_thm_def)
  qed
  ultimately show ?thesis using A by (auto simp: thm_ok_def assume_thm_def c thm_rep.truncate_def)
qed

typedef (overloaded) pure_thm = "{th. thm_ok th}"
  morphisms rep_thm Abs_thm
  using thm_ok_trivial by blast

abbreviation thm_rep_of :: "pure_thm \<Rightarrow> thm_rep" where
  "thm_rep_of th \<equiv> thm_rep.truncate (rep_thm th)"

abbreviation hyps_of :: "pure_thm \<Rightarrow> pterm list" where
  "hyps_of th \<equiv> th_hyps (rep_thm th)"

abbreviation cert_of :: "pure_thm \<Rightarrow> sign" where
  "cert_of th \<equiv> th_cert (rep_thm th)"

lemma thm_rep_of_thm_ok: "thm_ok (rep_thm th)"
  using rep_thm by blast

lemma thm_ok_parts:
  assumes "cert_of th = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
  shows "csig.thm_typed ct ar 0 (thm_rep_of th)" "\<forall>h\<in>set (hyps_of th). csig.hyp_ok ct ar h"
    "\<And>holds inhab. bicompose_sem ct alg ar holds inhab \<Longrightarrow>
      bicompose_sem.valid_thm alg ar holds (hyps_of th) (th_tpairs (thm_rep_of th)) (th_prop (thm_rep_of th))"
  using thm_rep_of_thm_ok[of th] assms by (auto simp: thm_ok_def thm_rep.truncate_def Let_def)

lemma sign_cases: obtains alg ar ct where "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
  by (cases c) auto


subsection \<open>Biresolution of theorems\<close>

text \<open>
  The new theorem of a result of \<^const>\<open>biresolution\<close> has the certificate of the proof state
  and the rules, which must agree, as \<open>Thm.join_certificate\<close> demands. Its hypotheses are those
  of the rule and of the proof state (\<open>union_hyps\<close>, the union of lists ordered by
  \<open>Term_Ord.fast_term_ord\<close>; only their set matters here).
\<close>

definition thm_of_bres :: "sign \<Rightarrow> pterm list \<Rightarrow> bres \<Rightarrow> thm_cert" where
  "thm_of_bres c hs x = \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x,
    th_hyps = hs, th_cert = c\<rparr>"

text \<open>
  \<open>biresolution_thms cfg vl trace match brules i state\<close>: the list of the results of
  \<^const>\<open>biresolution\<close> on theorems, each with the rule it was composed with; \<open>None\<close> if an
  exception is raised, if the certificates of the proof state and the rules do not agree, or if
  the configuration does not belong to the well-formed signature (in Isabelle, the algebra of a
  theory is well-formed). \<open>vl\<close> is \<open>Name.variant_list []\<close>.
\<close>

definition biresolution_thms :: "cfg \<Rightarrow> (name list \<Rightarrow> name list) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> (bool \<times> pure_thm) list \<Rightarrow>
    integer \<Rightarrow> pure_thm \<Rightarrow> (pure_thm \<times> (bool \<times> pure_thm)) list option" where
  "biresolution_thms cfg vl trace match_flg brules i state =
    (let c = cert_of state;
      R = (\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
        brevals (unify_ops cfg vl) (sg_alg c) thm_rep_of s0 xs)
     in if wf_algebra (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          (\<forall>r\<in>set brules. cert_of (snd r) = c) \<and> (\<exists>xs. R xs)
       then Some (map (\<lambda>(x, r). (Abs_thm (thm_of_bres c (List.union (hyps_of (snd r)) (hyps_of state)) x), r))
         (THE xs. R xs))
       else None)"

text \<open>
  The new theorems are theorems: they are well-typed and valid. Validity needs the hypotheses of
  the proof state and of the rule only: if they hold, the proof state and the rule are valid,
  since their hypotheses have no schematic variables.
\<close>

lemma thm_ok_thm_of_bres:
  assumes wf: "wf_algebra (sg_alg (cert_of state)) (sg_ar (cert_of state))"
    and br: "okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and res: "brresult (unify_ops cfg vl) (sg_alg (cert_of state)) thm_rep_of s0 (x, (e, rule))"
    and cfg: "cfg_alg cfg = sg_alg (cert_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and rules: "\<forall>r\<in>set brules. cert_of (snd r) = cert_of state"
  shows "thm_ok (thm_of_bres (cert_of state) (List.union (hyps_of rule) (hyps_of state)) x)"
proof -
  obtain alg ar ct where c: "cert_of state = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (rule sign_cases)
  interpret wf_csig ct alg ar using wf by (simp add: c)
  note res' = res[unfolded c, simplified]
  have r: "(e, rule) \<in> set brules"
    using biresolution_result[OF br res'] by blast
  have cr: "cert_of rule = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" using rules r c by force
  note st = thm_ok_parts[OF c] and ru = thm_ok_parts[OF cr]
  have ru_typed: "thm_typed ar 0 (thm_rep_of r)" if "(e, r) \<in> set brules" for e r
  proof -
    have "cert_of r = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" using rules that c by force
    then show ?thesis by (rule thm_ok_parts(1))
  qed
  let ?hs = "List.union (hyps_of rule) (hyps_of state)"
  have hs: "\<forall>h\<in>set ?hs. hyp_ok ar h" using st(2) ru(2) by auto
  have "thm_typed ar 0 \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x\<rparr>"
    by (rule biresolution_thm_typed[OF br res' cfg[unfolded c, simplified] vl st(1) _ ru_typed])
      simp_all
  moreover have "bicompose_sem.valid_thm alg ar holds ?hs (br_tpairs x) (br_prop x)"
    if "bicompose_sem ct alg ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ct alg ar holds inhab by fact
    show ?thesis unfolding valid_thm_iff[OF hs]
    proof
      assume h: "\<forall>h\<in>set ?hs. holds (tr h)"
      have "valid (th_tpairs (thm_rep_of state)) (th_prop (thm_rep_of state))"
        using st(3)[OF that] h unfolding valid_thm_iff[OF st(2)] by auto
      moreover have "valid (th_tpairs (thm_rep_of rule)) (th_prop (thm_rep_of rule))"
        using ru(3)[OF that] h unfolding valid_thm_iff[OF ru(2)] by auto
      ultimately show "valid (br_tpairs x) (br_prop x)"
        using biresolution_valid[OF br res' cfg[unfolded c, simplified] vl _ st(1)] ru(1) by blast
    qed
  qed
  ultimately show ?thesis using hs by (auto simp: thm_ok_def thm_of_bres_def c thm_rep.truncate_def)
qed

text \<open>
  Soundness: the results of \<^const>\<open>biresolution_thms\<close> are the new theorems of the results of
  \<^const>\<open>biresolution\<close>; as theorems, they are well-typed and valid.
\<close>

theorem biresolution_thms_results:
  assumes "biresolution_thms cfg vl trace match_flg brules i state = Some ys" "(th, r) \<in> set ys"
  obtains s0 x where "okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    "brresult (unify_ops cfg vl) (cfg_alg cfg) thm_rep_of s0 (x, r)"
    "rep_thm th = thm_of_bres (cert_of state) (List.union (hyps_of (snd r)) (hyps_of state)) x"
    "cert_of th = cert_of state"
proof -
  let ?c = "cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
    brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
  let ?hs = "\<lambda>r. List.union (hyps_of (snd r)) (hyps_of state)"
  from assms(1) have g: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and ys: "ys = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c (?hs r) x), r)) (THE xs. ?R xs)"
    by (auto simp: biresolution_thms_def Let_def split: if_splits)
  from ex obtain s0 xs where br: "okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and ev: "brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
    by blast
  have "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: okT_det brevals_det\<close>)
  with ys assms(2) obtain x where x: "(x, r) \<in> set xs" and th: "th = Abs_thm (thm_of_bres ?c (?hs r) x)"
    by auto
  have res: "brresult (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 (x, r)" by (rule brevals_brresult[OF ev x])
  obtain e rule where r: "r = (e, rule)" by (cases r)
  have "thm_ok (thm_of_bres ?c (?hs r) x)"
    unfolding r snd_conv by (rule thm_ok_thm_of_bres[OF g(1) br res[unfolded r] g(2)]) (use g(3,4) in auto)
  then have "rep_thm th = thm_of_bres ?c (?hs r) x" by (simp add: th Abs_thm_inverse)
  moreover from this have "cert_of th = ?c" by (simp add: thm_of_bres_def)
  ultimately show thesis using that[OF br] res g(2) by simp
qed

text \<open>
  Termination: \<^const>\<open>biresolution_thms\<close> returns the list of results if the subgoal exists, the
  signature is well-formed and the certificates agree, unless elim-resolution is requested for a
  rule without premises.
\<close>

theorem biresolution_thms_terminates:
  assumes br: "okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) (s0 :: (seq, pure_thm) rseq)"
    and wf: "wf_algebra (sg_alg (cert_of state)) (sg_ar (cert_of state))"
    and cfg: "cfg_alg cfg = sg_alg (cert_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and rules: "\<forall>r\<in>set brules. cert_of (snd r) = cert_of state"
    and eres: "\<forall>(e, r)\<in>set brules. e \<longrightarrow> 0 < nprems_of (thm_rep_of r)"
  shows "biresolution_thms cfg vl trace match_flg brules i state \<noteq> None"
proof -
  obtain alg ar ct where c: "cert_of state = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (rule sign_cases)
  interpret wf_csig ct alg ar using wf by (simp add: c)
  have st: "thm_typed ar 0 (thm_rep_of state)" by (rule thm_ok_parts(1)[OF c])
  have ru: "thm_typed ar 0 (thm_rep_of r) \<and> (e \<longrightarrow> 0 < nprems_of (thm_rep_of r))" if "(e, r) \<in> set brules" for e r
    using thm_ok_parts(1)[of r alg ar ct] rules eres that c by fastforce
  have "\<exists>xs. brevals (unify_ops cfg vl) alg thm_rep_of s0 xs"
  proof (rule biresolution_terminates[OF br cfg[unfolded c, simplified] vl st ru])
    fix stpairs Bs Bi C goal xs
    assume "brevals (unify_ops cfg vl) alg thm_rep_of s0 xs"
    then show "\<exists>xs. brevals (unify_ops cfg vl) alg thm_rep_of s0 xs" by blast
  qed
  with br wf cfg vl rules show ?thesis by (auto simp: biresolution_thms_def Let_def c)
qed

text \<open>
  Completeness: the results of \<^const>\<open>biresolution_thms\<close> contain the new theorems of all results
  of the composition of each rule that passes the quick test with the proof state (by
  \<^const>\<open>bicompose_aux\<close> for the rule lifted over the subgoal).
\<close>

theorem biresolution_thms_complete:
  assumes ys: "biresolution_thms cfg vl trace match_flg brules i state = Some ys"
    and eres: "\<forall>(e, r)\<in>set brules. e \<longrightarrow> 0 < nprems_of (thm_rep_of r)"
    and d: "okT (dest_state (thm_rep_of state) i) (stpairs, Bs, Bi, C)"
    and g: "okT (cprem_of (thm_rep_of state) i) goal"
    and r: "(e, rule) \<in> set brules"
    and t: "trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) e (thm_rep_of rule)"
    and ok: "okT (bicompose_aux (unify_ops cfg vl) (cfg_alg cfg) True match_flg True
      (pthm_of (thm_rep_of state)) (stpairs, Bs, Bi, C) True e
      (pthm_of (lift_rule goal (th_maxidx (thm_rep_of state)) (thm_rep_of rule))) (nprems_of (thm_rep_of rule))) xq"
    and bv: "bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
  shows "(Abs_thm (thm_of_bres (cert_of state) (List.union (hyps_of rule) (hyps_of state)) x), (e, rule)) \<in> set ys"
proof -
  let ?c = "cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
    brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
  from ys have g0: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and ys': "ys = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c (List.union (hyps_of (snd r)) (hyps_of state)) x), r))
      (THE xs. ?R xs)"
    by (auto simp: biresolution_thms_def Let_def split: if_splits)
  obtain alg ar ct where c: "?c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (rule sign_cases)
  interpret wf_csig ct alg ar using g0(1) by (simp add: c)
  from ex obtain s0 xs where br: "okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and ev: "brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
    by blast
  have the: "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: okT_det brevals_det\<close>)
  have st: "thm_typed ar 0 (thm_rep_of state)" by (rule thm_ok_parts(1)[OF c])
  have ru: "thm_typed ar 0 (thm_rep_of r) \<and> (e \<longrightarrow> 0 < nprems_of (thm_rep_of r))" if "(e, r) \<in> set brules" for e r
    using thm_ok_parts(1)[of r alg ar ct] g0(4) eres that c by fastforce
  have cfg: "cfg_alg cfg = alg" using g0(2) by (simp add: c)
  from biresolution_complete[OF br cfg g0(3)[rule_format] st ru] obtain stpairs' Bs' Bi' C' goal' xs' where
    d': "okT (dest_state (thm_rep_of state) i) (stpairs', Bs', Bi', C')"
    and g': "okT (cprem_of (thm_rep_of state) i) goal'"
    and ev': "brevals (unify_ops cfg vl) alg thm_rep_of s0 xs'"
    and cmp: "\<And>e rule xq rs x. (e, rule) \<in> set brules \<Longrightarrow>
      trace \<or> could_bires (strip_assums_hyp Bi') (strip_assums_concl Bi') e (thm_rep_of rule) \<Longrightarrow>
      okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of (thm_rep_of state))
        (stpairs', Bs', Bi', C') True e (pthm_of (lift_rule goal' (th_maxidx (thm_rep_of state)) (thm_rep_of rule)))
        (nprems_of (thm_rep_of rule))) xq \<Longrightarrow>
      bevals (unify_ops cfg vl) xq rs \<Longrightarrow> x \<in> set rs \<Longrightarrow> (x, (e, rule)) \<in> set xs'"
    by blast
  from d d' have "(stpairs', Bs', Bi', C') = (stpairs, Bs, Bi, C)" by (auto dest: okT_det)
  moreover from g g' have "goal' = goal" by (auto dest: okT_det)
  moreover from ev ev' have "xs' = xs" by (auto simp: c dest: brevals_det)
  ultimately have "(x, (e, rule)) \<in> set xs" using cmp[OF r _ _ bv x] t ok cfg by auto
  then show ?thesis by (force simp: ys' the)
qed

end
