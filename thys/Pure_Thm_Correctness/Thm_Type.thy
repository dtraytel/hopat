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


subsection \<open>Sort hypotheses\<close>

text \<open>
  A sort may be empty: no type built from type constructors has it. The validity
  @{const bicompose_sem.valid_thm} instantiates the type variables of empty sorts by fixed type
  variables, which have every sort by fiat. A theorem with sort hypotheses \<open>\<Sigma>\<close> (\<open>shyps\<close>) is
  valid if, provided that the sorts of \<open>\<Sigma>\<close> are not empty, its instances hold for every ground
  instantiation of the type variables that is well-sorted on the sorts that are not empty
  (\<open>valid_s\<close>). The sort hypotheses contain the sorts of the type variables of
  the theorem; then both notions of validity agree.
\<close>

context bicompose_sem
begin

definition inh :: "psort \<Rightarrow> bool" where
  "inh S \<longleftrightarrow> (\<exists>T. ground ar T \<and> no_tfrees T \<and> has_sort alg T S)"

definition gtinst_s :: "tinst \<Rightarrow> bool" where
  "gtinst_s \<rho> \<longleftrightarrow> (\<forall>v S. ground ar (\<rho> v S)) \<and> (\<forall>v S. inh S \<longrightarrow> has_sort alg (\<rho> v S) S)"

definition valid_s :: "psort set \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid_s \<Sigma> hs tps P \<longleftrightarrow> (\<forall>S\<in>\<Sigma>. inh S) \<longrightarrow>
    (\<forall>\<rho> \<sigma>. gtinst_s \<rho> \<longrightarrow> closed_on UNIV \<sigma> \<longrightarrow> rigid_subst \<sigma> \<longrightarrow>
      (\<forall>h\<in>set hs. holds (sm \<rho> \<sigma> h)) \<longrightarrow>
      (\<forall>(t, u)\<in>set tps. sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u) \<longrightarrow> holds (sm \<rho> \<sigma> P))"

lemma valid_s_valid_thm: "valid_s \<Sigma> hs tps P \<Longrightarrow> \<forall>S\<in>\<Sigma>. inh S \<Longrightarrow> valid_thm hs tps P"
  unfolding valid_s_def valid_thm_def gtinst_s_def gtinst_def wsinst_def by blast

lemma inst_cong_tvars:
  "(\<And>U v S. U \<in> tys t \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> \<rho> v S = \<rho>' v S) \<Longrightarrow> inst \<rho> t = inst \<rho>' t"
proof (induction t)
  case (Const a T)
  then show ?case using tsubst_cong[of T \<rho> \<rho>'] by simp
next
  case (Free a T)
  then show ?case using tsubst_cong[of T \<rho> \<rho>'] by simp
next
  case (Var x T)
  then show ?case using tsubst_cong[of T \<rho> \<rho>'] by simp
next
  case (Abs a T t)
  have "inst \<rho> t = inst \<rho>' t" using Abs.IH Abs.prems by auto
  moreover have "tsubst \<rho> T = tsubst \<rho>' T" using Abs.prems by (intro tsubst_cong) auto
  ultimately show ?case by simp
next
  case (App s t)
  have "inst \<rho> s = inst \<rho>' s" "inst \<rho> t = inst \<rho>' t" using App.IH App.prems by auto
  then show ?case by simp
qed simp

lemma sm_cong_tvars:
  "(\<And>U v S. U \<in> tys t \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> \<rho> v S = \<rho>' v S) \<Longrightarrow> sm \<rho> \<sigma> t = sm \<rho>' \<sigma> t"
  unfolding sm_def by (simp add: inst_cong_tvars[of t \<rho> \<rho>'])

text \<open>
  If the sorts of the type variables are among the sort hypotheses, the validity for all
  instantiations of the type variables of non-empty sorts follows from the validity for all
  instantiations: on empty sorts, an instantiation can be changed to fixed type variables.
\<close>

lemma valid_thm_valid_s:
  assumes v: "(\<forall>S\<in>\<Sigma>. inh S) \<Longrightarrow> valid_thm hs tps P"
    and S: "\<And>X U v S. X = P \<or> X \<in> set hs \<or> (\<exists>Y. (X, Y) \<in> set tps \<or> (Y, X) \<in> set tps) \<Longrightarrow>
      U \<in> tys X \<Longrightarrow> (v, S) \<in> tvars U \<Longrightarrow> S \<in> \<Sigma>"
  shows "valid_s \<Sigma> hs tps P"
  unfolding valid_s_def
proof (intro impI allI)
  fix \<rho> \<sigma> assume inS: "\<forall>S\<in>\<Sigma>. inh S" and g: "gtinst_s \<rho>" and cl: "closed_on UNIV \<sigma>"
    and rg: "rigid_subst \<sigma>" and h: "\<forall>h\<in>set hs. holds (sm \<rho> \<sigma> h)"
    and tp: "\<forall>(t, u)\<in>set tps. sm \<rho> \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> u"
  define \<rho>' where "\<rho>' v S = (if inh S then \<rho> v S else TFree STR ''a'' S)" for v S
  have g': "gtinst \<rho>'"
    using g by (auto simp: gtinst_def gtinst_s_def wsinst_def \<rho>'_def class_le_def)
  have e: "sm \<rho>' \<sigma> X = sm \<rho> \<sigma> X"
    if "X = P \<or> X \<in> set hs \<or> (\<exists>Y. (X, Y) \<in> set tps \<or> (Y, X) \<in> set tps)" for X
  proof (rule sm_cong_tvars)
    fix U v S assume "U \<in> tys X" "(v, S) \<in> tvars U"
    with S[OF that] inS show "\<rho>' v S = \<rho> v S" by (simp add: \<rho>'_def)
  qed
  have "\<forall>h\<in>set hs. holds (sm \<rho>' \<sigma> h)" using h e by auto
  moreover have "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma> u"
  proof (intro ballI, clarify)
    fix t u assume tu: "(t, u) \<in> set tps"
    have "sm \<rho>' \<sigma> t = sm \<rho> \<sigma> t" "sm \<rho>' \<sigma> u = sm \<rho> \<sigma> u"
      by (rule e, use tu in blast)+
    with tp tu show "sm \<rho>' \<sigma> t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma> u" by auto
  qed
  ultimately have "holds (sm \<rho>' \<sigma> P)" using v[OF inS] g' cl rg unfolding valid_thm_def by blast
  then show "holds (sm \<rho> \<sigma> P)" using e[of P] by simp
qed

end

text \<open>
  The sorts of a type (\<open>Sorts.insert_typ\<close>), the sort hypotheses added by a type environment
  (\<open>Envir.insert_sorts\<close>: the sorts of the types of its bindings), and the sort constraints
  added by it (\<open>Thm.insert_constraints_env\<close>: each binding of a type variable of a non-empty
  sort \<open>S\<close> to a type \<open>T\<close> that is not a type variable of sort \<open>S\<close> requires the normalized \<open>T\<close>,
  with its type variables replaced by a fixed type variable of their sorts, to have sort \<open>S\<close>). Sets model the
  ordered lists of \<open>thm.ML\<close>.
\<close>

fun atyp_sorts :: "ptyp \<Rightarrow> psort set" where
  "atyp_sorts (Type a Ts) = \<Union> (atyp_sorts ` set Ts)"
| "atyp_sorts (TFree a S) = {S}"
| "atyp_sorts (TVar v S) = {S}"

definition insert_sorts :: "tyenv \<Rightarrow> psort set \<Rightarrow> psort set" where
  "insert_sorts \<theta> \<Sigma> = \<Sigma> \<union> {S. \<exists>v S0 U. vt_lookup \<theta> v = Some (S0, U) \<and> S \<in> atyp_sorts U}"

fun smash_atyps :: "ptyp \<Rightarrow> ptyp" where
  "smash_atyps (Type a Ts) = Type a (map smash_atyps Ts)"
| "smash_atyps (TFree a S) = TFree STR ''a'' S"
| "smash_atyps (TVar v S) = TFree STR ''a'' S"

definition insert_constraints_env :: "tyenv \<Rightarrow> (ptyp \<times> psort) set \<Rightarrow> (ptyp \<times> psort) set" where
  "insert_constraints_env \<theta> C = C \<union> {(smash_atyps (tnorm \<theta> U), S) | v S U. vt_lookup \<theta> v = Some (S, U) \<and>
    S \<noteq> [] \<and> (\<forall>a. tnorm \<theta> U \<noteq> TFree a S) \<and> (\<forall>w. tnorm \<theta> U \<noteq> TVar w S)}"

lemma tvars_atyp_sorts: "(w, S) \<in> tvars T \<Longrightarrow> S \<in> atyp_sorts T"
  by (induction T) auto

lemma has_sort_smash: "has_sort alg (smash_atyps T) S \<longleftrightarrow> has_sort alg T S"
  by (induction T arbitrary: S) (auto simp: nth_mem)

lemma insert_constraints_env_ok:
  assumes "\<forall>(T, S)\<in>C. has_sort alg T S" "tsorted alg \<theta>"
  shows "\<forall>(T, S)\<in>insert_constraints_env \<theta> C. has_sort alg T S"
  using assms by (auto simp: insert_constraints_env_def has_sort_smash tsorted_def bsorted_def)

context csig
begin

lemma thm_typeds_mono: "thm_typeds ar lo \<Sigma> th \<Longrightarrow> \<Sigma> \<subseteq> \<Sigma>' \<Longrightarrow> thm_typeds ar lo \<Sigma>' th"
  unfolding thm_typeds_def by blast

lemma env_sorts_insert_sorts: "env_sorts \<theta> \<subseteq> insert_sorts \<theta> \<Sigma>"
  unfolding env_sorts_def insert_sorts_def using tvars_atyp_sorts by blast

lemma env_sorts_ok: "tsorted alg \<theta> \<Longrightarrow> S \<in> env_sorts \<theta> \<Longrightarrow> sort_ok alg S"
  unfolding env_sorts_def tsorted_def by (blast dest: tvars_envI2 intro: tcertD)

end


subsection \<open>The type of theorems\<close>

text \<open>
  The certificate of a theorem (\<open>Context.certificate\<close>, the theory) is modelled by its signature:
  the sort algebra, the arities of the type constructors and the declared types of the constants.
  The record \<^typ>\<open>thm_rep\<close> of the model is extended by the hypotheses and the certificate.
  Theorems are the records that are typed in their signature with non-negative indices
  (@{const csig.thm_typeds}; in particular, their constants occur at instances of their declared
  types, and the sorts of their type variables are certified sort hypotheses), whose hypotheses
  are well-typed and without schematic variables (@{const csig.hyp_ok}), whose sort constraints
  hold, and that are valid in every model of their signature.
\<close>

record sign =
  sg_alg :: algebra
  sg_ar :: "name \<Rightarrow> nat"
  sg_consts :: "name \<Rightarrow> ptyp option"

record thm_cert = thm_rep +
  th_constraints :: "(ptyp \<times> psort) set"
  th_shyps :: "psort set"
  th_hyps :: "pterm list"
  th_cert :: sign

definition thm_ok :: "thm_cert \<Rightarrow> bool" where
  "thm_ok th \<longleftrightarrow> (let alg = sg_alg (th_cert th); ar = sg_ar (th_cert th); ct = sg_consts (th_cert th) in
    csig.thm_typeds ct ar 0 {S \<in> th_shyps th. sort_ok alg S} (thm_rep.truncate th) \<and> (\<forall>h\<in>set (th_hyps th). csig.hyp_ok ct ar h) \<and>
    (\<forall>(T, S)\<in>th_constraints th. has_sort alg T S) \<and>
    (\<forall>holds inhab. bicompose_sem alg ar holds inhab \<longrightarrow>
      bicompose_sem.valid_s alg ar holds (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)))"

text \<open>The theorem \<open>A \<Longrightarrow> A\<close> (\<open>Thm.trivial\<close>) shows that there are theorems.\<close>

definition trivial_thm :: thm_cert where
  "trivial_thm = \<lparr>th_maxidx = 0, th_tpairs = [],
    th_prop = implies $ Var (STR ''A'', 0) propT $ Var (STR ''A'', 0) propT,
    th_constraints = {}, th_shyps = {}, th_hyps = [],
    th_cert = \<lparr>sg_alg = undefined, sg_ar = \<lambda>_. 0, sg_consts = \<lambda>_. None\<rparr>\<rparr>"

lemma thm_ok_trivial: "thm_ok trivial_thm"
proof -
  let ?A = "Var (STR ''A'', 0) propT" and ?ar = "\<lambda>_ :: name. 0 :: nat" and ?ct = "\<lambda>_ :: name. None :: ptyp option"
  interpret csig ?ct .
  have wp: "wft ?ar propT" "wft ?ar imp_type" "tvars propT = {}" "tvars imp_type = {}"
    by (simp_all add: propT_def imp_type_def tarity_def)
  have h: "has_type (\<lambda>_. propT) [] (implies $ ?A $ ?A) propT"
    by (simp add: has_type_implies has_type.Var)
  have ty: "tys (implies $ ?A $ ?A) = {imp_type, propT}" by (auto simp: implies_imp_type)
  then have w: "wt_term ?ar {} (\<lambda>_. propT) 0 (implies $ ?A $ ?A) propT"
    using h wp by (simp add: wt_term_def swf_tm_def implies_imp_type below_def tyA_def)
  have "thm_typeds ?ar 0 {S \<in> {}. sort_ok undefined S} \<lparr>th_maxidx = 0, th_tpairs = [], th_prop = implies $ ?A $ ?A\<rparr>"
    unfolding thm_typeds_def using w wp h
    by (auto simp: wt_thm_def scons_def vars_thm_def implies_imp_type tyA_def
      intro!: exI[of _ "{}"] exI[of _ "\<lambda>_. propT"] has_type_cok)
  moreover have "bicompose_sem.valid_s undefined ?ar holds {} [] [] (implies $ ?A $ ?A)"
    if "bicompose_sem undefined ?ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ?ct undefined ?ar holds inhab by fact
    have "valid_thm [] [] (implies $ ?A $ ?A)" unfolding valid_thm_Nil
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
    then show ?thesis by (rule valid_thm_valid_s) (use wp in \<open>auto simp: implies_imp_type\<close>)
  qed
  ultimately show ?thesis by (auto simp: thm_ok_def trivial_thm_def thm_rep.truncate_def Let_def)
qed

text \<open>
  The theorem \<open>A \<turnstile> A\<close> (\<open>Thm.assume\<close>) of a hypothesis \<open>A\<close>; its sort hypotheses are the sorts
  of the certified term \<open>A\<close>.
\<close>

definition assume_thm :: "sign \<Rightarrow> pterm \<Rightarrow> thm_cert" where
  "assume_thm c A = \<lparr>th_maxidx = -1, th_tpairs = [], th_prop = A, th_constraints = {},
    th_shyps = \<Union> (atyp_sorts ` csig.tys A), th_hyps = [A], th_cert = c\<rparr>"

lemma thm_ok_assume: "csig.hyp_ok (sg_consts c) (sg_ar c) A \<Longrightarrow> thm_ok (assume_thm c A)"
proof -
  assume A: "csig.hyp_ok (sg_consts c) (sg_ar c) A"
  obtain alg ar ct where c: "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (cases c) auto
  interpret csig ct .
  have "wft ar propT"
    using A by (intro has_type_wft[of "\<lambda>_. propT" "[]" A]) (auto simp: c hyp_ok_def wt_term_def tyA_def)
  then have wp: "tyA ar {} propT" by (simp add: tyA_def propT_def)
  from A have "thm_typeds ar 0 {S \<in> \<Union> (atyp_sorts ` tys A). sort_ok alg S} \<lparr>th_maxidx = -1, th_tpairs = [], th_prop = A\<rparr>"
    unfolding thm_typeds_def using wp
    by (auto simp: c hyp_ok_def wt_thm_def scons_def vars_thm_def
      intro!: exI[of _ "{}"] exI[of _ "\<lambda>_. propT"])
  moreover have "bicompose_sem.valid_s alg ar holds (\<Union> (atyp_sorts ` tys A)) [A] [] A"
    if "bicompose_sem alg ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ct alg ar holds inhab by fact
    show ?thesis by (simp add: valid_s_def)
  qed
  ultimately show ?thesis using A by (auto simp: thm_ok_def assume_thm_def c thm_rep.truncate_def)
qed

typedef (overloaded) pure_thm = "{th. thm_ok th}"
  morphisms rep_thm Abs_thm
  using thm_ok_trivial by blast

abbreviation thm_rep_of :: "pure_thm \<Rightarrow> thm_rep" where
  "thm_rep_of th \<equiv> thm_rep.truncate (rep_thm th)"

abbreviation constraints_of :: "pure_thm \<Rightarrow> (ptyp \<times> psort) set" where
  "constraints_of th \<equiv> th_constraints (rep_thm th)"

abbreviation shyps_of :: "pure_thm \<Rightarrow> psort set" where
  "shyps_of th \<equiv> th_shyps (rep_thm th)"

abbreviation hyps_of :: "pure_thm \<Rightarrow> pterm list" where
  "hyps_of th \<equiv> th_hyps (rep_thm th)"

abbreviation cert_of :: "pure_thm \<Rightarrow> sign" where
  "cert_of th \<equiv> th_cert (rep_thm th)"

lemma thm_rep_of_thm_ok: "thm_ok (rep_thm th)"
  using rep_thm by blast

lemma thm_ok_parts:
  assumes "cert_of th = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
  shows "csig.thm_typeds ct ar 0 {S \<in> shyps_of th. sort_ok alg S} (thm_rep_of th)" "\<forall>h\<in>set (hyps_of th). csig.hyp_ok ct ar h"
    "\<forall>(T, S)\<in>constraints_of th. has_sort alg T S"
    "\<And>holds inhab. bicompose_sem alg ar holds inhab \<Longrightarrow>
      bicompose_sem.valid_s alg ar holds (shyps_of th) (hyps_of th) (th_tpairs (thm_rep_of th)) (th_prop (thm_rep_of th))"
  using thm_rep_of_thm_ok[of th] assms by (auto simp: thm_ok_def thm_rep.truncate_def Let_def)

lemma sign_cases: obtains alg ar ct where "c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
  by (cases c) auto


subsection \<open>Biresolution of theorems\<close>

text \<open>
  The new theorem of a result of \<^const>\<open>biresolution\<close> has the certificate of the proof state
  and the rules, which must agree, as \<open>Thm.join_certificate\<close> demands. Its hypotheses are those
  of the rule and of the proof state (\<open>union_hyps\<close>, the union of lists ordered by
  \<open>Term_Ord.fast_term_ord\<close>; only their set matters here). Its sort hypotheses are those of the
  rule lifted over the subgoal (\<open>Thm.lift_rule\<close> adds the sorts of the subgoal, which are the sort
  hypotheses of the proof state) and of the proof state, with the sorts of the type environment
  (\<open>Envir.insert_sorts\<close>); its sort constraints are those of the rule and of the proof state, with
  those of the type environment (\<open>insert_constraints_env\<close>).
\<close>

definition thm_of_bres :: "sign \<Rightarrow> pure_thm \<Rightarrow> pure_thm \<Rightarrow> bres \<Rightarrow> thm_cert" where
  "thm_of_bres c state rule x =
    \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x,
     th_constraints = insert_constraints_env (tyenv (br_env x)) (constraints_of rule \<union> constraints_of state),
     th_shyps = insert_sorts (tyenv (br_env x)) ((shyps_of rule \<union> shyps_of state) \<union> shyps_of state),
     th_hyps = List.union (hyps_of rule) (hyps_of state), th_cert = c\<rparr>"

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
      R = (\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
        csig.brevals (unify_ops cfg vl) (sg_alg c) thm_rep_of s0 xs)
     in if wf_algebra (sg_alg c) (sg_ar c) \<and> cfg_alg cfg = sg_alg c \<and> (\<forall>xs. length (vl xs) = length xs) \<and>
          (\<forall>r\<in>set brules. cert_of (snd r) = c) \<and> (\<exists>xs. R xs)
       then Some (map (\<lambda>(x, r). (Abs_thm (thm_of_bres c state (snd r) x), r)) (THE xs. R xs))
       else None)"

text \<open>
  The new theorems are theorems: they are well-typed and valid. Validity needs the hypotheses and
  sort hypotheses of the proof state and of the rule only: if they hold or are not empty, the proof
  state and the rule are valid, since their hypotheses have no schematic variables.
\<close>

lemma thm_ok_thm_of_bres:
  assumes wf: "wf_algebra (sg_alg (cert_of state)) (sg_ar (cert_of state))"
    and br: "csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and res: "csig.brresult (unify_ops cfg vl) (sg_alg (cert_of state)) thm_rep_of s0 (x, (e, rule))"
    and cfg: "cfg_alg cfg = sg_alg (cert_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and rules: "\<forall>r\<in>set brules. cert_of (snd r) = cert_of state"
  shows "thm_ok (thm_of_bres (cert_of state) state rule x)"
proof -
  obtain alg ar ct where c: "cert_of state = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (rule sign_cases)
  interpret wf_csig ct alg ar using wf by (simp add: c wf_csig_def)
  note res' = res[unfolded c, simplified]
  have r: "(e, rule) \<in> set brules"
    using biresolution_result[OF br res'] by blast
  have cr: "cert_of rule = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" using rules r c by force
  note st = thm_ok_parts[OF c] and ru = thm_ok_parts[OF cr]
  have ru_typed: "thm_typeds ar 0 {S \<in> shyps_of r. sort_ok alg S} (thm_rep_of r)"
    if "(e, r) \<in> set brules" for e r
  proof -
    have "cert_of r = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" using rules that c by force
    then show ?thesis by (rule thm_ok_parts(1))
  qed
  have stc: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of state)"
    by (rule thm_typeds_mono[OF st(1)]) auto
  have ruc: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of rule)"
    by (rule thm_typeds_mono[OF ru(1)]) auto
  let ?\<theta> = "tyenv (br_env x)"
  let ?hs = "List.union (hyps_of rule) (hyps_of state)"
  let ?S = "insert_sorts ?\<theta> ((shyps_of rule \<union> shyps_of state) \<union> shyps_of state)"
  have hs: "\<forall>h\<in>set ?hs. hyp_ok ar h" using st(2) ru(2) by auto
  note bt = biresolution_thm_typed[OF br res' cfg[unfolded c, simplified] vl st(1) _ ru_typed]
  have srt: "tsorted alg ?\<theta>" by (rule bt(2)) auto
  have ty: "thm_typeds ar 0 {S \<in> ?S. sort_ok alg S}
      \<lparr>th_maxidx = maxidx (br_env x), th_tpairs = br_tpairs x, th_prop = br_prop x\<rparr>"
    by (rule thm_typeds_mono[OF bt(1)])
      (use env_sorts_insert_sorts env_sorts_ok[OF srt] in \<open>auto simp: insert_sorts_def\<close>)
  have cs: "\<forall>(T, S)\<in>insert_constraints_env ?\<theta> (constraints_of rule \<union> constraints_of state). has_sort alg T S"
    by (rule insert_constraints_env_ok[OF _ srt]) (use st(3) ru(3) in blast)
  have "bicompose_sem.valid_s alg ar holds ?S ?hs (br_tpairs x) (br_prop x)"
    if "bicompose_sem alg ar holds inhab" for holds inhab
  proof -
    interpret bicompose_sem ct alg ar holds inhab by fact
    show ?thesis
    proof (rule valid_thm_valid_s)
      assume inS: "\<forall>S\<in>?S. inh S"
      have "\<forall>S\<in>shyps_of state. inh S" "\<forall>S\<in>shyps_of rule. inh S"
        using inS by (auto simp: insert_sorts_def)
      then have vs: "valid_thm (hyps_of state) (th_tpairs (thm_rep_of state)) (th_prop (thm_rep_of state))"
        "valid_thm (hyps_of rule) (th_tpairs (thm_rep_of rule)) (th_prop (thm_rep_of rule))"
        using valid_s_valid_thm[OF st(4)[OF that]] valid_s_valid_thm[OF ru(4)[OF that]] by blast+
      show "valid_thm ?hs (br_tpairs x) (br_prop x)" unfolding valid_thm_iff[OF hs]
      proof
        assume h: "\<forall>h\<in>set ?hs. holds (tr h)"
        have "valid (th_tpairs (thm_rep_of state)) (th_prop (thm_rep_of state))"
          using vs(1) h unfolding valid_thm_iff[OF st(2)] by auto
        moreover have "valid (th_tpairs (thm_rep_of rule)) (th_prop (thm_rep_of rule))"
          using vs(2) h unfolding valid_thm_iff[OF ru(2)] by auto
        ultimately show "valid (br_tpairs x) (br_prop x)"
          using biresolution_valid[OF br res' cfg[unfolded c, simplified] vl _ stc] ruc by blast
      qed
    next
      fix X U v S
      assume X: "X = br_prop x \<or> X \<in> set ?hs \<or> (\<exists>Y. (X, Y) \<in> set (br_tpairs x) \<or> (Y, X) \<in> set (br_tpairs x))"
        and U: "U \<in> tys X" and vS: "(v, S) \<in> tvars U"
      from X consider "X \<in> set ?hs" | "U \<in> tys (br_prop x) \<or> (\<exists>(t, u)\<in>set (br_tpairs x). U \<in> tys t \<union> tys u)"
        using U by fastforce
      then show "S \<in> ?S"
      proof cases
        case 1
        with hs U vS show ?thesis by (auto simp: hyp_ok_def wt_term_def tyA_def)
      next
        case 2
        with thm_typeds_sorts[OF ty, of U v S] vS show ?thesis by simp
      qed
    qed
  qed
  then show ?thesis using hs ty cs
    by (auto simp: thm_ok_def thm_of_bres_def c thm_rep.truncate_def Let_def)
qed

text \<open>
  Soundness: the results of \<^const>\<open>biresolution_thms\<close> are the new theorems of the results of
  \<^const>\<open>biresolution\<close>; as theorems, they are well-typed and valid.
\<close>

theorem biresolution_thms_results:
  assumes "biresolution_thms cfg vl trace match_flg brules i state = Some ys" "(th, r) \<in> set ys"
  obtains s0 x where "csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    "csig.brresult (unify_ops cfg vl) (cfg_alg cfg) thm_rep_of s0 (x, r)"
    "rep_thm th = thm_of_bres (cert_of state) state (snd r) x"
    "cert_of th = cert_of state"
proof -
  let ?c = "cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
    csig.brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
  from assms(1) have g: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and ys: "ys = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c state (snd r) x), r)) (THE xs. ?R xs)"
    by (auto simp: biresolution_thms_def Let_def split: if_splits)
  from ex obtain s0 xs where br: "csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and ev: "csig.brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
    by blast
  have "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: csig.okT_det csig.brevals_det\<close>)
  with ys assms(2) obtain x where x: "(x, r) \<in> set xs" and th: "th = Abs_thm (thm_of_bres ?c state (snd r) x)"
    by auto
  have res: "csig.brresult (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 (x, r)" by (rule csig.brevals_brresult[OF ev x])
  obtain e rule where r: "r = (e, rule)" by (cases r)
  have "thm_ok (thm_of_bres ?c state (snd r) x)"
    unfolding r snd_conv by (rule thm_ok_thm_of_bres[OF g(1) br res[unfolded r] g(2)]) (use g(3,4) in auto)
  then have "rep_thm th = thm_of_bres ?c state (snd r) x" by (simp add: th Abs_thm_inverse)
  moreover from this have "cert_of th = ?c" by (simp add: thm_of_bres_def Let_def)
  ultimately show thesis using that[OF br] res g(2) by simp
qed

text \<open>
  Termination: \<^const>\<open>biresolution_thms\<close> returns the list of results if the subgoal exists, the
  signature is well-formed and the certificates agree, unless elim-resolution is requested for a
  rule without premises.
\<close>

theorem biresolution_thms_terminates:
  assumes br: "csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) (s0 :: (seq, pure_thm) rseq)"
    and wf: "wf_algebra (sg_alg (cert_of state)) (sg_ar (cert_of state))"
    and cfg: "cfg_alg cfg = sg_alg (cert_of state)" and vl: "\<And>xs. length (vl xs) = length xs"
    and rules: "\<forall>r\<in>set brules. cert_of (snd r) = cert_of state"
    and eres: "\<forall>(e, r)\<in>set brules. e \<longrightarrow> 0 < nprems_of (thm_rep_of r)"
  shows "biresolution_thms cfg vl trace match_flg brules i state \<noteq> None"
proof -
  obtain alg ar ct where c: "cert_of state = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>"
    by (rule sign_cases)
  interpret wf_csig ct alg ar using wf by (simp add: c wf_csig_def)
  have st: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of state)"
    by (rule thm_typeds_mono[OF thm_ok_parts(1)[OF c]]) auto
  have ru: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of r) \<and> (e \<longrightarrow> 0 < nprems_of (thm_rep_of r))"
    if "(e, r) \<in> set brules" for e r
    using thm_typeds_mono[OF thm_ok_parts(1)[of r alg ar ct], of "Collect (sort_ok alg)"] rules eres that c
    by fastforce
  have "\<exists>xs. csig.brevals (unify_ops cfg vl) alg thm_rep_of s0 xs"
  proof (rule biresolution_terminates[OF br cfg[unfolded c, simplified] vl st ru])
    fix stpairs Bs Bi C goal xs
    assume "csig.brevals (unify_ops cfg vl) alg thm_rep_of s0 xs"
    then show "\<exists>xs. csig.brevals (unify_ops cfg vl) alg thm_rep_of s0 xs" by blast
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
    and d: "csig.okT (dest_state (thm_rep_of state) i) (stpairs, Bs, Bi, C)"
    and g: "csig.okT (cprem_of (thm_rep_of state) i) goal"
    and r: "(e, rule) \<in> set brules"
    and t: "trace \<or> could_bires (strip_assums_hyp Bi) (strip_assums_concl Bi) e (thm_rep_of rule)"
    and ok: "csig.okT (bicompose_aux (unify_ops cfg vl) (cfg_alg cfg) True match_flg True
      (pthm_of (thm_rep_of state)) (stpairs, Bs, Bi, C) True e
      (pthm_of (lift_rule goal (th_maxidx (thm_rep_of state)) (thm_rep_of rule))) (nprems_of (thm_rep_of rule))) xq"
    and bv: "csig.bevals (unify_ops cfg vl) xq rs" and x: "x \<in> set rs"
  shows "(Abs_thm (thm_of_bres (cert_of state) state rule x), (e, rule)) \<in> set ys"
proof -
  let ?c = "cert_of state"
  let ?R = "\<lambda>xs. \<exists>s0. csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0 \<and>
    csig.brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
  from ys have g0: "wf_algebra (sg_alg ?c) (sg_ar ?c)" "cfg_alg cfg = sg_alg ?c" "\<forall>xs. length (vl xs) = length xs"
    "\<forall>r\<in>set brules. cert_of (snd r) = ?c" and ex: "\<exists>xs. ?R xs"
    and ys': "ys = map (\<lambda>(x, r). (Abs_thm (thm_of_bres ?c state (snd r) x), r))
      (THE xs. ?R xs)"
    by (auto simp: biresolution_thms_def Let_def split: if_splits)
  obtain alg ar ct where c: "?c = \<lparr>sg_alg = alg, sg_ar = ar, sg_consts = ct\<rparr>" by (rule sign_cases)
  interpret wf_csig ct alg ar using g0(1) by (simp add: c wf_csig_def)
  from ex obtain s0 xs where br: "csig.okT (biresolution trace match_flg thm_rep_of brules i (thm_rep_of state)) s0"
    and ev: "csig.brevals (unify_ops cfg vl) (sg_alg ?c) thm_rep_of s0 xs"
    by blast
  have the: "(THE xs. ?R xs) = xs"
    by (rule the_equality) (use br ev in \<open>auto dest: csig.okT_det csig.brevals_det\<close>)
  have st: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of state)"
    by (rule thm_typeds_mono[OF thm_ok_parts(1)[OF c]]) auto
  have ru: "thm_typeds ar 0 (Collect (sort_ok alg)) (thm_rep_of r) \<and> (e \<longrightarrow> 0 < nprems_of (thm_rep_of r))"
    if "(e, r) \<in> set brules" for e r
    using thm_typeds_mono[OF thm_ok_parts(1)[of r alg ar ct], of "Collect (sort_ok alg)"] g0(4) eres that c
    by fastforce
  have cfg: "cfg_alg cfg = alg" using g0(2) by (simp add: c)
  from biresolution_complete[OF br cfg g0(3)[rule_format] st ru] obtain stpairs' Bs' Bi' C' goal' xs' where
    d': "csig.okT (dest_state (thm_rep_of state) i) (stpairs', Bs', Bi', C')"
    and g': "csig.okT (cprem_of (thm_rep_of state) i) goal'"
    and ev': "csig.brevals (unify_ops cfg vl) alg thm_rep_of s0 xs'"
    and cmp: "\<And>e rule xq rs x. (e, rule) \<in> set brules \<Longrightarrow>
      trace \<or> could_bires (strip_assums_hyp Bi') (strip_assums_concl Bi') e (thm_rep_of rule) \<Longrightarrow>
      csig.okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of (thm_rep_of state))
        (stpairs', Bs', Bi', C') True e (pthm_of (lift_rule goal' (th_maxidx (thm_rep_of state)) (thm_rep_of rule)))
        (nprems_of (thm_rep_of rule))) xq \<Longrightarrow>
      csig.bevals (unify_ops cfg vl) xq rs \<Longrightarrow> x \<in> set rs \<Longrightarrow> (x, (e, rule)) \<in> set xs'"
    by blast
  from d d' have "(stpairs', Bs', Bi', C') = (stpairs, Bs, Bi, C)" by (auto dest: csig.okT_det)
  moreover from g g' have "goal' = goal" by (auto dest: csig.okT_det)
  moreover from ev ev' have "xs' = xs" by (auto simp: c dest: csig.brevals_det)
  ultimately have "(x, (e, rule)) \<in> set xs" using cmp[OF r _ _ bv x] t ok cfg by auto
  then show ?thesis by (force simp: ys' the)
qed

end
