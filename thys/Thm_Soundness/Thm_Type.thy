section \<open>The abstract type of theorems\<close>

theory Thm_Type
  imports Rules_Base Proof_Sig
begin

text \<open>
  A theorem of Isabelle (\<open>Thm.thm\<close>) carries its certificate (the theory), its maximal index, its
  sort hypotheses, its hypotheses, its flex-flex pairs, its proposition and its proofs, classic and
  tight. The
  certificate is modelled by the signature: the sort algebra, the arities of the type
  constructors, the types of the constants, and, for the proofs, the propositions of the axioms
  and theorems that proofs may use (with their closure and the order of their type variables,
  \<open>Proofterm.thm_of_proof\<close>). Theorems are the records that satisfy the invariant
  \<open>thm_wf\<close> in their signature and are valid in every model of it over a universe
  \<open>'u\<close> that inhabits their sort hypotheses. The proofs are data here; that they are valid
  proofs of the theorem is shown in session \<open>Thm_Proofs\<close>. Biresolution maps theorems to theorems;
  its results are those of the compositions of the rules with the proof state, and their
  enumeration terminates.
\<close>


subsection \<open>Signatures and models\<close>

record sign =
  sg_alg :: algebra
  sg_ar :: "name \<Rightarrow> nat"
  sg_consts :: "name \<Rightarrow> ptyp option"
  sg_close :: "pterm \<Rightarrow> pterm"
  sg_tyargs :: "pterm \<Rightarrow> (indexname \<times> psort) list"
  sg_ax :: "pterm \<Rightarrow> bool"
  sg_axioms :: "name \<Rightarrow> pterm option"

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

text \<open>The sorts of a term (\<open>Sorts.insert_term\<close>):\<close>

fun tm_sorts :: "pterm \<Rightarrow> psort set" where
  "tm_sorts (Const c T) = tsorts T"
| "tm_sorts (Free x T) = tsorts T"
| "tm_sorts (Var x T) = tsorts T"
| "tm_sorts (Bound i) = {}"
| "tm_sorts (Abs a T t) = tsorts T \<union> tm_sorts t"
| "tm_sorts (s $ t) = tm_sorts s \<union> tm_sorts t"

definition valid_in :: "sign \<Rightarrow> 'u model \<Rightarrow> psort set \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid_in c M = pure_model_gen.valid (sg_alg c) (sg_ar c) (sg_consts c) (m_mem M) (m_fun M) (m_app M)
    (m_lam M) (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"

text \<open>
  A model of a signature satisfies its axioms (\<open>Theory.axiom_table\<close>): each axiom holds in every
  instance in which the sorts of its type variables are inhabited (the sort hypotheses of
  \<open>Thm.axiom\<close>).
\<close>

definition is_model :: "sign \<Rightarrow> 'u model \<Rightarrow> bool" where
  "is_model c M \<longleftrightarrow> pure_model (sg_alg c) (sg_ar c) (m_mem M) (m_fun M) (m_app M) (m_lam M)
    (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M) \<and>
    (\<forall>a A. sg_axioms c a = Some A \<longrightarrow> valid_in c M (tm_sorts A) [] [] A)"

lemma is_modelD: "is_model c M \<Longrightarrow> pure_model (sg_alg c) (sg_ar c) (m_mem M) (m_fun M) (m_app M) (m_lam M)
    (m_bool M) (m_true M) (m_false M) (m_tcon M) (m_cls M) (m_cval M)"
  by (simp add: is_model_def)

lemma is_model_axiom: "is_model c M \<Longrightarrow> sg_axioms c a = Some A \<Longrightarrow> valid_in c M (tm_sorts A) [] [] A"
  by (simp add: is_model_def)


subsection \<open>Theorems\<close>

record thm_data = thm_rep +
  th_shyps :: "psort set"
  th_hyps :: "pterm list"
  th_sign :: sign
  th_proof :: "prf P"
  th_zproof :: "zproof Z"
  th_constraints :: "(ptyp \<times> psort) set"

text \<open>
  The invariant of theorems: well-typed, with closed hypotheses without schematic (type)
  variables and with non-negative indices bounded by the maximal index. Unlike
  \<^const>\<open>pure_sig_gen.thm_inv\<close>, it does not require the schematic variables of a theorem to
  have the same type (and the schematic type variables the same sort) wherever their names
  occur; the rules that combine two theorems do not keep this, only biresolution assumes it.
\<close>

context pure_sig
begin

definition thm_wf :: "integer \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "thm_wf m hs tps P \<longleftrightarrow> wt_thm m hs tps P \<and> -1 \<le> m \<and>
    (\<forall>v\<in>vars_thm tps P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>tvars_thm tps P. 0 \<le> snd (fst v))"

lemma thm_inv_wf: "thm_inv m hs tps P \<longleftrightarrow> thm_wf m hs tps P \<and> scons (tvars_thm tps P) \<and> vtcons (vars_thm tps P)"
  by (auto simp: thm_inv_def thm_wf_def)

lemma thm_inv0_wf: "thm_inv0 m hs tps P \<longleftrightarrow> thm_wf m hs tps P \<and> scons (tvars_thm tps P)"
  by (auto simp: thm_inv0_def thm_wf_def)

end

definition is_prf_sig :: "sign \<Rightarrow> bool" where
  "is_prf_sig c \<longleftrightarrow> prf_sig (sg_alg c) (sg_ar c) (sg_close c) (sg_tyargs c)"

definition thm_sem :: "'u itself \<Rightarrow> thm_data \<Rightarrow> bool" where
  "thm_sem U th \<longleftrightarrow> (pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<longrightarrow>
    pure_sig.thm_wf (sg_alg (th_sign th)) (sg_ar (th_sign th)) (sg_consts (th_sign th))
      (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th) \<and>
    (\<forall>M :: 'u model. is_model (th_sign th) M \<longrightarrow>
      valid_in (th_sign th) M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)))"

lemma thm_semI:
  assumes "pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow>
      pure_sig.thm_wf (sg_alg (th_sign th)) (sg_ar (th_sign th)) (sg_consts (th_sign th))
        (th_maxidx th) (th_hyps th) (th_tpairs th) (th_prop th)"
    and "\<And>M :: 'u model. pure_sig (sg_alg (th_sign th)) (sg_ar (th_sign th)) \<Longrightarrow> is_model (th_sign th) M \<Longrightarrow>
      valid_in (th_sign th) M (th_shyps th) (th_hyps th) (th_tpairs th) (th_prop th)"
  shows "thm_sem TYPE('u) th"
  using assms by (auto simp: thm_sem_def)

text \<open>
  The theorem \<open>A \<Longrightarrow> A\<close> (\<open>Thm.trivial\<close>) shows that there are
  theorems.
\<close>

definition sign0 :: sign where
  "sign0 = \<lparr>sg_alg = undefined, sg_ar = \<lambda>_. 0, sg_consts = \<lambda>_. None, sg_close = \<lambda>A. A, sg_tyargs = \<lambda>_. [],
    sg_ax = \<lambda>_. False, sg_axioms = \<lambda>_. None\<rparr>"

definition thm0 :: thm_data where
  "thm0 = \<lparr>th_maxidx = 0, th_tpairs = [],
    th_prop = implies $ Var (STR ''A'', 0) propT $ Var (STR ''A'', 0) propT, th_shyps = {}, th_hyps = [], th_sign = sign0,
    th_proof = None, th_zproof = None, th_constraints = {}\<rparr>"

lemma thm_sem_thm0: "thm_sem TYPE('u) thm0"
proof -
  let ?alg = "sg_alg sign0" and ?ar = "sg_ar sign0" and ?ct = "sg_consts sign0"
  let ?A = "Var (STR ''A'', 0) propT"
  let ?P = "implies $ ?A $ ?A"
  have "pure_sig.thm_wf ?alg ?ar ?ct 0 [] [] ?P \<and> (\<forall>M :: 'u model. is_model sign0 M \<longrightarrow> valid_in sign0 M {} [] [] ?P)"
    if ps: "pure_sig ?alg ?ar"
  proof -
    interpret pure_sig ?alg ?ar ?ct by (rule ps)
    have c: "cert_typ ?alg ?ar propT" "cert_typ ?alg ?ar imp_type"
      by (simp_all add: cert_typ_def propT_def imp_type_def tarity_def sign0_def)
    have wP: "wtp ?P" by (rule wtpI[of _ "\<lambda>_. propT"]) (use c in \<open>auto simp: closed_def implies_def imp_type_def const_typ_ok_def propT_def\<close>)
    have "thm_wf 0 [] [] ?P"
      using wP by (auto simp: thm_wf_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def
        implies_def imp_type_def propT_def)
    moreover have "valid_in sign0 M {} [] [] ?P" if M: "is_model sign0 M" for M :: "'u model"
    proof -
      interpret pure_model ?alg ?ar ?ct "m_mem M" "m_fun M" "m_app M" "m_lam M" "m_bool M" "m_true M"
        "m_false M" "m_tcon M" "m_cls M" "m_cval M"
        by (rule is_modelD[OF M])
      have "valid {} [] [] ?P"
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
  then show ?thesis by (simp add: thm_sem_def thm0_def)
qed

text \<open>
  The sort constraints of a theorem (\<open>Thm.constraints\<close>, the implicit proof obligations that
  \<open>Thm.solve_constraints\<close> discharges by the derivations of \<open>Sorts.of_sort_derivation\<close>): pairs of a
  type, whose atomic types are replaced by \<open>'a\<close> with their sorts, and a sort. Isabelle keeps them as
  an ordered list, tagged with the theory; only their set matters. They hold in the algebra of
  the signature, so solving them never fails:
\<close>

definition cons_ok :: "sign \<Rightarrow> (ptyp \<times> psort) set \<Rightarrow> bool" where
  "cons_ok c C \<longleftrightarrow> (pure_sig (sg_alg c) (sg_ar c) \<longrightarrow> (\<forall>(T, S)\<in>C. has_sort (sg_alg c) T S))"

lemma cons_ok_empty [simp]: "cons_ok c {}"
  and cons_ok_Un [simp]: "cons_ok c (A \<union> B) \<longleftrightarrow> cons_ok c A \<and> cons_ok c B"
  by (auto simp: cons_ok_def)

typedef (overloaded) 'u pure_thm = "{th. thm_sem TYPE('u) th \<and> cons_ok (th_sign th) (th_constraints th)}"
  morphisms rep_thm Abs_thm
  using thm_sem_thm0 by (auto simp: thm0_def)

abbreviation rep_of :: "'u pure_thm \<Rightarrow> thm_rep" where
  "rep_of th \<equiv> thm_rep.truncate (rep_thm th)"

abbreviation sign_of :: "'u pure_thm \<Rightarrow> sign" where
  "sign_of th \<equiv> th_sign (rep_thm th)"

abbreviation shyps_of :: "'u pure_thm \<Rightarrow> psort set" where
  "shyps_of th \<equiv> th_shyps (rep_thm th)"

abbreviation hyps_of :: "'u pure_thm \<Rightarrow> pterm list" where
  "hyps_of th \<equiv> th_hyps (rep_thm th)"

abbreviation proof_of :: "'u pure_thm \<Rightarrow> prf P" where
  "proof_of th \<equiv> th_proof (rep_thm th)"

abbreviation zproof_of :: "'u pure_thm \<Rightarrow> zproof Z" where
  "zproof_of th \<equiv> th_zproof (rep_thm th)"

abbreviation cons_of :: "'u pure_thm \<Rightarrow> (ptyp \<times> psort) set" where
  "cons_of th \<equiv> th_constraints (rep_thm th)"

lemma rep_of_sel [simp]:
  "th_maxidx (rep_of th) = th_maxidx (rep_thm th)" "th_tpairs (rep_of th) = th_tpairs (rep_thm th)"
  "th_prop (rep_of th) = th_prop (rep_thm th)"
  by (simp_all add: thm_rep.truncate_def)

lemma thm_sem_rep: "thm_sem TYPE('u) (rep_thm (th :: 'u pure_thm))"
  using rep_thm by blast

lemma pure_thm_cons [simp]: "cons_ok (sign_of th) (cons_of th)"
  using rep_thm by blast

lemma cons_ok_sign [simp]: "sign_of th = c \<Longrightarrow> cons_ok c (cons_of th)"
  using pure_thm_cons[of th] by simp

lemma rep_Abs_thm: "thm_sem TYPE('u) d \<Longrightarrow> cons_ok (th_sign d) (th_constraints d) \<Longrightarrow> rep_thm (Abs_thm d :: 'u pure_thm) = d"
  by (simp add: Abs_thm_inverse)

text \<open>Rules that keep or join the constraints of their premises:\<close>

definition with_cons :: "(ptyp \<times> psort) set \<Rightarrow> thm_data \<Rightarrow> thm_data" where
  "with_cons C d = d\<lparr>th_constraints := C\<rparr>"

lemma with_cons_sel [simp]:
  "th_maxidx (with_cons C d) = th_maxidx d" "th_tpairs (with_cons C d) = th_tpairs d"
  "th_prop (with_cons C d) = th_prop d" "th_shyps (with_cons C d) = th_shyps d"
  "th_hyps (with_cons C d) = th_hyps d" "th_sign (with_cons C d) = th_sign d"
  "th_proof (with_cons C d) = th_proof d" "th_zproof (with_cons C d) = th_zproof d"
  "th_constraints (with_cons C d) = C" "thm_rep.truncate (with_cons C d) = thm_rep.truncate d"
  by (simp_all add: with_cons_def thm_rep.truncate_def)

lemma thm_sem_with_cons [simp]: "thm_sem U (with_cons C d) \<longleftrightarrow> thm_sem U d"
  by (simp add: thm_sem_def)

text \<open>
  The constraints of the type bindings of an environment (\<open>Thm.insert_constraints_env\<close>): the
  normalized type with its atomic types replaced by \<open>'a\<close> (\<open>smash_atyps\<close>), unless the sort is
  empty or the type is an atomic type of the sort.
\<close>

definition smash_atyp :: "ptyp \<Rightarrow> ptyp" where
  "smash_atyp T = (case T of TVar _ S \<Rightarrow> TFree (String.implode (CHR 0x27 # ''a'')) S
    | TFree _ S \<Rightarrow> TFree (String.implode (CHR 0x27 # ''a'')) S | _ \<Rightarrow> T)"

definition cons_ignored :: "ptyp \<Rightarrow> psort \<Rightarrow> bool" where
  "cons_ignored T S \<longleftrightarrow> S = [] \<or> (case T of TFree _ S' \<Rightarrow> S = S' | TVar _ S' \<Rightarrow> S = S' | _ \<Rightarrow> False)"

definition env_constraints :: "env \<Rightarrow> (ptyp \<times> psort) set" where
  "env_constraints env = {(map_atyps smash_atyp (tnorm (tyenv env) U), S) | v S U.
    vt_lookup (tyenv env) v = Some (S, U) \<and> \<not> cons_ignored (tnorm (tyenv env) U) S}"

lemma has_sort_smash: "has_sort alg (map_atyps smash_atyp T) S \<longleftrightarrow> has_sort alg T S"
proof (induction T arbitrary: S)
  case (Type a Ts)
  have "has_sort alg (map_atyps smash_atyp (Ts ! i)) S' \<longleftrightarrow> has_sort alg (Ts ! i) S'" if "i < length Ts" for i S'
    by (rule Type.IH[OF nth_mem[OF that]])
  then show ?case by (auto simp del: has_sort.simps simp add: has_sort.simps(1))
qed (simp_all add: smash_atyp_def)

text \<open>The constraints of a well-sorted environment hold:\<close>

lemma cons_ok_env: "tsorted (sg_alg c) (tyenv env) \<Longrightarrow> cons_ok c (env_constraints env)"
  by (auto simp: cons_ok_def env_constraints_def has_sort_smash tsorted_def bsorted_def simp del: has_sort.simps)

text \<open>Every theorem is valid in every model of its signature:\<close>

theorem pure_thm_valid:
  fixes th :: "'u pure_thm" and M :: "'u model"
  assumes M: "is_model (sign_of th) M"
  shows "valid_in (sign_of th) M (shyps_of th) (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
proof -
  have "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))"
    by (rule pure_model.axioms(1)[OF is_modelD[OF M]])
  with thm_sem_rep[of th] M show ?thesis unfolding thm_sem_def by blast
qed

lemma pure_thm_wf:
  "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th)) \<Longrightarrow>
    pure_sig.thm_wf (sg_alg (sign_of th)) (sg_ar (sign_of th)) (sg_consts (sign_of th))
      (th_maxidx (rep_thm th)) (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
  using thm_sem_rep[of th] by (simp add: thm_sem_def)

subsection \<open>Solving the sort constraints\<close>

text \<open>
  \<open>Thm.solve_constraints\<close>: the constraints are discharged (in Isabelle by derivations of
  \<open>Sorts.of_sort_derivation\<close>, which only add to the digest of the proof body), and the tight proof
  is \<open>\<beta>\<close>-normalized (\<open>ZTerm.beta_norm_prooft\<close>).
\<close>

definition zsolve :: "zproof Z \<Rightarrow> zproof Z" where
  "zsolve m = bindM m (\<lambda>p. liftOZ (beta_norm_prooft p))"

definition solve_data :: "thm_data \<Rightarrow> thm_data" where
  "solve_data d = d\<lparr>th_zproof := zsolve (th_zproof d), th_constraints := {}\<rparr>"

lemma solve_data_sel [simp]:
  "th_maxidx (solve_data d) = th_maxidx d" "th_tpairs (solve_data d) = th_tpairs d"
  "th_prop (solve_data d) = th_prop d" "th_shyps (solve_data d) = th_shyps d"
  "th_hyps (solve_data d) = th_hyps d" "th_sign (solve_data d) = th_sign d"
  "th_proof (solve_data d) = th_proof d" "th_zproof (solve_data d) = zsolve (th_zproof d)"
  "th_constraints (solve_data d) = {}" "thm_rep.truncate (solve_data d) = thm_rep.truncate d"
  by (simp_all add: solve_data_def thm_rep.truncate_def)

lemma thm_sem_solve_data [simp]: "thm_sem U (solve_data d) \<longleftrightarrow> thm_sem U d"
  by (simp add: thm_sem_def)

text \<open>
  The invariant of the theorems if the schematic type variables have the same sort wherever
  their names occur; nothing is asked of the names of the schematic variables:
\<close>

lemma pure_thm_inv0:
  "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th)) \<Longrightarrow>
    scons (pure_sig_gen.tvars_thm (th_tpairs (rep_thm th)) (th_prop (rep_thm th))) \<Longrightarrow>
    pure_sig_gen.thm_inv0 (sg_alg (sign_of th)) (sg_ar (sign_of th)) (sg_consts (sign_of th))
      (th_maxidx (rep_thm th)) (hyps_of th) (th_tpairs (rep_thm th)) (th_prop (rep_thm th))"
  using pure_thm_wf[of th] by (simp add: pure_sig.thm_inv0_wf)


subsection \<open>Biresolution of theorems\<close>

text \<open>
  The sorts of the type bindings of an environment (\<open>Envir.insert_sorts\<close>, which does not look at
  the term bindings):
\<close>

definition env_sorts :: "env \<Rightarrow> psort set" where
  "env_sorts env = tyenv_sorts (tyenv env)"

text \<open>The sorts of an environment whose types have certified sorts:\<close>

lemma sorts_ok_tsorts: "sorts_ok alg U \<Longrightarrow> S \<in> tsorts U \<Longrightarrow> sort_ok alg S"
  by (induction U) auto

lemma scert_env_sorts: "scert alg (tyenv env) \<Longrightarrow> S \<in> env_sorts env \<Longrightarrow> sort_ok alg S"
  unfolding env_sorts_def tyenv_sorts_def scert_def using sorts_ok_tsorts by blast

end
