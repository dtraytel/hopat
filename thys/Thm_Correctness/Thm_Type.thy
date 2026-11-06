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

end
