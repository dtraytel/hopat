section \<open>A Witness for the Axioms of the Models\<close>

theory Thm_Model_ZFC
  imports "ZFC_in_HOL.ZFC_Cardinals" "Thm_Correctness.Thm_Consistency" "Thm_Correctness.Thm_Example"
    "Thm_Correctness.Thm_Classes"
begin

text \<open>
  The sets of \<open>ZFC_in_HOL\<close> form a universe (locale \<^locale>\<open>universe\<close>): the function space is
  \<^const>\<open>VPi\<close>, abstraction \<^const>\<open>VLambda\<close> and application \<^const>\<open>ZFC_Cardinals.app\<close>, and the truth values
  are the ordinals \<open>0\<close> and \<open>1\<close>.
\<close>

definition vbool :: V where
  "vbool = ZFC_in_HOL.set {0, 1}"

interpretation zfc: universe "\<lambda>x A. x \<in> elts A" "\<lambda>A B. VPi A (\<lambda>_. B)" ZFC_Cardinals.app VLambda vbool 1 0
proof unfold_locales
  fix f A B a assume "f \<in> elts (VPi A (\<lambda>_. B))" "a \<in> elts A"
  then show "ZFC_Cardinals.app f a \<in> elts B" by (rule VPi_D)
next
  fix A g B assume "\<And>a. a \<in> elts A \<Longrightarrow> g a \<in> elts B"
  then show "VLambda A g \<in> elts (VPi A (\<lambda>_. B))" by (rule VPi_I)
next
  fix a A g assume "a \<in> elts A"
  then show "ZFC_Cardinals.app (VLambda A g) a = g a" by (rule ZFC_Cardinals.beta)
next
  fix f A B f' assume "f \<in> elts (VPi A (\<lambda>_. B))" "f' \<in> elts (VPi A (\<lambda>_. B))"
    "\<And>a. a \<in> elts A \<Longrightarrow> ZFC_Cardinals.app f a = ZFC_Cardinals.app f' a"
  then show "f = f'" by (rule fun_ext)
next
  fix b show "b \<in> elts vbool \<longleftrightarrow> b = 1 \<or> b = 0" by (auto simp: vbool_def)
next
  show "(1::V) \<noteq> 0" by simp
qed

text \<open>
  Every signature has a model in this universe: type constructors are interpreted by a
  singleton, every set belongs to every class, and a constant denotes a chosen element of its
  type.
\<close>

sublocale pure_sig \<subseteq> zfc_model: pure_model alg ar ctab "\<lambda>x A. x \<in> elts A" "\<lambda>A B. VPi A (\<lambda>_. B)" ZFC_Cardinals.app
  VLambda vbool 1 0 "\<lambda>_ _. ZFC_in_HOL.set {0}" "\<lambda>_ _. True" "\<lambda>_ A. SOME a. a \<in> elts A"
proof unfold_locales
  fix A :: V assume "universe.une (\<lambda>x A. x \<in> elts A) A"
  then show "(SOME a. a \<in> elts A) \<in> elts A" by (auto simp: universe.une_def[OF zfc.universe_axioms] intro: someI)
qed (auto simp: universe.une_def[OF zfc.universe_axioms] vbool_def intro: VPi_D VPi_I fun_ext)


subsection \<open>Consistency of the equality fragment of \<open>Pure\<close>\<close>

text \<open>The model as a record (\<^typ>\<open>V model\<close>):\<close>

definition zfc_M :: "V model" where
  "zfc_M = \<lparr>m_mem = \<lambda>x A. x \<in> elts A, m_fun = \<lambda>A B. VPi A (\<lambda>_. B), m_app = ZFC_Cardinals.app,
    m_lam = VLambda, m_bool = vbool, m_true = 1, m_false = 0, m_tcon = \<lambda>_ _. ZFC_in_HOL.set {0},
    m_cls = \<lambda>_ _. True, m_cval = \<lambda>_ A. SOME a. a \<in> elts A\<rparr>"

lemma zfc_pure_model:
  assumes "pure_sig alg ar"
  shows "pure_model alg ar (m_mem zfc_M) (m_fun zfc_M) (m_app zfc_M) (m_lam zfc_M) (m_bool zfc_M)
    (m_true zfc_M) (m_false zfc_M) (m_tcon zfc_M) (m_cls zfc_M) (m_cval zfc_M)"
  unfolding zfc_M_def model.simps
  by (rule pure_model.intro[OF assms zfc.universe_axioms], unfold_locales)
    (auto simp: universe.une_def[OF zfc.universe_axioms] vbool_def intro: someI VPi_D VPi_I fun_ext)

text \<open>
  It is a model of every signature whose axioms are equality axioms, if the signature declares
  \<open>Pure.eq\<close> with its polymorphic type and \<open>prop\<close> without arguments:
\<close>

theorem zfc_is_model:
  assumes "pure_sig (sg_alg c) (sg_ar c)" "pure_sig.eq_ok (sg_consts c)" "sg_ar c STR ''prop'' = 0"
    "\<And>a A. sg_axioms c a = Some A \<Longrightarrow> \<exists>b\<in>eq_names. A = equality_axiom b"
  shows "is_model c zfc_M"
  by (rule is_model_eq_axioms[OF zfc_pure_model[OF assms(1)] assms(2-4)])

text \<open>
  So in such a signature, no theorem in the universe of sets without hypotheses and flex-flex
  pairs proves \<open>\<And>P. P\<close>, whatever its sort hypotheses (every sort is inhabited in this model):
\<close>

lemma zfc_sinh: "m_sinh zfc_M S"
proof -
  have "(1::V) \<in> elts vbool" using zfc.ubool_mem[of 1] by simp
  then show ?thesis unfolding m_sinh_def zfc_M_def by auto
qed

corollary zfc_consistent:
  fixes th :: "V pure_thm"
  assumes "pure_sig (sg_alg (sign_of th)) (sg_ar (sign_of th))" "pure_sig.eq_ok (sg_consts (sign_of th))"
    "sg_ar (sign_of th) STR ''prop'' = 0"
    "\<And>a A. sg_axioms (sign_of th) a = Some A \<Longrightarrow> \<exists>b\<in>eq_names. A = equality_axiom b"
    "hyps_of th = []" "th_tpairs (rep_of th) = []"
  shows "th_prop (rep_of th) \<noteq> all_const propT $ Abs x propT (Bound 0)"
proof (rule pure_thm_consistent[OF assms(1) zfc_is_model[OF assms(1-4)] assms(5,6)])
  show "\<forall>S\<in>shyps_of th. m_sinh zfc_M S" using zfc_sinh by blast
qed


subsection \<open>The example signature\<close>

text \<open>
  The signature \<^const>\<open>pure0\<close> of theory \<open>Thm_Example\<close> has this model. So all assumptions of
  the statements about theorems hold together for it: no theorem that the rules derive in it
  without hypotheses and flex-flex pairs is \<open>\<And>P. P\<close>, and its theorem \<open>A \<Longrightarrow> A\<close> is valid in the
  universe of sets.
\<close>

lemma zfc_model_pure0: "is_model pure0 zfc_M"
  by (rule zfc_is_model) (use sign_eq0 in \<open>simp_all add: pure_sig0 sign_eq_def\<close>)

theorem pure0_consistent:
  assumes "derivable d" "th_sign d = pure0" "th_hyps d = []" "th_tpairs d = []"
  shows "th_prop d \<noteq> all_const propT $ Abs x propT (Bound 0)"
  by (rule derivable_consistent[OF assms(1), where M = zfc_M]) (use assms in \<open>simp_all add: zfc_model_pure0 zfc_sinh\<close>)

corollary "valid_in pure0 zfc_M {} [] [] (mk_implies A0 A0)"
  using derivable_valid[OF derivable_thAA, of zfc_M] by (simp add: thAA_def mk_rep_def zfc_model_pure0)

text \<open>
  The same for the theorems of every signature that is reached from \<^const>\<open>pure0\<close> by
  declarations of constants and by class relations and arities that derivable theorems state
  (\<^const>\<open>extends_by\<close>, theory \<open>Thm_Classes\<close>):
\<close>

theorem pure0_extends_consistent:
  assumes "extends_by pure0 (th_sign d)" "derivable d" "th_hyps d = []" "th_tpairs d = []"
  shows "th_prop d \<noteq> all_const propT $ Abs x propT (Bound 0)"
  by (rule extends_by_consistent[OF assms(1) zfc_model_pure0 assms(2-4)]) (simp add: zfc_sinh)


subsection \<open>A class relation\<close>

text \<open>
  An instance of theorem \<open>add_classrel_model\<close> of theory \<open>Thm_Classes\<close>, to show that its
  assumptions hold together for a class relation that the algebra does not have: a signature
  with two unrelated classes \<open>A\<close> and \<open>B\<close>, their constants, and the axiom \<open>OFCLASS(?'a::A, B)\<close>
  (as \<open>Axclass.axiomatize_classrel\<close> adds it). The universe of sets with all classes
  interpreted as the class of all sets is a model of it. The theorem of the axiom (the data
  that the rule \<open>axiom\<close> gives it, without proofs) satisfies the invariant of theorems, and the
  signature with the algebra in which \<open>A\<close> is a subclass of \<open>B\<close> has the same model.
\<close>

definition cA :: pclass where "cA = STR ''A''"
definition cB :: pclass where "cB = STR ''B''"

definition alg1 :: algebra where "alg1 = Algebra (\<lambda>_ _. False) (\<lambda>_. []) {cA, cB}"
definition alg2 :: algebra where "alg2 = Algebra (\<lambda>x y. x = cA \<and> y = cB) (\<lambda>_. []) {cA, cB}"

definition ar1 :: "name \<Rightarrow> nat" where "ar1 a = (if a = STR ''itself'' then 1 else 0)"

definition itself_a :: ptyp where "itself_a = Type STR ''itself'' [TVar (STR ''a'', 0) []]"

definition ctab1 :: "name \<Rightarrow> ptyp option" where
  "ctab1 c = (if c = STR ''Pure.type'' then Some itself_a
    else if c = STR ''A_class'' \<or> c = STR ''B_class'' then Some (itself_a \<rightarrow>\<^sub>T propT) else None)"

definition axAB :: pterm where "axAB = mk_of_class (TVar (STR ''a'', 0) [cA]) cB"

definition sign1 :: sign where
  "sign1 = \<lparr>sg_alg = alg1, sg_ar = ar1, sg_consts = ctab1, sg_close = \<lambda>A. A, sg_tyargs = \<lambda>_. [],
    sg_ax = \<lambda>_. False, sg_axioms = (\<lambda>a. if a = STR ''A_subclass_B'' then Some axAB else None)\<rparr>"

definition thAB :: thm_data where
  "thAB = \<lparr>th_maxidx = 0, th_tpairs = [], th_prop = axAB, th_shyps = tm_sorts axAB, th_hyps = [],
    th_sign = sign1, th_proof = None, th_zproof = None, th_constraints = {}\<rparr>"

lemma class_names: "cA + STR ''_class'' = STR ''A_class''" "cB + STR ''_class'' = STR ''B_class''"
  unfolding cA_def cB_def by eval+

lemma pure_sig1: "pure_sig alg1 ar1" and pure_sig2: "pure_sig alg2 ar1"
  unfolding pure_sig_def by (unfold_locales; simp add: alg1_def alg2_def class_le_def cA_def cB_def)+

lemma class_const1: "pure_sig.class_const alg1 ctab1 (cB + STR ''_class'') cB"
  unfolding pure_sig.class_const_def[OF pure_sig1]
  by (simp add: class_names ctab1_def alg1_def itself_a_def)

lemma wtp_axAB: "pure_sig.wtp alg1 ar1 ctab1 axAB"
proof -
  interpret pure_sig alg1 ar1 ctab1 by (rule pure_sig1)
  let ?T = "TVar (STR ''a'', 0) [cA]"
  have c: "cert_typ alg1 ar1 (Type STR ''itself'' [?T])" "cert_typ alg1 ar1 (Type STR ''itself'' [?T] \<rightarrow>\<^sub>T propT)"
    by (simp_all add: cert_typ_def tarity_def ar1_def propT_def sort_ok_def alg1_def)
  have k: "const_typ_ok ctab1 STR ''Pure.type'' (Type STR ''itself'' [?T])"
    "const_typ_ok ctab1 STR ''B_class'' (Type STR ''itself'' [?T] \<rightarrow>\<^sub>T propT)"
    unfolding const_typ_ok_def ctab1_def itself_a_def propT_def
    by (auto intro!: exI[of _ "\<lambda>_ _. ?T"])
  show ?thesis
    by (rule wtpI[of _ "\<lambda>_. propT"])
      (use c k in \<open>auto simp: axAB_def mk_of_class_def class_suffix_def class_names closed_def propT_def\<close>)
qed

lemma is_model1: "is_model sign1 zfc_M"
  unfolding is_model_def
proof (intro conjI allI impI)
  have pm: "pure_model alg1 ar1 (m_mem zfc_M) (m_fun zfc_M) (m_app zfc_M) (m_lam zfc_M) (m_bool zfc_M)
      (m_true zfc_M) (m_false zfc_M) (m_tcon zfc_M) (m_cls zfc_M) (m_cval zfc_M)"
    by (rule zfc_pure_model[OF pure_sig1])
  then show "pure_model (sg_alg sign1) (sg_ar sign1) (m_mem zfc_M) (m_fun zfc_M) (m_app zfc_M) (m_lam zfc_M)
      (m_bool zfc_M) (m_true zfc_M) (m_false zfc_M) (m_tcon zfc_M) (m_cls zfc_M) (m_cval zfc_M)"
    by (simp add: sign1_def)
  fix a A assume "sg_axioms sign1 a = Some A"
  then have A: "A = axAB" by (simp add: sign1_def split: if_splits)
  interpret M: pure_model alg1 ar1 ctab1 "m_mem zfc_M" "m_fun zfc_M" "m_app zfc_M" "m_lam zfc_M" "m_bool zfc_M"
    "m_true zfc_M" "m_false zfc_M" "m_tcon zfc_M" "m_cls zfc_M" "m_cval zfc_M"
    by (rule pm)
  have wf: "M.wf_terms [] [] axAB" using wtp_axAB by (simp add: M.wf_terms_def M.wtp_def M.gterm_def)
  have "M.svalid (tm_sorts axAB) [] [] axAB"
  proof (rule M.svalidI)
    fix \<eta> \<xi> assume g: "M.good \<eta> \<xi>"
    show "M.holds_at \<eta> \<xi> axAB"
      unfolding axAB_def M.holds_mk_of_class[OF g class_const1 M.wtpD(2)[OF wtp_axAB[unfolded axAB_def]]]
      by (simp add: zfc_M_def)
  qed
  then show "valid_in sign1 zfc_M (tm_sorts A) [] [] A"
    using M.valid_svalid[OF wf] by (simp add: valid_in_def sign1_def A)
qed

lemma dok_thAB: "dok TYPE('u) thAB"
proof -
  have "pure_sig.thm_wf alg1 ar1 ctab1 0 [] [] axAB"
  proof -
    interpret pure_sig alg1 ar1 ctab1 by (rule pure_sig1)
    show ?thesis
      using wtp_axAB by (auto simp: thm_wf_def wt_thm_def ibelow_def vars_thm_def tvars_thm_def
        axAB_def mk_of_class_def ttvars_def propT_def)
  qed
  moreover have "valid_in sign1 M (tm_sorts axAB) [] [] axAB" if "is_model sign1 M" for M :: "'u model"
    by (rule is_model_axiom[OF that]) (simp add: sign1_def)
  moreover have "proofs_ok thAB" by (simp add: proofs_ok_def thAB_def returnW_def return_def)
  ultimately show ?thesis by (simp add: dok_def thm_ok_def thAB_def sign1_def)
qed

lemma classrel_ext12: "classrel_ext alg1 alg2 cA cB"
  by (auto simp: classrel_ext_def alg_le_def alg1_def alg2_def)

theorem is_model2: "is_model (sign1\<lparr>sg_alg := alg2\<rparr>) zfc_M" and "sign_le sign1 (sign1\<lparr>sg_alg := alg2\<rparr>)"
proof -
  have ax: "pure_sig.wtp (sg_alg sign1) (sg_ar sign1) (sg_consts sign1) A" if "sg_axioms sign1 a = Some A" for a A
    using that wtp_axAB by (simp add: sign1_def split: if_splits)
  note r = add_classrel_model[OF is_model1 dok_thAB, where ?c1.0 = cA and ?c2.0 = cB and alg' = alg2
      and a = "(STR ''a'', 0)"]
  show "is_model (sign1\<lparr>sg_alg := alg2\<rparr>) zfc_M"
    by (rule r(1)) (use ax class_const1 classrel_ext12 pure_sig2 in \<open>simp_all add: thAB_def sign1_def axAB_def\<close>)
  show "sign_le sign1 (sign1\<lparr>sg_alg := alg2\<rparr>)"
    by (rule r(2)) (use ax class_const1 classrel_ext12 pure_sig2 in \<open>simp_all add: thAB_def sign1_def axAB_def\<close>)
qed

text \<open>The extension is a proper one: a type variable of sort \<open>A\<close> has sort \<open>B\<close> in it only.\<close>

lemma "\<not> has_sort alg1 (TVar v [cA]) [cB]" "has_sort alg2 (TVar v [cA]) [cB]"
  by (simp_all add: sort_le_def class_le_def alg1_def alg2_def cA_def cB_def)

end
