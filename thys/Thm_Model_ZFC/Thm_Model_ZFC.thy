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

end
