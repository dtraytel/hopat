section \<open>A Witness for the Axioms of the Models\<close>

theory Thm_Model_ZFC
  imports "ZFC_in_HOL.ZFC_Cardinals" "Thm_Correctness.Thm_Model"
begin

text \<open>
  The sets of \<open>ZFC_in_HOL\<close> form a universe (locale \<^locale>\<open>universe\<close>): the function space is
  \<^const>\<open>VPi\<close>, abstraction \<^const>\<open>VLambda\<close> and application \<^const>\<open>app\<close>, and the truth values
  are the ordinals \<open>0\<close> and \<open>1\<close>.
\<close>

definition vbool :: V where
  "vbool = set {0, 1}"

interpretation zfc: universe "\<lambda>x A. x \<in> elts A" "\<lambda>A B. VPi A (\<lambda>_. B)" app VLambda vbool 1 0
proof unfold_locales
  fix f A B a assume "f \<in> elts (VPi A (\<lambda>_. B))" "a \<in> elts A"
  then show "app f a \<in> elts B" by (rule VPi_D)
next
  fix A g B assume "\<And>a. a \<in> elts A \<Longrightarrow> g a \<in> elts B"
  then show "VLambda A g \<in> elts (VPi A (\<lambda>_. B))" by (rule VPi_I)
next
  fix a A g assume "a \<in> elts A"
  then show "app (VLambda A g) a = g a" by (rule beta)
next
  fix f A B f' assume "f \<in> elts (VPi A (\<lambda>_. B))" "f' \<in> elts (VPi A (\<lambda>_. B))"
    "\<And>a. a \<in> elts A \<Longrightarrow> app f a = app f' a"
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

interpretation zfc_model: pure_model alg ar ctab "\<lambda>x A. x \<in> elts A" "\<lambda>A B. VPi A (\<lambda>_. B)" app VLambda
  vbool 1 0 "\<lambda>_ _. set {0}" "\<lambda>_ _. True" "\<lambda>_ A. SOME a. a \<in> elts A"
  if "pure_sig alg ar"
proof -
  interpret pure_sig alg ar ctab by (rule that)
  show "pure_model alg ar ctab (\<lambda>x A. x \<in> elts A) (\<lambda>A B. VPi A (\<lambda>_. B)) app VLambda vbool 1 0
    (\<lambda>_ _. set {0}) (\<lambda>_ _. True) (\<lambda>_ A. SOME a. a \<in> elts A)"
  proof unfold_locales
    show "zfc.une (set {0})" for As :: "V list" by (auto simp: zfc.une_def)
    show "(SOME a. a \<in> elts A) \<in> elts A" if "zfc.une A" for A
      using that by (auto simp: zfc.une_def intro: someI)
  qed simp_all
qed

end
