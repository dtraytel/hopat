section \<open>Translation of the parts of composed tight proofs\<close>

theory ZTerm_Bicompose
  imports ZTerm_Compose
begin

text \<open>
  The proofs of flattened premises and by assumption of \<open>ZTerm.bicompose_proof\<close> decompose tight
  terms with \<open>Pure.imp\<close> as \<^const>\<open>ZConst0\<close> and \<open>Pure.all\<close> as \<^const>\<open>ZConst1\<close>, the forms that
  the conversion of terms produces (\<open>Consts.typargs\<close>). On such canonical tight terms they
  translate to the annotated classic proofs.
\<close>

lemma bindZ_eq_returnZ: "bindZ m f = returnZ y \<longleftrightarrow> (\<exists>x. m = returnZ x \<and> f x = returnZ y)"
  by (auto simp: bindZ_def returnZ_def split: option.splits zres.splits)

lemma liftMZ_eq_returnZ: "liftMZ m = returnZ y \<longleftrightarrow> m = return y"
  by (auto simp: liftMZ_def returnZ_def return_def split: option.splits res.splits)

lemma returnZ_inj[simp]: "returnZ x = returnZ y \<longleftrightarrow> x = y"
  by (simp add: returnZ_def)

lemma class_suffix_ne_imp: "c + STR ''_class'' \<noteq> STR ''Pure.imp''"
proof
  assume "c + STR ''_class'' = STR ''Pure.imp''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.imp''))" by simp
  then show False by (simp add: plus_literal.rep_eq String.Literal.rep_eq zero_literal.rep_eq)
qed

context csig
begin

fun zcanon :: "zterm \<Rightarrow> bool" where
  "zcanon (ZConst0 c) \<longleftrightarrow> c \<noteq> STR ''Pure.all''"
| "zcanon (ZConst1 c T) \<longleftrightarrow> c \<noteq> STR ''Pure.imp''"
| "zcanon (ZConst c Ts) \<longleftrightarrow> c \<noteq> STR ''Pure.imp'' \<and> c \<noteq> STR ''Pure.all''"
| "zcanon (ZAbs a T t) \<longleftrightarrow> zcanon t"
| "zcanon (ZApp t u) \<longleftrightarrow> zcanon t \<and> zcanon u"
| "zcanon _ \<longleftrightarrow> True"

lemma ztargs_canon:
  "ztargs c T = return Ts \<Longrightarrow> (c = STR ''Pure.imp'' \<longrightarrow> Ts = []) \<and> (c = STR ''Pure.all'' \<longrightarrow> length Ts = 1)"
  by (auto simp: ztargs_def return_def raise_def split: if_splits ptyp.splits list.splits option.splits)

lemma zterm_of_zcanon: "zterm_of ta t = returnZ z \<Longrightarrow> ta = ztargs \<Longrightarrow> zcanon z"
proof (induction ta t arbitrary: z rule: zterm_of.induct)
  case (4 ta c T)
  then obtain Ts where Ts: "ztargs c T = return Ts"
    "z = (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))"
    by (auto simp: bindZ_eq_returnZ liftMZ_eq_returnZ)
  from ztargs_canon[OF Ts(1)] Ts(2) show ?case
    by (cases Ts rule: remdups_adj.cases) auto
next
  case (5 ta a T b)
  then show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (6 ta t u)
  then show ?case by (auto simp: bindZ_eq_returnZ split: option.splits if_splits; metis returnZ_def)
qed auto

end

context prf_wf_csig
begin

subsection \<open>Proofs of flattened premises\<close>

definition is_imp :: "pterm \<Rightarrow> bool" where
  "is_imp C \<longleftrightarrow> (\<exists>U A B. C = Const STR ''Pure.imp'' U $ A $ B)"

definition is_all :: "pterm \<Rightarrow> bool" where
  "is_all C \<longleftrightarrow> (\<exists>U a T t. C = Const STR ''Pure.all'' U $ Abs a T t)"

lemma fpp_a_leaf:
  "\<not> is_imp C \<Longrightarrow> \<not> is_all C \<Longrightarrow> flatten_params_proof_a i j n (C, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0)))
      (map PBound (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(i, j, n, (C, k))" rule: flatten_params_proof_a.cases) (auto simp: is_imp_def is_all_def)

lemma ZAppts_tr: "zprf_tr (ZAppts p ts) = proof_combt (zprf_tr p) (map zdec ts)"
  by (induction ts arbitrary: p) (simp_all add: ZAppts_def proof_combt_def)

lemma zdec_is_imp:
  assumes "zcanon z" "is_imp (zdec z)"
  shows "\<exists>A B. z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') A) B"
proof -
  from assms(2) obtain U A B where e: "zdec z = Const STR ''Pure.imp'' U $ A $ B" by (auto simp: is_imp_def)
  then obtain z1 z2 where z: "z = ZApp z1 z2" and e1: "zdec z1 = Const STR ''Pure.imp'' U $ A"
    by (cases z) (auto simp: of_class_def split: if_splits)
  then obtain z3 z4 where z1: "z1 = ZApp z3 z4" and e3: "zdec z3 = Const STR ''Pure.imp'' U"
    by (cases z1) (auto simp: of_class_def class_suffix_ne_imp split: if_splits)
  from e3 assms(1) z z1 have "z3 = ZConst0 STR ''Pure.imp''" by (cases z3) (auto simp: of_class_def split: if_splits)
  with z z1 show ?thesis by blast
qed

lemma zdec_is_all:
  assumes "zcanon z" "is_all (zdec z)"
  shows "\<exists>U a T t. z = ZApp (ZConst1 STR ''Pure.all'' U) (ZAbs a T t)"
proof -
  from assms(2) obtain U a T t where e: "zdec z = Const STR ''Pure.all'' U $ Abs a T t"
    by (auto simp: is_all_def)
  then obtain z1 z2 where z: "z = ZApp z1 z2" "zdec z1 = Const STR ''Pure.all'' U" "zdec z2 = Abs a T t"
    by (cases z) (auto simp: of_class_def split: if_splits)
  from z(2) assms(1) z(1) have "\<exists>U'. z1 = ZConst1 STR ''Pure.all'' U'" by (cases z1) (auto simp: of_class_def split: if_splits)
  moreover from z(3) have "\<exists>a T t. z2 = ZAbs a T t" by (cases z2) (auto simp: of_class_def split: if_splits)
  ultimately show ?thesis using z(1) by blast
qed

definition zis_imp :: "zterm \<Rightarrow> bool" where
  "zis_imp z \<longleftrightarrow> (\<exists>c A B. z = ZApp (ZApp (ZConst0 c) A) B)"

definition zis_all :: "zterm \<Rightarrow> bool" where
  "zis_all z \<longleftrightarrow> (\<exists>c U a T t. z = ZApp (ZConst1 c U) (ZAbs a T t))"

lemma zfpp_leaf:
  "\<not> zis_imp z \<Longrightarrow> \<not> zis_all z \<Longrightarrow> zflatten_params_proof i j n (z, k) =
    ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0)))
      (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(i, j, n, (z, k))" rule: zflatten_params_proof.cases) (auto simp: zis_imp_def zis_all_def)

lemma not_is_imp_zdec: "zcanon z \<Longrightarrow> \<not> zis_imp z \<Longrightarrow> \<not> is_imp (zdec z)"
  using zdec_is_imp unfolding zis_imp_def by blast

lemma not_is_all_zdec: "zcanon z \<Longrightarrow> \<not> zis_all z \<Longrightarrow> \<not> is_all (zdec z)"
  using zdec_is_all unfolding zis_all_def by blast

lemma zfpp_tr:
  "zcanon z \<Longrightarrow> zprf_tr (zflatten_params_proof i j n (z, k)) = flatten_params_proof_a i j n (zdec z, k)"
proof (induction z arbitrary: i j rule: measure_induct_rule[of size])
  case (less z)
  consider (imp) c A B where "z = ZApp (ZApp (ZConst0 c) A) B"
    | (all) c U a T t where "z = ZApp (ZConst1 c U) (ZAbs a T t)"
    | (other) "\<not> zis_imp z" "\<not> zis_all z"
    unfolding zis_imp_def zis_all_def by blast
  then show ?case
  proof cases
    case imp
    with less show ?thesis by (simp add: ZAppps_tr ZAppts_tr comp_def)
  next
    case all
    with less show ?thesis by (simp add: ZAppps_tr ZAppts_tr comp_def)
  qed (simp add: zfpp_leaf fpp_a_leaf not_is_imp_zdec not_is_all_zdec less.prems ZAppps_tr ZAppts_tr comp_def)
qed

subsection \<open>Proofs by assumption\<close>

lemma imp_prf_a_leaf: "\<not> is_imp C \<Longrightarrow> imp_prf_a C i m = PBound i"
  by (cases "(C, i, m)" rule: imp_prf_a.cases) (auto simp: is_imp_def)

lemma all_prf_a_leaf: "\<not> is_all C \<Longrightarrow> all_prf_a i m C = imp_prf_a C (- i) m"
  by (cases "(i, m, C)" rule: all_prf_a.cases) (auto simp: is_all_def)

lemma zimp_prf_leaf: "\<not> zis_imp z \<Longrightarrow> zimp_prf z i m = ZBoundp i"
  by (cases "(z, i, m)" rule: zimp_prf.cases) (auto simp: zis_imp_def)

lemma zall_prf_leaf: "\<not> zis_all z \<Longrightarrow> zall_prf i m z = zimp_prf z (- i) m"
  by (cases "(i, m, z)" rule: zall_prf.cases) (auto simp: zis_all_def)

lemma zimp_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zimp_prf z i m) = imp_prf_a (zdec z) i m"
proof (induction z arbitrary: i m rule: measure_induct_rule[of size])
  case (less z)
  show ?case
  proof (cases "zis_imp z")
    case True
    then obtain c A B where "z = ZApp (ZApp (ZConst0 c) A) B" by (auto simp: zis_imp_def)
    with less show ?thesis by simp
  qed (simp add: zimp_prf_leaf imp_prf_a_leaf not_is_imp_zdec less.prems)
qed

lemma zall_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zall_prf i m z) = all_prf_a i m (zdec z)"
proof (induction z rule: measure_induct_rule[of size])
  case (less z)
  show ?case
  proof (cases "zis_all z")
    case True
    then obtain c U a T t where "z = ZApp (ZConst1 c U) (ZAbs a T t)" by (auto simp: zis_all_def)
    with less show ?thesis by (simp add: zimp_prf_tr)
  qed (simp add: zall_prf_leaf all_prf_a_leaf not_is_all_zdec less.prems zimp_prf_tr)
qed
lemma zmk_asm_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zmk_asm_prf z i m) = mk_asm_prf_a (zdec z) i m"
  by (simp add: zmk_asm_prf_def mk_asm_prf_a_def zall_prf_tr)

end

end
