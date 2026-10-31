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

lemma class_suffix_ne_imp: "c + STR ''_class'' \<noteq> STR ''Pure.imp''"
proof
  assume "c + STR ''_class'' = STR ''Pure.imp''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.imp''))" by simp
  then show False by (simp add: plus_literal.rep_eq)
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
  then show ?case by (auto simp: bindZ_eq_returnZ returnZ_def split: option.splits if_splits)
qed (auto simp: returnZ_def)

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
  "zcanon z \<Longrightarrow> is_imp (zdec z) \<Longrightarrow> \<exists>A B. z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') A) B"
  by (cases z rule: zdec.cases; auto simp: is_imp_def of_class_def class_suffix_ne_imp;
    rename_tac f u; case_tac f rule: zdec.cases; auto simp: of_class_def class_suffix_ne_imp;
    rename_tac g v; case_tac g rule: zdec.cases; auto simp: of_class_def class_suffix_ne_imp)

lemma zdec_is_all:
  "zcanon z \<Longrightarrow> is_all (zdec z) \<Longrightarrow> \<exists>U a T t. z = ZApp (ZConst1 STR ''Pure.all'' U) (ZAbs a T t)"
  by (cases z rule: zdec.cases; auto simp: is_all_def of_class_def;
    rename_tac f u; case_tac f rule: zdec.cases; case_tac u rule: zdec.cases; auto simp: of_class_def)

lemma zfpp_tr:
  "zcanon (fst x) \<Longrightarrow> zprf_tr (zflatten_params_proof i j n x) = flatten_params_proof_a i j n (zdec (fst x), snd x)"
proof (induction i j n x rule: zflatten_params_proof.induct)
  case (1 i j n c A B k)
  then show ?case by (simp add: ZAppps_tr ZAppts_tr comp_def)
next
  case (2 i j n c U a T t k)
  then show ?case by (simp add: ZAppps_tr ZAppts_tr comp_def)
qed (use zdec_is_imp zdec_is_all in \<open>(simp add: ZAppps_tr ZAppts_tr comp_def, subst fpp_a_leaf, force+)\<close>)

subsection \<open>Proofs by assumption\<close>

lemma imp_prf_a_leaf: "\<not> is_imp C \<Longrightarrow> imp_prf_a C i m = PBound i"
  by (cases "(C, i, m)" rule: imp_prf_a.cases) (auto simp: is_imp_def)

lemma all_prf_a_leaf: "\<not> is_all C \<Longrightarrow> all_prf_a i m C = imp_prf_a C (- i) m"
  by (cases "(i, m, C)" rule: all_prf_a.cases) (auto simp: is_all_def)

lemma zimp_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zimp_prf z i m) = imp_prf_a (zdec z) i m"
proof (induction z i m rule: zimp_prf.induct)
  case (1 c A B i m)
  then show ?case by simp
qed (use zdec_is_imp in \<open>(simp, subst imp_prf_a_leaf, force+)\<close>)

lemma zall_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zall_prf i m z) = all_prf_a i m (zdec z)"
proof (induction i m z rule: zall_prf.induct)
  case (1 i m c U a T t)
  then show ?case by (simp add: zimp_prf_tr)
qed (use zdec_is_all in \<open>(simp add: zimp_prf_tr, subst all_prf_a_leaf, force+)\<close>)

lemma zmk_asm_prf_tr: "zcanon z \<Longrightarrow> zprf_tr (zmk_asm_prf z i m) = mk_asm_prf_a (zdec z) i m"
  by (simp add: zmk_asm_prf_def mk_asm_prf_a_def zall_prf_tr)

end

end
