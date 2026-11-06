section \<open>Composition of tight proofs\<close>

theory ZProof_Bicompose
  imports ZProof_Inst
begin

subsection \<open>Decoding\<close>

lemma class_suffix_imp: "c + STR ''_class'' \<noteq> STR ''Pure.imp''"
proof
  assume "c + STR ''_class'' = STR ''Pure.imp''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.imp''))" by simp
  then show False by (simp add: plus_literal.rep_eq String.Literal.rep_eq zero_literal.rep_eq)
qed

lemma class_suffix_all: "c + STR ''_class'' \<noteq> STR ''Pure.all''"
proof
  assume "c + STR ''_class'' = STR ''Pure.all''"
  then have "last (String.explode (c + STR ''_class'')) = last (String.explode (STR ''Pure.all''))" by simp
  then show False by (simp add: plus_literal.rep_eq String.Literal.rep_eq zero_literal.rep_eq)
qed

context pure_sig
begin

lemma zprf_tr_ZAbsps: "zprf_tr (ZAbsps ts p) = foldr (\<lambda>t p. AbsP (STR ''H'') t p) (map (Some \<circ> zdec) ts) (zprf_tr p)"
  by (induction ts) (simp_all add: ZAbsps_def)

lemma zprf_tr_ZAppts: "zprf_tr (ZAppts p ts) = proof_combt (zprf_tr p) (map zdec ts)"
  by (induction ts arbitrary: p) (simp_all add: ZAppts_def proof_combt_def)

lemma zprf_tr_leaf:
  "zprf_tr (ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0))) (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0))) (map PBound (removeAll (i - n) (downto (i - 1) 0)))"
  by (simp add: zprf_tr_ZAppps zprf_tr_ZAppts comp_def)

lemma match_of_class_App2: "match_of_class (t $ A $ B) = None"
  by (simp add: match_of_class_def split: pterm.splits)

lemma match_of_class_Abs: "match_of_class (t $ Abs a T b) = None"
  by (simp add: match_of_class_def split: pterm.splits)

abbreviation is_imp :: "pterm \<Rightarrow> bool" where
  "is_imp t \<equiv> \<exists>U A B. t = Const STR ''Pure.imp'' U $ A $ B"

abbreviation is_all :: "pterm \<Rightarrow> bool" where
  "is_all t \<equiv> \<exists>U a T b. t = Const STR ''Pure.all'' U $ Abs a T b"

lemma zterm_of_imp:
  assumes "zterm_of ztargs (Const STR ''Pure.imp'' U $ A $ B) = returnZ z"
  shows "\<exists>zA zB. z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zA) zB \<and> zterm_of ztargs A = returnZ zA \<and>
    zterm_of ztargs B = returnZ zB"
proof -
  have nc: "Const STR ''Pure.imp'' U $ A \<noteq> mk_of_class T c" for T c
    using class_suffix_imp[of c] by (auto simp: mk_of_class_def class_suffix_def)
  from assms nc show ?thesis
    by (auto simp: match_of_class_App2 bindZ_eq_returnZ liftMZ_eq_returnZ ztargs_def return_def
      split: option.splits)
qed

lemma zterm_of_all:
  assumes "zterm_of ztargs (Const STR ''Pure.all'' U $ Abs a T b) = returnZ z"
  shows "\<exists>U0 zb. z = ZApp (ZConst1 STR ''Pure.all'' U0) (ZAbs a (ztyp_of T) zb) \<and> zterm_of ztargs b = returnZ zb"
  using assms
  by (auto simp: match_of_class_Abs bindZ_eq_returnZ liftMZ_eq_returnZ ztargs_def return_def raise_def
    split: ptyp.splits list.splits if_splits)

lemma aflatten_leaf:
  "\<not> is_imp t \<Longrightarrow> \<not> is_all t \<Longrightarrow> aflatten_params_proof fA fT i j n (t, k) =
    proof_combP (proof_combt (PBound (k + i)) (map Bound (downto (j - 1) 0))) (map PBound (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(fA, fT, i, j, n, (t, k))" rule: aflatten_params_proof.cases) auto

lemma zflatten_leaf:
  "\<not> is_imp (zdec z) \<Longrightarrow> \<not> is_all (zdec z) \<Longrightarrow> zflatten_params_proof i j n (z, k) =
    ZAppps (ZAppts (ZBoundp (k + i)) (map ZBound (downto (j - 1) 0))) (map ZBoundp (removeAll (i - n) (downto (i - 1) 0)))"
  by (cases "(i, j, n, (z, k))" rule: zflatten_params_proof.cases) auto

lemma zprf_tr_zflatten_params_proof:
  "zterm_of ztargs t = returnZ z \<Longrightarrow> zdec z = t \<Longrightarrow>
    zprf_tr (zflatten_params_proof i j n (z, k)) = aflatten_params_proof Some Some i j n (t, k)"
proof (induction t arbitrary: z i j rule: measure_induct_rule[of size])
  case (less t)
  consider (imp) U A B where "t = Const STR ''Pure.imp'' U $ A $ B"
    | (all) U a T b where "t = Const STR ''Pure.all'' U $ Abs a T b"
    | (leaf) "\<not> is_imp t" "\<not> is_all t"
    by blast
  then show ?case
  proof cases
    case imp
    from zterm_of_imp[OF less.prems(1)[unfolded imp]] obtain zA zB where
      z: "z = ZApp (ZApp (ZConst0 STR ''Pure.imp'') zA) zB" and zB: "zterm_of ztargs B = returnZ zB" by blast
    have d: "zdec zA = A" "zdec zB = B" using less.prems(2) imp z by simp_all
    have "zprf_tr (zflatten_params_proof (i + 1) j n (zB, k)) = aflatten_params_proof Some Some (i + 1) j n (B, k)"
      by (rule less.IH[OF _ zB d(2)]) (simp add: imp)
    then show ?thesis by (simp add: imp z d(1))
  next
    case all
    from zterm_of_all[OF less.prems(1)[unfolded all]] obtain U0 zb where
      z: "z = ZApp (ZConst1 STR ''Pure.all'' U0) (ZAbs a (ztyp_of T) zb)" and zb: "zterm_of ztargs b = returnZ zb"
      by blast
    have d: "typ_of (ztyp_of T) = T" "zdec zb = b" using less.prems(2) all z by simp_all
    have "zprf_tr (zflatten_params_proof i (j + 1) n (zb, k)) = aflatten_params_proof Some Some i (j + 1) n (b, k)"
      by (rule less.IH[OF _ zb d(2)]) (simp add: all)
    then show ?thesis by (simp add: all z d(1))
  next
    case leaf
    then show ?thesis
      using less.prems(2) by (simp add: zflatten_leaf aflatten_leaf zprf_tr_leaf)
  qed
qed

end

end
