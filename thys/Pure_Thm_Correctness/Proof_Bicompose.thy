section \<open>Correctness of the proofs of composition\<close>

theory Proof_Bicompose
  imports Proof_Bridge
begin

context prf_csig
begin

subsection \<open>Proofs without terms and types\<close>

text \<open>
  The proofs that composition builds around the proofs of the rule and of the proof state only
  contain bound variables as terms; instantiation does not change them.
\<close>

abbreviation bnd_only :: "prf \<Rightarrow> bool" where
  "bnd_only \<equiv> prf_all (\<lambda>t. vars t = {} \<and> tys t = {}) (\<lambda>_. False)"

lemma map_types_no_tys: "tys t = {} \<Longrightarrow> map_types f t = t"
  by (induction t) auto

lemma prf_inst_bnd_only: "bnd_only p \<Longrightarrow> prf_inst \<rho> \<theta> lev p = p"
proof (induction p arbitrary: lev)
  case (AbsP a t p)
  then show ?case by (cases t) (auto simp: psubst_no_vars map_types_no_tys)
next
  case (PAppt p t)
  then show ?case by (cases t) (auto simp: psubst_no_vars map_types_no_tys)
next
  case (PAxm a A Ts)
  then show ?case by (cases Ts) auto
next
  case (Oracle a A Ts)
  then show ?case by (cases Ts) auto
next
  case (Abst a T p)
  then show ?case by (cases T) auto
next
  case (PThm hb)
  obtain h b where hb: "hb = (h, b)" by (cases hb)
  with PThm have "map_option (map (tsubst \<rho>)) (hd_types h) = hd_types h" by (cases "hd_types h") auto
  then show ?case using hb by (cases h) (simp add: hd_set_types_def)
qed auto

lemma prf_all_proof_combP: "prf_all P Q (proof_combP p qs) \<longleftrightarrow> prf_all P Q p \<and> (\<forall>q\<in>set qs. prf_all P Q q)"
  by (induction qs arbitrary: p rule: rev_induct) (auto simp: proof_combP_def)

lemma prf_all_proof_combt: "prf_all P Q (proof_combt p ts) \<longleftrightarrow> prf_all P Q p \<and> (\<forall>t\<in>set ts. P t)"
  by (induction ts arbitrary: p rule: rev_induct) (auto simp: proof_combt_def)

lemma prf_all_mk_AbsP[simp]: "prf_all P Q (mk_AbsP xs p) \<longleftrightarrow> prf_all P Q p"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma bnd_only_flatten_params_proof: "bnd_only (flatten_params_proof i j n (A, k))"
  by (induction i j n "(A, k)" arbitrary: A rule: flatten_params_proof.induct)
    (auto simp: prf_all_proof_combP prf_all_proof_combt)

lemma bnd_only_flatten_params_proof': "bnd_only (flatten_params_proof i j n x)"
  by (cases x) (simp add: bnd_only_flatten_params_proof)

lemma bnd_only_imp_prf: "bnd_only (imp_prf A i m)"
  by (induction A i m rule: imp_prf.induct) auto

lemma bnd_only_all_prf: "bnd_only (all_prf i m A)"
  by (induction i m A rule: all_prf.induct) (auto simp: bnd_only_imp_prf)

lemma bnd_only_mk_asm_prf: "bnd_only (mk_asm_prf A i m)"
  by (simp add: mk_asm_prf_def bnd_only_all_prf)

lemma prf_inst_mk_AbsP: "prf_inst \<rho> \<theta> lev (mk_AbsP xs p) = mk_AbsP xs (prf_inst \<rho> \<theta> lev p)"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma prf_inst_proof_combP:
  "prf_inst \<rho> \<theta> lev (proof_combP p qs) = proof_combP (prf_inst \<rho> \<theta> lev p) (map (prf_inst \<rho> \<theta> lev) qs)"
  by (induction qs arbitrary: p rule: rev_induct) (simp_all add: proof_combP_def)

lemma mk_AbsP_length: "length xs = length ys \<Longrightarrow> mk_AbsP xs p = mk_AbsP ys p"
  by (induction xs ys rule: list_induct2) (simp_all add: mk_AbsP_def)


subsection \<open>The composed proof\<close>

lemma ok_zip_eq: "length xs = length ys \<Longrightarrow> ok (zip_eq xs ys) (zip xs ys)"
  by (induction xs ys rule: list_induct2) auto

text \<open>The proof that \<^const>\<open>bicompose_core\<close> builds, if the terms can be normalized.\<close>

definition core_prf :: "bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow> pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow>
    prf \<Rightarrow> prf \<Rightarrow> prf" where
  "core_prf flatten Bs As A oldAs n m sprf p =
    mk_AbsP (Bs @ As) (PAppp
      (proof_combP sprf (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP p ((if 0 < n then [mk_asm_prf (the A) n m] else []) @
        map (if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x)))
          (zip oldAs (downto (integer_of_nat (length As) - 1) 0)))))"

lemma bicompose_core_eq:
  assumes "\<forall>X\<in>set (Bs @ As). \<exists>X'. ok (norm_term env X) X'" "length oldAs = length As"
    "A = None \<Longrightarrow> \<not> 0 < n"
  shows "bicompose_core env flatten Bs As A oldAs n m sprf p = returnP (core_prf flatten Bs As A oldAs n m sprf p)"
proof -
  from assms(1) obtain Ns where Ns: "list_all2 (\<lambda>X X'. ok (norm_term env X) X') (Bs @ As) Ns"
    using list_all2_exI[of "Bs @ As" "\<lambda>X X'. ok (norm_term env X) X'"] by blast
  then have m: "mapM (norm_term env) (Bs @ As) = return Ns" by (simp add: ok_mapM return_def)
  have l: "mk_AbsP Ns q = mk_AbsP (Bs @ As) q" for q
    using list_all2_lengthD[OF Ns] by (intro mk_AbsP_length) simp
  have z: "zip_eq oldAs (downto (integer_of_nat (length As) - 1) 0) =
      return (zip oldAs (downto (integer_of_nat (length As) - 1) 0))"
  proof -
    have "length (downto (integer_of_nat (length As) - 1) 0) = length As"
      by (simp add: downto_map integer_reps integer_of_nat.rep_eq)
    then have "ok (zip_eq oldAs (downto (integer_of_nat (length As) - 1) 0))
        (zip oldAs (downto (integer_of_nat (length As) - 1) 0))"
      using assms(2) by (intro ok_zip_eq) simp
    then show ?thesis by (simp add: return_def)
  qed
  show ?thesis
    using assms(3) by (cases A) (auto simp: bicompose_core_def core_prf_def m z l Let_def)
qed

lemma zip_downto:
  assumes "length xs = la"
  shows "zip xs (downto (integer_of_nat la - 1) 0) = map (\<lambda>k. (xs ! k, integer_of_nat (la - 1 - k))) [0..<la]"
proof -
  have "nat_of_integer (integer_of_nat la - 1 - 0 + 1) = la" by (simp add: integer_reps integer_of_nat.rep_eq)
  moreover have "integer_of_nat la - 1 - integer_of_nat k = integer_of_nat (la - 1 - k)" if "k < la" for k
    using that by (simp add: integer_eq_iff integer_of_nat.rep_eq of_nat_diff)
  ultimately show ?thesis using assms by (auto simp: downto_map intro!: nth_equalityI)
qed

text \<open>The proof of the composition is a proof of the new theorem, from proofs of its parts.\<close>

lemma core_prf_ok:
  assumes S: "prf_ok V H [] [] sp (list_implies (iBs @ [iBi]) iC)"
    and R: "prf_ok V H [] [] rp (list_implies (iPre @ iOlds) iB)" and BBi: "tr iB \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr iBi"
    and Ns: "length Ns = length Bs + length As" "\<forall>N\<in>set Ns. wty V [] N propT"
    and lens: "length iBs = length Bs" "length iOlds = length oldAs" "length oldAs = length As"
    and NB: "\<forall>j<length Bs. tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (iBs ! j)"
    and olds: "\<forall>k<length oldAs. prf_ok V H [] (rev Ns)
      ((if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))) (oldAs ! k, integer_of_nat (length As - 1 - k)))
      (iOlds ! k)"
    and pre: "(iPre = [] \<and> \<not> 0 < n) \<or> (\<exists>A1 iA1. iPre = [iA1] \<and> 0 < n \<and> A = Some A1 \<and>
      prf_ok V H [] (rev Ns) (mk_asm_prf A1 n m) iA1)"
  shows "prf_ok V H [] [] (core_prf flatten Bs As A oldAs n m sp rp) (list_implies Ns iC)"
proof -
  let ?f = "if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))"
  let ?qs = "(if 0 < n then [mk_asm_prf (the A) n m] else []) @
    map ?f (zip oldAs (downto (integer_of_nat (length As) - 1) 0))"
  have z: "map ?f (zip oldAs (downto (integer_of_nat (length As) - 1) 0)) =
      map (\<lambda>k. ?f (oldAs ! k, integer_of_nat (length As - 1 - k))) [0..<length oldAs]"
    using zip_downto[of oldAs "length As"] lens(3) by simp
  have o: "list_all2 (\<lambda>a P. prf_ok V H [] (rev Ns) a P) (map ?f (zip oldAs (downto (integer_of_nat (length As) - 1) 0))) iOlds"
    unfolding z using olds lens(2) by (auto simp: list_all2_conv_all_nth)
  have p: "list_all2 (\<lambda>a P. prf_ok V H [] (rev Ns) a P) (if 0 < n then [mk_asm_prf (the A) n m] else []) iPre"
    using pre by auto
  have args: "list_all2 (\<lambda>a P. prf_ok V H [] (rev Ns) a P) ?qs (iPre @ iOlds)"
    using list_all2_appendI[OF p o] .
  from prf_ok_compose[OF S R BBi _ Ns(2) _ args, of As] Ns(1) lens(1) NB
  have "prf_ok V H [] [] (mk_AbsP Ns (PAppp
      (proof_combP sp (map PBound (downto (integer_of_nat (length iBs) + integer_of_nat (length As) - 1)
        (integer_of_nat (length As)))))
      (proof_combP rp ?qs))) (list_implies Ns iC)"
    by simp
  moreover have "mk_AbsP Ns q = mk_AbsP (Bs @ As) q" for q using Ns(1) by (intro mk_AbsP_length) simp
  ultimately show ?thesis by (simp add: core_prf_def lens(1))
qed

lemma prf_inst_core_prf:
  "prf_inst \<rho> \<theta> 0 (core_prf flatten Bs As A oldAs n m sprf p) =
    core_prf flatten Bs As A oldAs n m (prf_inst \<rho> \<theta> 0 sprf) (prf_inst \<rho> \<theta> 0 p)"
  by (simp add: core_prf_def prf_inst_mk_AbsP prf_inst_proof_combP prf_inst_bnd_only bnd_only_mk_asm_prf
      bnd_only_flatten_params_proof' comp_def)

end

end
