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



subsection \<open>Proofs with bound variables as terms\<close>

abbreviation bnd_prf :: "prf \<Rightarrow> bool" where
  "bnd_prf \<equiv> prf_all (\<lambda>t. \<exists>j. 0 \<le> j \<and> t = Bound j) (\<lambda>_. False)"

lemma bnd_prf_bnd_only: "bnd_prf p \<Longrightarrow> bnd_only p"
  by (erule prf_all_mono) auto

lemma set_downto: "x \<in> set (downto a b) \<Longrightarrow> b \<le> x"
  by (induction a b rule: downto.induct) (subst (asm) downto.simps; auto split: if_splits)

lemma bnd_prf_flatten_params_proof: "0 \<le> j \<Longrightarrow> bnd_prf (flatten_params_proof i j n x)"
proof (induction i j n x rule: flatten_params_proof.induct)
qed (auto simp: prf_all_proof_combP prf_all_proof_combt dest: set_downto)

lemma bnd_prf_imp_prf: "bnd_prf (imp_prf A i m)"
  by (induction A i m rule: imp_prf.induct) auto

lemma bnd_prf_all_prf: "bnd_prf (all_prf i m A)"
  by (induction i m A rule: all_prf.induct) (auto simp: bnd_prf_imp_prf)

lemma bnd_prf_mk_asm_prf: "bnd_prf (mk_asm_prf A i m)"
  by (simp add: mk_asm_prf_def bnd_prf_all_prf)

lemma prf_all_core_prf:
  assumes "prf_all P Q sprf" "prf_all P Q p" "\<And>j. 0 \<le> j \<Longrightarrow> P (Bound j)"
  shows "prf_all P Q (core_prf flatten Bs As A oldAs n m sprf p)"
proof -
  have b: "prf_all P Q q" if "bnd_prf q" for q using that by (rule prf_all_mono) (use assms(3) in auto)
  have f: "prf_all P Q ((if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))) x)" for x
    using b[OF bnd_prf_flatten_params_proof[of 0]] by auto
  show ?thesis using assms(1,2) b[OF bnd_prf_mk_asm_prf] f
    by (auto simp: core_prf_def prf_all_proof_combP)
qed

subsection \<open>Renamed terms\<close>

lemma aconv_term_refl[simp]: "aconv_term t t"
  by (induction t) auto

lemma aconv_psubst_ren_term:
  "aconv_term (psubst \<rho> \<theta> lev (ren_term r t)) (psubst \<rho> (\<theta> \<circ> ren_ix r) lev t)"
  by (induction r t arbitrary: lev rule: ren_term.induct) (simp_all add: ren_ix_def)

end

context prf_wf_csig
begin

subsection \<open>Typing of instances through an environment\<close>

lemma typed_tctx_agree:
  assumes "typed env W' [] r U" "has_type W0 [] r U0" "x \<in> vars r"
  shows "tctx env W' x = tnorm (tyenv env) (W0 x)"
proof -
  have "(x, W0 x) \<in> vps r" by (rule has_type_vps[OF assms(2,3)])
  from typed_vps[OF assms(1) this] show ?thesis by simp
qed

lemma tsubst_tnorm_gsol:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tcons \<theta> T" "gsol alg ar \<theta> \<rho>"
  shows "tsubst \<rho> (tnorm \<theta> T) = tsubst \<rho> T"
  using ok_norm_type_tsol[of \<theta> T "tnorm \<theta> T" \<rho>] norm_type_ok[OF assms(1-3)] assms(4)
  by (simp add: gsol_def return_def)

lemma tsubst_tctx:
  assumes pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>"
  shows "tsubst \<rho> (tctx env W y) = tsubst \<rho> (W y)"
proof -
  have ti: "tinv ar (maxidx env) (tyenv env) A" by (rule pinvD(2)[OF pi])
  note ac = tinv_tacyc[OF ti] and tc = tinv_tcons_env[OF ti]
  have tW: "tcons (tyenv env) (W y)" by (rule tyw_tcons[OF ti pinvD(5)[OF pi]])
  show ?thesis
  proof (cases "vt_lookup (tenv env) y")
    case None
    then show ?thesis using tsubst_tnorm_gsol[OF ac tc tW g] by (simp add: vtyp_def)
  next
    case (Some Uu)
    obtain U u where Uu: "Uu = (U, u)" by (cases Uu)
    have "tnorm (tyenv env) U = tnorm (tyenv env) (W y)"
      using pinvD(6)[OF pi] Some Uu unfolding wcons_def by blast
    then show ?thesis using Some Uu tsubst_tnorm_gsol[OF ac tc tW g] by (simp add: vtyp_def)
  qed
qed

text \<open>
  An instance typed by the typing \<open>W\<close> of the unifier is, through \<open>f\<close>, an instance typed by the
  typing \<open>Wt\<close> of a theorem on the variables \<open>R\<close>, if both typings agree modulo the environment.
\<close>

lemma inst_typed_transfer:
  assumes ty: "inst_typed W V' [] \<rho> \<theta>" and pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>"
    and ag: "\<And>x. x \<in> R \<Longrightarrow> 0 \<le> snd x \<Longrightarrow> 0 \<le> snd (f x) \<and> tctx env W (f x) = tnorm (tyenv env) (Wt x)"
    and tc: "\<And>x. x \<in> R \<Longrightarrow> tcons (tyenv env) (Wt x)"
  shows "inst_typed Wt V' [] \<rho> (\<lambda>x. if x \<in> R then \<theta> (f x) else Free STR ''u'' (tsubst \<rho> (Wt x)))"
  unfolding inst_typed_def
proof (intro allI impI)
  fix x :: indexname assume x: "0 \<le> snd x"
  have ti: "tinv ar (maxidx env) (tyenv env) A" by (rule pinvD(2)[OF pi])
  note ac = tinv_tacyc[OF ti] and tcn = tinv_tcons_env[OF ti]
  show "wty V' [] (if x \<in> R then \<theta> (f x) else Free STR ''u'' (tsubst \<rho> (Wt x))) (tsubst \<rho> (Wt x))"
  proof (cases "x \<in> R")
    case True
    from ag[OF True x] have f: "0 \<le> snd (f x)" "tctx env W (f x) = tnorm (tyenv env) (Wt x)" by blast+
    have "tsubst \<rho> (W (f x)) = tsubst \<rho> (Wt x)"
      using tsubst_tctx[OF pi g, of "f x"] f(2) tsubst_tnorm_gsol[OF ac tcn tc[OF True] g] by simp
    with inst_typedD[OF ty f(1)] True show ?thesis by simp
  qed (simp add: wty_def has_type.Free)
qed

lemma sm_lift_pre_equiv:
  assumes "sm \<rho> \<sigma> (abs_pre p X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (abs_pre p Y)"
  shows "sm \<rho> \<sigma> (lift_pre p X) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> (lift_pre p Y)"
proof -
  have e: "sm \<rho> \<sigma> X \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> \<sigma> Y" using assms by (simp add: sm_abs_pre equiv_Abs_m_inj)
  show ?thesis
  proof (induction p)
    case (Cons i p)
    then show ?case
      by (cases i; simp only: lift_pre.simps sm_App sm_Abs; intro equiv_App equiv_Abs equiv_refl)
  qed (simp only: lift_pre.simps, rule e)
qed



subsection \<open>Terms of proofs that can be normalized\<close>

text \<open>
  A term of a proof without schematic variables that agrees up to the types of its constants and
  abstractions with a typed term, whose types are in \<open>A\<close>.
\<close>

definition ann0 :: "(indexname \<times> psort) set \<Rightarrow> pterm \<Rightarrow> bool" where
  "ann0 A t \<longleftrightarrow> (\<exists>t0 Ts T. remove_types t = remove_types t0 \<and> has_type (\<lambda>_. propT) Ts t0 T \<and> vars t0 = {} \<and>
    (\<forall>U\<in>set Ts \<union> tys t0. tyA ar A U)) \<and> (\<forall>U\<in>tys t. tvars U \<subseteq> A)"

lemma norm_term_Bound: "norm_term env (Bound j) = return (Bound j)"
  by (simp add: norm_term_def norm_term1.simps norm_term2.simps)

lemma ann_ok_env_Bound: "0 \<le> j \<Longrightarrow> ann_ok_env env (Bound j)"
  unfolding ann_ok_env_def
proof (intro conjI exI)
  assume j: "0 \<le> j"
  let ?rb = "replicate (Suc (nat_of_integer j)) (STR ''x'', propT)"
  show "swf_tm ar ?rb (Bound j)" using j by (simp add: swf_tm_def integer_reps)
qed (simp_all add: norm_term_Bound return_def)

lemma ann0_ann_ok_env:
  assumes "ann0 A t" and pi: "pinv alg ar A W env []"
  shows "ann_ok_env env t"
proof -
  from assms(1) obtain t0 Ts T where rt: "remove_types t = remove_types t0"
    and ht: "has_type (\<lambda>_. propT) Ts t0 T" and v: "vars t0 = {}" and tA: "\<forall>U\<in>set Ts \<union> tys t0. tyA ar A U"
    and tt: "\<forall>U\<in>tys t. tvars U \<subseteq> A"
    by (auto simp: ann0_def)
  have ti: "tinv ar (maxidx env) (tyenv env) A" by (rule pinvD(2)[OF pi])
  have "has_type (\<lambda>x. tnorm (tyenv env) propT) (map (tnorm (tyenv env)) Ts) (tnormt (tyenv env) t0)
      (tnorm (tyenv env) T)"
    by (rule has_type_tnormt[OF ht])
  then have tp: "typed env W Ts t0 T" unfolding typed_def by (rule has_type_vars) (use v in simp)
  have tw: "\<forall>U\<in>set Ts \<union> tys t0. tyw ar (tyenv env) A U" using tA tyA_tyw[OF ti] by blast
  have "\<exists>t0'. ok (norm_term env t0) t0'"
    by (rule norm_term_ok[OF pi tp]) (use tw v in \<open>simp_all add: below_def\<close>)
  moreover have "swf_tm ar (map (\<lambda>U. (STR ''x'', U)) Ts) t0"
  proof -
    have p: "proper t0" by (rule has_type_proper[OF ht])
    have "\<not> loose_bvar t0 (integer_of_nat (length Ts))" by (rule has_type_loose_bvar[OF ht])
    then have "no_loose_bound (tr t0) (length Ts)" using loose_bvar_tr[OF p, of "integer_of_nat (length Ts)"]
      by simp
    moreover have "twft ar t0" using tA by (simp add: twft_tys tyA_def)
    ultimately show ?thesis using p by (simp add: swf_tm_def)
  qed
  moreover have "\<forall>U\<in>tys t. tcons (tyenv env) U" using tt tinv_tcons[OF ti] by blast
  ultimately show ?thesis using rt v unfolding ann_ok_env_def by blast
qed



subsection \<open>Correctness of the proof of composition\<close>

text \<open>The renaming that the wrapper applies to the proof of the rule.\<close>

definition ren_prf :: "ren option \<Rightarrow> prf \<Rightarrow> prf" where
  "ren_prf r p = (case r of None \<Rightarrow> p | Some r \<Rightarrow> map_proof_terms (ren_term r) id p)"

text \<open>
  The main theorem on proofs: for a result of \<open>bicompose_aux\<close> for a well-typed proof state and a
  well-typed incremented rule with a common typing (as in @{thm [source] bicompose_aux_thm_typed}),
  with valid proofs whose terms have no schematic variables and can be normalized, \<open>bicompose_proof\<close>
  computes, without warnings or exceptions, a valid proof of the new theorem.
\<close>

theorem bicompose_proof_valid:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "wt_thm ar A W smax stpairs (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A W rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (W x)"
    and ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and cA: "tcert alg A"
    and nn: "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop. 0 \<le> snd x"
    and sv: "prf_valid alg ar W H stpairs sprf (list_implies (Bs @ [Bi]) C)"
    and rv: "prf_valid alg ar W H rtpairs rprf rprop"
    and sp0: "prf_vars sprf = {}" and rp0: "prf_vars rprf = {}"
    and sw: "prf_all (\<lambda>t. ann0 A t \<and> (\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<le> smax))
      (\<lambda>U. tyA ar A U \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> smax)) sprf"
    and rw: "prf_all (ann0 A) (tyA ar A) rprf"
  shows "\<exists>p. bicompose_proof (br_env r) smax flatten Bs (na_As (br_newas r)) (br_A r) (na_oldAs (br_newas r))
      (na_n (br_newas r)) (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1)
      (ren_prf (na_ren (br_newas r)) rprf) sprf = returnP p \<and>
    (\<exists>Wr. prf_valid alg ar Wr H (br_tpairs r) p (br_prop r))"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  have A2: "\<forall>p\<in>A. snd (fst p) \<le> ?m" using A(2) by blast
  from strip_prems_ok[OF ns] obtain rAsB where "ok (strip_prems nsubgoal [] rprop) rAsB" by blast
  then obtain rAs B where sp1: "ok (strip_prems nsubgoal [] rprop) (rAs, B)" by (cases rAsB) auto
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF sp1]) (use rule(1) in \<open>simp add: wt_thm_def\<close>)
  have wS: "\<forall>X\<in>set Bs. wt_term ar A W smax X propT" "wt_term ar A W smax Bi propT"
    "wt_term ar A W smax C propT"
    using wt_term_list_implies[of ar A W smax "Bs @ [Bi]" C] state(1) by (auto simp: wt_thm_def)
  have wR: "\<forall>X\<in>set (rev rAs). wt_term ar A W rmax X propT" "wt_term ar A W rmax B propT"
    using wt_term_list_implies[of ar A W rmax "rev rAs" B] rule(1) P by (auto simp: wt_thm_def)
  text \<open>Further terms that keep their types in the unifier: the subgoal, the conclusion of the rule
    and the flex-flex pairs.\<close>
  define tpT where "tpT m t u = (SOME T. wt_term ar A W m t T \<and> wt_term ar A W m u T)" for m t u
  have tpS: "wt_term ar A W smax t (tpT smax t u) \<and> wt_term ar A W smax u (tpT smax t u)"
    if "(t, u) \<in> set stpairs" for t u
    unfolding tpT_def by (rule someI_ex) (use state(1) that in \<open>auto simp: wt_thm_def\<close>)
  have tpR: "wt_term ar A W rmax t (tpT rmax t u) \<and> wt_term ar A W rmax u (tpT rmax t u)"
    if "(t, u) \<in> set rtpairs" for t u
    unfolding tpT_def by (rule someI_ex) (use rule(1) that in \<open>auto simp: wt_thm_def\<close>)
  define xsS where "xsS = (Bi, propT) # concat (map (\<lambda>(t, u). [(t, tpT smax t u), (u, tpT smax t u)]) stpairs)"
  define xsR where "xsR = (B, propT) # concat (map (\<lambda>(t, u). [(t, tpT rmax t u), (u, tpT rmax t u)]) rtpairs)"
  have xs: "\<forall>(X, T)\<in>set (xsS @ xsR). (wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S) \<or>
      (wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop)"
  proof -
    have "wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S" if "(X, T) \<in> set xsS" for X T
      using that wS(2) tpS by (fastforce simp: xsS_def vars_thm_def vars_list_implies)
    moreover have "wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop" if "(X, T) \<in> set xsR" for X T
      using that wR(2) tpR by (fastforce simp: xsR_def vars_thm_def vars_list_implies P)
    ultimately show ?thesis by auto
  qed
  text \<open>The call of the body.\<close>
  have "\<exists>rAs B env s' W0. ok (strip_prems nsubgoal [] rprop) (rAs, B) \<and> env = empty_env ?m \<and>
      okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s' \<and>
      okT (bicompose_body (unify_ops cfg vl)
        (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B))
        env eres_flg rAs) s' \<and>
      pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) W0 \<and>
      results_typed (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)
        (xsS @ xsR)"
    by (rule bicompose_aux_call[where incremented=True, OF cfg finA state rule A(1) A2 A(3) A(3) cA _ ns er fl vl xs])
      blast+
  then obtain rAs' B' env s' W0 where sp1': "ok (strip_prems nsubgoal [] rprop) (rAs', B')"
    and e1: "env = empty_env ?m"
    and ok': "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s'"
    and body: "okT (bicompose_body (unify_ops cfg vl)
        (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B'))
        env eres_flg rAs') s'"
    and pa: "pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B') W0"
    and rty: "results_typed (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B')
        (xsS @ xsR)"
    by blast
  from sp1 sp1' have rAsB: "rAs' = rAs" "B' = B" by simp_all
  note body = body[unfolded rAsB] and pa = pa[unfolded rAsB] and rty = rty[unfolded rAsB]
  define sp where "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  note pa = pa[folded sp_def] and rty = rty[folded sp_def] and body = body[folded sp_def]
  have sel: "bs_cfg sp = cfg" "bs_vl sp = vl" "bs_A sp = A" "bs_env sp = env" "bs_eres sp = eres_flg"
    "bs_rAs sp = rAs" "bc_smax (bs_ctx sp) = smax" "bc_Bs (bs_ctx sp) = Bs" "bc_C (bs_ctx sp) = C"
    "bc_Bi (bs_ctx sp) = Bi" "bc_lifted (bs_ctx sp) = lifted" "bc_flatten (bs_ctx sp) = flatten"
    "bc_nlift (bs_ctx sp) = nlift" "bc_rtpairs (bs_ctx sp) = rtpairs"
    by (simp_all add: sp_def call_spec_def Let_def nlift_def)
  have ss: "s' = s" using okT_det[OF ok' ok] .
  have te: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: e1 empty_env_def)
  have mx: "maxidx env = ?m" by (simp add: e1)
  have pal: "pinv_all sp" by (rule pinv_allW_pinv_all[OF pa])
  have bi: "binv sp s"
    by (rule bicompose_body_binv) (use body ss cfg finA pal in \<open>simp_all add: sel\<close>)
  have "rchar sp r"
    by (rule bresult_rchar) (use res bi cfg finA pal in \<open>simp_all add: sel\<close>)
  then obtain A1o na tus env' tps where its: "itsok sp A1o na tus"
    and pu: "punifier env (dps_of tus) env' tps" and pr: "prres alg ar A env' tps"
    and ue: "uelem alg cfg env tus (El_R env' tps)" and ad: "okT (addth (bs_ctx sp) A1o na (env', tps)) r"
    by (auto simp: rchar_def sel)
  from rty[unfolded results_typed_def sel, rule_format, OF its[unfolded sel] ue]
  obtain W' e0 W'' where pi': "pinv alg ar A W' env' []" and tp: "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab"
    and BC: "\<forall>X\<in>insert C (set Bs). wtprop A W' env' X"
    and pi'': "pinv alg ar A W'' env' []" and As: "\<forall>X\<in>set (na_As na). wtprop A W'' env' X"
    and W''d: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> smax < snd v \<and> snd v \<le> maxidx env \<and> (\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u)"
    and sk1: "lifted \<longrightarrow> 0 \<le> nlift \<and> (\<forall>X\<in>set (na_As na). nlift \<le> ilength (spine_hyps X))"
    and nA: "\<exists>As0 n dps tps1. okT (newAs vl (bs_ctx sp) As0 n dps tps1) na \<and> set As0 \<subseteq> set (rev rAs) \<and>
      (\<forall>X\<in>set As0. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x) \<and>
      As0 = (if eres_flg then tl (rev rAs) else rev rAs)"
    and sk2: "lifted \<longrightarrow> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
    and rsx: "rs_typed ar A (xsS @ xsR) W' env'"
    by (auto simp: sel)
  show ?thesis sorry
qed

end

end
