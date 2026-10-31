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

lemma has_type_aconv':
  "aconv_term t u \<Longrightarrow> has_type W Ts t T \<Longrightarrow> has_type W Ts u T"
proof (induction t u arbitrary: Ts T rule: aconv_term.induct)
  case (1 t1 u1 t2 u2)
  from "1.prems"(2) obtain A where s: "has_type W Ts t1 (A \<rightarrow>\<^sub>T T)" and u: "has_type W Ts u1 A"
    by (auto elim: has_type_elims)
  from "1.prems"(1) have "aconv_term t1 t2" "aconv_term u1 u2" by simp_all
  from has_type.App[OF "1.IH"(1)[OF this(1) s] "1.IH"(2)[OF this(2) u]] show ?case .
next
  case (2 a T1 t1 b T2 t2)
  then show ?case by (auto elim!: has_type_elims intro: has_type.Abs)
qed auto

lemma aconv_term_sym': "aconv_term t u \<Longrightarrow> aconv_term u t"
  by (induction t u rule: aconv_term.induct) auto

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



subsection \<open>Renaming terms without schematic variables\<close>

text \<open>The renaming that the wrapper applies to the proof of the rule.\<close>

definition ren_prf :: "ren option \<Rightarrow> prf \<Rightarrow> prf" where
  "ren_prf r p = (case r of None \<Rightarrow> p | Some r \<Rightarrow> map_proof_terms (ren_term r) id p)"

lemma remove_types_ren_term: "remove_types (ren_term r t) = ren_term r (remove_types t)"
  by (induction r t rule: ren_term.induct) simp_all

lemma tys_ren_term[simp]: "tys (ren_term r t) = tys t"
  by (induction r t rule: ren_term.induct) simp_all

lemma aconv_ren_term: "vars t = {} \<Longrightarrow> aconv_term t (ren_term r t)"
  by (induction r t rule: ren_term.induct) simp_all

lemma ann0_ren_term: "ann0 A t \<Longrightarrow> ann0 A (ren_term r t)"
proof -
  assume "ann0 A t"
  then obtain t0 Ts T where rt: "remove_types t = remove_types t0" and ht: "has_type (\<lambda>_. propT) Ts t0 T"
    and v: "vars t0 = {}" and tA: "\<forall>U\<in>set Ts \<union> tys t0. tyA ar A U" and tt: "\<forall>U\<in>tys t. tvars U \<subseteq> A"
    by (auto simp: ann0_def)
  have "remove_types (ren_term r t) = remove_types (ren_term r t0)" by (simp add: remove_types_ren_term rt)
  moreover have "has_type (\<lambda>_. propT) Ts (ren_term r t0) T" by (rule has_type_aconv'[OF aconv_ren_term[OF v] ht])
  moreover have "vars (ren_term r t0) = {}" using v by (simp add: vars_ren_term)
  ultimately show ?thesis using tA tt unfolding ann0_def by (intro conjI exI[of _ "ren_term r t0"]) auto
qed

lemma prf_all_map_proof_terms:
  "prf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> P (f t)) \<Longrightarrow> prf_all P Q (map_proof_terms f id p)"
proof (induction p)
  case (PThm hb)
  then show ?case by (cases hb) (simp add: map_ident option.map_ident)
qed (auto simp: map_ident option.map_ident)

lemma prf_vars_map_proof_terms_ren: "prf_vars p = {} \<Longrightarrow> prf_vars (map_proof_terms (ren_term r) id p) = {}"
proof (induction p)
  case (AbsP a t p)
  then show ?case by (cases t) (auto simp: vars_ren_term)
next
  case (PAppt p t)
  then show ?case by (cases t) (auto simp: vars_ren_term)
next
  case (PThm hb)
  then show ?case by (cases hb) simp
qed simp_all

lemma ren_prf_props:
  assumes "prf_all (ann0 A) Q p" "prf_vars p = {}"
  shows "prf_all (ann0 A) Q (ren_prf r p)" "prf_vars (ren_prf r p) = {}"
  using assms prf_all_map_proof_terms[of "ann0 A" Q p] ann0_ren_term prf_vars_map_proof_terms_ren
  by (auto simp: ren_prf_def split: option.splits)

subsection \<open>Auxiliary facts on instances\<close>

lemma anns_proper_prf_all: "prf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> proper t) \<Longrightarrow> anns_proper p"
  by (induction P Q p rule: prf_all.induct) (auto split: option.splits)

lemma ann0_proper: "ann0 A t \<Longrightarrow> proper t"
  unfolding ann0_def using has_type_proper proper_remove_types by metis

text \<open>Instances of proofs without schematic variables depend only on the instances of their types.\<close>

lemma prf_inst_tcong:
  assumes "prf_vars p = {}"
    "prf_all (\<lambda>t. \<forall>U\<in>tys t. tsubst \<rho> U = tsubst \<rho>' U) (\<lambda>U. tsubst \<rho> U = tsubst \<rho>' U) p"
  shows "prf_inst \<rho> \<theta> lev p = prf_inst \<rho>' \<theta>' lev p"
proof -
  have ps: "psubst \<rho> \<theta> l t = psubst \<rho>' \<theta>' l t" if "vars t = {}" "\<forall>U\<in>tys t. tsubst \<rho> U = tsubst \<rho>' U" for l t
    using that by (induction \<rho> \<theta> l t rule: psubst.induct) auto
  from assms show ?thesis
  proof (induction p arbitrary: lev)
    case (Abst a T p)
    then show ?case by (cases T) auto
  next
    case (AbsP a t p)
    then show ?case by (cases t) (auto simp: ps)
  next
    case (PAppt p t)
    then show ?case by (cases t) (auto simp: ps)
  next
    case (PAxm a A Ts)
    then show ?case by (cases Ts) (simp_all add: map_eq_conv)
  next
    case (Oracle a A Ts)
    then show ?case by (cases Ts) (simp_all add: map_eq_conv)
  next
    case (PThm hb)
    obtain h b where hb: "hb = (h, b)" by (cases hb)
    have "map_option (map (tsubst \<rho>)) (hd_types h) = map_option (map (tsubst \<rho>')) (hd_types h)"
      using PThm hb by (cases "hd_types h") (simp_all add: map_eq_conv)
    then show ?case using hb by simp
  qed simp_all
qed

lemma prf_aeq_proof_combP: "prf_aeq p p' \<Longrightarrow> prf_aeq (proof_combP p qs) (proof_combP p' qs)"
  by (induction qs arbitrary: p p' rule: rev_induct) (auto simp: proof_combP_def intro: prf_aeq.intros)

lemma prf_aeq_mk_AbsP: "prf_aeq p p' \<Longrightarrow> prf_aeq (mk_AbsP xs p) (mk_AbsP xs p')"
  by (induction xs) (auto simp: mk_AbsP_def ann_eq_def intro: prf_aeq.AbsP)

lemma prf_aeq_core_prf:
  assumes "prf_aeq sp sp'" "prf_aeq rp rp'"
  shows "prf_aeq (core_prf flatten Bs As A oldAs n m sp rp) (core_prf flatten Bs As A oldAs n m sp' rp')"
  unfolding core_prf_def
  by (intro prf_aeq_mk_AbsP prf_aeq.PAppp prf_aeq_proof_combP assms)

lemma prf_vars_proof_combP: "prf_vars (proof_combP p qs) = prf_vars p \<union> (\<Union>q\<in>set qs. prf_vars q)"
  by (induction qs arbitrary: p rule: rev_induct) (auto simp: proof_combP_def)

lemma prf_vars_mk_AbsP[simp]: "prf_vars (mk_AbsP xs p) = prf_vars p"
  by (induction xs) (simp_all add: mk_AbsP_def)

lemma prf_vars_bnd_only: "bnd_only p \<Longrightarrow> prf_vars p = {}"
  by (induction p) (auto split: option.splits)

lemma prf_vars_core_prf:
  "prf_vars (core_prf flatten Bs As A oldAs n m sp rp) = prf_vars sp \<union> prf_vars rp"
proof -
  have "prf_vars q = {}" if "q \<in> set ((if 0 < n then [mk_asm_prf (the A) n m] else []) @
      map (if flatten then flatten_params_proof 0 0 n else (\<lambda>x. PBound (snd x))) zs)" for q zs
    using that prf_vars_bnd_only[OF bnd_only_mk_asm_prf] prf_vars_bnd_only[OF bnd_only_flatten_params_proof']
    by (auto split: if_splits)
  then show ?thesis by (auto simp: core_prf_def prf_vars_proof_combP)
qed

text \<open>Instances of terms typed modulo a type environment that the type instantiation solves.\<close>

lemma psubst_tnormt:
  "(\<forall>U\<in>tys t. tsubst \<rho> (tnorm \<theta> U) = tsubst \<rho> U) \<Longrightarrow> psubst \<rho> \<theta>' lev (tnormt \<theta> t) = psubst \<rho> \<theta>' lev t"
  by (induction t arbitrary: lev) auto

lemma typed_psubst_wty:
  assumes tp: "typed env W [] X T" and pi: "pinv alg ar A W env []" and g: "gsol alg ar (tyenv env) \<rho>"
    and tc: "\<forall>U\<in>tys X. tcons (tyenv env) U" "tcons (tyenv env) T"
    and th: "\<forall>x\<in>vars X. wty V' [] (\<theta> x) (tsubst \<rho> (W x))"
  shows "wty V' [] (psubst \<rho> \<theta> 0 X) (tsubst \<rho> T)"
proof -
  have ti: "tinv ar (maxidx env) (tyenv env) A" by (rule pinvD(2)[OF pi])
  note ac = tinv_tacyc[OF ti] and tcn = tinv_tcons_env[OF ti]
  have h: "has_type (tctx env W) [] (tnormt (tyenv env) X) (tnorm (tyenv env) T)"
    using tp by (simp add: typed_def)
  have "has_type V' (map (tsubst \<rho>) [] @ []) (psubst \<rho> \<theta> (integer_of_nat (length ([] :: ptyp list)))
      (tnormt (tyenv env) X)) (tsubst \<rho> (tnorm (tyenv env) T))"
  proof (rule has_type_psubst[OF h])
    show "\<forall>x\<in>vars (tnormt (tyenv env) X). has_type V' [] (\<theta> x) (tsubst \<rho> (tctx env W x))"
      using th tsubst_tctx[OF pi g] by (auto simp: wty_def)
  qed
  moreover have "psubst \<rho> \<theta> 0 (tnormt (tyenv env) X) = psubst \<rho> \<theta> 0 X"
    by (rule psubst_tnormt) (use tc tsubst_tnorm_gsol[OF ac tcn _ g] in blast)
  moreover have "tsubst \<rho> (tnorm (tyenv env) T) = tsubst \<rho> T" by (rule tsubst_tnorm_gsol[OF ac tcn tc(2) g])
  moreover have "\<forall>v\<in>vars (psubst \<rho> \<theta> 0 X). 0 \<le> snd v" using th by (auto simp: vars_psubst wty_def)
  ultimately show ?thesis by (simp add: wty_def)
qed

text \<open>The renamed premises of a lifted rule.\<close>

lemma aconv_psubst_lift_pre_ren:
  assumes "\<forall>x\<in>pvars p. \<theta>b x = \<theta>a x" "\<forall>x\<in>vars X0. \<theta>b x = \<theta>a (ren_ix r x)"
  shows "aconv_term (psubst \<rho> \<theta>a lev (lift_pre p (ren_term r X0))) (psubst \<rho> \<theta>b lev (lift_pre p X0))"
  using assms
proof (induction p X0 arbitrary: lev rule: lift_pre.induct)
  case (1 X0)
  have "psubst \<rho> \<theta>b lev X0 = psubst \<rho> (\<theta>a \<circ> ren_ix r) lev X0" by (rule psubst_cong) (use 1 in simp)
  then show ?case using aconv_psubst_ren_term[of \<rho> \<theta>a lev r X0] by simp
next
  case (2 c H p X0)
  have "psubst \<rho> \<theta>a lev H = psubst \<rho> \<theta>b lev H" by (rule psubst_cong) (use "2.prems"(1) in simp)
  moreover have "psubst \<rho> \<theta>a lev c = psubst \<rho> \<theta>b lev c" by (rule psubst_cong) (use "2.prems"(1) in simp)
  ultimately show ?case using "2.IH"[of lev] "2.prems" by simp
next
  case (3 c a T p X0)
  have "psubst \<rho> \<theta>a lev c = psubst \<rho> \<theta>b lev c" by (rule psubst_cong) (use "3.prems"(1) in simp)
  then show ?case using "3.IH"[of "lev + 1"] "3.prems" by simp
qed

lemma tr_list_implies_cong:
  assumes "list_all2 (\<lambda>X Y. tr X \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr Y) Xs Ys" "tr C \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr D"
  shows "tr (list_implies Xs C) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_implies Ys D)"
  using assms(1)
proof (induction rule: list_all2_induct)
  case Nil
  have "list_implies [] E = E" for E by simp
  then show ?case using assms(2) by (simp only:)
next
  case (Cons x xs y ys)
  have e: "tr (list_implies (z # zs) E) = tr implies \<degree> tr z \<degree> tr (list_implies zs E)" for z zs E by simp
  show ?case unfolding e by (intro equiv_App equiv_refl Cons.hyps(1) Cons.IH)
qed

lemma tr_psubst_rlist_abs:
  assumes "\<forall>x\<in>vars X. \<not> loose_bvar (\<theta> x) 0"
  shows "tr (psubst \<rho> \<theta> 0 (rlist_abs ps X)) = Abs_m (length ps) (tr (psubst \<rho> \<theta> 0 X))"
  using assms
proof (induction ps arbitrary: X)
  case (Cons aT ps)
  obtain a T where aT: "aT = (a, T)" by (cases aT)
  have "psubst \<rho> \<theta> 1 X = psubst \<rho> \<theta> 0 X" using psubst_closed_lev[of X \<theta> 1 \<rho>] Cons.prems by simp
  with Cons.IH[of "Abs a T X"] Cons.prems show ?case by (simp add: aT flip: Abs_m_Suc')
qed simp

lemma vars_assum_problems:
  assumes "assum_problems m A = (params, asms, concl)" "cok A"
  shows "vars A = (\<Union>X\<in>set asms. vars X) \<union> vars concl"
proof -
  obtain A' Gs where sa: "strip_assums_all [] A = (params, A')" and si: "strip_assums_imp m [] A' = (Gs, concl)"
    and asms: "asms = rev Gs"
    using assms(1) unfolding assum_problems_def
    by (cases "strip_assums_all [] A"; cases "strip_assums_imp m [] (snd (strip_assums_all [] A))") auto
  from strip_assums_all_list_forall[OF sa assms(2)] have A: "A = list_forall (rev params) A'" and cA': "cok A'"
    by auto
  have "A' = list_implies (rev Gs) concl" by (rule strip_assums_imp_list_implies[OF si cA'])
  then show ?thesis using A asms by (simp add: vars_list_implies)
qed

subsection \<open>Correctness of the proof of composition\<close>

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
    and cA: "tcert alg A" and lo: "-1 \<le> smax" and A0: "\<forall>p\<in>A. 0 \<le> snd (fst p)"
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
  define xsR where "xsR = (B, propT) # map (\<lambda>X. (X, propT)) (rev rAs) @
    concat (map (\<lambda>(t, u). [(t, tpT rmax t u), (u, tpT rmax t u)]) rtpairs)"
  have xsS': "\<forall>(X, T)\<in>set xsS. wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S"
    using wS(2) tpS by (fastforce simp: xsS_def vars_thm_def vars_list_implies)
  have xsR': "\<forall>(X, T)\<in>set xsR. wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop"
    using wR tpR by (fastforce simp: xsR_def vars_thm_def vars_list_implies P)
  have xs: "\<forall>(X, T)\<in>set (xsS @ xsR). (wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S) \<or>
      (wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop)"
    using xsS' xsR' by fastforce
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
    and W''d: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> lifted \<and> smax < snd v \<and> snd v \<le> maxidx env \<and>
      (\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u)"
    and sk1: "lifted \<longrightarrow> 0 \<le> nlift \<and> (\<forall>X\<in>set (na_As na). nlift \<le> ilength (spine_hyps X))"
    and nA: "\<exists>As0 n dps tps1. okT (newAs vl (bs_ctx sp) As0 n dps tps1) na \<and> set As0 \<subseteq> set (rev rAs) \<and>
      (\<forall>X\<in>set As0. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x) \<and>
      As0 = (if eres_flg then tl (rev rAs) else rev rAs)"
    and sk2: "lifted \<longrightarrow> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
    and rsx: "rs_typed ar A (xsS @ xsR) W' env'"
    by blast
  text \<open>The problem, as in the soundness theorem \<open>rchar_valid\<close>.\<close>
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    unfolding sp_def by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs" "bc_match ctx = match_flg"
    by (simp_all add: ctx_def)
  have sp_sel: "bs_eres sp = eres_flg" "bs_ctx sp = ctx" "bs_vl sp = vl" "bs_rAs sp = rAs" "bs_env sp = env"
    "bs_A sp = A"
    by (simp_all add: sp')
  obtain Pre As0 n dps tps1 where
    rAs': "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps"
    and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "A1o = (case Pre of [] \<Rightarrow> None | A1 # _ \<Rightarrow> Some A1)" and Pn: "Pre = [] \<longleftrightarrow> \<not> 0 < n"
    and Pe: "Pre = [] \<longleftrightarrow> \<not> eres_flg"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> 1 \<le> n \<and> n \<le> integer_of_nat (length asms) \<and>
      (rlist_abs params concl, rlist_abs params (asms ! (nat_of_integer n - 1))) \<in> set dps \<and>
      (rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
  proof -
    from its consider (res) tps1 where "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
        "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      | (eres) n asm tps1 where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
        "A1o = Some (er_A1 (eres_of sp))"
        "okT (newAs vl ctx (er_As (eres_of sp)) n
          [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      using its unfolding itsok_def sp_sel ctx_sel by blast
    then show thesis
    proof cases
      case res
      have "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
      with res show thesis
        by (intro that[of "[]" "rev rAs" 0 "[BBi]" tps1]) (simp_all add: nlift_def)
    next
      case eres
      have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
      obtain A1 As where rA: "rev rAs = A1 # As"
        using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
      obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
        by (cases "assum_problems (nlift + 1) A1")
      have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
        using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
      have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
      have "ilength asms \<le> nlift + 1"
        by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
      moreover have nl: "n \<le> ilength asms" using eres(2,3) er(2)
        by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
      ultimately have nle: "n \<le> nlift + 1" by simp
      show thesis
      proof (rule that[of "[A1]" As n "[BBi, (rlist_abs params concl, rlist_abs params asm)]" tps1])
        show "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
          using eres(7) er by simp
        show "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
          using eres(5) er by (auto simp: eres_prob_def sp' ctx_sel)
        show "A1o = (case [A1] of [] \<Rightarrow> None | A1 # _ \<Rightarrow> Some A1)" using eres(6) er by simp
        show "\<exists>params' asms' concl'. eres_flg \<and> [A1] = [A1'] \<and>
            assum_problems (nlift + 1) A1' = (params', asms', concl') \<and> 1 \<le> n \<and>
            n \<le> integer_of_nat (length asms') \<and>
            (rlist_abs params' concl', rlist_abs params' (asms' ! (nat_of_integer n - 1))) \<in>
              set [BBi, (rlist_abs params concl, rlist_abs params asm)] \<and>
            (rlist_abs params' (asms' ! (nat_of_integer n - 1)), rlist_abs params' concl') \<in> set tus"
          if "A1' \<in> set [A1]" for A1'
          using that eres(1,2,4,5) ap er nl by (auto simp: eres_prob_def ilength_eq)
      qed (use rA eres(1,2) nle cnt in auto)
    qed
  qed
  have nnn: "na_n na = n" by (rule newAs_na_ren(2)[OF na])
  have flat: "list_all2 (\<lambda>A1 A'. if flatten then ok (flatten_params vl n A1) A' else A1 = A') (na_oldAs na) (na_As na)"
    using newAs_cases(1)[OF na] by (simp add: ctx_sel)
  have renc: "(na_ren na = None \<and> na_oldAs na = As0) \<or> (lifted \<and>
      na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0) \<and>
      na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0)"
    using newAs_na_ren(1)[OF na] by (simp add: ctx_sel)
  have As0eq: "As0 = (if eres_flg then tl (rev rAs) else rev rAs)"
    using rAs' Pe pre by (cases Pre) auto
  from nA obtain As0' n' dps' tps1' where "As0' = (if eres_flg then tl (rev rAs) else rev rAs)"
    and "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x"
    by blast
  with As0eq have rnt: "\<forall>X\<in>set As0. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x"
    by simp
  text \<open>The proof is computed without warnings or exceptions.\<close>
  have pe: "penv_inv alg ar W'' env'" by (rule pinvD(1)[OF pi''])
  have swf: "swf_env ar env'" by (rule penv_inv_swf_env[OF pe])
  have tiE: "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi'])
  note acE = tinv_tacyc[OF tiE] and tcE = tinv_tcons_env[OF tiE]
  have etE: "\<forall>U\<in>etys env'. tcons (tyenv env') U" using pinvD(3)[OF pi'] tyw_tcons[OF tiE] by blast
  have tcA: "tcons (tyenv env') U" if "tvars U \<subseteq> A" for U using that tinv_tcons[OF tiE] by blast
  define rp' where "rp' = ren_prf (na_ren na) rprf"
  have rw': "prf_all (ann0 A) (tyA ar A) rp'" and rp'0: "prf_vars rp' = {}"
    using ren_prf_props[OF rw rp0] by (simp_all add: rp'_def)
  have sA: "prf_all (ann_ok_env env') (tcons (tyenv env')) sprf"
    by (rule prf_all_mono[OF sw]) (auto intro: ann0_ann_ok_env[OF _ pi'] tcA simp: tyA_def)
  have rA: "prf_all (ann_ok_env env') (tcons (tyenv env')) rp'"
    by (rule prf_all_mono[OF rw']) (auto intro: ann0_ann_ok_env[OF _ pi'] tcA simp: tyA_def)
  have normBA: "\<forall>X\<in>set (Bs @ na_As na). \<exists>X'. ok (norm_term env' X) X'"
    using BC As wtprop_norm_ok[OF pi'] wtprop_norm_ok[OF pi''] by auto
  have lold: "length (na_oldAs na) = length (na_As na)" using list_all2_lengthD[OF flat] .
  have A1oN: "A1o = None \<Longrightarrow> \<not> 0 < na_n na" using A1o Pn nnn by (cases Pre) auto
  let ?core = "core_prf flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1)"
  have core: "bicompose_core env' flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) sprf q =
      returnP (?core sprf q)" for q
    by (rule bicompose_core_eq[OF normBA lold A1oN])
  have "br_env r = env' \<and> br_A r = A1o \<and> br_newas r = na" using ad by (cases rule: addth_cases) auto
  then have rbr: "br_env r = env'" "br_A r = A1o" "br_newas r = na" by simp_all
  have "\<exists>p. bicompose_proof env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) rp' sprf =
      returnP p \<and>
      (env_is_empty env' \<and> p = ?core sprf rp' \<or>
       \<not> env_is_empty env' \<and> above env' smax \<and>
         (\<exists>rp''. p = ?core sprf rp'' \<and> prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp'') \<or>
       \<not> env_is_empty env' \<and> \<not> above env' smax \<and> prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p)"
  proof (cases "env_is_empty env'")
    case True
    then show ?thesis by (simp add: bicompose_proof_def core)
  next
    case ne: False
    show ?thesis
    proof (cases "above env' smax")
      case True
      from norm_proof_remove_types_ok[OF acE tcE etE rA] obtain rp'' where
        "norm_proof_remove_types env' rp' = returnP rp''" "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
        by blast
      with ne True show ?thesis by (auto simp: bicompose_proof_def core)
    next
      case False
      have "prf_all (ann_ok_env env') (tcons (tyenv env')) (?core sprf rp')"
        by (rule prf_all_core_prf[OF sA rA ann_ok_env_Bound])
      from norm_proof_remove_types_ok[OF acE tcE etE this] obtain p where
        "norm_proof_remove_types env' (?core sprf rp') = returnP p"
        "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
        by blast
      with ne False show ?thesis by (auto simp: bicompose_proof_def core)
    qed
  qed
  then obtain p where bp: "bicompose_proof env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1)
      rp' sprf = returnP p"
    and pc: "env_is_empty env' \<and> p = ?core sprf rp' \<or>
       \<not> env_is_empty env' \<and> above env' smax \<and>
         (\<exists>rp''. p = ?core sprf rp'' \<and> prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp'') \<or>
       \<not> env_is_empty env' \<and> \<not> above env' smax \<and> prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
    by blast
  text \<open>The new theorem is typed by \<open>tctx env' W''\<close> and its variables have non-negative indices.\<close>
  have pi: "pinv alg ar A W0 env (dps_of tus)"
  proof -
    from its consider (res) "\<not> eres_flg" "tus = bc_dpairs (bs_ctx sp)"
      | (eres) n asm where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
      unfolding itsok_def sel by blast
    then show ?thesis
    proof cases
      case res
      with pa show ?thesis by (simp add: pinv_allW_def sel)
    next
      case eres
      then have "asm \<in> set (asms_of sp)" by (simp add: integer_reps)
      with pa eres(1,5) show ?thesis by (simp add: pinv_allW_def sel)
    qed
  qed
  from ue obtain s0 xs0 where u0: "unifiers alg env tus = Some (Ok s0)" "evals cfg s0 xs0"
    "El_R env' tps \<in> set xs0"
    by (auto simp: uelem_def)
  have fresh: "v \<notin> fst ` bvps env' \<and> (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
    if "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u" "snd v \<le> maxidx env" for v
  proof -
    have v: "vt_lookup (tenv env) v = None" "v \<notin> fst ` bvps env"
      using te(1) by (auto simp: bvps_def vt_is_empty_lookup)
    from unifiers_fresh[OF cfg finA pi u0 v that] unifiers_fresh_tps[OF cfg finA pi u0 v that]
    show ?thesis by blast
  qed
  have imp: "tyA ar A imp_type"
    using state(1) by (auto simp: wt_thm_def wt_term_def tys_list_implies)
  have ib: "\<forall>X\<in>insert C (set Bs). ibelow smax X" using state(2) by simp
  have ag: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> bc_smax (bs_ctx sp) < snd v \<and> v \<notin> fst ` bvps env' \<and>
      (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
  proof (intro allI impI)
    fix v assume "W'' v \<noteq> W' v"
    with W''d have "smax < snd v" "snd v \<le> maxidx env" "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u"
      by blast+
    with fresh[of v] show "bc_smax (bs_ctx sp) < snd v \<and> v \<notin> fst ` bvps env' \<and>
        (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
      by (simp add: sel)
  qed
  have BC': "\<forall>X\<in>insert (bc_C (bs_ctx sp)) (set (bc_Bs (bs_ctx sp))). wtprop A W' env' X \<and> ibelow (bc_smax (bs_ctx sp)) X"
    using BC ib by (simp add: sel)
  have sk: "bc_lifted (bs_ctx sp) \<Longrightarrow> 0 \<le> bc_nlift (bs_ctx sp) \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift (bs_ctx sp))) (spine_hyps X)). ibelow (bc_smax (bs_ctx sp)) H)"
    using sk1 sk2 by (simp add: sel)
  have imp': "tyA ar (tvars_env (tyenv env') \<union> A) imp_type" using tyA_mono[OF imp] by blast
  note at = addth_typed[OF ad pi' tp BC' pi'' As sk ag imp']
  have wtr: "wt_thm ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') (br_tpairs r) (br_prop r)"
    by (rule at(1))
  have tyr: "thm_typeds ar 0 (UNIV \<union> env_sorts (tyenv (br_env r)))
      \<lparr>th_maxidx = maxidx (br_env r), th_tpairs = br_tpairs r, th_prop = br_prop r\<rparr>"
    by (rule bicompose_aux_thm_typed(1)[OF ok res cfg finA state rule A(1) _ A(3) ns er fl vl _ lo _ _ cA])
      (use A(2) A0 nn in auto)
  have nnr: "\<forall>x\<in>vars_thm (br_tpairs r) (br_prop r). 0 \<le> snd x" using tyr by (simp add: thm_typeds_def)
  have wtyr: "wty (tctx env' W'') [] X T" if "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') X T"
    "vars X \<subseteq> vars_thm (br_tpairs r) (br_prop r)" for X T
    using that nnr by (auto simp: wty_def wt_term_def)
  have "prf_valid alg ar (tctx env' W'') H (br_tpairs r) p (br_prop r)"
    unfolding prf_valid_def
  proof (intro allI impI)
    fix V' \<rho> \<theta>
    assume g: "ginst alg ar \<rho>" and ty: "inst_typed (tctx env' W'') V' [] \<rho> \<theta>"
      and sol: "\<forall>(t, u)\<in>set (br_tpairs r). tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
    text \<open>An instance of all variables, and its extension through the unifier.\<close>
    define \<theta>0 where "\<theta>0 x = (if 0 \<le> snd x then \<theta> x else Free STR ''u'' (tsubst \<rho> (tctx env' W'' x)))" for x
    have ty0x: "wty V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W'' x))" for x
    proof (cases "0 \<le> snd x")
      case True
      then show ?thesis using inst_typedD[OF ty True] by (simp add: \<theta>0_def)
    next
      case False
      then show ?thesis by (simp add: \<theta>0_def wty_def has_type.Free)
    qed
    have ty0: "\<forall>x. wty V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W'' x))" using ty0x by blast
    have cl0x: "proper (\<theta>0 x)" "\<not> loose_bvar (\<theta>0 x) 0" for x
    proof -
      have h: "has_type V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W'' x))" using ty0x[of x] by (simp add: wty_def)
      show "proper (\<theta>0 x)" by (rule has_type_proper[OF h])
      show "\<not> loose_bvar (\<theta>0 x) 0" using has_type_loose_bvar[OF h] by simp
    qed
    have cl0: "\<forall>x. proper (\<theta>0 x) \<and> \<not> loose_bvar (\<theta>0 x) 0" using cl0x by blast
    obtain \<rho>' \<sigma>' \<theta>' where ie: "iext env' \<rho> (isubst \<theta>0) \<rho>' \<sigma>'" and g': "ginst alg ar \<rho>'"
      and cl': "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0"
      and unb\<theta>: "\<And>x. vt_lookup (tenv env') x = None \<Longrightarrow> \<theta>' x = \<theta>0 x"
      and tyc: "\<And>T. tcons (tyenv env') T \<Longrightarrow> tsubst \<rho> (tnorm (tyenv env') T) = tsubst \<rho>' T"
      and smeq: "\<And>t. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t)"
      and tyb: "\<And>V''. \<forall>x. wty V'' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W'' x)) \<Longrightarrow>
        \<forall>x. wty V'' [] (\<theta>' x) (tsubst \<rho>' (W'' x))"
      by (rule inst_bridge[OF pi'' g cl0]) blast
    have tyall': "\<forall>x. wty V' [] (\<theta>' x) (tsubst \<rho>' (W'' x))" by (rule tyb[OF ty0])
    then have ty': "inst_typed W'' V' [] \<rho>' \<theta>'" by (simp add: inst_typed_def)
    from ie have gs': "gsol alg ar (tyenv env') \<rho>'" and ps: "psat (\<sigma>' \<circ> cren \<rho>') env'"
      and agT: "\<And>v S. vt_lookup (tyenv env') v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
      unfolding iext_def by blast+
    have cl'x: "proper (\<theta>' x)" "\<not> loose_bvar (\<theta>' x) 0" for x using cl' by blast+
    have eq0: "psubst \<rho> \<theta>0 l t = psubst \<rho> \<theta> l t" if "\<forall>x\<in>vars t. 0 \<le> snd x" for l t
      by (rule psubst_cong) (use that in \<open>simp add: \<theta>0_def\<close>)
    have tr0: "tr (psubst \<rho> \<theta>0 0 t) = sm \<rho> (isubst \<theta>0) t" for t
      by (rule tr_psubst_sm) (use cl0x in blast)
    have tr': "tr (psubst \<rho>' \<theta>' 0 t) = sm \<rho>' (isubst \<theta>') t" for t
      by (rule tr_psubst_sm) (use cl'x in blast)
    text \<open>The flex-flex pairs of the unifier and the problem are solved.\<close>
    have sol0: "\<forall>(t, u)\<in>set (br_tpairs r). sm \<rho> (isubst \<theta>0) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> (isubst \<theta>0) u"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set (br_tpairs r)"
      have v: "\<forall>x\<in>vars t. 0 \<le> snd x" "\<forall>x\<in>vars u. 0 \<le> snd x" using nnr tu by (auto simp: vars_thm_def)
      have "tr (psubst \<rho> \<theta>0 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 u)" using sol tu eq0[OF v(1)] eq0[OF v(2)] by auto
      then show "sm \<rho> (isubst \<theta>0) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> (isubst \<theta>0) u" by (simp add: tr0)
    qed
    have tps_wf: "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u" using tp ptpok_swf by fast
    have tsol: "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
      by (rule addth_tpairs[OF ad ie rigid_isubst swf tps_wf]) (use sol0 in auto)
    have dsol: "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
    proof -
      have "\<forall>(t, u)\<in>set tps. mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma>' \<circ> cren \<rho>') (tr u)"
        using tsol by (simp add: sm_def mk_subst_inst)
      with pu ps have "dsolved_all (\<sigma>' \<circ> cren \<rho>') (dps_of tus)" by (auto simp: punifier_def)
      with that have "dsolved (\<sigma>' \<circ> cren \<rho>') ([], t, u)" by fastforce
      then show ?thesis by (simp add: dsolved_Nil unifies_def sm_def mk_subst_inst)
    qed
    have dsol': "tr (psubst \<rho>' \<theta>' 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 u)" if "(t, u) \<in> set tus" for t u
    proof -
      have "tr (psubst \<rho>' \<theta>' 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t" by (rule equiv_sym[OF smeq])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" by (rule dsol[OF that])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 u)" by (rule smeq)
      finally show ?thesis .
    qed
    have tcW: "tcons (tyenv env') (W x)" for x
    proof -
      have "tyA ar A (W x)" using A(3) by blast
      then show ?thesis using tcA by (simp add: tyA_def)
    qed
    have rs: "typed env' W' [] X T" if "(X, T) \<in> set (xsS @ xsR)" for X T
      using rsx that by (auto simp: rs_typed_def)
    text \<open>The instance of the proof state.\<close>
    define RS where "RS = vars_thm stpairs (list_implies (Bs @ [Bi]) C)"
    have RSs: "snd x \<le> smax" if "x \<in> RS" for x
      using that state(1,2) by (fastforce simp: RS_def vars_thm_def ibelow_def wt_thm_def wt_term_def below_def)
    have agS: "0 \<le> snd (id x) \<and> tctx env' W'' (id x) = tnorm (tyenv env') (W x)" if "x \<in> RS" "0 \<le> snd x" for x
    proof -
      have "W'' x = W' x" using W''d RSs[OF that(1)] by fastforce
      then have e: "tctx env' W'' x = tctx env' W' x" by (simp add: vtyp_def split: option.splits)
      have "\<exists>X T U. x \<in> vars X \<and> typed env' W' [] X T \<and> has_type W [] X U"
      proof -
        from that(1) consider X where "X \<in> insert C (set Bs)" "x \<in> vars X" | "x \<in> vars Bi"
          | t u where "(t, u) \<in> set stpairs" "x \<in> vars t \<or> x \<in> vars u"
          by (auto simp: RS_def vars_thm_def vars_list_implies)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using BC wS by (fastforce simp: wtprop_def wt_term_def)
        next
          case 2
          then show ?thesis using rs[of Bi propT] wS(2) by (fastforce simp: xsS_def wt_term_def)
        next
          case 3
          then show ?thesis using rs[of t "tpT smax t u"] rs[of u "tpT smax t u"] tpS[OF 3(1)]
            by (fastforce simp: xsS_def wt_term_def)
        qed
      qed
      then obtain X T U where "x \<in> vars X" "typed env' W' [] X T" "has_type W [] X U" by blast
      from typed_tctx_agree[OF this(2,3,1)] e that(2) show ?thesis by simp
    qed
    define \<theta>S where "\<theta>S = (\<lambda>x. if x \<in> RS then \<theta>' (id x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyS: "inst_typed W V' [] \<rho>' \<theta>S"
      unfolding \<theta>S_def by (rule inst_typed_transfer[OF ty' pi'' gs' agS]) (simp_all add: tcW)
    have psS: "psubst \<rho>' \<theta>S l X = psubst \<rho>' \<theta>' l X" if "vars X \<subseteq> RS" for l X
      by (rule psubst_cong) (use that in \<open>auto simp: \<theta>S_def\<close>)
    have solS: "tr (psubst \<rho>' \<theta>S 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>S 0 u)" if "(t, u) \<in> set stpairs" for t u
    proof -
      have "vars t \<subseteq> RS" "vars u \<subseteq> RS" using that by (auto simp: RS_def vars_thm_def)
      moreover have "(t, u) \<in> set tus" using that tus by auto
      ultimately show ?thesis using dsol' by (simp add: psS)
    qed
    have Sok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 sprf)
        (list_implies (map (psubst \<rho>' \<theta>' 0) Bs @ [psubst \<rho>' \<theta>' 0 Bi]) (psubst \<rho>' \<theta>' 0 C))"
    proof -
      have "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>S 0 sprf) (psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C))"
        by (rule prf_validD[OF sv g' tyS solS])
      moreover have "prf_inst \<rho>' \<theta>S 0 sprf = prf_inst \<rho>' \<theta>' 0 sprf" by (rule prf_inst_cong) (simp add: sp0)
      moreover have "psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C) = psubst \<rho>' \<theta>' 0 (list_implies (Bs @ [Bi]) C)"
        by (rule psS) (auto simp: RS_def vars_thm_def)
      ultimately show ?thesis by (simp add: psubst_list_implies')
    qed
    text \<open>The instance of the rule, through the renaming of its new premises.\<close>
    define RR where "RR = vars_thm rtpairs rprop"
    define rn where "rn = ren_of na smax"
    have RRn: "0 \<le> snd x" if "x \<in> RR" for x using that nn by (auto simp: RR_def)
    have rnidx: "snd (rn x) = snd x" for x by (simp add: rn_def ren_of_def ren_ix_def split: option.splits)
    have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
      using lifted_over_lifted_rule[OF rule(2) sp1] by simp
    have rnid: "rn x = x" if "snd x \<le> smax \<or> \<not> lifted \<or> (\<exists>(t, u)\<in>set dps. fst x \<in> fst ` vars t) \<or>
        (\<exists>(t, u)\<in>set rtpairs. fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u)" for x
    proof -
      from renc consider "na_ren na = None"
        | "lifted" "na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0)" by (elim disjE conjE) auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis by (simp add: rn_def ren_of_def)
      next
        case 2
        show ?thesis
        proof (rule ccontr)
          assume "rn x \<noteq> x"
          then have sx: "smax < snd x"
            and rnn: "ren_name (fst (rename_bvs dps (rtpairs @ tps1) Bi As0)) (fst x) \<noteq> fst x"
            using 2(2) by (auto simp: rn_def ren_of_def ren_ix_def prod_eq_iff split: if_splits)
          from rename_bvs_unknowns[OF rnn]
          have a: "\<forall>(t, u)\<in>set dps. fst x \<notin> fst ` vars t"
            and b: "\<forall>(t, u)\<in>set (rtpairs @ tps1). fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u" .
          from that show False
          proof (elim disjE)
            assume "snd x \<le> smax"
            with sx show False by simp
          next
            assume "\<not> lifted"
            with 2(1) show False by simp
          next
            assume "\<exists>(t, u)\<in>set dps. fst x \<in> fst ` vars t"
            with a show False by blast
          next
            assume "\<exists>(t, u)\<in>set rtpairs. fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u"
            then obtain t u where "(t, u) \<in> set rtpairs" "fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u" by blast
            with b show False by fastforce
          qed
        qed
      qed
    qed
    have W'x: "W'' x = W' x" if "snd x \<le> smax \<or> \<not> lifted \<or> (\<exists>(t, u)\<in>set tus. x \<in> vars t \<or> x \<in> vars u)" for x
      using W''d that by fastforce
    text \<open>The variables of the rule outside its new premises are neither renamed nor retyped.\<close>
    have keep: "rn x = x \<and> W'' x = W' x"
      if "x \<in> vars B \<or> (\<exists>X\<in>set Pre. x \<in> vars X) \<or> (\<exists>(t, u)\<in>set rtpairs. x \<in> vars t \<or> x \<in> vars u)" for x
    proof (cases "snd x \<le> smax \<or> \<not> lifted")
      case True
      then show ?thesis using rnid W'x by blast
    next
      case False
      then have sx: "smax < snd x" and lf: lifted by auto
      from lr[OF lf] obtain p Bi0 As1 B0 where ls: "lsplit Bi = (p, Bi0)" and rA: "rev rAs = map (lift_pre p) As1"
        and B: "B = lift_pre p B0" by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
        by auto
      have ibBi: "ibelow smax Bi" using state(2) by simp
      have pv: "snd y \<le> smax" if "y \<in> pvars p" for y
        using that ibBi by (auto simp: Bi ibelow_def vars_lift_pre)
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)" using lf by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      from that consider "x \<in> vars B" | X where "X \<in> set Pre" "x \<in> vars X"
        | t u where "(t, u) \<in> set rtpairs" "x \<in> vars t \<or> x \<in> vars u"
        by blast
      then show ?thesis
      proof cases
        case 1
        have "x \<notin> pvars p" using pv sx by fastforce
        with 1 have "x \<in> vars B0" by (auto simp: B vars_lift_pre)
        then have "x \<in> vars (fst BBi)" by (simp add: BBi vars_abs_pre)
        moreover have "BBi \<in> set tus" using tus by auto
        ultimately show ?thesis using rnid[of x] W'x[of x] dps by (cases BBi) force
      next
        case 2
        from pre[OF 2(1)] obtain params asms concl where er: "eres_flg" "Pre = [X]"
          and ap: "assum_problems (nlift + 1) X = (params, asms, concl)" and n1: "1 \<le> n"
          and cd: "(rlist_abs params concl, rlist_abs params (asms ! (nat_of_integer n - 1))) \<in> set dps"
          and ac: "(rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
          by blast
        have cX: "cok X" using rule(1) 2(1) rAs' by (auto simp: wt_thm_def P)
        from rA rAs' er(2) obtain X1 where X: "X = lift_pre p X1" by (cases As1) auto
        have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using er(1) by (simp add: nlift_def)
        have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ ap[unfolded X]] Bi cnt n(4) by simp
        then have "\<forall>A\<in>set asms. \<forall>y\<in>vars A. snd y \<le> smax" using pv vars_phyps by blast
        with vars_assum_problems[OF ap cX] 2(2) sx have "x \<in> vars concl" by fastforce
        then show ?thesis using rnid[of x] W'x[of x] cd ac by (fastforce simp: vars_rlist_abs)
      next
        case 3
        then show ?thesis using rnid[of x] W'x[of x] tus by fastforce
      qed
    qed
    have agW': "tctx env' W' x = tnorm (tyenv env') (W x)" if "x \<in> RR" for x
    proof -
      have "\<exists>X T U. x \<in> vars X \<and> typed env' W' [] X T \<and> has_type W [] X U"
      proof -
        from that consider "x \<in> vars B" | X where "X \<in> set (rev rAs)" "x \<in> vars X"
          | t u where "(t, u) \<in> set rtpairs" "x \<in> vars t \<or> x \<in> vars u"
          by (auto simp: RR_def vars_thm_def vars_list_implies P)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using rs[of B propT] wR(2) by (fastforce simp: xsR_def wt_term_def)
        next
          case 2
          then show ?thesis using rs[of X propT] wR(1) by (fastforce simp: xsR_def wt_term_def)
        next
          case 3
          then show ?thesis using rs[of t "tpT rmax t u"] rs[of u "tpT rmax t u"] tpR[OF 3(1)]
            by (fastforce simp: xsR_def wt_term_def)
        qed
      qed
      then obtain X T U where "x \<in> vars X" "typed env' W' [] X T" "has_type W [] X U" by blast
      from typed_tctx_agree[OF this(2,3,1)] show ?thesis .
    qed
    have agR: "0 \<le> snd (rn x) \<and> tctx env' W'' (rn x) = tnorm (tyenv env') (W x)" if "x \<in> RR" "0 \<le> snd x" for x
    proof -
      have "tctx env' W'' (rn x) = tctx env' W' x"
      proof (cases "\<exists>X\<in>set As0. x \<in> vars X")
        case True
        with rnt show ?thesis by (auto simp: rn_def)
      next
        case False
        with that(1) have "x \<in> vars B \<or> (\<exists>X\<in>set Pre. x \<in> vars X) \<or> (\<exists>(t, u)\<in>set rtpairs. x \<in> vars t \<or> x \<in> vars u)"
          using rAs' by (auto simp: RR_def vars_thm_def vars_list_implies P)
        from keep[OF this] show ?thesis by (simp add: vtyp_def split: option.splits)
      qed
      with agW'[OF that(1)] rnidx that(2) show ?thesis by simp
    qed
    define \<theta>R where "\<theta>R = (\<lambda>x. if x \<in> RR then \<theta>' (rn x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyR: "inst_typed W V' [] \<rho>' \<theta>R"
      unfolding \<theta>R_def by (rule inst_typed_transfer[OF ty' pi'' gs' agR]) (simp_all add: tcW)
    have psR: "psubst \<rho>' \<theta>R l X = psubst \<rho>' \<theta>' l X" if "vars X \<subseteq> RR" "\<forall>x\<in>vars X. rn x = x" for l X
      by (rule psubst_cong) (use that in \<open>auto simp: \<theta>R_def\<close>)
    have clR: "\<not> loose_bvar (\<theta>R x) 0" for x using cl'x by (simp add: \<theta>R_def)
    have solR: "tr (psubst \<rho>' \<theta>R 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 u)" if "(t, u) \<in> set rtpairs" for t u
    proof -
      have v: "vars t \<subseteq> RR" "vars u \<subseteq> RR" using that by (auto simp: RR_def vars_thm_def)
      have k: "\<forall>x\<in>vars t. rn x = x" "\<forall>x\<in>vars u. rn x = x" using that keep by blast+
      have "psubst \<rho>' \<theta>R 0 t = psubst \<rho>' \<theta>' 0 t" "psubst \<rho>' \<theta>R 0 u = psubst \<rho>' \<theta>' 0 u"
        using psR[OF v(1) k(1)] psR[OF v(2) k(2)] by simp_all
      moreover have "(t, u) \<in> set tus" using that tus by auto
      ultimately show ?thesis using dsol' by simp
    qed
    have Rok0: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>R 0 rprf) (psubst \<rho>' \<theta>R 0 rprop)"
      by (rule prf_validD[OF rv g' tyR solR])
    have ptR: "prf_inst \<rho>' \<theta>R 0 rprf = prf_inst \<rho>' \<theta>'' 0 rprf" for \<theta>'' by (rule prf_inst_cong) (simp add: rp0)
    have Rok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 rp') (psubst \<rho>' \<theta>R 0 rprop)"
    proof (cases "na_ren na")
      case None
      then show ?thesis using Rok0 ptR[of \<theta>'] by (simp add: rp'_def ren_prf_def)
    next
      case (Some rr)
      have "prf_aeq (prf_inst \<rho>' (\<theta>' \<circ> ren_ix rr) 0 rprf) (prf_inst \<rho>' \<theta>' 0 (map_proof_terms (ren_term rr) id rprf))"
      proof (rule map_proof_terms_ren_inst)
        show "\<forall>x. proper (\<theta>' x)" using cl'x by blast
        show "\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>y\<in>vars (\<theta>' x). 0 \<le> snd y)" using tyall' by (auto simp: wty_def)
        show "anns_proper rprf" by (rule anns_proper_prf_all[OF rw ann0_proper])
      qed (simp_all add: rp0)
      with Rok0 ptR[of "\<theta>' \<circ> ren_ix rr"] Some show ?thesis
        by (auto simp: rp'_def ren_prf_def intro: prf_ok_aeq)
    qed
    text \<open>The conclusion of the rule and the subgoal have equivalent instances.\<close>
    have Bkeep: "psubst \<rho>' \<theta>R 0 B = psubst \<rho>' \<theta>' 0 B"
      using keep by (intro psR) (auto simp: RR_def vars_thm_def vars_list_implies P)
    have BBi_eq: "tr (psubst \<rho>' \<theta>R 0 B) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 Bi)"
    proof (cases lifted)
      case False
      then have "BBi = (B, Bi)" by (simp add: BBi_def)
      with dsol'[of B Bi] tus Bkeep show ?thesis by auto
    next
      case True
      from lr[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
        by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      from dsol'[of "abs_pre p B0" "abs_pre p Bi0"] tus BBi
      have "sm \<rho>' (isubst \<theta>') (abs_pre p B0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' (isubst \<theta>') (abs_pre p Bi0)" by (simp add: tr')
      from sm_lift_pre_equiv[OF this] Bkeep show ?thesis by (simp add: tr' B Bi)
    qed
    text \<open>The instance of the new theorem and its relation to the instance through the unifier.\<close>
    have wS': "\<forall>X\<in>set Bs. wfp ar X" "wfp ar C" using BC by (auto simp: wtprop_def)
    have wN: "\<forall>X\<in>set (na_As na). wfp ar X" using As by (auto simp: wtprop_def)
    have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax C" using state(2) by simp_all
    note rg = rigid_isubst[of \<theta>0] and clI = closed_isubst[OF cl0]
    obtain Hs C' where bprop: "br_prop r = list_implies Hs C'"
      and relH: "list_all2 (\<lambda>X Y. sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
      and relC: "sm \<rho> (isubst \<theta>0) C' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' C"
    proof -
      note obt = that
      have rel_unb: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Xs Xs" if "\<forall>X\<in>set Xs. wfp ar X \<and> unb env' X" for Xs
        using that by (intro list.rel_refl_strong) (simp add: inst_rel_unb[OF ie rg clI])
      have rel_norm: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Xs Ys"
        if "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y) Xs Ys" "\<forall>X\<in>set Xs. wfp ar X" for Xs Ys
      proof -
        have "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y \<and> X \<in> set Xs) Xs Ys"
          using that(1) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
        then show ?thesis by (rule list_all2_mono) (use that(2) inst_rel_norm[OF ie rg clI swf] in blast)
      qed
      have unbS: "\<forall>X\<in>set Bs. unb env' X" "unb env' C" if "above env' smax"
        using iS above_unb[OF that] by auto
      have fin: "thesis" if h1: "br_prop r = list_implies Hs C'"
        and h2: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
        and h3: "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'"
        for Hs C'
      proof (rule obt[OF h1])
        show "list_all2 (\<lambda>X Y. sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
          using h2 by (rule list_all2_mono) simp
        show "sm \<rho> (isubst \<theta>0) C' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' C" using h3 by simp
      qed
      from ad show thesis
      proof (cases rule: addth_cases)
        case empty
        have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) (Bs @ na_As na)"
          using wS' wN unb_empty[OF empty(1)] by (intro rel_unb) auto
        moreover have "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C"
          by (rule inst_rel_unb[OF ie rg clI wS'(2) unb_empty[OF empty(1)]])
        ultimately show thesis by (rule fin[rotated]) (simp add: empty(2) sel)
      next
        case (norm ntps Hs C')
        from norm(4) consider (lifted) As' where "above env' smax" "lifted" "C' = C" "Hs = Bs @ As'"
            "list_all2 (\<lambda>X X'. okT (norm_term_skip env' nlift X) X') (na_As na) As'"
          | (above) As' where "above env' smax" "C' = C" "Hs = Bs @ As'"
            "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (na_As na) As'"
          | (all) "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (Bs @ na_As na) Hs" "ok (norm_term env' C) C'"
          unfolding sel by blast
        then have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs \<and> inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'"
        proof cases
          case lifted
          from sk1 sk2 lifted(2) have n0: "0 \<le> nlift"
            and h: "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H"
            by auto
          have sku: "skip_unb env' nlift X" if "X \<in> set (na_As na)" for X
            by (rule skip_unb_take[OF n0]) (use h that above_unb[OF lifted(1)] in blast)
          have "list_all2 (\<lambda>X X'. okT (norm_term_skip env' nlift X) X' \<and> X \<in> set (na_As na)) (na_As na) As'"
            using lifted(5) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
          then have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (na_As na) As'"
            by (rule list_all2_mono) (use wN sku inst_rel_skip[OF ie rg clI swf] in blast)
          moreover have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Bs Bs"
            using wS' unbS[OF lifted(1)] by (intro rel_unb) auto
          ultimately show ?thesis
            using lifted inst_rel_unb[OF ie rg clI wS'(2) unbS(2)[OF lifted(1)]] by (simp add: list_all2_appendI)
        next
          case above
          have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (na_As na) As'" by (rule rel_norm[OF above(4) wN])
          moreover have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Bs Bs"
            using wS' unbS[OF above(1)] by (intro rel_unb) auto
          ultimately show ?thesis
            using above inst_rel_unb[OF ie rg clI wS'(2) unbS(2)[OF above(1)]] by (simp add: list_all2_appendI)
        next
          case all
          have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
            by (rule rel_norm[OF all(1)]) (use wS' wN in auto)
          with inst_rel_norm[OF ie rg clI swf wS'(2) all(2)] show ?thesis by simp
        qed
        then have rr: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
          "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'" by blast+
        show thesis by (rule fin[OF _ rr]) (simp add: norm(2))
      qed
    qed
    define Ns where "Ns = map (psubst \<rho> \<theta>0 0) Hs"
    have lHs: "length Hs = length Bs + length (na_As na)" using list_all2_lengthD[OF relH] by simp
    have rel_tr: "tr (psubst \<rho> \<theta>0 0 Y) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 X)"
      if "sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X" for X Y
    proof -
      have "tr (psubst \<rho> \<theta>0 0 Y) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X" using that by (simp add: tr0)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 X)" by (rule smeq)
      finally show ?thesis .
    qed
    have relN: "tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 ((Bs @ na_As na) ! j))" if "j < length Hs" for j
      using rel_tr list_all2_nthD2[OF relH that] that by (simp add: Ns_def)
    text \<open>Typing of the instance of the new theorem.\<close>
    have tyr0: "inst_typed (tctx env' W'') V' [] \<rho> \<theta>0" using ty0 by (simp add: inst_typed_def)
    have wtP: "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') (br_prop r) propT"
      using wtr by (simp add: wt_thm_def)
    have "wty (tctx env' W'') [] (br_prop r) propT" by (rule wtyr[OF wtP]) (simp add: vars_thm_def)
    from wty_psubst[OF this tyr0] have wtyP: "wty V' [] (psubst \<rho> \<theta>0 0 (br_prop r)) propT" by simp
    have wtyN: "\<forall>N\<in>set Ns. wty V' [] N propT" "wty V' [] (psubst \<rho> \<theta>0 0 C') propT"
      using wty_list_implies[OF wtyP[unfolded bprop psubst_list_implies']] by (auto simp: Ns_def)
    have wtyR: "wty V' [] (psubst \<rho>' \<theta>R 0 X) propT" if "X \<in> set (rev rAs)" for X
    proof -
      have "wty W [] X propT"
        using wR(1) that nn by (auto simp: wty_def wt_term_def vars_thm_def vars_list_implies P)
      from wty_psubst[OF this tyR] show ?thesis by simp
    qed
    have cokR: "cok X" if "X \<in> set (rev rAs)" for X using rule(1) that by (auto simp: wt_thm_def P)
    text \<open>The premise of the rule proved by an assumption.\<close>
    have pre_ok: "(map (psubst \<rho>' \<theta>R 0) Pre = [] \<and> \<not> 0 < na_n na) \<or>
      (\<exists>A1 iA1. map (psubst \<rho>' \<theta>R 0) Pre = [iA1] \<and> 0 < na_n na \<and> A1o = Some A1 \<and>
        prf_ok V' H [] (rev Ns) (mk_asm_prf A1 (na_n na) (nlift + 1)) iA1)"
    proof (cases Pre)
      case Nil
      then show ?thesis using Pn nnn by simp
    next
      case (Cons A1 Pre')
      then have A1: "A1 \<in> set Pre" by simp
      from pre[OF A1] obtain params asms concl where er: "eres_flg" "Pre = [A1]"
        and ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and n1: "1 \<le> n" "n \<le> integer_of_nat (length asms)"
        and ac: "(rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
        by blast
      have A1r: "A1 \<in> set (rev rAs)" using rAs' er(2) by simp
      have vA1: "vars A1 \<subseteq> RR" using A1r by (auto simp: RR_def vars_thm_def vars_list_implies P)
      have kA1: "\<forall>x\<in>vars A1. rn x = x" using keep A1 by blast
      let ?asm = "asms ! (nat_of_integer n - 1)"
      have va: "vars ?asm \<subseteq> vars A1" "vars concl \<subseteq> vars A1"
      proof -
        have "nat_of_integer n - 1 < length asms" using n1 by (simp add: integer_reps integer_of_nat.rep_eq)
        then show "vars ?asm \<subseteq> vars A1" "vars concl \<subseteq> vars A1"
          using vars_assum_problems[OF ap cokR[OF A1r]] by auto
      qed
      have "tr (psubst \<rho>' \<theta>' 0 (rlist_abs params ?asm)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 (rlist_abs params concl))"
        by (rule dsol'[OF ac])
      then have "tr (psubst \<rho>' \<theta>' 0 ?asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 concl)"
        using cl'x by (simp add: tr_psubst_rlist_abs equiv_Abs_m_inj)
      moreover have "psubst \<rho>' \<theta>R 0 ?asm = psubst \<rho>' \<theta>' 0 ?asm" "psubst \<rho>' \<theta>R 0 concl = psubst \<rho>' \<theta>' 0 concl"
        using va vA1 kA1 by (auto intro!: psR)
      ultimately have e: "tr (psubst \<rho>' \<theta>R 0 ?asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 concl)" by simp
      have "prf_ok V' H [] (rev Ns) (mk_asm_prf A1 n (nlift + 1)) (psubst \<rho>' \<theta>R 0 A1)"
        by (rule mk_asm_prf_ok[OF cokR[OF A1r] _ wtyR[OF A1r] ap n1 e]) (simp add: closed_inst_def clR)
      then show ?thesis using er(2) A1o nnn n1 by auto
    qed
    text \<open>The new premises, from the premises of the rule.\<close>
    let ?la = "length (na_As na)" and ?lb = "length Bs"
    have lold0: "length (na_oldAs na) = length As0" using renc by auto
    have revN: "rev Ns ! (?la - 1 - k) = Ns ! (?lb + k)" if "k < ?la" for k
      using that lHs by (simp add: Ns_def rev_nth)
    have olds: "\<forall>k<length (na_oldAs na). prf_ok V' H [] (rev Ns)
      ((if flatten then flatten_params_proof 0 0 (na_n na) else (\<lambda>x. PBound (snd x)))
        (na_oldAs na ! k, integer_of_nat (?la - 1 - k))) (map (psubst \<rho>' \<theta>R 0) As0 ! k)"
    proof (intro allI impI)
      fix k assume k: "k < length (na_oldAs na)"
      have kA: "k < ?la" "k < length As0" using k lold lold0 by auto
      let ?A = "na_oldAs na ! k" and ?A' = "na_As na ! k" and ?Ao = "As0 ! k"
      have A0r: "?Ao \<in> set (rev rAs)" using kA rAs' by auto
      have vA0: "vars ?Ao \<subseteq> RR" using A0r by (auto simp: RR_def vars_thm_def vars_list_implies P)
      have rel: "aconv_term (psubst \<rho>' \<theta>' 0 ?A) (psubst \<rho>' \<theta>R 0 ?Ao) \<and> cok ?A"
      proof -
        from renc consider "na_ren na = None" "na_oldAs na = As0"
          | (ren) "lifted" "na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0)"
            "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0"
          by (elim disjE conjE) auto
        then show ?thesis
        proof cases
          case 1
          then have "rn x = x" for x by (simp add: rn_def ren_of_def)
          with 1 vA0 cokR[OF A0r] show ?thesis by (auto simp: psR)
        next
          case ren
          let ?r = "rename_bvs dps (rtpairs @ tps1) Bi As0"
          from lr[OF ren(1)] obtain p Bi0 As1 where ls: "lsplit Bi = (p, Bi0)" and rA: "rev rAs = map (lift_pre p) As1"
            and big: "\<forall>X\<in>set As1. \<forall>x\<in>vars X. smax < snd x"
            by (auto simp: lifted_rule_def)
          from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
            by auto
          from A0r rA obtain X0 where X0: "?Ao = lift_pre p X0" "X0 \<in> set As1" by auto
          have ibBi: "ibelow smax Bi" using state(2) by simp
          have pv: "snd y \<le> smax" if "y \<in> pvars p" for y
            using that ibBi by (auto simp: Bi ibelow_def vars_lift_pre)
          have A: "?A = lift_pre p (ren_term ?r X0)"
            using ren(3) kA X0 by (simp add: Bi strip_apply_lift_pre[OF ok at])
          have "aconv_term (psubst \<rho>' \<theta>' 0 (lift_pre p (ren_term ?r X0))) (psubst \<rho>' \<theta>R 0 (lift_pre p X0))"
          proof (rule aconv_psubst_lift_pre_ren)
            show "\<forall>x\<in>pvars p. \<theta>R x = \<theta>' x"
              using vA0 X0(1) pv rnid by (auto simp: \<theta>R_def vars_lift_pre)
            show "\<forall>x\<in>vars X0. \<theta>R x = \<theta>' (ren_ix ?r x)"
              using vA0 X0 big ren(2) by (auto simp: \<theta>R_def vars_lift_pre rn_def ren_of_def)
          qed
          moreover have "cok ?A"
          proof -
            have "wfp ar ?Ao" using wR(1) A0r cokR[OF A0r] by (auto simp: wfp_def wt_term_def swf_tm_def)
            then have "wfp ar ?A" using wfp_lift_pre_ren_term[of ar p ?r X0] X0(1) A by simp
            then show ?thesis by (simp add: wfp_def)
          qed
          ultimately show ?thesis using A X0(1) by simp
        qed
      qed
      have trA: "tr (psubst \<rho>' \<theta>' 0 ?A) = tr (psubst \<rho>' \<theta>R 0 ?Ao)" using rel aconv_term_tr by blast
      have wA0: "wty V' [] (psubst \<rho>' \<theta>R 0 ?Ao) propT" by (rule wtyR[OF A0r])
      have wA: "wty V' [] (psubst \<rho>' \<theta>' 0 ?A) propT"
      proof -
        have "has_type V' [] (psubst \<rho>' \<theta>' 0 ?A) propT"
          using wA0 rel has_type_aconv'[OF aconv_term_sym'] by (auto simp: wty_def)
        moreover have "\<forall>v\<in>vars (psubst \<rho>' \<theta>' 0 ?A). 0 \<le> snd v" using tyall' by (auto simp: vars_psubst wty_def)
        ultimately show ?thesis by (simp add: wty_def)
      qed
      have relk: "tr (rev Ns ! (?la - 1 - k)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 ?A')"
        using relN[of "?lb + k"] revN[OF kA(1)] lHs kA by (simp add: nth_append)
      have wNk: "wty V' [] (rev Ns ! (?la - 1 - k)) propT"
        using wtyN(1) revN[OF kA(1)] lHs kA by (simp add: Ns_def)
      have k': "?la - 1 - k < length (rev Ns)" using kA lHs by (simp add: Ns_def)
      show "prf_ok V' H [] (rev Ns) ((if flatten then flatten_params_proof 0 0 (na_n na) else (\<lambda>x. PBound (snd x)))
          (?A, integer_of_nat (?la - 1 - k))) (map (psubst \<rho>' \<theta>R 0) As0 ! k)"
      proof (cases flatten)
        case True
        have fl: "ok (flatten_params vl n ?A) ?A'" using list_all2_nthD[OF flat] k True by simp
        have wA': "wty V' [] (psubst \<rho>' \<theta>' 0 ?A') propT"
        proof -
          have "wtprop A W'' env' ?A'" using As kA by simp
          then have tp': "typed env' W'' [] ?A' propT" and tw: "\<forall>U\<in>tys ?A'. tyw ar (tyenv env') A U"
            by (auto simp: wtprop_def)
          have ti'': "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi''])
          have "wty V' [] (psubst \<rho>' \<theta>' 0 ?A') (tsubst \<rho>' propT)"
          proof (rule typed_psubst_wty[OF tp' pi'' gs'])
            show "\<forall>U\<in>tys ?A'. tcons (tyenv env') U" using tw tyw_tcons[OF ti''] by blast
            show "tcons (tyenv env') propT" by (simp add: tcons_def propT_def)
            show "\<forall>x\<in>vars ?A'. wty V' [] (\<theta>' x) (tsubst \<rho>' (W'' x))" using tyall' by blast
          qed
          then show ?thesis by (simp add: propT_def)
        qed
        have "prf_ok V' H [] (rev Ns) (flatten_params_proof 0 0 n (?A, integer_of_nat (?la - 1 - k))) (psubst \<rho>' \<theta>' 0 ?A)"
        proof (rule flatten_params_proof_ok[OF _ _ fl _ wA wA' k' wNk relk])
          show "cok ?A" using rel by blast
          show "closed_inst \<theta>' ?A" using cl'x by (simp add: closed_inst_def)
          show "length (vl (map fst (strip_params ?A))) = length (strip_params ?A)" using vl by simp
          show "\<forall>h\<in>set (rev Ns). wty V' [] h propT" using wtyN(1) by simp
        qed
        then show ?thesis using True nnn kA trA wA0 by (auto intro: prf_ok.conv)
      next
        case False
        have AA: "?A' = ?A" using list_all2_nthD[OF flat] k False by simp
        have "prf_ok V' H [] (rev Ns) (PBound (integer_of_nat (?la - 1 - k))) (rev Ns ! (?la - 1 - k))"
          using prf_ok.PBound[of "integer_of_nat (?la - 1 - k)" "rev Ns" V' "[]" H] k' wNk
          by (simp add: integer_reps)
        moreover have "tr (rev Ns ! (?la - 1 - k)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 ?Ao)" using relk AA trA by simp
        ultimately show ?thesis using False kA wA0 by (auto intro: prf_ok.conv)
      qed
    qed
    text \<open>The composed proof of the instances.\<close>
    let ?core = "core_prf flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1)"
    have core_ok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 (?core sprf rp')) (list_implies Ns (psubst \<rho>' \<theta>' 0 C))"
      unfolding prf_inst_core_prf
    proof (rule core_prf_ok[OF Sok _ BBi_eq _ wtyN(1) _ _ lold _ olds pre_ok])
      show "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 rp')
          (list_implies (map (psubst \<rho>' \<theta>R 0) Pre @ map (psubst \<rho>' \<theta>R 0) As0) (psubst \<rho>' \<theta>R 0 B))"
        using Rok by (simp add: P rAs' psubst_list_implies')
      show "length Ns = length Bs + length (na_As na)" using lHs by (simp add: Ns_def)
      show "length (map (psubst \<rho>' \<theta>' 0) Bs) = length Bs" by simp
      show "length (map (psubst \<rho>' \<theta>R 0) As0) = length (na_oldAs na)" using lold0 by simp
      show "\<forall>j<length Bs. tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)"
      proof (intro allI impI)
        fix j assume j: "j < length Bs"
        then show "tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)"
          using relN[of j] lHs by (simp add: nth_append)
      qed
    qed
    text \<open>The proof that was computed is equivalent to the instance of the composed proof.\<close>
    have pinst: "prf_aeq (prf_inst \<rho>' \<theta>' 0 (?core sprf rp')) (prf_inst \<rho> \<theta>0 0 p)"
    proof -
      from pc consider (e) "env_is_empty env'" "p = ?core sprf rp'"
        | (a) rp'' where "\<not> env_is_empty env'" "above env' smax" "p = ?core sprf rp''"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
        | (g) "\<not> env_is_empty env'" "\<not> above env' smax"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
        by blast
      then show ?thesis
      proof cases
        case e
        have "\<rho>' = \<rho>" using agT e(1) by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
        moreover have "\<theta>' = \<theta>0" using unb\<theta> e(1) by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
        ultimately show ?thesis using e(2) by (simp add: prf_aeq.refl)
      next
        case a
        have unbT: "vt_lookup (tyenv env') v = None" if "snd v \<le> smax" for v
          using a(2) that unfolding above_def by (blast intro: vt_above_lookup)
        have tcong: "tsubst \<rho> U = tsubst \<rho>' U" if "\<forall>(v, S)\<in>tvars U. snd v \<le> smax" for U
          by (rule tsubst_cong) (use that unbT agT in fastforce)
        have "prf_inst \<rho>' \<theta>' 0 sprf = prf_inst \<rho> \<theta>0 0 sprf"
          by (rule prf_inst_tcong[OF sp0], rule prf_all_mono[OF sw]) (use tcong in auto)
        moreover have "prf_aeq (prf_inst \<rho>' \<theta>' 0 rp') (prf_inst \<rho> \<theta>0 0 rp'')"
          by (rule norm_proof_inst[OF a(4) rA ie swf smeq cl0 cl' _ tyc]) (use ty0 in \<open>auto simp: wty_def\<close>)
        ultimately show ?thesis using a(3)
          by (simp add: prf_inst_core_prf) (rule prf_aeq_core_prf[OF prf_aeq.refl])
      next
        case g
        have "prf_all (ann_ok_env env') (tcons (tyenv env')) (?core sprf rp')"
          by (rule prf_all_core_prf[OF sA rA ann_ok_env_Bound])
        from norm_proof_inst[OF g(3) this ie swf smeq cl0 cl' _ tyc] ty0 show ?thesis
          by (auto simp: wty_def)
      qed
    qed
    have okp: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 p) (list_implies Ns (psubst \<rho>' \<theta>' 0 C))"
      by (rule prf_ok_aeq[OF core_ok pinst])
    have pv: "prf_vars p = {}"
    proof -
      have c: "prf_vars (?core sprf q) = {}" if "prf_vars q = {}" for q
        using that sp0 by (simp add: prf_vars_core_prf)
      from pc consider (e) "env_is_empty env'" "p = ?core sprf rp'"
        | (a) rp'' where "\<not> env_is_empty env'" "above env' smax" "p = ?core sprf rp''"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
        | (g) "\<not> env_is_empty env'" "\<not> above env' smax"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
        by blast
      then show ?thesis
      proof cases
        case e
        then show ?thesis using c[OF rp'0] by simp
      next
        case a
        then show ?thesis using c[OF prf_vars_prf_rel[OF a(4) rp'0]] by simp
      next
        case g
        then show ?thesis using prf_vars_prf_rel[OF g(3) c[OF rp'0]] by simp
      qed
    qed
    have "prf_inst \<rho> \<theta>0 0 p = prf_inst \<rho> \<theta> 0 p" by (rule prf_inst_cong) (simp add: pv)
    moreover have "psubst \<rho> \<theta> 0 (br_prop r) = psubst \<rho> \<theta>0 0 (br_prop r)"
      using eq0[of "br_prop r" 0] nnr by (simp add: vars_thm_def)
    moreover have "tr (list_implies Ns (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 (br_prop r))"
    proof -
      have "tr (psubst \<rho>' \<theta>' 0 C) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 C')" by (rule equiv_sym[OF rel_tr[OF relC]])
      then have "tr (list_implies Ns (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_implies Ns (psubst \<rho> \<theta>0 0 C'))"
        by (intro tr_list_implies_cong) (simp_all add: list.rel_refl)
      then show ?thesis by (simp add: bprop psubst_list_implies' Ns_def)
    qed
    ultimately show "prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 (br_prop r))"
      using prf_ok.conv[OF okp _ wtyP] by simp
  qed
  then show ?thesis using bp rbr by (auto simp: nlift_def rp'_def)
qed

end

end
