section \<open>The indices of the schematic variables of proofs\<close>

theory Proof_Indices
  imports Proof_Bicompose
begin

text \<open>
  The composition of proofs (\<open>bicompose_proof_valid\<close>) asks the proof of the lifted rule to
  have its schematic variables above the maximal index of the proof state, because the
  renaming of the rule renames all variables of its proof. Lifting increments the indices, so
  this holds if the indices of the variables of the proofs of theorems are not negative; this
  property is preserved by lifting and composition.
\<close>

definition prf_idx :: "(integer \<Rightarrow> bool) \<Rightarrow> prf \<Rightarrow> bool" where
  "prf_idx P p \<longleftrightarrow> (\<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. P (snd (fst v)))"

lemma prf_idx_simps [simp]:
  "prf_idx P (Abst a T p) \<longleftrightarrow> prf_idx P p"
  "prf_idx P (AbsP a t p) \<longleftrightarrow> (\<forall>u\<in>set_option t. \<forall>v\<in>vars u. P (snd (fst v))) \<and> prf_idx P p"
  "prf_idx P (PAppt p t) \<longleftrightarrow> prf_idx P p \<and> (\<forall>u\<in>set_option t. \<forall>v\<in>vars u. P (snd (fst v)))"
  "prf_idx P (PAppp p q) \<longleftrightarrow> prf_idx P p \<and> prf_idx P q"
  "prf_idx P MinProof" "prf_idx P (PBound i)" "prf_idx P (Hyp u)" "prf_idx P (PAxm a A Us)"
  "prf_idx P (PClass U c)" "prf_idx P (Oracle a A Us)" "prf_idx P (PThm (h, b))"
  by (auto simp: prf_idx_def)

lemma prf_idx_mono: "prf_idx P p \<Longrightarrow> (\<And>i. P i \<Longrightarrow> Q i) \<Longrightarrow> prf_idx Q p"
  by (auto simp: prf_idx_def)

lemma prf_idx_proof_combP: "prf_idx P (proof_combP p qs) \<longleftrightarrow> prf_idx P p \<and> (\<forall>q\<in>set qs. prf_idx P q)"
  unfolding proof_combP_def by (induction qs arbitrary: p) auto

lemma prf_idx_proof_combt:
  "prf_idx P (proof_combt p ts) \<longleftrightarrow> prf_idx P p \<and> (\<forall>t\<in>set ts. \<forall>v\<in>vars t. P (snd (fst v)))"
  unfolding proof_combt_def by (induction ts arbitrary: p) auto

lemma prf_idx_mk_AbsP: "prf_idx P (mk_AbsP xs p) \<longleftrightarrow> prf_idx P p"
  unfolding mk_AbsP_def by (induction xs) auto


subsection \<open>Lifting\<close>

lemma prf_idx_lift_prf: "prf_idx (\<lambda>i. P (i + inc)) p \<Longrightarrow> prf_idx P (lift_prf inc Ts lev p)"
  by (induction inc Ts lev p rule: lift_prf.induct) (fastforce simp: vars_incr_idx)+

lemma prf_idx_spine: "prf_idx P (snd (snd (foldr mk_app bs (a, b, PBound c))))"
  by (induction bs) (auto simp: mk_app_def split: prod.splits)

lemma prf_idx_lift_prems: "prf_idx (\<lambda>i. P (i + inc)) pf \<Longrightarrow> prf_idx P (lift_prems inc k pf Ts bs i j G)"
  by (induction inc k pf Ts bs i j G rule: lift_prems.induct)
    (auto simp: prf_idx_proof_combP prf_idx_lift_prf prf_idx_spine)

theorem prf_idx_lift_proof: "prf_idx (\<lambda>i. P (i + inc)) pf \<Longrightarrow> prf_idx P (lift_proof G inc prems pf)"
  by (simp add: lift_proof_def prf_idx_mk_AbsP prf_idx_lift_prems)

context prf_sig
begin

lemma prf_above_idx: "prf_above m p \<longleftrightarrow> prf_idx (\<lambda>i. m < i) p"
  by (simp add: prf_above_def prf_idx_def)

corollary prf_above_lift_proof:
  assumes "prf_idx (\<lambda>i. 0 \<le> i) pf"
  shows "prf_above gmax (lift_proof G (gmax + 1) prems pf)"
  unfolding prf_above_idx by (rule prf_idx_lift_proof, rule prf_idx_mono[OF assms]) simp

end

corollary prf_nonneg_lift_proof:
  assumes "prf_idx (\<lambda>i. 0 \<le> i) pf" and "-1 \<le> gmax"
  shows "prf_idx (\<lambda>i. 0 \<le> i) (lift_proof G (gmax + 1) prems pf)"
  by (rule prf_idx_lift_proof, rule prf_idx_mono[OF assms(1)]) (use assms(2) in simp)


subsection \<open>Composition\<close>

lemma prf_idx_imp_prf: "prf_idx P (imp_prf A i m)"
  by (induction A i m rule: imp_prf.induct) auto

lemma prf_idx_mk_asm_prf: "prf_idx P (mk_asm_prf A i m)"
proof -
  have "prf_idx P (all_prf i m A)" by (induction i m A rule: all_prf.induct) (auto simp: prf_idx_imp_prf)
  then show ?thesis by (simp add: mk_asm_prf_def)
qed

lemma prf_idx_flatten_params_proof: "prf_idx P (flatten_params_proof i j n x)"
  by (induction i j n x rule: flatten_params_proof.induct) (auto simp: prf_idx_proof_combP prf_idx_proof_combt)

lemma prf_idx_core_prf:
  "prf_idx P sprf \<Longrightarrow> prf_idx P p \<Longrightarrow> prf_idx P (core_prf flatten lb oldAs A n m sprf p)"
  by (auto simp: core_prf_def prf_idx_proof_combP prf_idx_mk_asm_prf prf_idx_flatten_params_proof)

text \<open>Normalization:\<close>

context prf_sig
begin

lemma vars_remove_types [simp]: "vars (remove_types t) = vars t"
  by (induction t) auto

lemma loose_bvar_remove_types [simp]: "loose_bvar (remove_types t) k = loose_bvar t k"
  by (induction t arbitrary: k) auto

lemma remove_types_env_props:
  "acyc (remove_types_env env) \<longleftrightarrow> acyc env" "closed_env (remove_types_env env) \<longleftrightarrow> closed_env env"
  "evars (remove_types_env env) = evars env"
proof -
  have l: "vt_lookup (tenv (remove_types_env env)) x = Some (U, u) \<longleftrightarrow>
      (\<exists>u0. vt_lookup (tenv env) x = Some (U, u0) \<and> u = remove_types u0)" for x U u
    by auto
  have b: "bnds (remove_types_env env) = (\<lambda>(x, U, u). (x, U, remove_types u)) ` bnds env"
    unfolding bnds_def l by force
  have "dep (remove_types_env env) = dep env" unfolding dep_def l by force
  then show "acyc (remove_types_env env) \<longleftrightarrow> acyc env" by (simp add: acyc_def)
  show "closed_env (remove_types_env env) \<longleftrightarrow> closed_env env"
  proof
    assume c: "closed_env (remove_types_env env)"
    show "closed_env env" unfolding closed_env_def
    proof (intro allI impI)
      fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
      then have "vt_lookup (tenv (remove_types_env env)) x = Some (U, remove_types u)" by simp
      with c have "closed (remove_types u)" unfolding closed_env_def by blast
      then show "closed u" by (simp add: closed_def)
    qed
  next
    assume c: "closed_env env"
    show "closed_env (remove_types_env env)" unfolding closed_env_def
    proof (intro allI impI)
      fix x U u assume "vt_lookup (tenv (remove_types_env env)) x = Some (U, u)"
      then obtain u0 where u0: "vt_lookup (tenv env) x = Some (U, u0)" "u = remove_types u0" by auto
      from c u0(1) have "closed u0" unfolding closed_env_def by blast
      with u0(2) show "closed u" by (simp add: closed_def)
    qed
  qed
  show "evars (remove_types_env env) = evars env" by (force simp: evars_def b)
qed

lemma prf_idx_ren_prf: "prf_idx P (ren_prf r p) \<longleftrightarrow> prf_idx P p"
proof (cases r)
  case (Some r')
  have "prf_idx P (map_proof_terms (ren_term r') id p) \<longleftrightarrow> prf_idx P p"
  proof (induction p)
    case (PThm x)
    then show ?case by (cases x) simp
  qed (fastforce simp: vars_ren_term)+
  with Some show ?thesis by (simp add: ren_prf_def)
qed (simp add: ren_prf_def)

lemma vars_norm_term_idx:
  assumes nt: "ok (norm_term E t) t'" and ac: "acyc E" "closed_env E" "tacyc (tyenv E)" and v: "v \<in> vars t'"
  shows "\<exists>w\<in>vars t \<union> evars E. fst w = fst v"
proof -
  have "vars t' \<subseteq> vars (env_apply E t)" by (rule beta_reds_vars[OF norm_term_env_apply(1)[OF nt ac]])
  with v obtain w where "w \<in> vars (unf E t)" "fst w = fst v" by (auto simp: env_apply_def vars_inst)
  with vars_unf_sub[OF ac(1)] show ?thesis by blast
qed

lemma prf_idx_norm_proof:
  "norm_proof E q = returnP q' \<Longrightarrow>
    (\<And>t t'. t \<in> prf_terms q \<Longrightarrow> ok (norm_term E t) t' \<Longrightarrow> \<forall>v\<in>vars t'. P (snd (fst v))) \<Longrightarrow> prf_idx P q'"
proof (induction q arbitrary: q')
  case (PThm x)
  then show ?case by (cases x) (auto simp: bindP_eq_returnP)
qed (fastforce simp: bindP_eq_returnP map_optionP_eq_returnP dest!: norm_term_P_returnP)+

theorem prf_idx_bicompose_proof:
  assumes res: "bicompose_proof env smax flatten Bs As A oldAs n m rprf sprf = returnP p"
    and r: "prf_idx P rprf" and s: "prf_idx P sprf" and e: "\<forall>w\<in>evars env. P (snd (fst w))"
    and ac: "acyc env" "closed_env env" "tacyc (tyenv env)"
  shows "prf_idx P p"
proof -
  let ?E = "remove_types_env env"
  have ac': "acyc ?E" "closed_env ?E" "tacyc (tyenv ?E)" using ac by (simp_all add: remove_types_env_props)
  have np: "prf_idx P q'" if nq: "norm_proof ?E q = returnP q'" and q: "prf_idx P q" for q q'
  proof (rule prf_idx_norm_proof[OF nq])
    fix t t' assume t: "t \<in> prf_terms q" and nt: "ok (norm_term ?E t) t'"
    show "\<forall>v\<in>vars t'. P (snd (fst v))"
    proof
      fix v assume "v \<in> vars t'"
      from vars_norm_term_idx[OF nt ac' this] obtain w where w: "w \<in> vars t \<union> evars env" "fst w = fst v"
        by (auto simp: remove_types_env_props)
      from w(1) have "P (snd (fst w))" using q t e by (auto simp: prf_idx_def)
      with w(2) show "P (snd (fst v))" by simp
    qed
  qed
  have core: "prf_idx P x" if c: "bicompose_core env flatten Bs As A oldAs n m sprf q = returnP x"
    and q: "prf_idx P q" for q x
    using bicompose_core_returnP[OF c] q s by (simp add: prf_idx_mk_AbsP prf_idx_core_prf)
  consider "bicompose_core env flatten Bs As A oldAs n m sprf rprf = returnP p"
    | r' where "norm_proof ?E rprf = returnP r'" "bicompose_core env flatten Bs As A oldAs n m sprf r' = returnP p"
    | q where "bicompose_core env flatten Bs As A oldAs n m sprf rprf = returnP q" "norm_proof ?E q = returnP p"
    using res unfolding bicompose_proof_def norm_proof_remove_types_def
    by (auto simp: bindP_eq_returnP split: if_splits)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (rule core[OF _ r])
  next
    case (2 r')
    show ?thesis by (rule core[OF 2(2) np[OF 2(1) r]])
  next
    case (3 q)
    show ?thesis by (rule np[OF 3(2) core[OF 3(1) r]])
  qed
qed

end

end
