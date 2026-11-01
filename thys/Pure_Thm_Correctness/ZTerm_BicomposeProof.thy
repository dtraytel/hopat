section \<open>Correctness of the composition of tight proofs\<close>

theory ZTerm_BicomposeProof
  imports ZTerm_NormProof
begin

text \<open>
  Tight proofs keep schematic variables that do not occur in their theorems (hidden variables):
  their visible normalisation (\<open>ZTerm.norm_proof\<close>) instantiates only the variables of the
  theorems. Isabelle identifies a schematic variable by its name and its type, the judgment of
  the model by its name: proof and theorem share one typing. The renaming of the new premises of
  a lifted rule may give a variable the name of a hidden variable of the rule's proof with
  another type; this harmless case is excluded by the main theorem.
\<close>

context prf_wf_csig
begin

subsection \<open>Renaming\<close>

definition zrnf :: "ren \<Rightarrow> integer \<Rightarrow> indexname \<Rightarrow> indexname" where
  "zrnf r m x = (if m < snd x then ren_ix r x else x)"

lemma ren_of_zrnf: "na_ren na = Some r \<Longrightarrow> ren_of na m = zrnf r m"
  by (intro ext) (simp add: ren_of_def zrnf_def)

lemma psubst_zren_term:
  "-1 \<le> m \<Longrightarrow> psubst \<rho> \<theta> lev (zdec (zren_term r m t)) = psubst \<rho> (\<theta> \<circ> zrnf r m) lev (zdec t)"
  by (induction r m t arbitrary: lev rule: zren_term.induct) (auto simp: zrnf_def ren_ix_def psubst_of_class)

lemma vars_of_class[simp]: "vars (of_class T c) = {}"
  by (simp add: of_class_def)

lemma vars_zren_term: "-1 \<le> m \<Longrightarrow> vars (zdec (zren_term r m t)) = zrnf r m ` vars (zdec t)"
  by (induction r m t rule: zren_term.induct) (auto simp: zrnf_def ren_ix_def)

lemma zren_proof_inst:
  assumes "zconst_free p" "-1 \<le> m"
  shows "\<exists>p'. zren_proof r m p = returnZ p' \<and> zconst_free p' \<and>
    (\<forall>\<rho> \<theta> lev. prf_inst \<rho> \<theta> lev (zprf_tr p') = prf_inst \<rho> (\<theta> \<circ> zrnf r m) lev (zprf_tr p)) \<and>
    prf_vars (zprf_tr p') = zrnf r m ` prf_vars (zprf_tr p)"
  using assms(1) unfolding zren_proof_def
proof (induction p)
  case (ZAbst a T p)
  then show ?case by auto
next
  case (ZAbsp a t p)
  then show ?case by (auto simp: psubst_zren_term[OF assms(2)] vars_zren_term[OF assms(2)] comp_def)
next
  case (ZAppt p t)
  then show ?case by (auto simp: psubst_zren_term[OF assms(2)] vars_zren_term[OF assms(2)] comp_def)
next
  case (ZAppp p q)
  then show ?case by (auto simp: image_Un)
qed auto


subsection \<open>Instances and typings of proofs with variables\<close>

lemma prf_inst_tcong_vars:
  assumes "\<forall>x\<in>prf_vars p. \<theta> x = \<theta>' x"
    "prf_all (\<lambda>t. \<forall>U\<in>tys t. tsubst \<rho> U = tsubst \<rho>' U) (\<lambda>U. tsubst \<rho> U = tsubst \<rho>' U) p"
  shows "prf_inst \<rho> \<theta> lev p = prf_inst \<rho>' \<theta>' lev p"
proof -
  have ps: "psubst \<rho> \<theta> l t = psubst \<rho>' \<theta>' l t"
    if "\<forall>x\<in>vars t. \<theta> x = \<theta>' x" "\<forall>U\<in>tys t. tsubst \<rho> U = tsubst \<rho>' U" for l t
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

lemma prf_valid_cong_vars:
  assumes v: "prf_valid alg ar W H tps p P" and W: "\<forall>x\<in>vars_thm tps P \<union> prf_vars p. W' x = W x"
  shows "prf_valid alg ar W' H tps p P"
  unfolding prf_valid_def
proof (intro allI impI)
  fix V' \<rho> \<theta> assume g: "ginst alg ar \<rho>" and ty: "inst_typed W' V' [] \<rho> \<theta>"
    and s: "\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
  let ?X = "vars_thm tps P \<union> prf_vars p"
  define \<theta>1 where "\<theta>1 x = (if x \<in> ?X then \<theta> x else Free STR ''u'' (tsubst \<rho> (W x)))" for x
  have ty1: "inst_typed W V' [] \<rho> \<theta>1"
    unfolding inst_typed_def
  proof (intro allI impI)
    fix x :: indexname assume x: "0 \<le> snd x"
    show "wty V' [] (\<theta>1 x) (tsubst \<rho> (W x))"
    proof (cases "x \<in> ?X")
      case True
      with inst_typedD[OF ty x] W show ?thesis by (simp add: \<theta>1_def)
    qed (simp add: \<theta>1_def wty_def has_type.Free)
  qed
  have e: "psubst \<rho> \<theta>1 0 t = psubst \<rho> \<theta> 0 t" if "vars t \<subseteq> vars_thm tps P" for t
    by (rule psubst_cong) (use that in \<open>auto simp: \<theta>1_def\<close>)
  have "prf_ok V' H [] [] (prf_inst \<rho> \<theta>1 0 p) (psubst \<rho> \<theta>1 0 P)"
  proof (rule prf_validD[OF v g ty1])
    fix t u assume tu: "(t, u) \<in> set tps"
    then have "vars t \<subseteq> vars_thm tps P" "vars u \<subseteq> vars_thm tps P" by (auto simp: vars_thm_def)
    with tu s show "tr (psubst \<rho> \<theta>1 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>1 0 u)" by (auto simp: e)
  qed
  moreover have "prf_inst \<rho> \<theta>1 0 p = prf_inst \<rho> \<theta> 0 p" by (rule prf_inst_cong) (simp add: \<theta>1_def)
  moreover have "psubst \<rho> \<theta>1 0 P = psubst \<rho> \<theta> 0 P" by (rule e) (simp add: vars_thm_def)
  ultimately show "prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 P)" by simp
qed

text \<open>
  The typing of the unifier can be changed on variables that are neither bound nor occur in the
  bindings.
\<close>

lemma pinv_retype:
  assumes pi: "pinv alg ar A W env []"
    and ch: "\<forall>x. W' x \<noteq> W x \<longrightarrow> vt_lookup (tenv env) x = None \<and> x \<notin> fst ` bvps env \<and>
      tyw ar (tyenv env) A (W' x)"
  shows "pinv alg ar A W' env []"
proof -
  have pe: "penv_inv alg ar W env" using pi by (simp add: pinv_def)
  have eqb: "W' y = W y" if "y \<in> fst ` bvps env" for y using ch that by blast
  have wt: "wt_env W' env"
    unfolding wt_env_def
  proof (intro allI impI)
    fix x U u assume l: "vt_lookup (tenv env) x = Some (U, u)"
    with pe have "typed env W [] u U" unfolding penv_inv_def wt_env_def by blast
    moreover have "tctx env W' y = tctx env W y" if "y \<in> vars u" for y
    proof -
      have "y \<in> fst ` bvps env" using bvpsI[OF l] that by (auto simp: vars_vps)
      then show ?thesis using eqb[of y] by (simp add: vtyp_def split: option.split)
    qed
    ultimately show "typed env W' [] u U"
      unfolding typed_def by (auto intro: has_type_vars_cong)
  qed
  have eqd: "W' x = W x" if "vt_lookup (tenv env) x = Some (U, u)" for x U u
    using spec[OF ch, of x] that by auto
  have wc0: "wcons W env" using pi by (simp add: pinv_def)
  have wc: "wcons W' env" unfolding wcons_def
  proof (intro allI impI)
    fix x U u assume "vt_lookup (tenv env) x = Some (U, u)"
    with wc0 eqd[OF this] show "tnorm (tyenv env) U = tnorm (tyenv env) (W' x)"
      unfolding wcons_def by metis
  qed
  have ty0: "\<forall>x. tyw ar (tyenv env) A (W x)" using pi by (simp add: pinv_def)
  have ty: "\<forall>x. tyw ar (tyenv env) A (W' x)"
  proof
    fix x show "tyw ar (tyenv env) A (W' x)"
      using spec[OF ty0, of x] spec[OF ch, of x] by (cases "W' x = W x") auto
  qed
  show ?thesis using pi wt wc ty by (simp add: pinv_def penv_inv_def)
qed

end

end
