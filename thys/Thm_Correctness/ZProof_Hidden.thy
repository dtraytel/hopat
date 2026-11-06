section \<open>Hidden variables of proofs\<close>

theory ZProof_Hidden
  imports ZProof_Decode
begin

text \<open>
  A schematic variable of a proof that does not occur in its theorem is hidden. The tight
  proofs of \<open>ZTerm\<close> instantiate only the visible variables when they are normalized with
  respect to an environment, so that a hidden variable may become identical to a visible
  variable of the same name. Their invariant is therefore stronger than validity: the proof is
  valid after any renaming that gives the hidden variables (pairs of a name and a type) names of
  their own (\<open>hvalid\<close>). This implies validity.
\<close>

subsection \<open>Renaming hidden variables\<close>

fun rnv :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<Rightarrow> ptyp \<Rightarrow> indexname) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "rnv V \<nu> (Var x T) = (if (x, T) \<in> V then Var x T else Var (\<nu> x T) T)"
| "rnv V \<nu> (Abs a T t) = Abs a T (rnv V \<nu> t)"
| "rnv V \<nu> (s $ t) = rnv V \<nu> s $ rnv V \<nu> t"
| "rnv V \<nu> t = t"

definition prf_rnv :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<Rightarrow> ptyp \<Rightarrow> indexname) \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_rnv V \<nu> = map_proof_terms (rnv V \<nu>) id"

definition prf_vars :: "prf \<Rightarrow> (indexname \<times> ptyp) set" where
  "prf_vars p = (\<Union>t\<in>prf_terms p. vars t)"

lemma finite_prf_terms [simp]: "finite (prf_terms p)"
  by (induction p) auto

lemma finite_vars_pterm: "finite (vars t)"
  by (induction t) auto

lemma finite_prf_vars [simp]: "finite (prf_vars p)"
  by (simp add: prf_vars_def finite_vars_pterm)

text \<open>
  A separation of the hidden variables \<open>X - V\<close>: they get pairwise different names, which are
  not names of visible variables.
\<close>

definition hsep :: "(indexname \<times> ptyp) set \<Rightarrow> (indexname \<Rightarrow> ptyp \<Rightarrow> indexname) \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "hsep V \<nu> X \<longleftrightarrow> inj_on (\<lambda>(x, T). \<nu> x T) (X - V) \<and> (\<forall>(x, T)\<in>X - V. \<nu> x T \<notin> fst ` V)"

lemma infinite_indexnames: "infinite (UNIV :: indexname set)"
proof -
  have "inj (\<lambda>i :: integer. (STR '''', i))" by (auto intro: injI)
  moreover have "infinite (UNIV :: integer set)" by (rule infinite_UNIV_char_0)
  ultimately have "infinite (range (\<lambda>i :: integer. (STR '''', i)))" by (auto dest: finite_imageD)
  then show ?thesis by (auto dest: finite_subset[OF subset_UNIV])
qed

text \<open>Separations exist that avoid any finite set \<open>N\<close> of names:\<close>

lemma hsep_exists:
  assumes "finite X" "finite V" "finite N"
  obtains \<nu> where "hsep V \<nu> X" "\<forall>(x, T)\<in>X - V. \<nu> x T \<notin> N"
proof -
  let ?A = "X - V" and ?B = "UNIV - (N \<union> fst ` V)"
  have fA: "finite ?A" using assms(1) by simp
  have iB: "infinite ?B"
  proof
    assume "finite ?B"
    then have "finite (?B \<union> (N \<union> fst ` V))" using assms(2,3) by simp
    then show False using infinite_indexnames by (simp add: Un_commute)
  qed
  obtain B' where B': "B' \<subseteq> ?B" "finite B'" "card B' = card ?A"
    using infinite_arbitrarily_large[OF iB, of "card ?A"] by blast
  obtain f where f: "bij_betw f ?A B'" using finite_same_card_bij[OF fA B'(2) B'(3)[symmetric]] by blast
  let ?\<nu> = "\<lambda>x T. f (x, T)"
  have "inj_on (\<lambda>(x, T). ?\<nu> x T) ?A" using f by (simp add: bij_betw_def case_prod_beta')
  moreover have "f (x, T) \<in> ?B" if "(x, T) \<in> ?A" for x T using that f B'(1) by (auto simp: bij_betw_def)
  ultimately show thesis by (intro that[of ?\<nu>]) (auto simp: hsep_def)
qed

context prf_sig
begin

lemma ap_rnv:
  assumes "\<And>x T U. (x, T) \<in> vars t \<Longrightarrow> (x, T) \<in> V \<Longrightarrow> \<sigma>' x U = \<sigma> x U"
    and "\<And>x T U. (x, T) \<in> vars t \<Longrightarrow> (x, T) \<notin> V \<Longrightarrow> \<sigma>' (\<nu> x T) U = \<sigma> x U"
  shows "ap \<rho> \<sigma>' (rnv V \<nu> t) = ap \<rho> \<sigma> t"
  using assms by (induction t) auto

lemma prf_ap_rnv:
  assumes "\<And>x T U. (x, T) \<in> prf_vars p \<Longrightarrow> (x, T) \<in> V \<Longrightarrow> \<sigma>' x U = \<sigma> x U"
    and "\<And>x T U. (x, T) \<in> prf_vars p \<Longrightarrow> (x, T) \<notin> V \<Longrightarrow> \<sigma>' (\<nu> x T) U = \<sigma> x U"
  shows "prf_ap \<rho> \<sigma>' (prf_rnv V \<nu> p) = prf_ap \<rho> \<sigma> p"
proof -
  have mo: "map_option (ap \<rho> \<sigma>') (map_option (rnv V \<nu>) t) = map_option (ap \<rho> \<sigma>) t"
    if "\<forall>u\<in>set_option t. vars u \<subseteq> prf_vars p" for t
    using that assms by (cases t) (auto intro!: ap_rnv)
  have "vars u \<subseteq> prf_vars p" if "u \<in> prf_terms q" "prf_terms q \<subseteq> prf_terms p" for u q
    using that by (auto simp: prf_vars_def)
  then have "prf_terms q \<subseteq> prf_terms p \<Longrightarrow> prf_ap \<rho> \<sigma>' (prf_rnv V \<nu> q) = prf_ap \<rho> \<sigma> q" for q
  proof (induction q)
    case (AbsP a t q)
    then show ?case using mo[of t] by (auto simp: prf_ap_def prf_rnv_def)
  next
    case (PAppt q t)
    then show ?case using mo[of t] by (auto simp: prf_ap_def prf_rnv_def)
  next
    case (PAppp q1 q2)
    then show ?case by (auto simp: prf_ap_def prf_rnv_def)
  next
    case (Abst a T q)
    then show ?case by (auto simp: prf_ap_def prf_rnv_def option.map_ident id_def)
  qed (auto simp: prf_ap_def prf_rnv_def option.map_comp option.map_ident comp_def id_def)
  then show ?thesis by blast
qed

text \<open>Validity after every separation of the hidden variables:\<close>

definition hvalid :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm set \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> bool" where
  "hvalid ax H tps p \<phi> \<longleftrightarrow> (\<forall>\<nu>. hsep (vars_thm tps \<phi>) \<nu> (prf_vars p) \<longrightarrow>
    prf_valid ax H tps (prf_rnv (vars_thm tps \<phi>) \<nu> p) \<phi>)"

theorem hvalid_prf_valid:
  assumes hv: "hvalid ax H tps p \<phi>"
  shows "prf_valid ax H tps p \<phi>"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
  let ?V = "vars_thm tps \<phi>" and ?X = "prf_vars p"
  obtain \<nu> where sep: "hsep ?V \<nu> ?X" by (rule hsep_exists[of ?X ?V "{}"]) auto
  let ?g = "\<lambda>(x, T). \<nu> x T"
  have inj: "inj_on ?g (?X - ?V)" and fr: "\<forall>(x, T)\<in>?X - ?V. \<nu> x T \<notin> fst ` ?V"
    using sep by (simp_all add: hsep_def)
  define h where "h y = (if y \<in> ?g ` (?X - ?V) then fst (inv_into (?X - ?V) ?g y) else y)" for y
  define \<sigma>' where "\<sigma>' y U = \<sigma> (h y) U" for y U
  have hid: "\<sigma>' (\<nu> x T) U = \<sigma> x U" if "(x, T) \<in> ?X - ?V" for x T U
  proof -
    have "\<nu> x T = ?g (x, T)" by simp
    then have "inv_into (?X - ?V) ?g (\<nu> x T) = (x, T)" using inv_into_f_f[OF inj that] by simp
    then show ?thesis using that by (force simp: \<sigma>'_def h_def)
  qed
  have vis: "\<sigma>' x U = \<sigma> x U" if "(x, T) \<in> ?V" for x T U
  proof -
    have "x \<notin> ?g ` (?X - ?V)" using fr that by (force simp: image_iff)
    then show ?thesis by (simp add: \<sigma>'_def h_def)
  qed
  have \<sigma>': "gsubst \<sigma>'"
    using \<sigma> unfolding gsubst_def wt_subst_def closed_subst_def \<sigma>'_def by blast
  have apV: "ap \<rho> \<sigma>' t = ap \<rho> \<sigma> t" if "vars t \<subseteq> ?V" for t
    unfolding ap_def by (rule vsubst_cong) (use that vis in \<open>auto simp: vars_inst\<close>)
  have tV: "vars t \<subseteq> ?V" "vars u \<subseteq> ?V" if "(t, u) \<in> set tps" for t u
    using that by (auto simp: vars_thm_def)
  have "prf_ok ax H e [] (prf_ap \<rho> \<sigma>' (prf_rnv ?V \<nu> p)) (ap \<rho> \<sigma>' \<phi>)"
  proof (rule prf_validD[OF hv[unfolded hvalid_def, rule_format, OF sep] \<rho> \<sigma>'])
    fix t u assume "(t, u) \<in> set tps"
    with sol[of t u] tV[of t u] apV show "ap \<rho> \<sigma>' t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>' u" by simp
  qed
  moreover have "prf_ap \<rho> \<sigma>' (prf_rnv ?V \<nu> p) = prf_ap \<rho> \<sigma> p"
    by (rule prf_ap_rnv) (use vis hid in auto)
  moreover have "ap \<rho> \<sigma>' \<phi> = ap \<rho> \<sigma> \<phi>" by (rule apV) (simp add: vars_thm_def)
  ultimately show "prf_ok ax H e [] (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> \<phi>)" by simp
qed

end

end
