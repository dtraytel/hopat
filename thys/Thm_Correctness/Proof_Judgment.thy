section \<open>A judgment for proof terms\<close>

theory Proof_Judgment
  imports Thm_Type "Pure_Thm.Pure_Proofterm"
begin

text \<open>
  The judgment \<open>prf_ok ax H e Hs p \<phi>\<close> states that the proof term \<open>p\<close> of
  \<^file>\<open>~~/src/Pure/proofterm.ML\<close> proves the proposition \<open>\<phi>\<close>. Schematic variables are typed by
  themselves, as in the terms; \<open>e\<close> types the loose bound variables of the term level
  (\<open>Abst\<close>), \<open>Hs\<close> are the propositions of the bound variables of the proof level (\<open>AbsP\<close>),
  innermost first, and \<open>H\<close> is the set of hypotheses (\<open>Hyp\<close>). Propositions are identified up
  to \<open>\<alpha>\<beta>\<eta>\<close>-conversion (rule \<open>conv\<close>).

  The judgment is declarative: it does not reconstruct missing annotations, but asks for terms
  and types that fit them. Annotations are compared after erasing the types of constants and
  abstractions and the names of bound variables (\<open>Proofterm.remove_types\<close>), up to \<open>\<beta>\<eta>\<close>.

  An axiom, oracle or theorem with proposition \<open>A\<close> proves the instance at type arguments
  \<open>Us\<close> of the closure of \<open>A\<close> over its variables (\<open>Proofchecker.thm_of_proof\<close>) if \<open>ax A\<close>;
  a class proof of \<open>T :: c\<close> proves \<open>OFCLASS(T, c)\<close> if \<open>T\<close> has sort \<open>c\<close> in the algebra. \<^const>\<open>MinProof\<close>, which stands for
  a missing proof, proves nothing.
\<close>


subsection \<open>Erasure\<close>

fun erase :: "pterm \<Rightarrow> pterm" where
  "erase (Abs a T t) = Abs STR '''' dummyT (erase t)"
| "erase (s $ t) = erase s $ erase t"
| "erase (Const c T) = Const c dummyT"
| "erase t = t"

abbreviation ueq :: "pterm \<Rightarrow> pterm \<Rightarrow> bool" (infix \<open>\<approx>\<close> 50) where
  "s \<approx> t \<equiv> equivclp (sup beta eta) (erase s) (erase t)"

lemma erase_remove_types [simp]: "erase (remove_types t) = erase t"
  by (induction t) simp_all

lemma erase_alpha: "s \<rightarrow>\<^sub>\<alpha> t \<Longrightarrow> erase s = erase t"
  by (induction set: alpha) simp_all

lemma loose_bvar1_erase [simp]: "loose_bvar1 (erase t) k = loose_bvar1 t k"
  by (induction t arbitrary: k) simp_all

lemma erase_lift [simp]: "erase (lift t k) = lift (erase t) k"
  by (induction t arbitrary: k) simp_all

lemma erase_subst [simp]: "erase (s[t/k]) = (erase s)[erase t/k]"
  by (induction s arbitrary: t k) (simp_all add: subst_Bound)

lemma erase_beta: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> erase s \<rightarrow>\<^sub>\<beta> erase t"
  by (induction set: beta) auto

lemma erase_eta: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> erase s \<rightarrow>\<^sub>\<eta> erase t"
proof (induction set: eta)
  case (eta s a T d)
  then show ?case using eta.eta[of "erase s" "STR ''''" dummyT "erase d"] by simp
qed auto




subsection \<open>Annotations\<close>

text \<open>Type annotations may contain \<^const>\<open>dummyT\<close>, which fits every type.\<close>

inductive tmatch :: "ptyp \<Rightarrow> ptyp \<Rightarrow> bool" where
  dummy: "tmatch dummyT U"
| Type: "list_all2 tmatch Ts Us \<Longrightarrow> tmatch (Type a Ts) (Type a Us)"
| TFree: "tmatch (TFree a S) (TFree a S)"
| TVar: "tmatch (TVar v S) (TVar v S)"

lemma tmatch_refl [simp]: "tmatch T T"
  by (induction T) (auto intro: tmatch.intros list.rel_refl_strong)

definition tann_ok :: "ptyp option \<Rightarrow> ptyp \<Rightarrow> bool" where
  "tann_ok T U \<longleftrightarrow> (case T of None \<Rightarrow> True | Some T \<Rightarrow> tmatch T U)"

definition ann_ok :: "pterm option \<Rightarrow> pterm \<Rightarrow> bool" where
  "ann_ok t u \<longleftrightarrow> (case t of None \<Rightarrow> True | Some t \<Rightarrow> t \<approx> u)"

lemma tann_ok_simps [simp]: "tann_ok None U" "tann_ok (Some T) U \<longleftrightarrow> tmatch T U"
  and ann_ok_simps [simp]: "ann_ok None u" "ann_ok (Some t) u \<longleftrightarrow> t \<approx> u"
  by (simp_all add: tann_ok_def ann_ok_def)


subsection \<open>Propositions of atoms\<close>

text \<open>The instance of type variables at type arguments, by position:\<close>

definition tyinst :: "(indexname \<times> psort) list \<Rightarrow> ptyp list \<Rightarrow> tinst" where
  "tyinst vs Us v S = (case map_of (zip vs Us) (v, S) of Some U \<Rightarrow> U | None \<Rightarrow> TVar v S)"

text \<open>\<open>Logic.mk_of_class\<close>\<close>

definition of_class :: "ptyp \<Rightarrow> pclass \<Rightarrow> pterm" where
  "of_class T c = Const (c + STR ''_class'') (Type STR ''itself'' [T] \<rightarrow>\<^sub>T propT) $
    Const STR ''Pure.type'' (Type STR ''itself'' [T])"

text \<open>
  The closure of the proposition of an atom over its variables and the order of its type
  variables are parameters; the closure is closed, has no schematic variables, and its type
  variables are among the type arguments.
\<close>

locale prf_sig = pure_sig alg ar ctab
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option" +
  fixes close :: "pterm \<Rightarrow> pterm" and tyargs :: "pterm \<Rightarrow> (indexname \<times> psort) list"
  assumes closed_close: "closed (close A)" and vars_close: "vars (close A) = {}"
    and ttvars_close: "ttvars (close A) \<subseteq> set (tyargs A)"
    and ar_prop: "ar STR ''prop'' = 0"
begin

definition atom_prop :: "pterm \<Rightarrow> ptyp list \<Rightarrow> pterm" where
  "atom_prop A Us = inst (tyinst (tyargs A) Us) (close A)"

definition atom_ok :: "pterm \<Rightarrow> ptyp list option \<Rightarrow> ptyp list \<Rightarrow> bool" where
  "atom_ok A Us' Us \<longleftrightarrow> list_all2 (\<lambda>(v, S) U. has_sort alg U S \<and> cert_typ alg ar U) (tyargs A) Us \<and>
    (case Us' of None \<Rightarrow> True | Some Us'' \<Rightarrow> Us'' = Us)"

lemma cert_propT [simp]: "cert_typ alg ar propT" and cert_imp_type [simp]: "cert_typ alg ar imp_type"
  by (simp_all add: cert_typ_def propT_def imp_type_def tarity_def ar_prop)

lemma conv_ueq: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> s \<approx> t"
  unfolding conv_def
proof (induction rule: equivclp_induct)
  case (step t u)
  then show ?case
    by (auto simp: conv_step_def dest: erase_alpha erase_beta erase_eta
      intro: equivclp_trans[OF _ r_into_equivclp] equivclp_trans[OF _ equivclp_sym[OF r_into_equivclp]])
qed simp


subsection \<open>The judgment\<close>

inductive prf_ok :: "(pterm \<Rightarrow> bool) \<Rightarrow> pterm set \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> pterm list \<Rightarrow> prf \<Rightarrow> pterm \<Rightarrow> bool"
  for ax H where
  conv: "prf_ok ax H e Hs p \<phi> \<Longrightarrow> \<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> \<psi> \<Longrightarrow> e \<turnstile> \<psi> : propT \<Longrightarrow> prf_ok ax H e Hs p \<psi>"
| PBound: "0 \<le> i \<Longrightarrow> nat_of_integer i < length Hs \<Longrightarrow> e \<turnstile> Hs ! nat_of_integer i : propT \<Longrightarrow>
    prf_ok ax H e Hs (PBound i) (Hs ! nat_of_integer i)"
| AbsP: "e \<turnstile> A : propT \<Longrightarrow> ann_ok t A \<Longrightarrow> prf_ok ax H e (A # Hs) p B \<Longrightarrow>
    prf_ok ax H e Hs (AbsP a t p) (implies $ A $ B)"
| Abst: "tann_ok T U \<Longrightarrow> cert_typ alg ar U \<Longrightarrow> prf_ok ax H (e\<langle>0:U\<rangle>) (map (incr_bv 1 0) Hs) p B \<Longrightarrow>
    prf_ok ax H e Hs (Abst a T p) (all_const U $ Abs b U B)"
| PAppt: "prf_ok ax H e Hs p (all_const U $ f) \<Longrightarrow> e \<turnstile> t : U \<Longrightarrow> ann_ok t' t \<Longrightarrow>
    prf_ok ax H e Hs (PAppt p t') (f $ t)"
| PAppp: "prf_ok ax H e Hs p (implies $ A $ B) \<Longrightarrow> prf_ok ax H e Hs q A \<Longrightarrow> prf_ok ax H e Hs (PAppp p q) B"
| Hyp: "t \<in> H \<Longrightarrow> e \<turnstile> t : propT \<Longrightarrow> prf_ok ax H e Hs (Hyp t) t"
| PAxm: "ax A \<Longrightarrow> atom_ok A Us' Us \<Longrightarrow> e \<turnstile> atom_prop A Us : propT \<Longrightarrow>
    prf_ok ax H e Hs (PAxm a A Us') (atom_prop A Us)"
| Oracle: "ax A \<Longrightarrow> atom_ok A Us' Us \<Longrightarrow> e \<turnstile> atom_prop A Us : propT \<Longrightarrow>
    prf_ok ax H e Hs (Oracle a A Us') (atom_prop A Us)"
| PThm: "ax (hd_prop h) \<Longrightarrow> atom_ok (hd_prop h) (hd_types h) Us \<Longrightarrow> e \<turnstile> atom_prop (hd_prop h) Us : propT \<Longrightarrow>
    prf_ok ax H e Hs (PThm (h, b)) (atom_prop (hd_prop h) Us)"
| PClass: "has_sort alg T [c] \<Longrightarrow> e \<turnstile> of_class T c : propT \<Longrightarrow> prf_ok ax H e Hs (PClass T c) (of_class T c)"

lemma prf_ok_typing: "prf_ok ax H e Hs p \<phi> \<Longrightarrow> e \<turnstile> \<phi> : propT"
proof (induction rule: prf_ok.induct)
  case (AbsP e A t Hs p B a)
  then show ?case by (simp add: typing_implies)
next
  case (Abst T U e Hs p B a b)
  have "cert_typ alg ar (all_type U)" using Abst(2) by (simp add: all_type_def cert_typ_fun)
  with Abst show ?case by (simp add: typing_all_const)
next
  case (PAppt e Hs p U f t t')
  then show ?case by (auto simp: all_const_def)
next
  case (PAppp e Hs p A B q)
  then show ?case by (simp add: typing_implies)
qed

end



subsection \<open>Soundness\<close>

lemma vsubst_no_vars: "vars t = {} \<Longrightarrow> vsubst \<sigma> t = t"
  by (induction t) auto

lemma loose_bvar_inst [simp]: "loose_bvar (inst \<rho> t) k = loose_bvar t k"
  by (induction t arbitrary: k) auto

lemma vars_inst_empty: "vars t = {} \<Longrightarrow> vars (inst \<rho> t) = {}"
  by (induction t) auto

context prf_sig
begin

text \<open>Substitutions of the schematic variables by free variables exist:\<close>

definition free_subst :: vsubst where
  "free_subst x T = Free (fst x) T"

lemma gsubst_free_subst: "gsubst free_subst"
  by (auto simp: gsubst_def wt_subst_def closed_subst_def closed_def free_subst_def)

lemma cinst_tyinst:
  assumes "list_all2 (\<lambda>(v, S) U. has_sort alg U S \<and> cert_typ alg ar U) vs Us"
  shows "cinst (tyinst vs Us)"
proof -
  have "has_sort alg (tyinst vs Us v S) S \<and> (sort_ok alg S \<longrightarrow> cert_typ alg ar (tyinst vs Us v S))" for v S
  proof (cases "map_of (zip vs Us) (v, S)")
    case (Some U)
    from map_of_SomeD[OF this] obtain i where "i < length vs" "vs ! i = (v, S)" "Us ! i = U"
      using assms by (auto simp: set_zip list_all2_lengthD)
    with list_all2_nthD[OF assms, of i] Some show ?thesis by (auto simp: tyinst_def)
  qed (simp add: tyinst_def cert_typ_def del: has_sort.simps)
  then show ?thesis by (simp add: cinst_def wsinst_def cert_inst_def)
qed

lemma closed_atom_prop: "closed (atom_prop A Us)"
  using closed_close by (simp add: atom_prop_def closed_def)

lemma ap_close: "ap \<rho> \<sigma> (close A) = inst \<rho> (close A)"
  by (simp add: ap_def vsubst_no_vars vars_inst_empty vars_close)

end

locale prf_model = prf_sig alg ar ctab close tyargs +
  pure_model alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval
  for alg ar ctab close tyargs and umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix \<open>\<in>\<^sub>u\<close> 50)
    and ufun uapp ulam ubool utrue ufalse tcon cls cval
begin

lemma ubval_true [simp]: "ubval b = utrue \<longleftrightarrow> b"
  using utrue_ufalse by (simp add: ubval_def)

lemma tsem_propT [simp]: "tsem \<eta> propT = ubool"
  by (simp add: propT_def)

lemma holds_atD: "closed t \<Longrightarrow> holds_at \<eta> \<xi> t \<Longrightarrow> sem \<eta> \<xi> bv t = utrue"
  by (simp add: holds_at_def sem_closed[of t \<eta> \<xi> "\<lambda>_. utrue" bv])

lemma sem_all_app:
  assumes "sem \<eta> \<xi> bv f \<in>\<^sub>u ufun (tsem \<eta> U) ubool" "sem \<eta> \<xi> bv (all_const U $ f) = utrue" "v \<in>\<^sub>u tsem \<eta> U"
  shows "uapp (sem \<eta> \<xi> bv f) v = utrue"
  using assms by (simp add: all_const_def csem_def all_val_def uapp_ulam all_type_def)

text \<open>
  Soundness: if the axioms and class propositions that the proofs use are valid, a proposition
  that is proved holds at every valuation under which its hypotheses hold.
\<close>

theorem prf_ok_sound:
  assumes g: "good \<eta> \<xi>"
    and axv: "\<And>A. ax A \<Longrightarrow> valid [] [] (close A)"
    and clv: "\<And>T c. has_sort alg T [c] \<Longrightarrow> valid [] [] (of_class T c)"
    and hyp: "\<And>h. h \<in> H \<Longrightarrow> closed h \<and> holds_at \<eta> \<xi> h"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> \<forall>A\<in>set Hs. sem \<eta> \<xi> bv A = utrue \<Longrightarrow>
    sem \<eta> \<xi> bv \<phi> = utrue"
proof (induction arbitrary: bv rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  have "sem \<eta> \<xi> bv \<phi> = sem \<eta> \<xi> bv \<psi>"
    by (rule sem_conv[OF g prf_ok_typing[OF conv.hyps(1)] conv.hyps(3,2) conv.prems(1)])
  with conv show ?case by simp
next
  case (PBound i Hs e)
  then show ?case by simp
next
  case (AbsP e A t Hs p B a)
  have b: "sem \<eta> \<xi> bv A \<in>\<^sub>u ubool" "sem \<eta> \<xi> bv B \<in>\<^sub>u ubool"
    using sem_typing[OF g AbsP.hyps(1) AbsP.prems(1)] sem_typing[OF g prf_ok_typing[OF AbsP.hyps(3)] AbsP.prems(1)]
    by simp_all
  show ?case using sem_implies[OF b] AbsP.IH[OF AbsP.prems(1)] AbsP.prems(2) by simp
next
  case (Abst T U e Hs p B a b)
  have bv: "bvals \<eta> (e\<langle>0:U\<rangle>) (push v bv)" if "v \<in>\<^sub>u tsem \<eta> U" for v
    by (rule bvals_push[OF Abst.prems(1) that])
  have b: "sem \<eta> \<xi> (push v bv) B \<in>\<^sub>u ubool" if "v \<in>\<^sub>u tsem \<eta> U" for v
    using sem_typing[OF g prf_ok_typing[OF Abst.hyps(3)] bv[OF that]] by simp
  have hs: "sem \<eta> \<xi> (push v bv) (incr_bv 1 0 A) = sem \<eta> \<xi> bv A" for v A
  proof -
    have "sem \<eta> \<xi> (push v bv) (incr_bv 1 0 A) = sem \<eta> \<xi> (\<lambda>i. if i < 0 then push v bv i else push v bv (i + 1)) A"
      by (rule sem_incr_bv) simp_all
    also have "\<dots> = sem \<eta> \<xi> bv A" by (rule sem_bv_cong) (simp add: push_def)
    finally show ?thesis .
  qed
  have "sem \<eta> \<xi> (push v bv) B = utrue" if "v \<in>\<^sub>u tsem \<eta> U" for v
    using Abst.IH[OF bv[OF that]] Abst.prems(2) hs by simp
  then show ?case by (subst sem_all[OF b]) simp_all
next
  case (PAppt e Hs p U f t t')
  have tf: "e \<turnstile> f : U \<rightarrow>\<^sub>T propT"
    using prf_ok_typing[OF PAppt.hyps(1)] by (auto simp: all_const_def)
  have "sem \<eta> \<xi> bv f \<in>\<^sub>u ufun (tsem \<eta> U) ubool" using sem_typing[OF g tf PAppt.prems(1)] by simp
  moreover have "sem \<eta> \<xi> bv t \<in>\<^sub>u tsem \<eta> U" by (rule sem_typing[OF g PAppt.hyps(2) PAppt.prems(1)])
  ultimately show ?case using sem_all_app PAppt.IH[OF PAppt.prems] by simp
next
  case (PAppp e Hs p A B q)
  have t: "e \<turnstile> A : propT" "e \<turnstile> B : propT"
    using prf_ok_typing[OF PAppp.hyps(1)] by (simp_all add: typing_implies)
  have b: "sem \<eta> \<xi> bv A \<in>\<^sub>u ubool" "sem \<eta> \<xi> bv B \<in>\<^sub>u ubool"
    using sem_typing[OF g t(1) PAppp.prems(1)] sem_typing[OF g t(2) PAppp.prems(1)] by simp_all
  show ?case using sem_implies[OF b] PAppp.IH(1)[OF PAppp.prems] PAppp.IH(2)[OF PAppp.prems] by simp
next
  case (Hyp t e Hs)
  with hyp[OF Hyp.hyps(1)] show ?case by (blast intro: holds_atD)
next
  case (PAxm A Us' Us e Hs a)
  have "holds_at \<eta> \<xi> (ap (tyinst (tyargs A) Us) free_subst (close A))"
    by (rule validD[OF axv[OF PAxm.hyps(1)] g cinst_tyinst gsubst_free_subst])
      (use PAxm.hyps(2) in \<open>simp_all add: atom_ok_def\<close>)
  then show ?case
    using closed_atom_prop[of A Us] by (intro holds_atD) (simp_all add: ap_close atom_prop_def)
next
  case (Oracle A Us' Us e Hs a)
  have "holds_at \<eta> \<xi> (ap (tyinst (tyargs A) Us) free_subst (close A))"
    by (rule validD[OF axv[OF Oracle.hyps(1)] g cinst_tyinst gsubst_free_subst])
      (use Oracle.hyps(2) in \<open>simp_all add: atom_ok_def\<close>)
  then show ?case
    using closed_atom_prop[of A Us] by (intro holds_atD) (simp_all add: ap_close atom_prop_def)
next
  case (PThm h Us e Hs b)
  have "holds_at \<eta> \<xi> (ap (tyinst (tyargs (hd_prop h)) Us) free_subst (close (hd_prop h)))"
    by (rule validD[OF axv[OF PThm.hyps(1)] g cinst_tyinst gsubst_free_subst])
      (use PThm.hyps(2) in \<open>simp_all add: atom_ok_def\<close>)
  then show ?case
    using closed_atom_prop[of "hd_prop h" Us] by (intro holds_atD) (simp_all add: ap_close atom_prop_def)
next
  case (PClass T c e Hs)
  have ci: "cinst TVar" by (simp add: cinst_def wsinst_def cert_inst_def cert_typ_def del: has_sort.simps)
  have "holds_at \<eta> \<xi> (ap TVar free_subst (of_class T c))"
    by (rule validD[OF clv[OF PClass.hyps(1)] g ci gsubst_free_subst]) simp_all
  moreover have "ap TVar free_subst (of_class T c) = of_class T c"
    by (simp add: ap_def of_class_def free_subst_def)
  moreover have "closed (of_class T c)" by (simp add: of_class_def closed_def)
  ultimately show ?case by (simp add: holds_atD)
qed

end


subsection \<open>Instances\<close>

context prf_sig
begin

text \<open>
  The instance of a proof: the term annotations are instantiated, the type annotations and
  type arguments substituted; hypotheses are unchanged (they have no schematic variables).
\<close>

definition prf_ap :: "tinst \<Rightarrow> vsubst \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_ap \<rho> \<sigma> = map_proof_terms (ap \<rho> \<sigma>) (tsubst \<rho>)"

lemma tsubst_dummyT [simp]: "tsubst \<rho> dummyT = dummyT"
  by (simp add: dummyT_def)

lemma tmatch_tsubst: "tmatch T U \<Longrightarrow> tmatch (tsubst \<rho> T) (tsubst \<rho> U)"
proof (induction rule: tmatch.induct)
  case (Type Ts Us a)
  then show ?case by (simp, intro tmatch.Type) (auto simp: list_all2_map1 list_all2_map2 elim: list_all2_mono)
qed (auto intro: tmatch.intros)

lemma erase_ap_erase: "erase (ap \<rho> \<sigma> (erase t)) = erase (ap \<rho> \<sigma> t)"
  by (induction t) simp_all

lemma ueq_ap:
  assumes c: "closed_subst \<sigma>" and st: "s \<approx> t"
  shows "ap \<rho> \<sigma> s \<approx> ap \<rho> \<sigma> t"
proof -
  have "equivclp (sup beta eta) (erase (ap \<rho> \<sigma> x)) (erase (ap \<rho> \<sigma> y))"
    if "equivclp (sup beta eta) x y" for x y
    using that
  proof (induction rule: equivclp_induct)
    case (step y z)
    have "sup beta eta (erase (ap \<rho> \<sigma> y)) (erase (ap \<rho> \<sigma> z)) \<or> sup beta eta (erase (ap \<rho> \<sigma> z)) (erase (ap \<rho> \<sigma> y))"
      using step(2) by (auto simp: ap_def intro!: erase_beta erase_eta beta_vsubst[OF _ c] eta_vsubst[OF _ c] beta_inst eta_inst)
    from equivclp_into_equivclp[OF step(3) this] show ?case .
  qed simp
  from this[OF st] show ?thesis by (simp add: erase_ap_erase)
qed

lemma ann_ok_ap: "ann_ok t u \<Longrightarrow> closed_subst \<sigma> \<Longrightarrow> ann_ok (map_option (ap \<rho> \<sigma>) t) (ap \<rho> \<sigma> u)"
  by (cases t) (simp_all add: ueq_ap)

lemma tann_ok_tsubst: "tann_ok T U \<Longrightarrow> tann_ok (map_option (tsubst \<rho>) T) (tsubst \<rho> U)"
  by (cases T) (simp_all add: tmatch_tsubst)

lemma map_of_zip_map:
  "length vs = length Us \<Longrightarrow> map_of (zip vs (map f Us)) x = map_option f (map_of (zip vs Us) x)"
  by (induction vs Us rule: list_induct2) auto

lemma tyinst_map:
  "length vs = length Us \<Longrightarrow> (v, S) \<in> set vs \<Longrightarrow> tyinst vs (map f Us) v S = f (tyinst vs Us v S)"
proof -
  assume l: "length vs = length Us" and m: "(v, S) \<in> set vs"
  then have "map_of (zip vs Us) (v, S) \<noteq> None"
    by (simp add: map_of_zip_is_None[OF l])
  then show ?thesis by (auto simp: tyinst_def map_of_zip_map[OF l])
qed

lemma has_sort_cinst: "cinst \<rho> \<Longrightarrow> has_sort alg T S \<Longrightarrow> has_sort alg (tsubst \<rho> T) S"
  by (rule has_sort_tsubst) (auto simp: wsinst_def dest: cinstD)

lemma ap_atom_prop:
  assumes l: "length (tyargs A) = length Us"
  shows "ap \<rho> \<sigma> (atom_prop A Us) = atom_prop A (map (tsubst \<rho>) Us)"
proof -
  have "ap \<rho> \<sigma> (atom_prop A Us) = inst (\<lambda>v S. tsubst \<rho> (tyinst (tyargs A) Us v S)) (close A)"
    by (simp add: atom_prop_def ap_def vsubst_no_vars vars_inst_empty vars_close inst_inst)
  also have "\<dots> = atom_prop A (map (tsubst \<rho>) Us)"
    unfolding atom_prop_def
  proof (rule inst_cong)
    fix U assume "U \<in> typs (close A)"
    then have "tvars U \<subseteq> set (tyargs A)" using ttvars_close[of A] by (auto simp: ttvars_def)
    then show "tsubst (\<lambda>v S. tsubst \<rho> (tyinst (tyargs A) Us v S)) U = tsubst (tyinst (tyargs A) (map (tsubst \<rho>) Us)) U"
      by (intro tsubst_cong) (auto simp: tyinst_map[OF l])
  qed
  finally show ?thesis .
qed

lemma atom_ok_ap:
  assumes "atom_ok A Us' Us" "cinst \<rho>"
  shows "atom_ok A (map_option (map (tsubst \<rho>)) Us') (map (tsubst \<rho>) Us)"
proof -
  have "has_sort alg (tsubst \<rho> U) S \<and> cert_typ alg ar (tsubst \<rho> U)"
    if "has_sort alg U S \<and> cert_typ alg ar U" for U S
    using that has_sort_cinst[OF assms(2)] cinstD(2)[OF assms(2)] cert_typ_tsubst by blast
  with assms(1) show ?thesis
    by (auto simp: atom_ok_def list_all2_map2 elim: list_all2_mono split: option.splits)
qed

theorem prf_ok_ap:
  assumes \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>" and H: "\<And>h. h \<in> H \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> prf_ok ax H (ienv \<rho> e) (map (ap \<rho> \<sigma>) Hs) (prf_ap \<rho> \<sigma> p) (ap \<rho> \<sigma> \<phi>)"
proof (induction rule: prf_ok.induct)
  note ty = typing_ap_inst[OF _ cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]
  {
    case (conv e Hs p \<phi> \<psi>)
    show ?case
      by (rule prf_ok.conv[OF conv.IH conv_vsubst[OF conv_inst[OF conv.hyps(2) cert_inst_inst_ok[OF cinstD(2)[OF \<rho>]]]
          gsubstD(1)[OF \<sigma>], folded ap_def]])
        (use ty[OF conv.hyps(3)] in simp)
  next
    case (PBound i Hs e)
    then show ?case using ty[OF PBound.hyps(3)] prf_ok.PBound[of i "map (ap \<rho> \<sigma>) Hs"] by (simp add: prf_ap_def)
  next
    case (AbsP e A t Hs p B a)
    then show ?case using ty[OF AbsP.hyps(1)] ann_ok_ap[OF AbsP.hyps(2) gsubstD(2)[OF \<sigma>]]
      by (auto simp: prf_ap_def intro!: prf_ok.AbsP)
  next
    case (Abst T U e Hs p B a b)
    have eq: "map (ap \<rho> \<sigma>) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (ap \<rho> \<sigma>) Hs)"
      by (simp add: ap_lift[OF gsubstD(1)[OF \<sigma>]])
    from Abst.IH[unfolded eq tsubst_shift] show ?case
      using tann_ok_tsubst[OF Abst.hyps(1)] cert_typ_tsubst[OF Abst.hyps(2) cinstD(2)[OF \<rho>]]
      by (simp add: prf_ap_def prf_ok.Abst)
  next
    case (PAppt e Hs p U f t t')
    then show ?case using ty[OF PAppt.hyps(2)] ann_ok_ap[OF PAppt.hyps(3) gsubstD(2)[OF \<sigma>]]
      by (auto simp: prf_ap_def intro!: prf_ok.PAppt)
  next
    case (PAppp e Hs p A B q)
    then show ?case by (auto simp: prf_ap_def intro: prf_ok.PAppp)
  next
    case (Hyp t e Hs)
    have "ap \<rho> \<sigma> t = t" using H[OF Hyp.hyps(1)] by (simp add: ap_ground)
    with Hyp ty[OF Hyp.hyps(2)] show ?case by (simp add: prf_ap_def prf_ok.Hyp)
  next
    case (PAxm A Us' Us e Hs a)
    have l: "length (tyargs A) = length Us" using PAxm.hyps(2) by (auto simp: atom_ok_def dest: list_all2_lengthD)
    have "prf_ok ax H (ienv \<rho> e) (map (ap \<rho> \<sigma>) Hs) (PAxm a A (map_option (map (tsubst \<rho>)) Us'))
        (atom_prop A (map (tsubst \<rho>) Us))"
      by (rule prf_ok.PAxm) (use PAxm.hyps(1) atom_ok_ap[OF PAxm.hyps(2) \<rho>] ty[OF PAxm.hyps(3)] in \<open>simp_all add: ap_atom_prop[OF l]\<close>)
    then show ?case by (simp add: prf_ap_def ap_atom_prop[OF l])
  next
    case (Oracle A Us' Us e Hs a)
    have l: "length (tyargs A) = length Us" using Oracle.hyps(2) by (auto simp: atom_ok_def dest: list_all2_lengthD)
    have "prf_ok ax H (ienv \<rho> e) (map (ap \<rho> \<sigma>) Hs) (Oracle a A (map_option (map (tsubst \<rho>)) Us'))
        (atom_prop A (map (tsubst \<rho>) Us))"
      by (rule prf_ok.Oracle) (use Oracle.hyps(1) atom_ok_ap[OF Oracle.hyps(2) \<rho>] ty[OF Oracle.hyps(3)] in \<open>simp_all add: ap_atom_prop[OF l]\<close>)
    then show ?case by (simp add: prf_ap_def ap_atom_prop[OF l])
  next
    case (PThm h Us e Hs b)
    have l: "length (tyargs (hd_prop h)) = length Us" using PThm.hyps(2) by (auto simp: atom_ok_def dest: list_all2_lengthD)
    have "prf_ok ax H (ienv \<rho> e) (map (ap \<rho> \<sigma>) Hs)
        (PThm (hd_set_types h (map_option (map (tsubst \<rho>)) (hd_types h)), b)) (atom_prop (hd_prop h) (map (tsubst \<rho>) Us))"
      by (rule prf_ok.PThm[of _ "hd_set_types h (map_option (map (tsubst \<rho>)) (hd_types h))", simplified])
        (use PThm.hyps(1) atom_ok_ap[OF PThm.hyps(2) \<rho>] ty[OF PThm.hyps(3)] in \<open>simp_all add: ap_atom_prop[OF l]\<close>)
    then show ?case by (simp add: prf_ap_def ap_atom_prop[OF l])
  next
    case (PClass T c e Hs)
    have "has_sort alg (tsubst \<rho> T) [c]" by (rule has_sort_cinst[OF \<rho> PClass.hyps(1)])
    moreover have "ap \<rho> \<sigma> (of_class T c) = of_class (tsubst \<rho> T) c" by (simp add: of_class_def)
    ultimately show ?case using ty[OF PClass.hyps(2)] by (simp add: prf_ap_def prf_ok.PClass)
  }
qed

end


subsection \<open>Substitution of free variables\<close>

text \<open>
  \<open>fsubst \<tau> t\<close> replaces the free variables of \<open>t\<close> by terms that may have loose bound
  variables (lifted below binders). It turns fresh free variables back into parameters.
\<close>

fun fsubst :: "(name \<Rightarrow> ptyp \<Rightarrow> pterm) \<Rightarrow> pterm \<Rightarrow> pterm" where
  "fsubst \<tau> (Free x T) = \<tau> x T"
| "fsubst \<tau> (Abs a T t) = Abs a T (fsubst (\<lambda>x U. lift (\<tau> x U) 0) t)"
| "fsubst \<tau> (s $ t) = fsubst \<tau> s $ fsubst \<tau> t"
| "fsubst \<tau> t = t"

lemma fsubst_lift: "0 \<le> k \<Longrightarrow> fsubst (\<lambda>x U. lift (\<tau> x U) k) (lift t k) = lift (fsubst \<tau> t) k"
proof (induction t arbitrary: \<tau> k)
  case (Abs a T t)
  have "fsubst (\<lambda>x U. lift (lift (\<tau> x U) k) 0) (lift t (k + 1)) = fsubst (\<lambda>x U. lift (lift (\<tau> x U) 0) (k + 1)) (lift t (k + 1))"
    using lift_lift[of 0 k] Abs.prems by simp
  also have "\<dots> = lift (fsubst (\<lambda>x U. lift (\<tau> x U) 0) t) (k + 1)"
    using Abs.IH[of "k + 1" "\<lambda>x U. lift (\<tau> x U) 0"] Abs.prems by simp
  finally show ?case by simp
qed simp_all

lemma fsubst_subst: "0 \<le> k \<Longrightarrow> fsubst \<tau> (t[s/k]) = (fsubst (\<lambda>x U. lift (\<tau> x U) k) t)[fsubst \<tau> s/k]"
proof (induction t arbitrary: \<tau> k s)
  case (Abs a T t)
  have "fsubst \<tau> ((Abs a T t)[s/k]) = Abs a T (fsubst (\<lambda>x U. lift (\<tau> x U) 0) (t[lift s 0/k + 1]))" by simp
  also have "\<dots> = Abs a T ((fsubst (\<lambda>x U. lift (lift (\<tau> x U) 0) (k + 1)) t)[fsubst (\<lambda>x U. lift (\<tau> x U) 0) (lift s 0)/k + 1])"
    using Abs.IH[of "k + 1"] Abs.prems by simp
  also have "\<dots> = Abs a T ((fsubst (\<lambda>x U. lift (lift (\<tau> x U) k) 0) t)[lift (fsubst \<tau> s) 0/k + 1])"
    using lift_lift[of 0 k] Abs.prems fsubst_lift[of 0 \<tau> s] by simp
  finally show ?case by simp
qed (simp_all add: subst_Bound)

lemma loose_bvar1_fsubst:
  "\<not> loose_bvar1 t k \<Longrightarrow> (\<And>x U. \<not> loose_bvar1 (\<tau> x U) k) \<Longrightarrow> 0 \<le> k \<Longrightarrow> \<not> loose_bvar1 (fsubst \<tau> t) k"
proof (induction t arbitrary: \<tau> k)
  case (Abs a T t)
  have "\<not> loose_bvar1 (lift (\<tau> x U) 0) (k + 1)" for x U using Abs.prems(2,3) by simp
  with Abs show ?case by simp
qed simp_all

lemma beta_fsubst: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> fsubst \<tau> s \<rightarrow>\<^sub>\<beta> fsubst \<tau> t"
proof (induction arbitrary: \<tau> set: beta)
  case (beta a T s t)
  show ?case using fsubst_subst[of 0 \<tau> s t] by simp
qed auto

lemma eta_fsubst: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> fsubst \<tau> s \<rightarrow>\<^sub>\<eta> fsubst \<tau> t"
proof (induction arbitrary: \<tau> set: eta)
  case (eta s a T d)
  have "\<not> loose_bvar1 (fsubst (\<lambda>x U. lift (\<tau> x U) 0) s) 0"
    by (rule loose_bvar1_fsubst) (use eta in simp_all)
  then show ?case using eta.eta[of "fsubst (\<lambda>x U. lift (\<tau> x U) 0) s" a T "fsubst \<tau> d"] fsubst_subst[of 0 \<tau> s d]
    by simp
qed auto

lemma beta_eta_fsubst: "(sup beta eta)\<^sup>*\<^sup>* s t \<Longrightarrow> (sup beta eta)\<^sup>*\<^sup>* (fsubst \<tau> s) (fsubst \<tau> t)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl beta_fsubst eta_fsubst)

lemma unname_fsubst: "unname (fsubst \<tau> t) = fsubst (\<lambda>x U. unname (\<tau> x U)) (unname t)"
  by (induction t arbitrary: \<tau>) simp_all

lemma erase_fsubst: "erase (fsubst \<tau> t) = fsubst (\<lambda>x U. erase (\<tau> x U)) (erase t)"
  by (induction t arbitrary: \<tau>) simp_all

lemma ueq_fsubst:
  assumes st: "s \<approx> t"
  shows "fsubst \<tau> s \<approx> fsubst \<tau> t"
proof -
  let ?\<tau> = "\<lambda>x U. erase (\<tau> x U)"
  have "equivclp (sup beta eta) (fsubst ?\<tau> x) (fsubst ?\<tau> y)" if "equivclp (sup beta eta) x y" for x y
    using that
  proof (induction rule: equivclp_induct)
    case (step y z)
    have "sup beta eta (fsubst ?\<tau> y) (fsubst ?\<tau> z) \<or> sup beta eta (fsubst ?\<tau> z) (fsubst ?\<tau> y)"
      using step(2) by (auto intro: beta_fsubst eta_fsubst)
    from equivclp_into_equivclp[OF step(3) this] show ?case .
  qed simp
  from this[OF st] show ?thesis by (simp add: erase_fsubst)
qed

lemma fsubst_id: "(\<And>x U. x \<in> fnames t \<Longrightarrow> \<tau> x U = Free x U) \<Longrightarrow> fsubst \<tau> t = t"
  by (induction t arbitrary: \<tau>) auto

lemma fnames_inst [simp]: "fnames (inst \<rho> t) = fnames t"
  by (induction t) simp_all

text \<open>The atoms of a proof, and the free variables of its annotations:\<close>

fun prf_atoms :: "prf \<Rightarrow> pterm set" where
  "prf_atoms (Abst a T p) = prf_atoms p"
| "prf_atoms (AbsP a t p) = prf_atoms p"
| "prf_atoms (PAppt p t) = prf_atoms p"
| "prf_atoms (PAppp p q) = prf_atoms p \<union> prf_atoms q"
| "prf_atoms (PAxm a A Us) = {A}"
| "prf_atoms (Oracle a A Us) = {A}"
| "prf_atoms (PThm (h, b)) = {hd_prop h}"
| "prf_atoms p = {}"

fun prf_fnames :: "prf \<Rightarrow> name set" where
  "prf_fnames (Abst a T p) = prf_fnames p"
| "prf_fnames (AbsP a t p) = (case t of None \<Rightarrow> {} | Some t \<Rightarrow> fnames t) \<union> prf_fnames p"
| "prf_fnames (PAppt p t) = prf_fnames p \<union> (case t of None \<Rightarrow> {} | Some t \<Rightarrow> fnames t)"
| "prf_fnames (PAppp p q) = prf_fnames p \<union> prf_fnames q"
| "prf_fnames p = {}"

lemma finite_prf_atoms [simp]: "finite (prf_atoms p)" and finite_prf_fnames [simp]: "finite (prf_fnames p)"
  by (induction p rule: prf_atoms.induct) (auto split: option.split)

fun prf_fsubst :: "(name \<Rightarrow> ptyp \<Rightarrow> pterm) \<Rightarrow> prf \<Rightarrow> prf" where
  "prf_fsubst \<tau> (Abst a T p) = Abst a T (prf_fsubst (\<lambda>x U. lift (\<tau> x U) 0) p)"
| "prf_fsubst \<tau> (AbsP a t p) = AbsP a (map_option (fsubst \<tau>) t) (prf_fsubst \<tau> p)"
| "prf_fsubst \<tau> (PAppt p t) = PAppt (prf_fsubst \<tau> p) (map_option (fsubst \<tau>) t)"
| "prf_fsubst \<tau> (PAppp p q) = PAppp (prf_fsubst \<tau> p) (prf_fsubst \<tau> q)"
| "prf_fsubst \<tau> p = p"

context prf_sig
begin

lemma typing_fsubst:
  "e \<turnstile> t : T \<Longrightarrow> (\<And>x U. cert_typ alg ar U \<Longrightarrow> e \<turnstile> \<tau> x U : U) \<Longrightarrow> e \<turnstile> fsubst \<tau> t : T"
proof (induction arbitrary: \<tau> rule: typing.induct)
  case (Abs T e t U a)
  have "e\<langle>0:T\<rangle> \<turnstile> lift (\<tau> x V) 0 : V" if "cert_typ alg ar V" for x V using Abs.prems[OF that] by auto
  with Abs show ?case by auto
qed auto

lemma conv_fsubst:
  assumes ty: "e \<turnstile> s : T" "e \<turnstile> t : T" and \<tau>: "\<And>x U. cert_typ alg ar U \<Longrightarrow> e \<turnstile> \<tau> x U : U"
    and c: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "fsubst \<tau> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> fsubst \<tau> t"
proof -
  have "e \<turnstile> fsubst \<tau> s : T" "e \<turnstile> fsubst \<tau> t : T"
    by (rule typing_fsubst[OF ty(1)], rule \<tau>, assumption) (rule typing_fsubst[OF ty(2)], rule \<tau>, assumption)
  then have ws: "wt s" "wt (fsubst \<tau> s)" "wt (fsubst \<tau> t)"
    using ty by (auto simp: wt_def)
  obtain u v where uv: "(sup beta eta)\<^sup>*\<^sup>* s u" "(sup beta eta)\<^sup>*\<^sup>* t v" "aconv_term u v"
    using conv_iff[OF ws(1)] c by blast
  have "aconv_term (fsubst \<tau> u) (fsubst \<tau> v)"
    using uv(3) by (simp add: aconv_term_unname unname_fsubst)
  then show ?thesis using conv_iff[OF ws(2)] ws(3) beta_eta_fsubst[OF uv(1)] beta_eta_fsubst[OF uv(2)] by blast
qed

lemma fsubst_all_const [simp]: "fsubst \<tau> (all_const U) = all_const U"
  and fsubst_implies [simp]: "fsubst \<tau> implies = implies"
  by (simp_all add: all_const_def implies_def)

lemma fsubst_of_class [simp]: "fsubst \<tau> (of_class T c) = of_class T c"
  by (simp add: of_class_def)

lemma fnames_close_atom_prop: "fnames (atom_prop A Us) = fnames (close A)"
  by (simp add: atom_prop_def)

theorem prf_ok_fsubst:
  assumes H: "\<And>h. h \<in> H \<Longrightarrow> fnames h \<inter> N = {}"
  shows "prf_ok ax H e Hs p \<phi> \<Longrightarrow> (\<And>x U. cert_typ alg ar U \<Longrightarrow> e \<turnstile> \<tau> x U : U) \<Longrightarrow> (\<And>x U. x \<notin> N \<Longrightarrow> \<tau> x U = Free x U) \<Longrightarrow>
    (\<forall>A\<in>prf_atoms p. fnames (close A) \<inter> N = {}) \<Longrightarrow>
    prf_ok ax H e (map (fsubst \<tau>) Hs) (prf_fsubst \<tau> p) (fsubst \<tau> \<phi>)"
proof (induction arbitrary: \<tau> rule: prf_ok.induct)
  case (conv e Hs p \<phi> \<psi>)
  have "prf_ok ax H e (map (fsubst \<tau>) Hs) (prf_fsubst \<tau> p) (fsubst \<tau> \<phi>)"
    by (rule conv.IH) (use conv.prems in auto)
  moreover have "fsubst \<tau> \<phi> \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> fsubst \<tau> \<psi>"
    by (rule conv_fsubst[OF prf_ok_typing[OF conv.hyps(1)] conv.hyps(3) _ conv.hyps(2)]) (use conv.prems in auto)
  moreover have "e \<turnstile> fsubst \<tau> \<psi> : propT" by (rule typing_fsubst[OF conv.hyps(3)]) (use conv.prems in auto)
  ultimately show ?case by (rule prf_ok.conv)
next
  case (PBound i Hs e)
  then show ?case using typing_fsubst[OF PBound.hyps(3) PBound.prems(1)] prf_ok.PBound[of i "map (fsubst \<tau>) Hs"] by simp
next
  case (AbsP e A t Hs p B a)
  then show ?case using typing_fsubst[OF AbsP.hyps(1) AbsP.prems(1)]
    by (auto intro!: prf_ok.AbsP simp: ann_ok_def ueq_fsubst split: option.splits)
next
  case (Abst T U e Hs p B a b)
  let ?\<tau> = "\<lambda>x U. lift (\<tau> x U) 0"
  have IH: "prf_ok ax H (e\<langle>0:U\<rangle>) (map (fsubst ?\<tau>) (map (incr_bv 1 0) Hs)) (prf_fsubst ?\<tau> p) (fsubst ?\<tau> B)"
  proof (rule Abst.IH)
    show "e\<langle>0:U\<rangle> \<turnstile> ?\<tau> x V : V" if "cert_typ alg ar V" for x V using Abst.prems(1)[OF that] by auto
  qed (use Abst.prems in simp_all)
  have eq: "map (fsubst ?\<tau>) (map (incr_bv 1 0) Hs) = map (incr_bv 1 0) (map (fsubst \<tau>) Hs)"
    using fsubst_lift[of 0 \<tau>] by simp
  from IH[unfolded eq] show ?case using Abst.hyps(1,2) by (simp add: prf_ok.Abst)
next
  case (PAppt e Hs p U f t t')
  then show ?case using typing_fsubst[OF PAppt.hyps(2) PAppt.prems(1)]
    by (auto intro!: prf_ok.PAppt simp: ann_ok_def ueq_fsubst split: option.splits)
next
  case (PAppp e Hs p A B q)
  have "prf_ok ax H e (map (fsubst \<tau>) Hs) (prf_fsubst \<tau> p) (implies $ fsubst \<tau> A $ fsubst \<tau> B)"
    using PAppp.IH(1)[of \<tau>] PAppp.prems by simp
  moreover have "prf_ok ax H e (map (fsubst \<tau>) Hs) (prf_fsubst \<tau> q) (fsubst \<tau> A)"
    using PAppp.IH(2)[of \<tau>] PAppp.prems by simp
  ultimately show ?case by (simp add: prf_ok.PAppp)
next
  case (Hyp t e Hs)
  have "fsubst \<tau> t = t" using H[OF Hyp.hyps(1)] Hyp.prems(2) by (auto intro: fsubst_id)
  with Hyp show ?case by (simp add: prf_ok.Hyp)
next
  case (PAxm A Us' Us e Hs a)
  have "fsubst \<tau> (atom_prop A Us) = atom_prop A Us"
    by (rule fsubst_id) (use PAxm.prems(2,3) in \<open>auto simp: fnames_close_atom_prop\<close>)
  with PAxm show ?case by (simp add: prf_ok.PAxm)
next
  case (Oracle A Us' Us e Hs a)
  have "fsubst \<tau> (atom_prop A Us) = atom_prop A Us"
    by (rule fsubst_id) (use Oracle.prems(2,3) in \<open>auto simp: fnames_close_atom_prop\<close>)
  with Oracle show ?case by (simp add: prf_ok.Oracle)
next
  case (PThm h Us e Hs b)
  have "fsubst \<tau> (atom_prop (hd_prop h) Us) = atom_prop (hd_prop h) Us"
    by (rule fsubst_id) (use PThm.prems(2,3) in \<open>auto simp: fnames_close_atom_prop\<close>)
  with PThm show ?case by (simp add: prf_ok.PThm)
next
  case (PClass T c e Hs)
  then show ?case by (simp add: prf_ok.PClass)
qed

end

end
