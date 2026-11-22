section \<open>Proofs: Thm_Subst_Rules\<close>

theory Thm_Subst_Rules_Proofs
  imports "Thm_Soundness.Thm_Subst_Rules" Thm_Rules_Proofs
begin

text \<open>
  The classic and tight proofs of the results of the rules of theory \<open>Thm_Subst_Rules\<close> are valid
  (the part of the invariant of theorems that session \<open>Thm_Soundness\<close> leaves out).
\<close>

text \<open>
  \<open>Thm.incr_indexes\<close> applies \<open>Proofterm.incr_indexes\<close> and \<open>ZTerm.incr_indexes_proof\<close> to the
  proofs if the increment is positive.
\<close>

lemma zterm_ok_zsubst_term':
  "zterm_ok t \<Longrightarrow> (\<And>T. ztyp_ok T \<Longrightarrow> ztyp_ok (tf T)) \<Longrightarrow>
    (\<And>x T u. vf (x, T) = Some u \<Longrightarrow> ztyp_ok T \<Longrightarrow> zterm_ok u) \<Longrightarrow> zterm_ok (zsubst_term tf vf t)"
  by (induction tf vf t rule: zsubst_term.induct) (auto split: option.splits)

lemma prf_idx_abshyp: "prf_idx P p \<Longrightarrow> prf_idx P (abshyp h i p)"
  by (induction h i p rule: abshyp.induct) auto

lemma prf_nolb_abshyp: "prf_nolb k p \<Longrightarrow> prf_nolb k (abshyp h i p)"
  by (induction h i p arbitrary: k rule: abshyp.induct) auto

lemma zinv_zabshyp: "zinv p \<Longrightarrow> zinv (zabshyp h l p)"
  by (induction h l p rule: zabshyp.induct) auto

lemma znolb_zabshyp: "znolb k p \<Longrightarrow> znolb k (zabshyp h l p)"
  by (induction h l p arbitrary: k rule: zabshyp.induct) auto

lemma zhyps_zabshyp: "zhyps (zabshyp h l p) \<subseteq> zhyps p"
  by (induction h l p rule: zabshyp.induct) auto

lemma zinv_ZAbsts: "zinv (ZAbsts xs p) \<longleftrightarrow> (\<forall>(a, T)\<in>set xs. ztyp_ok T) \<and> zinv p"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x) (simp add: ZAbsts_def)
qed (simp add: ZAbsts_def)

lemma znolb_ZAbsts: "znolb k (ZAbsts xs p) \<longleftrightarrow> znolb (k + integer_of_nat (length xs)) p"
proof (induction xs arbitrary: k)
  case (Cons x xs)
  obtain a T where x: "x = (a, T)" by (cases x)
  have "k + 1 + integer_of_nat (length xs) = k + integer_of_nat (length (x # xs))"
    by (simp add: integer_of_nat_eq_of_nat)
  moreover have "znolb k (ZAbsts (x # xs) p) = znolb (k + 1) (ZAbsts xs p)" by (simp add: ZAbsts_def x)
  ultimately show ?case by (simp only: Cons.IH)
qed (simp add: ZAbsts_def)

lemma zhyps_ZAbsts [simp]: "zhyps (ZAbsts xs p) = zhyps p"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x) (simp add: ZAbsts_def)
qed (simp add: ZAbsts_def)

lemma prf_idx_mk_Abst: "prf_idx P (mk_Abst ps p) \<longleftrightarrow> prf_idx P p"
  by (induction ps) (auto simp: mk_Abst_def)

lemma prf_nolb_mk_Abst: "prf_nolb k (mk_Abst ps p) \<longleftrightarrow> prf_nolb (k + integer_of_nat (length ps)) p"
  by (induction ps arbitrary: k) (auto simp: mk_Abst_def algebra_simps integer_of_nat_eq_of_nat)

lemma prf_idx_prf_abstract_over_aux: "prf_idx P p \<Longrightarrow> prf_idx P (prf_abstract_over_aux v lev p)"
  unfolding prf_idx_def using abstract_over_aux_sub by (fastforce dest: prf_terms_prf_abstract_over_aux)

lemma prf_nolb_prf_abstract_over_aux:
  "prf_nolb k p \<Longrightarrow> lev \<le> k \<Longrightarrow> prf_nolb (k + 1) (prf_abstract_over_aux v lev p)"
proof (induction v lev p arbitrary: k rule: prf_abstract_over_aux.induct)
  case (2 v lev a T p)
  from "2.prems" have "prf_nolb (k + 1) p" "lev + 1 \<le> k + 1" by simp_all
  from "2.IH"[OF this] show ?case by simp
qed (auto simp: prf_abstract_term_eq loose_bvar_abstract_over_aux')

lemma zterm_ok_zabstract_term: "zterm_ok t \<Longrightarrow> zterm_ok (zabstract_term z i t)"
  by (induction z i t rule: zabstract_term.induct) auto

lemma zloose_zabstract_term:
  "\<not> zloose t k \<Longrightarrow> lev \<le> k \<Longrightarrow> \<not> zloose (zabstract_term z lev t) (k + 1)"
proof (induction z lev t arbitrary: k rule: zabstract_term.induct)
  case (1 z i x T t)
  show ?case
  proof (cases "aconv_zterm (ZAbs x T t) z")
    case False
    from "1.prems" have "\<not> zloose t (k + 1)" "i + 1 \<le> k + 1" by simp_all
    from "1.IH"[OF False this] False show ?thesis by simp
  qed (use "1.prems" in simp)
qed (auto simp: zloose_le)

lemma zinv_zabstract_proof: "zinv p \<Longrightarrow> zinv (zabstract_proof z i p)"
proof (induction z i p rule: zabstract_proof.induct)
  case (4 z i c instT inst)
  then show ?case by (auto simp: zterm_ok_zabstract_term)
qed (auto simp: zterm_ok_zabstract_term)

lemma znolb_zabstract_proof: "znolb k p \<Longrightarrow> lev \<le> k \<Longrightarrow> znolb (k + 1) (zabstract_proof z lev p)"
proof (induction z lev p arbitrary: k rule: zabstract_proof.induct)
  case (1 z i x T p)
  from "1.prems" have "znolb (k + 1) p" "i + 1 \<le> k + 1" by simp_all
  from "1.IH"[OF this] show ?case by simp
qed (auto simp: zloose_zabstract_term)

lemma zhyps_zabstract_proof [simp]: "zhyps (zabstract_proof z i p) = zhyps p"
  by (induction z i p rule: zabstract_proof.induct) auto

lemma zterm_ok_zvars: "zterm_ok t \<Longrightarrow> (x, U) \<in> zvars t \<Longrightarrow> ztyp_ok U"
  by (induction t) auto

lemma prf_nolb_prf_abstract_over_free:
  "prf_nolb 0 p \<Longrightarrow> prf_nolb 0 (forall_intr_proof x (Free x T) p)"
  using prf_nolb_prf_abstract_over_aux[of 0 p 0] by (simp add: forall_intr_proof_def prf_abstract_over_def)

lemma vars_prf_generalize:
  assumes "\<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. 0 \<le> snd (fst v)" "0 \<le> gi"
  shows "\<forall>t\<in>prf_terms (map_proof_terms (generalize_term tf fr gi) g p). \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
proof (intro ballI)
  fix t v assume "t \<in> prf_terms (map_proof_terms (generalize_term tf fr gi) g p)" "v \<in> vars t"
  then obtain s where s: "s \<in> prf_terms p" "v \<in> vars (generalize_term tf fr gi s)"
    by (auto simp: prf_terms_map_proof_terms)
  obtain y U where v: "v = (y, U)" by (cases v)
  from vars_generalize_term[of y U tf fr gi s] s(2) v
  have "(\<exists>U'. (y, U') \<in> vars s) \<or> gi \<le> snd y" by simp
  then show "0 \<le> snd (fst v)" using assms s(1) v by (force)
qed

lemma prf_terms_forall_intr_proof:
  "t \<in> prf_terms (forall_intr_proof a x p) \<Longrightarrow> \<exists>s\<in>prf_terms p. \<exists>l. t = abstract_over_aux x l s"
  using prf_terms_prf_abstract_over_aux by (simp add: forall_intr_proof_def prf_abstract_over_def)

lemma prf_idx_generalize_thm_proof:
  assumes p: "prf_idx (\<lambda>i. 0 \<le> i) pf" and gi: "0 \<le> gi"
  shows "prf_idx (\<lambda>i. 0 \<le> i) (generalize_thm_proof tfrees frees gi tps P pf)"
proof -
  let ?P = "\<lambda>p. \<forall>t\<in>prf_terms p. \<forall>v\<in>vars t. 0 \<le> snd (fst v)"
  have p1: "?P (map_proof_terms (generalize_term tfrees [] gi) (generalizeT tfrees gi) pf)"
    by (rule vars_prf_generalize[OF p[unfolded prf_idx_def] gi])
  have fi: "?P (forall_intr_proof a x q)" if "?P q" for a x q
    using that abstract_over_aux_sub by (fastforce dest: prf_terms_forall_intr_proof)
  have p2: "?P (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) xs q)" if "?P q" for xs q
    using that
  proof (induction xs arbitrary: q)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    show ?case using Cons.IH[OF fi[OF Cons.prems]] by (simp add: x)
  qed simp
  have p3: "?P (foldr (\<lambda>(x, T) p. PAppt p (Some (Var (clean_index (x, gi)) T))) xs q)" if "?P q" for xs q
    using that
  proof (induction xs)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    have "0 \<le> snd (clean_index (a, gi))" using clean_index_ge[of gi a] gi by simp
    with Cons show ?case by (simp add: x)
  qed simp
  have g: "?P (generalize_proof tfrees fr gi P pf)" for fr
    unfolding generalize_proof_def Let_def by (rule p3, rule p2, rule p1)
  show ?thesis
    unfolding generalize_thm_proof_def Let_def prf_idx_def
    using g vars_prf_generalize[OF g gi] by simp
qed

lemma prf_nolb_generalize_thm_proof:
  assumes p: "prf_nolb 0 pf"
  shows "prf_nolb 0 (generalize_thm_proof tfrees frees gi tps P pf)"
proof -
  have p1: "prf_nolb 0 (map_proof_terms (generalize_term tf fr gi) g q)" if "prf_nolb 0 q" for tf fr g q
    by (rule prf_nolb_map[OF _ _ that]) (simp_all add: loose_bvar_generalize_term')
  have p2: "prf_nolb 0 (fold (\<lambda>(x, T) p. forall_intr_proof x (Free x T) p) xs q)" if "prf_nolb 0 q" for xs q
    using that
  proof (induction xs arbitrary: q)
    case (Cons x xs)
    obtain a T where x: "x = (a, T)" by (cases x)
    show ?case using Cons.IH[OF prf_nolb_prf_abstract_over_free[OF Cons.prems]] by (simp add: x)
  qed simp
  have p3: "prf_nolb 0 (foldr (\<lambda>(x, T) p. PAppt p (Some (Var (clean_index (x, gi)) T))) xs q)" if "prf_nolb 0 q" for xs q
    using that
  proof (induction xs)
    case (Cons x xs)
    then show ?case by (cases x) simp
  qed simp
  have g: "prf_nolb 0 (generalize_proof tfrees fr gi P pf)" for fr
    unfolding generalize_proof_def Let_def by (rule p3, rule p2, rule p1[OF p])
  show ?thesis unfolding generalize_thm_proof_def Let_def using g p1[OF g] by simp
qed

lemma zinv_zgeneralize_proof:
  assumes z: "zgeneralize_proof tfrees frees gi p = return q" and p: "zinv p" and gi: "0 \<le> gi"
  shows "zinv q" "znolb 0 p \<Longrightarrow> znolb 0 q" "zhyps q = zhyps p"
proof -
  define tf :: "indexname \<times> psort \<Rightarrow> ztyp option"
    where "tf = (\<lambda>((a, i), S). if i = -1 \<and> a \<in> set tfrees then Some (ZTVar (a, gi) S) else None)"
  define var :: "indexname \<times> ztyp \<Rightarrow> zterm option"
    where "var = (\<lambda>((x, i), T). if i = -1 \<and> x \<in> set frees then Some (ZVar (clean_index (x, gi)) T) else None)"
  have m: "map_zproof (zsubst_type tf) (\<lambda>t. return (zsubst_term (zsubst_type tf) var t)) p = return q"
    using z by (simp add: zgeneralize_proof_def Let_def tf_def var_def)
  have tf: "ztyp_ok U" if "tf (v, S) = Some U" for v S U
    using that gi by (cases v) (auto simp: tf_def split: if_splits)
  have tok: "ztyp_ok (zsubst_type tf T)" if "ztyp_ok T" for T
    by (rule ztyp_ok_zsubst_type[OF that tf])
  have vok: "zterm_ok u" if "var (x, T) = Some u" "ztyp_ok T" for x T u
  proof -
    obtain a i where x: "x = (a, i)" by (cases x)
    show ?thesis using that gi clean_index_ge[of gi a] by (auto simp: var_def x split: if_splits)
  qed
  have vcl: "\<not> zloose u 0" if "var v = Some u" for v u
    using that by (auto simp: var_def split: if_splits prod.splits)
  show "zinv q"
    by (rule zinv_map_zproof[OF m p tok]) (use tok vok in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
  have zc: "zconsts_ok p" using p by (simp add: zinv_def)
  have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zsubst_type tf) var t) k"
    using zloose_zsubst_term vcl by blast
  show "znolb 0 p \<Longrightarrow> znolb 0 q" by (rule znolb_map_zproof[OF m zc]) (use zl in auto)
  show "zhyps q = zhyps p" by (rule zhyps_map_zproof[OF m])
qed

lemma zinv_map_zsubst_type:
  assumes m: "map_zproof (zsubst_type f) (\<lambda>t. return (zsubst_term (zsubst_type f) (\<lambda>_. None) t)) p = return q"
    and p: "zinv p" and f: "\<And>v S U. f (v, S) = Some U \<Longrightarrow> ztyp_ok U"
  shows "zinv q" "znolb 0 p \<Longrightarrow> znolb 0 q" "zhyps q = zhyps p"
proof -
  have tok: "ztyp_ok (zsubst_type f T)" if "ztyp_ok T" for T by (rule ztyp_ok_zsubst_type[OF that f])
  show "zinv q" by (rule zinv_map_zproof[OF m p tok]) (use tok in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
  have zc: "zconsts_ok p" using p by (simp add: zinv_def)
  have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zsubst_type f) (\<lambda>_. None) t) k"
    using zloose_zsubst_term[of _ _ "\<lambda>_. None"] by simp
  show "znolb 0 p \<Longrightarrow> znolb 0 q" by (rule znolb_map_zproof[OF m zc]) (use zl in auto)
  show "zhyps q = zhyps p" by (rule zhyps_map_zproof[OF m])
qed

lemma prf_idx_map_types: "prf_idx P p \<Longrightarrow> prf_idx P (map_proof_terms (map_types f) g p)"
  by (fastforce simp: prf_idx_def prf_terms_map_proof_terms vars_map_types)

lemma prf_nolb_map_types: "prf_nolb 0 p \<Longrightarrow> prf_nolb 0 (map_proof_terms (map_types f) g p)"
  by (rule prf_nolb_map) simp_all

context prf_sig
begin

lemma prf_valid_beta_reds:
  assumes p: "prf_valid ax H tps pf \<phi>" and l: "list_all2 (\<lambda>(t, u) (t', u'). t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps tps'"
    and red: "\<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* \<phi>'" and w: "wtp \<phi>"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "prf_valid ax H tps' pf \<phi>'"
proof (rule prf_validI)
  fix e \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
  have ws: "wt_subst \<sigma>" using \<sigma> by (simp add: gsubst_def)
  have p0: "prf_ok ax H (ieqs \<rho> \<sigma> tps) e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>)" by (rule prf_validD[OF p \<rho> \<sigma>])
  have p1: "prf_ok ax H (ieqs \<rho> \<sigma> tps') e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>)"
  proof (rule prf_ok_eqs[OF _ p0])
    fix l r e' T assume lr: "(l, r) \<in> ieqs \<rho> \<sigma> tps" and c: "closed l" "closed r"
      and tl: "e' \<turnstile> l : T" "e' \<turnstile> r : T"
    from lr obtain t u where tu: "(t, u) \<in> set tps" and lt: "l = ap \<rho> \<sigma> t" and ru: "r = ap \<rho> \<sigma> u" by auto
    from tu obtain i where i: "i < length tps" "tps ! i = (t, u)" by (auto simp: in_set_conv_nth)
    have il: "i < length tps'" using i(1) list_all2_lengthD[OF l] by simp
    obtain t' u' where tu': "tps' ! i = (t', u')" by (cases "tps' ! i")
    from list_all2_nthD[OF l i(1)] i(2) tu' have red': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" "u \<rightarrow>\<^sub>\<beta>\<^sup>* u'" by simp_all
    have m': "(t', u') \<in> set tps'" using nth_mem[OF il] tu' by simp
    have ra: "l \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> t'" "r \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> u'"
      unfolding lt ru by (rule beta_reds_ap[OF red'(1) ws], rule beta_reds_ap[OF red'(2) ws])
    have c': "closed (ap \<rho> \<sigma> t')" "closed (ap \<rho> \<sigma> u')" using beta_reds_closed[OF ra(1) c(1)] beta_reds_closed[OF ra(2) c(2)] .
    have t': "e' \<turnstile> ap \<rho> \<sigma> t' : T" "e' \<turnstile> ap \<rho> \<sigma> u' : T"
      using subject_reduction_beta'[OF ra(1) tl(1)] subject_reduction_beta'[OF ra(2) tl(2)] .
    have "(ap \<rho> \<sigma> t', ap \<rho> \<sigma> u') \<in> ceqs (ieqs \<rho> \<sigma> tps')" using pmapI[OF m', of "ap \<rho> \<sigma>"] c' by simp
    from eqv.eqv_ax[OF this t'] have m: "eqv (ceqs (ieqs \<rho> \<sigma> tps')) e' (ap \<rho> \<sigma> t') (ap \<rho> \<sigma> u')" .
    have cl: "l \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t'" "r \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u'"
      using conv_beta_eta[OF _ ra(1)] conv_beta_eta[OF _ ra(2)] tl by (auto simp: wt_def)
    show "eqv (ceqs (ieqs \<rho> \<sigma> tps')) e' l r"
      by (rule eqv.eqv_trans[OF eqv.eqv_trans[OF eqv.eqv_conv[OF cl(1) tl(1) t'(1)] m]
        eqv.eqv_sym[OF eqv.eqv_conv[OF cl(2) tl(2) t'(2)]]])
  qed
  have ra: "ap \<rho> \<sigma> \<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* ap \<rho> \<sigma> \<phi>'" by (rule beta_reds_ap[OF red ws])
  have ta: "e \<turnstile> ap \<rho> \<sigma> \<phi> : propT" by (rule typing_ap_wtp[OF w \<rho> \<sigma>])
  show "prf_ok ax H (ieqs \<rho> \<sigma> tps') e [] (prf_ap \<rho> \<sigma> pf) (ap \<rho> \<sigma> \<phi>')"
    by (rule prf_ok.conv[OF p1 conv_beta_eta[OF _ ra] subject_reduction_beta'[OF ra ta]]) (use ta in \<open>auto simp: wt_def\<close>)
qed

lemma zvalid_beta_reds:
  assumes p: "zvalid ax H tps pf \<phi>" and l: "list_all2 (\<lambda>(t, u) (t', u'). t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> u \<rightarrow>\<^sub>\<beta>\<^sup>* u') tps tps'"
    and red: "\<phi> \<rightarrow>\<^sub>\<beta>\<^sup>* \<phi>'" and w: "wtp \<phi>"
    and tw: "\<forall>(t, u)\<in>set tps. closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
  shows "zvalid ax H tps' pf \<phi>'"
proof -
  obtain w0 where w0: "pcerase w0 = pcerase (zprf_tr pf)" "prf_valid ax H tps w0 \<phi>" using p by (rule zvalidE)
  from zvalidI[OF w0(1) prf_valid_beta_reds[OF w0(2) l red w tw]] show ?thesis .
qed

end


lemma proofs_ok_adjust_maxidx:
  fixes th :: "'u pure_thm"
  assumes po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm (adjust_maxidx_thm i (rep_of th)) (shyps_of th) (hyps_of th)
    (sign_of th) (proof_of th) (zproof_of th))) \<Longrightarrow>
    proofs_ok (mk_thm (adjust_maxidx_thm i (rep_of th)) (shyps_of th) (hyps_of th)
    (sign_of th) (proof_of th) (zproof_of th))" (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  assume "is_prf_sig (th_sign ?th)"
  then have "proofs_ok (rep_thm th)" by (intro po_th) simp
  then show "proofs_ok ?th" by (simp add: proofs_ok_def)
qed

lemma proofs_ok_renamed_prop:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (renamed_prop P (rep_of th)) r"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  from ok have a: "aconv_term (th_prop (rep_of th)) P"
    and r: "r = mk_rep (th_maxidx (rep_of th)) (th_tpairs (rep_of th)) P"
    by (auto simp: renamed_prop_def returnW_def raiseW_def split: if_splits)
  have u: "unname P = unname (th_prop (rep_of th))" using a by (simp add: aconv_term_unname)
  have vt: "vars P = vars (th_prop (rep_of th))" "ttvars P = ttvars (th_prop (rep_of th))"
    by (metis u vars_unname, metis u ttvars_unname)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w: "wtp (th_prop (rep_of th))" using pure_thm_wf[of th] ps by (simp add: thm_wf_def wt_thm_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume q: "proof_of th = returnW pf"
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) pf (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using p q by (simp_all add: proofs_ok_def Let_def)
    then show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and>
        prf_nolb 0 pf"
      using renamed_prop_proof_valid[OF ok vq(1) w] by simp
  next
    fix z assume q: "zproof_of th = return z"
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) z (th_prop (rep_of th))" "zinv z"
      "znolb 0 z" "zhyps_ok z"
      using p q by (simp_all add: proofs_ok_def Let_def)
    then show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z"
      using zrenamed_prop_proof_valid[OF ok vq(1) w] by simp
  qed
qed

lemma proofs_ok_incr_indexes:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (incr_indexes_thm i (rep_of th)) r"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (incr_indexes_prf i (proof_of th)) (incr_indexes_zprf i (zproof_of th)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof (cases "i = 0")
  case True
  with ok have r: "r = rep_of th" by (auto simp: incr_indexes_thm_def returnW_def raiseW_def)
  have e: "rep_thm th = with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th))"
    by (simp add: r mk_thm_def with_cons_def)
  assume psig: "is_prf_sig (th_sign ?th)"
  have "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  then have "proofs_ok (with_cons (cons_of th) (mk_thm r (shyps_of th) (hyps_of th) (sign_of th) (proof_of th) (zproof_of th)))"
    using e by metis
  then show "proofs_ok ?th" using True by (simp add: incr_indexes_prf_def incr_indexes_zprf_def)
next
  case False
  let ?c = "sign_of th" and ?inc = "\<lambda>(t, u). (incr_indexes [] i t, incr_indexes [] i u)"
  from ok False have i: "0 \<le> i"
    and r: "r = mk_rep (th_maxidx (rep_of th) + i) (map ?inc (th_tpairs (rep_of th)))
      (incr_indexes [] i (th_prop (rep_of th)))"
    by (auto simp: incr_indexes_thm_def returnW_def raiseW_def split: if_splits)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "incr_indexes_prf i (proof_of th) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = incr_indexes_proof i q"
      using False by (auto simp: incr_indexes_prf_def bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      using incr_indexes_proof_valid[OF vq(1), of i] by (simp add: r mk_rep_def pf)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
      using vq(2) i incr_indexes_vars[of _ i]
      by (fastforce simp: pf incr_indexes_proof_def prf_idx_def prf_terms_map_proof_terms)
    moreover have "prf_nolb 0 pf" unfolding pf incr_indexes_proof_def
      by (rule prf_nolb_map[OF _ _ vq(3)])
        (simp_all add: incr_indexes_idx loose_bvar_incr_idx_Nil)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "incr_indexes_zprf i (zproof_of th) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zincr_indexes_proof i q = return z"
      using False by (auto simp: incr_indexes_zprf_def bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    define var where "var = (\<lambda>((x, j), T). if 0 \<le> j then Some (ZVar (x, j + i) T) else None)"
    have m: "map_zproof (zincr_tvar i) (\<lambda>t. return (zsubst_term (zincr_tvar i) var t)) q = return z"
      using z by (simp add: zincr_indexes_proof_def Let_def var_def)
    have var: "\<And>v u. var v = Some u \<Longrightarrow> \<not> zloose u 0"
      by (auto simp: var_def split: if_splits)
    have var': "\<And>x T u. var (x, T) = Some u \<Longrightarrow> ztyp_ok T \<Longrightarrow> zterm_ok u"
      using i by (auto simp: var_def split: if_splits)
    have zc: "zconsts_ok q" and zo: "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp_all add: zinv_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      using zincr_indexes_proof_valid[OF vq(1) z i zo zc] by (simp add: r mk_rep_def)
    moreover have "zinv z"
      by (rule zinv_map_zproof[OF m vq(2)])
        (use ztyp_ok_zincr_tvar[OF _ i] var' in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
    moreover have "znolb 0 z"
    proof -
      have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term (zincr_tvar i) var t) k"
        using zloose_zsubst_term var by blast
      show ?thesis by (rule znolb_map_zproof[OF m zc _ _ vq(3)]) (use zl in auto)
    qed
    moreover have "zhyps_ok z" using vq(4) zhyps_map_zproof[OF m] by (simp add: zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" by simp
  qed
qed

lemma proofs_ok_implies_intr:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (implies_intr (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct \<union> shyps_of th)
    (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)))))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct \<union> shyps_of th)
    (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zimplies_intr_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_t (crep_of ct)))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  obtain A U m where cr: "crep_of ct = CTerm A U m" by (cases "crep_of ct")
  let ?hs = "filter (\<lambda>h. \<not> aconv_term A h) (hyps_of th)"
  have ok': "okT (implies_intr (CTerm A U m) (rep_of th)) r" using ok by (simp add: cr)
  from ok' have U: "U = propT"
    and r: "r = mk_rep (max m (th_maxidx (rep_of th))) (th_tpairs (rep_of th)) (mk_implies A (th_prop (rep_of th)))"
    by (auto simp: implies_intr_def returnW_def raiseW_def split: if_splits)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm A U m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  have wA: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) A" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    show ?thesis using wfc[OF ps] U by (auto simp: cterm_wf_def intro: wtpI[of _ "\<lambda>_. propT"])
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have wf: "cterm_wf (CTerm A U m)" by (rule wfc[OF ps])
  have wA': "wtp A" by (rule wA[OF ps])
  have pA: "pnn A" using wf by (simp add: cterm_wf_def pnn_iff)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have H: "\<And>t. t \<in> set (hyps_of th) \<Longrightarrow> vars t = {} \<and> ttvars t = {}"
    using w0 by (simp add: thm_wf_def wt_thm_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (implies_intr_proof (ct_t (crep_of ct)) p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = implies_intr_proof A q"
      by (auto simp: bindP_eq_returnP cr)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set ?hs) (th_tpairs r) pf (th_prop r)"
      using implies_intr_rule_proof_valid[OF ok' vq(1) wA' H] by (simp add: pf)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using prf_idx_abshyp[OF vq(2)] prf_nolb_abshyp[OF vq(3)] by (simp_all add: pf implies_intr_proof_def)
    ultimately show "prf_valid (sg_ax ?c) (set (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)))
        (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
      by (simp add: cr)
  next
    fix z assume "bindM (zproof_of th) (zimplies_intr_proof ztargs (ct_t (crep_of ct))) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zimplies_intr_proof ztargs A q = return z"
      by (auto simp: bindZ_eq_returnZ cr)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    from z obtain h where h: "zterm_of ztargs A = return h" and zh: "z = ZAbsp STR ''H'' h (zabshyp h 0 q)"
      by (auto simp: zimplies_intr_proof_def bindZ_eq_returnZ)
    have "zvalid (sg_ax ?c) (set ?hs) (th_tpairs r) z (th_prop r)"
      using zimplies_intr_rule_proof_valid[OF ok' vq(1) wA' pnn_noneg[OF pA] H _ z] vq(4)
      by (simp add: zhyps_ok_def)
    moreover have "zinv z"
      using zterm_ok_zterm_of_pnn[OF h pA] zinv_zabshyp[OF vq(2)] by (simp add: zh)
    moreover have "znolb 0 z"
      using zloose_zterm_of[OF h] wtpD(1)[OF wA'] znolb_zabshyp[OF vq(3)] by (simp add: zh closed_def)
    moreover have "zhyps_ok z" using vq(4) zhyps_zabshyp by (fastforce simp: zh zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c) (set (filter (\<lambda>h. \<not> aconv_term (ct_t (crep_of ct)) h) (hyps_of th)))
        (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: cr)
  qed
qed

lemma proofs_ok_permute_prems:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (permute_data j k (rep_of th)) (r, prems', m)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
    (bindM (zproof_of th) (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) prems' j m)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)))
    (bindM (zproof_of th) (zpermute_prems_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) prems' j m)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  have okp: "okT (permute_prems j k (rep_of th)) r" using ok by (simp add: permute_prems_def returnW_def, blast)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
  note pw = permute_data_wf[OF ok w]
  have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
  have pA: "pnn A" "\<not> loose_bvar A 0" if "A \<in> set prems'" for A
  proof -
    have "A \<in> set (strip_imp_prems (th_prop (rep_of th)))" using that pw(6) by simp
    note sub = strip_imp_prems_sub[OF this]
    show "pnn A" using pP sub by (auto simp: pnn_def)
    show "\<not> loose_bvar A 0" using sub wtpD(1)[OF w] by (auto simp: closed_def)
  qed
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (permute_prems_proof prems' j m p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = permute_prems_proof prems' j m q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule permute_prems_proof_valid[OF ok vq(1) w])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using vq(2,3) by (simp_all add: pf permute_prems_proof_def Let_def prf_idx_mk_AbsP prf_idx_proof_combP
        prf_nolb_proof_combP, auto)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zpermute_prems_proof ztargs prems' j m) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zpermute_prems_proof ztargs prems' j m q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zpermute_prems_proof_valid[OF ok vq(1) w _ z]) (use pA pnn_noneg in blast)
    moreover from z obtain Ps where Ps: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) prems' Ps"
      and zq: "z = ZAbsps Ps (ZAppps q (map ZBoundp (downto (integer_of_nat (length prems') - 1)
        (integer_of_nat (length prems') - j) @ downto (m - 1) 0 @ downto (integer_of_nat (length prems') - j - 1) m)))"
      by (auto simp: zpermute_prems_proof_def Let_def bindZ_eq_returnZ mapZ_eq_returnZ)
    have Pz: "zterm_ok t \<and> \<not> zloose t 0" if "t \<in> set Ps" for t
    proof -
      from that obtain i where i: "i < length Ps" "t = Ps ! i" by (auto simp: in_set_conv_nth)
      have il: "i < length prems'" using i(1) list_all2_lengthD[OF Ps] by simp
      have zt: "zterm_of ztargs (prems' ! i) = return t" using list_all2_nthD[OF Ps il] i(2) by simp
      show ?thesis using zterm_ok_zterm_of_pnn[OF zt pA(1)] zloose_zterm_of[OF zt] pA(2) nth_mem[OF il]
        by simp
    qed
    have "zinv z" using vq(2) Pz by (auto simp: zq zinv_ZAbsps zinv_ZAppps)
    moreover have "znolb 0 z" using vq(3) Pz by (auto simp: zq znolb_ZAbsps znolb_ZAppps)
    moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def zhyps_ZAppps)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" by simp
  qed
qed

lemma proofs_ok_rotate_rule:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (rotate_data k i (rep_of th)) (r, Bs, Bi', params, asms, m)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
    (bindM (zproof_of th) (zrotate_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)))
    (bindM (zproof_of th) (zrotate_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) Bs Bi' params asms m)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  have okr: "okT (rotate_rule k i (rep_of th)) r" using ok by (simp add: rotate_rule_def returnW_def, blast)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
  note rw = rotate_data_wf[OF ok w]
  have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
  have sub_pnn: "pnn A" if "vars A \<subseteq> vars (th_prop (rep_of th))" "ttvars A \<subseteq> ttvars (th_prop (rep_of th))" for A
    using pP that by (auto simp: pnn_iff)
  have pB: "pnn A" "\<not> loose_bvar A 0" if "A \<in> set (Bs @ [Bi'])" for A
    using rw(6) that sub_pnn by (blast+)
  have pA: "pnn A" "\<not> loose_bvar A (integer_of_nat (length params))" if "A \<in> set asms" for A
    using rw(7) that sub_pnn by (blast+)
  have pT: "tnn T" if "(a, T) \<in> set params" for a T
    using rw(8) that pP by (fastforce simp: pnn_iff tnn_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  have dl: "\<not> loose_bvar (Bound j) (integer_of_nat (length params))"
    if "j \<in> set (downto (integer_of_nat (length params) - 1) 0)" for j
    using downto_le[OF that] by simp
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (rotate_proof Bs Bi' params asms m p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = rotate_proof Bs Bi' params asms m q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule rotate_proof_valid[OF ok vq(1) w])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
      using vq(2) by (simp add: pf rotate_proof_def Let_def prf_idx_mk_AbsP prf_idx_proof_combP prf_idx_mk_Abst
        prf_idx_proof_combt, auto)
    moreover have "prf_nolb 0 pf"
      using vq(3) dl by (simp add: pf rotate_proof_def Let_def prf_nolb_proof_combP prf_nolb_mk_Abst
        prf_nolb_proof_combt, auto)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zrotate_proof ztargs Bs Bi' params asms m) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zrotate_proof ztargs Bs Bi' params asms m q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zrotate_proof_valid[OF ok vq(1) w _ _ _ z])
        (use pB pA pT pnn_noneg tnn_tnoneg in \<open>blast+\<close>)
    moreover from z obtain Bs' asms' where B: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) (Bs @ [Bi']) Bs'"
      and A: "list_all2 (\<lambda>A t. zterm_of ztargs A = return t) asms asms'"
      and zq: "z = ZAbsps Bs' (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs)) 1) @
        [ZAbsts (map (\<lambda>(a, T). (a, ztyp_of T)) params) (ZAbsps asms'
          (ZAppps (ZAppts (ZBoundp (integer_of_nat (length asms))) (map ZBound (downto (integer_of_nat (length params) - 1) 0)))
            (map ZBoundp (downto (integer_of_nat (length asms) - m - 1) 0 @
              downto (integer_of_nat (length asms) - 1) (integer_of_nat (length asms) - m)))))]))"
      by (auto simp: zrotate_proof_def bindZ_eq_returnZ mapZ_eq_returnZ Let_def)
    have Bz: "zterm_ok t \<and> \<not> zloose t 0" if "t \<in> set Bs'" for t
    proof -
      from that obtain j where j: "j < length Bs'" "t = Bs' ! j" by (auto simp: in_set_conv_nth)
      have jl: "j < length (Bs @ [Bi'])" using j(1) list_all2_lengthD[OF B] by simp
      have zt: "zterm_of ztargs ((Bs @ [Bi']) ! j) = return t" using list_all2_nthD[OF B jl] j(2) by simp
      show ?thesis using zterm_ok_zterm_of_pnn[OF zt pB(1)] zloose_zterm_of[OF zt] pB(2) nth_mem[OF jl] by simp
    qed
    have Az: "zterm_ok t \<and> \<not> zloose t (integer_of_nat (length params))" if "t \<in> set asms'" for t
    proof -
      from that obtain j where j: "j < length asms'" "t = asms' ! j" by (auto simp: in_set_conv_nth)
      have jl: "j < length asms" using j(1) list_all2_lengthD[OF A] by simp
      have zt: "zterm_of ztargs (asms ! j) = return t" using list_all2_nthD[OF A jl] j(2) by simp
      show ?thesis using zterm_ok_zterm_of_pnn[OF zt pA(1)] zloose_zterm_of[OF zt] pA(2) nth_mem[OF jl] by simp
    qed
    have Tz: "\<forall>(a, T)\<in>set (map (\<lambda>(a, T). (a, ztyp_of T)) params). ztyp_ok T"
      using pT ztyp_ok_ztyp_of by (auto)
    have dz: "\<not> zloose (ZBound j) (integer_of_nat (length params))"
      if "j \<in> set (downto (integer_of_nat (length params) - 1) 0)" for j
      using downto_le[OF that] by simp
    have "zinv z" using vq(2) Bz Az Tz
      by (auto simp: zq zinv_ZAbsps zinv_ZAppps zinv_ZAbsts zinv_ZAppts)
    moreover have "znolb 0 z" using vq(3) Bz Az dz
      by (auto simp: zq znolb_ZAbsps znolb_ZAppps znolb_ZAbsts znolb_ZAppts)
    moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def zhyps_ZAppps)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" by simp
  qed
qed

lemma proofs_ok_forall_intr:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (forall_intr (hyps_of th) (crep_of ct) (rep_of th)) r" and c: "csign_of ct = sign_of th"
    and sc: "sign_closed (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zforall_intr_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
      (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)))))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zforall_intr_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct))
      (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  obtain x T m where cr: "crep_of ct = CTerm x T m" by (cases "crep_of ct")
  have ok': "okT (forall_intr (hyps_of th) (CTerm x T m) (rep_of th)) r" using ok by (simp add: cr)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm x T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
  have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
  have px: "pnn x" using wf by (simp add: cterm_wf_def pnn_iff)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using w0 by (simp add: thm_wf_def)
  have tT: "tnn T" using typing_tvars_closed[OF tx cx] px unfolding tnn_def pnn_iff by (force)
  have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
    using sc by (simp_all add: sign_closed_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (forall_intr_proof (var_name (ct_t (crep_of ct))) (ct_t (crep_of ct)) p))
        = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = forall_intr_proof (var_name x) x q"
      by (auto simp: bindP_eq_returnP cr)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule forall_intr_rule_proof_valid[OF ok' vq(1) wt tx]) (simp add: scl)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using prf_idx_prf_abstract_over_aux[OF vq(2)] prf_nolb_prf_abstract_over_aux[OF vq(3), of 0]
      by (simp_all add: pf forall_intr_proof_def prf_abstract_over_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zforall_intr_proof ztargs (ct_T (crep_of ct)) (var_name (ct_t (crep_of ct)))
        (ct_t (crep_of ct))) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zforall_intr_proof ztargs T (var_name x) x q = return z"
      by (auto simp: bindZ_eq_returnZ cr)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
    have cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) q"
    proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
      show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
      fix t assume "zterm_ok t"
      then show "\<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T"
        using zterm_ok_zvars by (fastforce simp: ztyp_ok_def zcanon_def)
    qed simp
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zforall_intr_rule_proof_valid[OF ok' vq(1) wt tx pnn_noneg[OF px] eqc cz z])
    moreover from z obtain zx where zx: "zterm_of ztargs x = return zx"
      and zq: "z = ZAbst (var_name x) (ztyp_of T) (zabstract_proof zx 0 q)"
      by (auto simp: zforall_intr_proof_def bindZ_eq_returnZ)
    have "zinv z" using zinv_zabstract_proof[OF vq(2)] ztyp_ok_ztyp_of[OF tT] by (simp add: zq)
    moreover have "znolb 0 z" using znolb_zabstract_proof[OF vq(3), of 0] by (simp add: zq)
    moreover have "zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def)
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" by simp
  qed
qed

lemma proofs_ok_abstract_rule:
  fixes th :: "'u pure_thm"
  assumes res: "okT (abstract_rule_res b (hyps_of th) (crep_of ct) (rep_of th)) (r, U, f, g)"
    and c: "csign_of ct = sign_of th" and se: "sign_eq (sign_of th)" and sc: "sign_closed (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
      (ct_t (crep_of ct)) f g)))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct \<union> shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)))
    (bindM (zproof_of th) (zabstract_rule_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (ct_T (crep_of ct)) U b
      (ct_t (crep_of ct)) f g)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  obtain x T m where cr: "crep_of ct = CTerm x T m" by (cases "crep_of ct")
  have ok': "okT (abstract_rule b (hyps_of th) (CTerm x T m) (rep_of th)) r"
    and ad: "okT (abstract_rule_data b (hyps_of th) (CTerm x T m) (rep_of th)) (U, f, g)"
    using abstract_rule_res_ok[OF res] by (simp_all add: cr)
  have eq: "pure_sig_gen.eq_ok (sg_consts ?c)" using se by (simp add: sign_eq_def)
  have wfc: "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) (CTerm x T m)"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
    using pure_cterm_wf[of ct] ps c by (simp add: cr)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have wf: "cterm_wf (CTerm x T m)" by (rule wfc[OF ps])
  have tx: "\<And>e. e \<turnstile> x : T" and cx: "closed x" using wf by (simp_all add: cterm_wf_def)
  have px: "pnn x" using wf by (simp add: cterm_wf_def pnn_iff)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using w0 by (simp add: thm_wf_def)
  have w: "wtp (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def wt_thm_def)
  note sh = abstract_rule_shape[OF ok' ad eq w tx cx]
  have tT: "tvars T \<subseteq> ttvars x" by (rule typing_tvars_closed[OF tx cx])
  have pP: "pnn (th_prop (rep_of th))" using w0 by (simp add: thm_wf_def vars_thm_def tvars_thm_def pnn_iff)
  have tnT: "tnn T" using tT px unfolding tnn_def pnn_iff by (force)
  have tnU: "tnn U"
  proof -
    obtain t0 u0 a0 z0 where d0: "dest_eq_fun (th_prop (rep_of th)) = Some (U, t0, u0)"
      by (rule abstract_rule_data_ok[OF ad tx])
    from dest_eq_any_wtp[OF eq dest_eq_any_dest_eq_fun[OF d0] w] obtain A where
      P0: "th_prop (rep_of th) = eq_const A $ t0 $ u0" by blast
    from d0 P0 have "U = A" by (simp add: propT_def)
    with pP show ?thesis unfolding P0 by (simp add: pnn_def)
  qed
  have pf: "pnn f" "pnn g" using sh(6-9) pP tT px unfolding pnn_iff by (blast)+
  have scl: "fnames (sg_close ?c A) = {}" "TFree b' S \<notin> tatoms (sg_close ?c A)" for A b' S
    using sc by (simp_all add: sign_closed_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (abstract_rule_proof b (ct_t (crep_of ct)) p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = abstract_rule_proof b x q"
      by (auto simp: bindP_eq_returnP cr)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule abstract_rule_proof_valid[OF ok' vq(1) wt tx]) (simp add: scl)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using prf_idx_prf_abstract_over_aux[OF vq(2)] prf_nolb_prf_abstract_over_aux[OF vq(3), of 0]
      by (simp_all add: pf abstract_rule_proof_def forall_intr_proof_def prf_abstract_over_def equality_axm_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zabstract_rule_proof ztargs (ct_T (crep_of ct)) U b (ct_t (crep_of ct)) f g)
        = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zabstract_rule_proof ztargs T U b x f g q = return z"
      by (auto simp: bindZ_eq_returnZ cr)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
    have cz: "zprf_all (\<lambda>t. \<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T) (\<lambda>_. True) q"
    proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
      show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
      fix t assume "zterm_ok t"
      then show "\<forall>(yi, U)\<in>zvars t. typ_of U = T \<longrightarrow> U = ztyp_of T"
        using zterm_ok_zvars by (fastforce simp: ztyp_ok_def zcanon_def)
    qed simp
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zabstract_rule_proof_valid(1)[OF ok' vq(1) wt tx ad pnn_noneg[OF px] pnn_noneg[OF pf(1)]
        pnn_noneg[OF pf(2)] zc cz _ z]) (use sc in \<open>simp add: zeq_close_ok_def sign_closed_def\<close>)
    moreover from z obtain f' g' ax0 zx where f': "zterm_of ztargs f = return f'" and g': "zterm_of ztargs g = return g'"
      and ax0: "zaxiom_proof STR ''abstract_rule'' [(tvar_a, ztyp_of T), (tvar_b, ztyp_of U)]
        [(STR ''f'', f'), (STR ''g'', g')] = return ax0"
      and zx: "zterm_of ztargs x = return zx" and zq: "z = ZAppp ax0 (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
      by (auto simp: zabstract_rule_proof_def zforall_intr_proof_def bindZ_eq_returnZ)
    have "zinv ax0 \<and> znolb 0 ax0 \<and> zhyps ax0 = {}"
      by (rule zaxiom_proof_ok[OF ax0])
        (use zterm_ok_zterm_of_pnn[OF f' pf(1)] zterm_ok_zterm_of_pnn[OF g' pf(2)]
          zloose_zterm_of[OF f'] zloose_zterm_of[OF g'] sh(10,11) ztyp_ok_ztyp_of[OF tnT] ztyp_ok_ztyp_of[OF tnU]
          in \<open>auto simp: zeq_vars_def closed_def\<close>)
    moreover have "zinv (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
      using zinv_zabstract_proof[OF vq(2)] ztyp_ok_ztyp_of[OF tnT] by simp
    moreover have "znolb 0 (ZAbst b (ztyp_of T) (zabstract_proof zx 0 q))"
      using znolb_zabstract_proof[OF vq(3), of 0] by simp
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (simp add: zq zhyps_ok_def)
  qed
qed

lemma proofs_ok_generalize:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (generalize tfrees frees gi (hyps_of th) (rep_of th)) r" and sc: "sign_closed (sign_of th)"
    and ne: "\<not> (tfrees = [] \<and> frees = [])"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th)) (th_prop (rep_of th)) p)))
    (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th)) (th_prop (rep_of th)) p)))
    (bindM (zproof_of th) (zgeneralize_proof tfrees frees gi)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th"
  from ok ne have gi: "th_maxidx (rep_of th) < gi"
    by (auto simp: generalize_def returnW_def raiseW_def Let_def split: if_splits)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wt: "wt_thm (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    and mx: "-1 \<le> th_maxidx (rep_of th)"
    using w0 by (simp_all add: thm_wf_def)
  have gi0: "0 \<le> gi" using gi mx by (simp add: integer_arith)
  have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
    using sc by (simp_all add: sign_closed_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th))
        (th_prop (rep_of th)) p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q"
      and pf: "pf = generalize_thm_proof tfrees frees gi (th_tpairs (rep_of th)) (th_prop (rep_of th)) q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule generalize_tfrees_proof_valid[OF ok vq(1) wt _ _ vq(3)])
        (simp_all add: scl tf_in_def)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" unfolding pf by (rule prf_idx_generalize_thm_proof[OF vq(2) gi0])
    moreover have "prf_nolb 0 pf" unfolding pf by (rule prf_nolb_generalize_thm_proof[OF vq(3)])
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zgeneralize_proof tfrees frees gi) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zgeneralize_proof tfrees frees gi q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
    have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zgeneralize_proof_valid[OF ok vq(1) wt mx prf_nolb_zprf_tr[OF vq(3)] zc eqc z])
    moreover note zg = zinv_zgeneralize_proof[OF z vq(2) gi0]
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(3,4) by (simp add: zhyps_ok_def)
  qed
qed

lemma proofs_ok_varifyT_global:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (varifyT_global vl fixed (hyps_of th) (rep_of th)) (names, r)" and sc: "sign_closed (sign_of th)"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p))) (bindM (zproof_of th) (zvarifyT_proof names)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th" and ?\<phi> = "varify_tfree names"
  note sh = varifyT_global_shape[OF ok]
  have gen: "?\<phi> = gen_atom (varA names) (varg names)" by (rule varify_tfree_gen_atom) (use sh(4) in blast)
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wP: "wtp (th_prop (rep_of th))" and wh: "\<And>h. h \<in> set (hyps_of th) \<Longrightarrow> wtp h \<and> vars h = {} \<and> ttvars h = {}"
    using w0 by (auto simp: thm_wf_def wt_thm_def)
  have scl: "fnames (sg_close ?c A) = {}" "TFree b S \<notin> tatoms (sg_close ?c A)" for A b S
    using sc by (simp_all add: sign_closed_def)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (varifyT_proof names p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = varifyT_proof names q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule varifyT_global_proof_valid[OF ok vq(1) wP wh _ vq(3)]) (use sc in \<open>auto simp: sign_closed_def\<close>)
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] vq(2,3)
      by (simp_all add: pf varifyT_proof_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zvarifyT_proof names) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zvarifyT_proof names q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
    have eqc: "zeq_close_ok" using scl by (simp add: zeq_close_ok_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zvarifyT_global_proof_valid[OF ok vq(1) wP wh prf_nolb_zprf_tr[OF vq(3)] zc eqc z])
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
    proof (cases "names = []")
      case True
      then show ?thesis using z vq(2,3) by (simp add: zvarifyT_proof_def)
    next
      case False
      define fv :: "indexname \<times> psort \<Rightarrow> ztyp option" where "fv = (\<lambda>((a, i), S). if i = -1
        then map_option (\<lambda>(v, S'). ZTVar v S') (map_of names (a, S)) else None)"
      have m: "map_zproof (zsubst_type fv) (\<lambda>t. return (zsubst_term (zsubst_type fv) (\<lambda>_. None) t)) q = return z"
        using z False by (simp add: zvarifyT_proof_def Let_def fv_def)
      have f: "ztyp_ok U" if "fv (v, S) = Some U" for v S U
      proof -
        obtain a i where v: "v = (a, i)" by (cases v)
        from that obtain w S' where "map_of names (a, S) = Some (w, S')" "U = ZTVar w S'"
          by (auto simp: v fv_def split: if_splits)
        with sh(4)[of a S w S'] show ?thesis by simp
      qed
      from zinv_map_zsubst_type[OF m vq(2) f] vq(3) show ?thesis by simp
    qed
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
  qed
qed

lemma proofs_ok_legacy_freezeT:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (legacy_freezeT vl (rep_of th)) r" and f: "ok (full_prop_of (th_tpairs (rep_of th)) (th_prop (rep_of th))) P1"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1)))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p))) (bindM (zproof_of th) (zlegacy_freezeT_proof vl P1)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th" and ?\<phi> = "freeze_tvar (legacy_freeze_names vl P1)"
  note sh = legacy_freezeT_shape[OF ok f]
  have sub: "vars X \<subseteq> vars P1" "typs X \<subseteq> typs P1"
    if "X \<in> insert (th_prop (rep_of th)) (fst ` set (th_tpairs (rep_of th)) \<union> snd ` set (th_tpairs (rep_of th)))" for X
    using full_prop_of_sub[OF f that] by simp_all
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have fv: "vars P1 \<subseteq> vars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th)) \<and>
      ttvars P1 \<subseteq> tvars_thm (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    by (rule full_prop_of_vars[OF f])
  have nP: "noneg P1" using fv w0 by (intro pnn_noneg) (auto simp: thm_wf_def pnn_iff)
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (legacy_freezeT_proof vl P1 p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = legacy_freezeT_proof vl P1 q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      unfolding pf by (rule legacy_freezeT_proof_valid[OF ok f vq(1)])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf" "prf_nolb 0 pf"
      using prf_idx_map_types[OF vq(2)] prf_nolb_map_types[OF vq(3)] vq(2,3)
      by (simp_all add: pf legacy_freezeT_proof_def Let_def)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zlegacy_freezeT_proof vl P1) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zlegacy_freezeT_proof vl P1 q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zlegacy_freezeT_proof_valid[OF ok f vq(1) nP zc z])
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
    proof (cases "legacy_freeze_names vl P1 = []")
      case True
      then show ?thesis using z vq(2,3) by (simp add: zlegacy_freezeT_proof_def)
    next
      case False
      define fv :: "indexname \<times> psort \<Rightarrow> ztyp option"
        where "fv = (\<lambda>(ix, S). map_option (\<lambda>a. ZTVar (a, -1) S) (map_of (legacy_freeze_names vl P1) ix))"
      have m: "map_zproof (zsubst_type fv) (\<lambda>t. return (zsubst_term (zsubst_type fv) (\<lambda>_. None) t)) q = return z"
        using z False by (simp add: zlegacy_freezeT_proof_def Let_def fv_def)
      have f: "ztyp_ok U" if "fv (v, S) = Some U" for v S U
        using that by (auto simp: fv_def)
      from zinv_map_zsubst_type[OF m vq(2) f] vq(3) show ?thesis by simp
    qed
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
  qed
qed

lemma proofs_ok_of_class:
  fixes ct :: pure_cterm
  assumes ok: "okT (Pure_Subst_Rules.of_class (sg_alg (csign_of ct)) T c) r"
    and P: "ct_t (crep_of ct) = mk_of_class T c" and so: "tm_sorts (mk_of_class T c) \<subseteq> csorts_of ct"
    and cc: "pure_sig_gen.class_const (sg_alg (csign_of ct)) (sg_consts (csign_of ct)) (c + STR ''_class'') c"
    and se: "sign_eq (csign_of ct)"
  shows "is_prf_sig (th_sign (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c))
    (return (OFCLASSp (ztyp_of T) c)))) \<Longrightarrow>
    proofs_ok (mk_thm r (csorts_of ct) [] (csign_of ct) (returnW (PClass T c))
    (return (OFCLASSp (ztyp_of T) c)))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "csign_of ct" and ?P = "mk_of_class T c"
  obtain U m where cr: "crep_of ct = CTerm ?P U m" using P by (cases "crep_of ct") simp
  from ok have r: "r = mk_rep (maxidx_of_term ?P) [] ?P"
    by (auto simp: Pure_Subst_Rules.of_class_def returnW_def raiseW_def Let_def split: if_splits)
  have common: "pure_sig_gen.wtp (sg_alg ?c) (sg_ar ?c) (sg_consts ?c) ?P \<and> cert_typ (sg_alg ?c) (sg_ar ?c) T \<and> tnn T \<and>
      (\<forall>v\<in>vars ?P. 0 \<le> snd (fst v)) \<and> (\<forall>v\<in>ttvars ?P. 0 \<le> snd (fst v))"
    if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof -
    interpret pure_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" by (rule ps)
    have wf: "cterm_wf (CTerm ?P U m)" using pure_cterm_wf[OF ps] by (simp add: cr)
    from of_class_cterm[OF wf] show ?thesis by simp
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_eq "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c" "sg_ax ?c"
    using se by (simp add: sign_eq_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  from common[OF ps] have w: "wtp ?P" and cT: "cert_typ (sg_alg ?c) (sg_ar ?c) T" and tT: "tnn T" by simp_all
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "returnW (PClass T c) = returnW pf"
    then have pf: "pf = PClass T c" by (simp add: returnW_def)
    have "prf_valid (sg_ax ?c) (set []) (th_tpairs r) (PClass T c) (th_prop r)"
      by (rule of_class_proof_valid[OF ok cT w])
    then show "prf_valid (sg_ax ?c) (set []) (th_tpairs r) pf (th_prop r) \<and> prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf"
      by (simp add: pf)
  next
    fix z assume "(return (OFCLASSp (ztyp_of T) c) :: zproof Z) = return z"
    then have z: "z = OFCLASSp (ztyp_of T) c" by (simp add: return_def)
    have "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r)"
      unfolding z by (rule zof_class_proof_valid[OF ok cT w])
    moreover have "zinv z" using ztyp_ok_ztyp_of[OF tT] by (simp add: z)
    ultimately show "zvalid (sg_ax ?c) (set []) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and> zhyps_ok z"
      by (simp add: z zhyps_ok_def)
  qed
qed

lemma proofs_ok_instantiate:
  fixes th :: "'u pure_thm"
  assumes ok: "okT (instantiate (sg_alg (sign_of th)) bt (instT_of cTs) (insts_of cts) (rep_of th)) r"
    and ne: "\<not> (cTs = [] \<and> cts = [])"
    and sT0: "\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th"
    and st0: "\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th"
    and po_th: "is_prf_sig (sign_of th) \<Longrightarrow> proofs_ok (rep_thm th)"
  shows "is_prf_sig (th_sign (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
    (bindM (zproof_of th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts))))) \<Longrightarrow>
    proofs_ok (mk_thm r (shyps_of th \<union> inst_sorts cTs cts) (hyps_of th) (sign_of th)
    (bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)))
    (bindM (zproof_of th) (zinstantiate_proof (pure_sig_gen.ztargs (sg_consts (sign_of th))) (inst_Ts cTs) (inst_ts cts))))"
    (is "_ \<Longrightarrow> proofs_ok ?th")
proof -
  let ?c = "sign_of th" and ?iT = "instT_of cTs" and ?is = "insts_of cts"
  have ne': "\<not> (?iT = [] \<and> ?is = [])" using ne by (simp add: instT_of_def insts_of_def)
  have ix: "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) ?iT" "list_all (\<lambda>x. 0 \<le> snd (fst (fst x))) ?is"
    using instantiate_shape(6,7)[OF ok ne'] .
  have sT: "\<forall>(v, cT)\<in>set cTs. cty_sign (rep_ctyp cT) = sign_of th \<and> snd (fst v) \<noteq> -1"
  proof (clarify, rule conjI)
    fix x i S cT assume m: "(((x, i), S), cT) \<in> set cTs"
    with sT0 show "cty_sign (rep_ctyp cT) = sign_of th" by auto
    from m have "(((x, i), S), (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT))) \<in> set ?iT"
      by (force simp: instT_of_def)
    with ix(1) have "0 \<le> i" by (auto simp: list_all_iff)
    then show "snd (fst ((x, i), S)) \<noteq> -1" by auto
  qed
  have st: "\<forall>(v, ct)\<in>set cts. csign_of ct = sign_of th \<and> snd (fst v) \<noteq> -1"
  proof (clarify, rule conjI)
    fix x i T ct assume m: "(((x, i), T), ct) \<in> set cts"
    with st0 show "csign_of ct = sign_of th" by auto
    from m have "(((x, i), T), (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct))) \<in> set ?is"
      by (force simp: insts_of_def)
    with ix(2) have "0 \<le> i" by (auto simp: list_all_iff)
    then show "snd (fst ((x, i), T)) \<noteq> -1" by auto
  qed
  have cTok: "\<forall>x\<in>set ?iT. cert_typ (sg_alg ?c) (sg_ar ?c) (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
      (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof
    fix x assume "x \<in> set ?iT"
    then obtain v cT where v: "(v, cT) \<in> set cTs" and x: "x = (v, (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT)))"
      by (auto simp: instT_of_def)
    with sT have s: "cty_sign (rep_ctyp cT) = ?c" by auto
    from pure_ctyp_ok[of cT] ps s show "cert_typ (sg_alg ?c) (sg_ar ?c) (fst (snd x)) \<and> tnn (fst (snd x)) \<and>
        (\<forall>w\<in>tvars (fst (snd x)). snd (fst w) \<le> snd (snd x))"
      by (auto simp: x ctyp_ok_def tnn_def)
  qed
  have ctok: "\<forall>x\<in>set ?is. pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c)
      (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))" if ps: "pure_sig (sg_alg ?c) (sg_ar ?c)"
  proof
    fix x assume "x \<in> set ?is"
    then obtain v ct where v: "(v, ct) \<in> set cts"
      and x: "x = (v, (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct)))"
      by (auto simp: insts_of_def)
    with st have s: "csign_of ct = ?c" by auto
    from pure_cterm_wf[of ct] ps s show "pure_sig.cterm_wf (sg_alg ?c) (sg_ar ?c) (sg_consts ?c)
        (CTerm (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x))))"
      by (simp add: x)
  qed
  have sorts: "tsorts (fst (snd x)) \<subseteq> inst_sorts cTs cts" if "x \<in> set ?iT" for x
  proof -
    from that obtain v cT where v: "(v, cT) \<in> set cTs" and x: "x = (v, (cty_T (rep_ctyp cT), cty_maxidx (rep_ctyp cT)))"
      by (auto simp: instT_of_def)
    from pure_ctyp_ok[of cT] have "tsorts (cty_T (rep_ctyp cT)) \<subseteq> cty_sorts (rep_ctyp cT)" by (simp add: ctyp_ok_def)
    with v show ?thesis by (auto simp: x inst_sorts_def)
  qed
  assume psig: "is_prf_sig (th_sign ?th)"
  then interpret prf_sig "sg_alg ?c" "sg_ar ?c" "sg_consts ?c" "sg_close ?c" "sg_tyargs ?c"
    by (simp add: is_prf_sig_def)
  have ps: "pure_sig (sg_alg ?c) (sg_ar ?c)" using psig by (simp add: is_prf_sig_def prf_sig_def)
  have w0: "thm_wf (th_maxidx (rep_of th)) (hyps_of th) (th_tpairs (rep_of th)) (th_prop (rep_of th))"
    using pure_thm_wf[of th] ps by simp
  have wP: "wtp (th_prop (rep_of th))" and H: "\<And>h. h \<in> set (hyps_of th) \<Longrightarrow> vars h = {} \<and> ttvars h = {}"
    and tw: "\<forall>(t, u)\<in>set (th_tpairs (rep_of th)). closed t \<and> closed u \<and> (\<exists>T. \<forall>e. e \<turnstile> t : T \<and> e \<turnstile> u : T)"
    using w0 by (auto simp: thm_wf_def wt_thm_def)
  define tt where "tt = map (\<lambda>(v, (u, U, j)). (v, (u, j))) ?is"
  note rd = instantiate_reds[OF ok ne' cTok[OF ps] ctok[OF ps], folded tt_def]
  let ?\<rho> = "tab_inst ?iT" and ?\<sigma> = "tab_subst tt"
  have \<rho>0: "cinst (tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)))" using rd(1) by (simp add: tab_inst_Ts)
  have \<sigma>0: "wt_subst (tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)))"
    using rd(2) by (simp add: tab_subst_ts tt_def)
  have eqs: "tab_inst (map (\<lambda>(v, T). (v, (T, -1))) (inst_Ts cTs)) = ?\<rho>"
    "tab_subst (map (\<lambda>(v, t). (v, (t, -1))) (inst_ts cts)) = ?\<sigma>"
    by (simp_all add: tab_inst_Ts tab_subst_ts tt_def)
  have wS: "wtp (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))" by (rule wtp_ap[OF wP rd(1) rd(2)[folded gsubst_def]])
  note twS = tpairs_ap[OF tw rd(1) rd(2)]
  note lS = list_all2_map_beta[OF rd(5)]
  have p: "proofs_ok (rep_thm th)" by (rule po_th) (use psig in simp)
  have nn_ct: "pnn (ct_t (crep_of ct))" if "(v, ct) \<in> set cts" for v ct
    using ctok[OF ps] that by (force simp: insts_of_def cterm_wf_def pnn_iff')
  have cl_ct: "closed (ct_t (crep_of ct))" if "(v, ct) \<in> set cts" for v ct
    using ctok[OF ps] that by (force simp: insts_of_def cterm_wf_def)
  \<comment> \<open>the substitution of the classic proofs\<close>
  let ?\<sigma>r = "tab_subst (map (\<lambda>(v, t). (v, (remove_types t, -1))) (inst_ts cts))"
  have ip: "instantiate_proof (inst_Ts cTs) (inst_ts cts) w = map_proof_terms (\<lambda>t. vsubst ?\<sigma>r (inst ?\<rho> t)) (tsubst ?\<rho>) w"
    for w by (simp add: instantiate_proof_def inst_m_fst instT_m_fst Let_def flip: eqs(1))
  have \<sigma>r_cases: "?\<sigma>r x T = Var x T \<or> (\<exists>v ct. (v, ct) \<in> set cts \<and> ?\<sigma>r x T = remove_types (ct_t (crep_of ct)))"
    for x T
  proof (cases "lookup_var (map (\<lambda>(v, t). (v, (remove_types t, -1 :: integer))) (inst_ts cts)) (x, T)")
    case (Some r')
    then obtain t where t: "((x, T), t) \<in> set (inst_ts cts)" "r' = (remove_types t, -1)"
      by (auto dest: lookup_var_map_Some)
    then obtain v ct where "(v, ct) \<in> set cts" "t = ct_t (crep_of ct)" by (auto simp: inst_ts_def)
    moreover have "?\<sigma>r x T = remove_types t" using Some t(2) unfolding tab_subst_def by simp
    ultimately show ?thesis by blast
  next
    case None
    then have "?\<sigma>r x T = Var x T" unfolding tab_subst_def by simp
    then show ?thesis by blast
  qed
  have \<sigma>r: "w \<in> vars (?\<sigma>r x T) \<Longrightarrow> w = (x, T) \<or> 0 \<le> snd (fst w)" for w x T
    using \<sigma>r_cases[of x T] nn_ct by (auto simp: pnn_def)
  have \<sigma>rc: "closed_subst ?\<sigma>r"
    unfolding closed_subst_def
  proof (intro allI)
    fix x T show "closed (?\<sigma>r x T)" using \<sigma>r_cases[of x T] cl_ct by (auto simp: closed_def)
  qed
  show "proofs_ok ?th" unfolding proofs_ok_def Let_def mk_thm_sel
  proof (rule conjI; intro allI impI)
    fix pf assume "bindW (proof_of th) (\<lambda>p. returnW (instantiate_proof (inst_Ts cTs) (inst_ts cts) p)) = returnW pf"
    then obtain q where q: "proof_of th = returnW q" and pf: "pf = instantiate_proof (inst_Ts cTs) (inst_ts cts) q"
      by (auto simp: bindP_eq_returnP)
    have vq: "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))"
      "prf_idx (\<lambda>i. 0 \<le> i) q" "prf_nolb 0 q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have "prf_valid (sg_ax ?c) (set (hyps_of th))
        (map (\<lambda>(t, u). (ap ?\<rho> ?\<sigma> t, ap ?\<rho> ?\<sigma> u)) (th_tpairs (rep_of th))) pf (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))"
      using instantiate_proof_valid[OF vq(1) \<rho>0 \<sigma>0 H] unfolding pf eqs by (simp add: ap_def)
    then have "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r)"
      by (rule prf_valid_beta_reds[OF _ lS rd(4) wS twS])
    moreover have "prf_idx (\<lambda>i. 0 \<le> i) pf"
      using vq(2) vars_vsubst_inst_nonneg[OF _ \<sigma>r]
      by (fastforce simp: pf ip prf_idx_def prf_terms_map_proof_terms)
    moreover have "prf_nolb 0 pf" unfolding pf ip
      by (rule prf_nolb_map[OF _ _ vq(3)]) (simp_all add: \<sigma>rc)
    ultimately show "prf_valid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) pf (th_prop r) \<and>
        prf_idx (\<lambda>i. 0 \<le> i) pf \<and> prf_nolb 0 pf" by simp
  next
    fix z assume "bindM (zproof_of th) (zinstantiate_proof ztargs (inst_Ts cTs) (inst_ts cts)) = return z"
    then obtain q where q: "zproof_of th = return q" and z: "zinstantiate_proof ztargs (inst_Ts cTs) (inst_ts cts) q = return z"
      by (auto simp: bindZ_eq_returnZ)
    have vq: "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs (rep_of th)) q (th_prop (rep_of th))" "zinv q"
      "znolb 0 q" "zhyps_ok q"
      using p q by (simp_all add: proofs_ok_def Let_def)
    have zc: "zconsts_ok q" using vq(2) by (simp add: zinv_def)
    have cz: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. zcanon T) (\<lambda>_. True) q"
    proof (rule zprf_all_mono[of zterm_ok ztyp_ok])
      show "zprf_all zterm_ok ztyp_ok q" using vq(2) by (simp add: zinv_def)
      fix t assume "zterm_ok t"
      then show "\<forall>(x, T)\<in>zvars t. zcanon T" using zterm_ok_zvars by (fastforce simp: ztyp_ok_def)
    qed simp
    have kT: "\<forall>((v, S), T)\<in>set (inst_Ts cTs). snd v \<noteq> -1 \<and> tnoneg T"
      using sT cTok[OF ps] by (fastforce simp: inst_Ts_def instT_of_def intro: tnn_tnoneg)
    have kt: "\<forall>((v, T), t)\<in>set (inst_ts cts). snd v \<noteq> -1 \<and> tnoneg T \<and> noneg t"
    proof (clarsimp simp: inst_ts_def)
      fix x i T ct assume m: "(((x, i), T), ct) \<in> set cts"
      with st have i: "i \<noteq> -1" by auto
      from m have mi: "(((x, i), T), (ct_t (crep_of ct), ct_T (crep_of ct), ct_maxidx (crep_of ct))) \<in> set ?is"
        by (force simp: insts_of_def)
      have TU: "T = ct_T (crep_of ct)" by (rule check_inst_eq'[OF rd(3) mi])
      from ctok[OF ps] mi have wf: "cterm_wf (CTerm (ct_t (crep_of ct)) (ct_T (crep_of ct)) (ct_maxidx (crep_of ct)))"
        by force
      then have "tvars (ct_T (crep_of ct)) \<subseteq> ttvars (ct_t (crep_of ct))"
        by (intro typing_tvars_closed) (auto simp: cterm_wf_def)
      with wf have "tnn T" by (force simp: TU cterm_wf_def tnn_def)
      moreover have "pnn (ct_t (crep_of ct))" using nn_ct m by blast
      ultimately show "i \<noteq> -1 \<and> tnoneg T \<and> noneg (ct_t (crep_of ct))" using i tnn_tnoneg pnn_noneg by blast
    qed
    have "zvalid (sg_ax ?c) (set (hyps_of th)) (map (\<lambda>(t, u). (ap ?\<rho> ?\<sigma> t, ap ?\<rho> ?\<sigma> u)) (th_tpairs (rep_of th))) z
        (ap ?\<rho> ?\<sigma> (th_prop (rep_of th)))"
      using zinstantiate_proof_valid[OF vq(1) \<rho>0 \<sigma>0 H kT kt cz zc z] unfolding eqs by (simp add: ap_def)
    then have "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r)"
      by (rule zvalid_beta_reds[OF _ lS rd(4) wS twS])
    moreover have "zinv z \<and> znolb 0 z \<and> zhyps z = zhyps q"
    proof -
      let ?ty = "zsubst_type (map_of (map (\<lambda>(v, T). (v, ztyp_of T)) (inst_Ts cTs)))"
      from z obtain zinst where zi0: "mapM (\<lambda>((v, T), t). do {t' \<leftarrow> zterm_of ztargs t; return ((v, ztyp_of T), t')})
          (inst_ts cts) = return zinst"
        and m: "map_zproof ?ty (\<lambda>t. return (zsubst_term ?ty (lookup_zvar zinst) t)) q = return z"
        by (auto simp: zinstantiate_proof_def bindZ_eq_returnZ Let_def)
      have zi: "list_all2 (\<lambda>((v, T), t) e. \<exists>t'. zterm_of ztargs t = return t' \<and> e = ((v, ztyp_of T), t'))
          (inst_ts cts) zinst"
        using zi0[unfolded mapZ_eq_returnZ] by (rule list_all2_mono) (auto simp: bindZ_eq_returnZ split: prod.splits)
      have zv: "zterm_ok u \<and> \<not> zloose u 0" if "lookup_zvar zinst w = Some u" for w u
      proof -
        from lookup_zvar_SomeD[OF that] have "(w, u) \<in> set zinst" .
        then obtain i where i: "i < length zinst" "zinst ! i = (w, u)" by (auto simp: in_set_conv_nth)
        have il: "i < length (inst_ts cts)" using i(1) list_all2_lengthD[OF zi] by simp
        obtain vT t where vt: "inst_ts cts ! i = (vT, t)" by (cases "inst_ts cts ! i")
        from list_all2_nthD[OF zi il] vt i(2) have zt: "zterm_of ztargs t = return u" by (cases vT) auto
        from nth_mem[OF il] vt obtain v ct where "(v, ct) \<in> set cts" "t = ct_t (crep_of ct)"
          by (auto simp: inst_ts_def)
        with nn_ct cl_ct have "pnn t" "closed t" by blast+
        then show ?thesis using zterm_ok_zterm_of_pnn[OF zt] zloose_zterm_of[OF zt] by (simp add: closed_def)
      qed
      have ft: "ztyp_ok U" if "map_of (map (\<lambda>(v, T). (v, ztyp_of T)) (inst_Ts cTs)) vS = Some U" for vS U
      proof -
        from map_of_SomeD[OF that] obtain T where "(vS, T) \<in> set (inst_Ts cTs)" "U = ztyp_of T" by auto
        with cTok[OF ps] show ?thesis by (force simp: inst_Ts_def instT_of_def intro: ztyp_ok_ztyp_of)
      qed
      have tok: "ztyp_ok (?ty T)" if "ztyp_ok T" for T by (rule ztyp_ok_zsubst_type[OF that ft])
      have "zinv z" by (rule zinv_map_zproof[OF m vq(2) tok]) (use tok zv in \<open>auto intro!: zterm_ok_zsubst_term'\<close>)
      moreover have "znolb 0 z"
      proof -
        have zl: "\<And>t k. 0 \<le> k \<Longrightarrow> \<not> zloose t k \<Longrightarrow> \<not> zloose (zsubst_term ?ty (lookup_zvar zinst) t) k"
          using zloose_zsubst_term zv by blast
        show ?thesis by (rule znolb_map_zproof[OF m zc _ _ vq(3)]) (use zl in auto)
      qed
      ultimately show ?thesis using zhyps_map_zproof[OF m] by simp
    qed
    ultimately show "zvalid (sg_ax ?c) (set (hyps_of th)) (th_tpairs r) z (th_prop r) \<and> zinv z \<and> znolb 0 z \<and>
        zhyps_ok z" using vq(4) by (simp add: zhyps_ok_def)
  qed
qed

end
