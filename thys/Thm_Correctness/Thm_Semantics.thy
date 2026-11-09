section \<open>A Semantics of Pure's Meta-Logic\<close>

theory Thm_Semantics
  imports Thm_Model
begin

text \<open>
  Validity of theorems in the models of \<^theory>\<open>Thm_Correctness.Thm_Model\<close>. A theorem with
  hypotheses \<open>hs\<close>, flex-flex pairs \<open>tps\<close> and proposition \<open>P\<close> is valid if, for every instance
  \<open>(\<rho>, \<sigma>)\<close> that solves the flex-flex pairs, every model and every valuation \<open>(\<eta>, \<xi>)\<close> of the
  variables of the instance under which the hypotheses hold, the proposition holds. The flex-flex
  pairs are constraints on the instances, solved up to \<open>\<alpha>\<beta>\<eta>\<close>-conversion, as unification solves
  them. Within a fixed model and valuation (locale \<open>pure_valuation\<close>), the meaning of the spine
  of a proposition (its assumptions and parameters) is derived from the semantics of \<open>\<Longrightarrow>\<close> and
  \<open>\<And>\<close>.
\<close>




subsection \<open>Ground terms and instances\<close>

text \<open>Lifted propositions: the parameters of a prefix.\<close>

fun lparams :: "litem list \<Rightarrow> binders" where
  "lparams [] = []"
| "lparams (LImp c H # p) = lparams p"
| "lparams (LAll c a T # p) = (a, T) # lparams p"

lemma abs_pre_abs_list: "abs_pre p X = abs_list (lparams p) X"
  by (induction p rule: lparams.induct) auto

lemma map_snd_lparams [simp]: "map snd (lparams p) = ptys p"
  by (induction p rule: lparams.induct) auto

context pure_sig
begin

text \<open>Closed terms of a type, in every environment:\<close>

definition gterm :: "pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "gterm t T \<longleftrightarrow> closed t \<and> (\<forall>e. e \<turnstile> t : T)"

text \<open>Substitutions of the schematic variables by well-typed closed terms:\<close>

definition gsubst :: "vsubst \<Rightarrow> bool" where
  "gsubst \<sigma> \<longleftrightarrow> wt_subst \<sigma>"

lemma gtermI: "closed t \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> gterm t T"
  unfolding gterm_def using typing_closed by blast

lemma gtermD: "gterm t T \<Longrightarrow> closed t" "gterm t T \<Longrightarrow> e \<turnstile> t : T"
  unfolding gterm_def by blast+

lemma gsubstD: "gsubst \<sigma> \<Longrightarrow> wt_subst \<sigma>" "gsubst \<sigma> \<Longrightarrow> closed_subst \<sigma>"
  unfolding gsubst_def wt_subst_def by blast+

lemma cinst_comp:
  assumes "cinst \<rho>" "cinst \<rho>0"
  shows "cinst (\<lambda>v S. tsubst \<rho> (\<rho>0 v S))"
proof -
  have ws: "has_sort alg (\<rho>' v S) S" if "wsinst alg \<rho>'" for \<rho>' v S
    using that unfolding wsinst_def by blast
  have ce: "cert_typ alg ar (\<rho>' v S)" if "cert_inst \<rho>'" "sort_ok alg S" for \<rho>' v S
    using that unfolding cert_inst_def by blast
  have "has_sort alg (tsubst \<rho> (\<rho>0 v S)) S" for v S
    by (rule has_sort_tsubst[OF ws[OF cinstD(1)[OF assms(2)]]]) (auto intro: ws[OF cinstD(1)[OF assms(1)]])
  moreover have "cert_typ alg ar (tsubst \<rho> (\<rho>0 v S))" if "sort_ok alg S" for v S
    by (rule cert_typ_tsubst[OF ce[OF cinstD(2)[OF assms(2)] that] cinstD(2)[OF assms(1)]])
  ultimately show ?thesis by (auto simp: cinst_def wsinst_def cert_inst_def)
qed

lemma loose_bvar_ap [simp]: "gsubst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (ap \<rho> \<sigma> t) k \<longleftrightarrow> loose_bvar t k"
  by (simp add: ap_def gsubstD)

lemma typing_ap_inst:
  "e \<turnstile> t : T \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> (\<lambda>i. tsubst \<rho> (e i)) \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
  by (rule typing_ap[OF typing_inst[OF _ cert_inst_inst_ok]])

lemma gterm_ap:
  "cert_inst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> closed t \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> gterm (ap \<rho> \<sigma> t) (tsubst \<rho> T)"
  by (rule gtermI[OF _ typing_ap_inst]) (auto simp: closed_def gsubstD)

text \<open>The instance of a term with loose bound variables:\<close>

abbreviation (input) ienv :: "tinst \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> ptyp" where
  "ienv \<rho> e \<equiv> \<lambda>i. tsubst \<rho> (e i)"

lemma ap_implies [simp]: "ap \<rho> \<sigma> implies = implies"
  by (simp add: ap_def)

lemma ap_all_const [simp]: "ap \<rho> \<sigma> (all_const T) = all_const (tsubst \<rho> T)"
  by (simp add: ap_def)

lemma ap_list_implies: "ap \<rho> \<sigma> (list_implies As B) = list_implies (map (ap \<rho> \<sigma>) As) (ap \<rho> \<sigma> B)"
  by (induction As) auto

lemma typing_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p X : propT \<Longrightarrow>
    pushes e (ptys p) \<turnstile> X : propT \<and> (\<forall>T\<in>set (ptys p). cert_typ alg ar T)"
proof (induction p arbitrary: e)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons.prems(1) obtain U where "c = Const STR ''Pure.imp'' U" by auto
    with LImp have "dest_imp (lift_pre (i # p) X) = Some (H, lift_pre p X)" by simp
    from typing_dest_imp(5)[OF Cons.prems(2) this] have "e \<turnstile> lift_pre p X : propT" .
    from Cons.IH[OF _ this] Cons.prems(1) LImp show ?thesis by simp
  next
    case (LAll c a T)
    with Cons.prems(1) obtain U where "c = Const STR ''Pure.all'' U" by auto
    with LAll have "dest_all (lift_pre (i # p) X) = Some (a, T, lift_pre p X)" by simp
    note ty = typing_dest_all[OF Cons.prems(2) this]
    from Cons.IH[OF _ ty(5)] Cons.prems(1) LAll ty(4) show ?thesis by simp
  qed
qed simp

lemma loose_bvar_lift_pre:
  "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> \<not> loose_bvar (lift_pre p X) k \<Longrightarrow> \<not> loose_bvar X (k + ilength (ptys p))"
proof (induction p arbitrary: k)
  case (Cons i p)
  show ?case
  proof (cases i)
    case (LImp c H)
    with Cons show ?thesis by auto
  next
    case (LAll c a T)
    with Cons.prems have "\<not> loose_bvar (lift_pre p X) (k + 1)" by auto
    from Cons.IH[OF _ this] Cons.prems(1) LAll show ?thesis by (simp add: ac_simps)
  qed
qed simp

lemma typing_lift_pre_imp:
  assumes "litem_ok i" "e \<turnstile> lift_pre (i # p) X : propT" "i = LImp c H"
  shows "lift_pre (i # p) X = implies $ H $ lift_pre p X" "e \<turnstile> H : propT" "e \<turnstile> lift_pre p X : propT"
proof -
  from assms(1,3) obtain U where "c = Const STR ''Pure.imp'' U" by auto
  with assms(3) have "dest_imp (lift_pre (i # p) X) = Some (H, lift_pre p X)" by simp
  from typing_dest_imp[OF assms(2) this]
  show "lift_pre (i # p) X = implies $ H $ lift_pre p X" "e \<turnstile> H : propT" "e \<turnstile> lift_pre p X : propT"
    by simp_all
qed

lemma typing_lift_pre_all:
  assumes "litem_ok i" "e \<turnstile> lift_pre (i # p) X : propT" "i = LAll c a T"
  shows "lift_pre (i # p) X = all_const T $ Abs a T (lift_pre p X)" "e\<langle>0:T\<rangle> \<turnstile> lift_pre p X : propT"
proof -
  from assms(1,3) obtain U where "c = Const STR ''Pure.all'' U" by auto
  with assms(3) have "dest_all (lift_pre (i # p) X) = Some (a, T, lift_pre p X)" by simp
  from typing_dest_all[OF assms(2) this]
  show "lift_pre (i # p) X = all_const T $ Abs a T (lift_pre p X)" "e\<langle>0:T\<rangle> \<turnstile> lift_pre p X : propT"
    by simp_all
qed

end


subsection \<open>Values of bound variables\<close>

context pure_model
begin

text \<open>Values of the parameters of a prefix, outermost first:\<close>

fun vpushes :: "(integer \<Rightarrow> 'u) \<Rightarrow> 'u list \<Rightarrow> integer \<Rightarrow> 'u" where
  "vpushes bv [] = bv"
| "vpushes bv (u # us) = vpushes (push u bv) us"

lemma vpushes_shift: "0 \<le> i \<Longrightarrow> vpushes bv us (i + ilength us) = bv i"
proof (induction us arbitrary: bv i)
  case (Cons u us)
  have "vpushes (push u bv) us ((i + 1) + ilength us) = push u bv (i + 1)"
    by (rule Cons.IH) (use Cons.prems in \<open>simp add: integer_arith\<close>)
  then show ?case using Cons.prems by (simp add: push_def algebra_simps integer_arith)
qed simp

fun uapps :: "'u \<Rightarrow> 'u list \<Rightarrow> 'u" where
  "uapps f [] = f"
| "uapps f (u # us) = uapps (uapp f u) us"

lemma sem_abs_list:
  "list_all2 (\<lambda>(x, T) u. u \<in>\<^sub>u tsem \<eta> T) bs us \<Longrightarrow>
    uapps (sem \<eta> \<xi> bv (abs_list bs X)) us = sem \<eta> \<xi> (vpushes bv us) X"
proof (induction bs us arbitrary: bv rule: list_all2_induct)
  case (Cons b bs u us)
  obtain x T where b: "b = (x, T)" by (cases b)
  with Cons.hyps(1) have "u \<in>\<^sub>u tsem \<eta> T" by simp
  then have "uapp (sem \<eta> \<xi> bv (abs_list (b # bs) X)) u = sem \<eta> \<xi> (push u bv) (abs_list bs X)"
    by (simp add: b uapp_ulam)
  with Cons.IH show ?case by simp
qed simp

lemma tsem_propT [simp]: "tsem \<eta> propT = ubool"
  by (simp add: propT_def)

lemma bvals_ienv_push:
  "bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow> u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<Longrightarrow> bvals \<eta> (ienv \<rho> (e\<langle>0:T\<rangle>)) (push u bv)"
  using bvals_push[of \<eta> "ienv \<rho> e" bv u "tsubst \<rho> T"] by (simp add: tsubst_shift)

lemma bvals_vpushes:
  "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) Ts us \<Longrightarrow> bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow>
    bvals \<eta> (ienv \<rho> (pushes e Ts)) (vpushes bv us)"
proof (induction Ts us arbitrary: e bv rule: list_all2_induct)
  case (Cons T Ts u us)
  from Cons.IH[OF bvals_ienv_push[OF Cons.prems Cons.hyps(1)]] show ?case by simp
qed simp

lemma bvals0: "bvals \<eta> (ienv \<rho> (\<lambda>_. propT)) (\<lambda>_. utrue)"
  by (simp add: bvals_def ubool_mem tsubst_propT)

lemma list_all2_pairs: "list_all2 (\<lambda>(x, T) u. P T u) bs us \<longleftrightarrow> list_all2 P (map snd bs) us"
  by (simp add: list_all2_map1 split_def)

text \<open>Truth of closed propositions is invariant under conversion:\<close>

lemma holds_at_conv:
  assumes "good \<eta> \<xi>" "gterm A propT" "gterm B propT" "A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B" "holds_at \<eta> \<xi> A"
  shows "holds_at \<eta> \<xi> B"
proof -
  have "sem \<eta> \<xi> (\<lambda>_. utrue) A = sem \<eta> \<xi> (\<lambda>_. utrue) B"
    by (rule sem_conv[OF assms(1) gtermD(2)[OF assms(2), of "\<lambda>_. propT"]
      gtermD(2)[OF assms(3), of "\<lambda>_. propT"] assms(4)]) (simp add: bvals_def ubool_mem)
  with assms(5) show ?thesis by (simp add: holds_at_def)
qed

end


subsection \<open>Truth under a valuation\<close>

locale pure_valuation = pure_model alg ar ctab umem ufun uapp ulam ubool utrue ufalse tcon cls cval
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option"
    and umem :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix \<open>\<in>\<^sub>u\<close> 50) and ufun uapp ulam ubool utrue ufalse tcon cls cval +
  fixes \<eta> :: "'u tval" and \<xi> :: "'u vval"
  assumes good: "good \<eta> \<xi>"
begin

abbreviation holds :: "pterm \<Rightarrow> bool" where
  "holds A \<equiv> holds_at \<eta> \<xi> A"

abbreviation hb :: "(integer \<Rightarrow> 'u) \<Rightarrow> pterm \<Rightarrow> bool" where
  "hb bv A \<equiv> sem \<eta> \<xi> bv A = utrue"

abbreviation bv0 :: "integer \<Rightarrow> 'u" where
  "bv0 \<equiv> \<lambda>_. utrue"

lemma holds_hb: "holds A \<longleftrightarrow> hb bv0 A"
  by (simp add: holds_at_def)

text \<open>Values of parameters, outermost first:\<close>

abbreviation pvals :: "tinst \<Rightarrow> binders \<Rightarrow> 'u list \<Rightarrow> bool" where
  "pvals \<rho> ps us \<equiv> list_all2 (\<lambda>(a, T) u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) ps us"

lemma pvals_snd: "map snd ps = map snd qs \<Longrightarrow> pvals \<rho> ps us \<longleftrightarrow> pvals \<rho> qs us"
  by (simp add: list_all2_pairs[of "\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"])

lemma bvals_vpushes_p:
  "pvals \<rho> ps us \<Longrightarrow> bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow> bvals \<eta> (ienv \<rho> (pushes e (map snd ps))) (vpushes bv us)"
  by (rule bvals_vpushes) (simp_all add: list_all2_pairs[of "\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"])

lemma pvals_inst:
  "pvals \<rho> ps us \<Longrightarrow> list_all2 (\<lambda>(x, T) u. u \<in>\<^sub>u tsem \<eta> T) (map (\<lambda>(x, T). (x, tsubst \<rho> T)) ps) us"
  by (simp add: list_all2_map1 split_def)

lemma sem_ap_bool:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> A : propT" "bvals \<eta> (ienv \<rho> e) bv"
  shows "sem \<eta> \<xi> bv (ap \<rho> \<sigma> A) \<in>\<^sub>u ubool"
  using sem_typing[OF good typing_ap_inst[OF assms(3,1) gsubstD(1)[OF assms(2)]] assms(4)]
  by (simp add: tsubst_propT)

lemma hb_imp:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> H : propT" "e \<turnstile> B : propT" "bvals \<eta> (ienv \<rho> e) bv"
  shows "hb bv (ap \<rho> \<sigma> (implies $ H $ B)) \<longleftrightarrow> (hb bv (ap \<rho> \<sigma> H) \<longrightarrow> hb bv (ap \<rho> \<sigma> B))"
  using sem_implies[OF sem_ap_bool[OF assms(1,2,3,5)] sem_ap_bool[OF assms(1,2,4,5)]] by simp

lemma hb_all:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "e\<langle>0:T\<rangle> \<turnstile> b : propT" "bvals \<eta> (ienv \<rho> e) bv"
  shows "hb bv (ap \<rho> \<sigma> (all_const T $ Abs a T b)) \<longleftrightarrow>
    (\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow> hb (push u bv) (ap \<rho> \<sigma> b))"
proof -
  have "sem \<eta> \<xi> (push u bv) (ap \<rho> \<sigma> b) \<in>\<^sub>u ubool" if "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for u
    by (rule sem_ap_bool[OF assms(1,2,3) bvals_ienv_push[OF assms(4) that]])
  from sem_all[where T = "tsubst \<rho> T" and bv = bv and b = "ap \<rho> \<sigma> b" and a = a, OF this]
  show ?thesis by simp
qed

lemma sem_list_implies:
  "(\<forall>A\<in>set As. sem \<eta> \<xi> bv A \<in>\<^sub>u ubool) \<Longrightarrow> sem \<eta> \<xi> bv B \<in>\<^sub>u ubool \<Longrightarrow>
    sem \<eta> \<xi> bv (list_implies As B) \<in>\<^sub>u ubool \<and> (hb bv (list_implies As B) \<longleftrightarrow> ((\<forall>A\<in>set As. hb bv A) \<longrightarrow> hb bv B))"
proof (induction As)
  case (Cons A As)
  then have b: "sem \<eta> \<xi> bv A \<in>\<^sub>u ubool" "sem \<eta> \<xi> bv (list_implies As B) \<in>\<^sub>u ubool" by simp_all
  from sem_implies[OF b] Cons show ?case by auto
qed simp

text \<open>Closed propositions:\<close>

lemma gterm_bool: "gterm A propT \<Longrightarrow> sem \<eta> \<xi> bv0 A \<in>\<^sub>u ubool"
  using sem_typing[OF good gtermD(2), of A propT "\<lambda>_. propT"] by (simp add: bvals_def ubool_mem)

lemma holds_conv: "gterm A propT \<Longrightarrow> gterm B propT \<Longrightarrow> A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B \<Longrightarrow> holds A \<Longrightarrow> holds B"
  by (rule holds_at_conv[OF good])

lemma holds_imp: "gterm A propT \<Longrightarrow> gterm B propT \<Longrightarrow> holds (implies $ A $ B) \<longleftrightarrow> (holds A \<longrightarrow> holds B)"
  using sem_implies[OF gterm_bool gterm_bool] by (simp add: holds_at_def)

lemma holds_list_implies:
  assumes "gterm (list_implies As B) propT"
  shows "holds (list_implies As B) \<longleftrightarrow> ((\<forall>A\<in>set As. holds A) \<longrightarrow> holds B)"
  using assms
proof (induction As)
  case (Cons A As)
  have g: "gterm A propT" "gterm (list_implies As B) propT"
    using Cons.prems typing_implies by (auto simp: gterm_def closed_def implies_def)
  with Cons.IH show ?case by (auto simp: holds_imp)
qed simp

lemma holds_list_impliesI:
  assumes "gterm (list_implies As B) propT" "(\<And>A. A \<in> set As \<Longrightarrow> holds A) \<Longrightarrow> holds B"
  shows "holds (list_implies As B)"
  using holds_list_implies[OF assms(1)] assms(2) by blast

lemma holds_list_impliesD:
  assumes "gterm (list_implies As B) propT" "holds (list_implies As B)" "\<And>A. A \<in> set As \<Longrightarrow> holds A"
  shows "holds B"
  using holds_list_implies[OF assms(1)] assms(2,3) by blast


subsection \<open>The spine of a proposition\<close>

text \<open>
  The semantics of the spine of a proposition \<open>A\<close>, for an instance \<open>(\<rho>, \<sigma>)\<close>, values \<open>bv\<close>
  of its loose bound variables and values \<open>us\<close> of its parameters (outermost first). The \<open>n\<close>-th
  assumption is ignored. The spine is that of \<open>A\<close>; the instance is applied to the hypotheses
  and the conclusion.
\<close>

function asem :: "tinst \<Rightarrow> vsubst \<Rightarrow> integer \<Rightarrow> (integer \<Rightarrow> 'u) \<Rightarrow> 'u list \<Rightarrow> pterm \<Rightarrow> bool" where
  "asem \<rho> \<sigma> n bv us A =
    (case dest_imp A of
      Some (H, B) \<Rightarrow> ((n \<noteq> 1 \<longrightarrow> hb bv (ap \<rho> \<sigma> H)) \<longrightarrow> asem \<rho> \<sigma> (n - 1) bv us B)
    | None \<Rightarrow>
      (case dest_all A of
        Some (a, T, b) \<Rightarrow> (case us of [] \<Rightarrow> True | u # us' \<Rightarrow> asem \<rho> \<sigma> n (push u bv) us' b)
      | None \<Rightarrow> hb bv (ap \<rho> \<sigma> A)))"
  by auto
termination by (relation "measure (\<lambda>(_, _, _, _, _, A). size A)") (auto dest: dest_size)

declare asem.simps [simp del]

text \<open>A proposition holds iff its spine semantics holds for all values of its parameters.\<close>

lemma holds_asem:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
  shows "e \<turnstile> A : propT \<Longrightarrow> bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow> n \<le> 0 \<Longrightarrow>
    hb bv (ap \<rho> \<sigma> A) \<longleftrightarrow> (\<forall>us. pvals \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n bv us A)"
proof (induction A arbitrary: n bv e rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    note ty = typing_dest_imp[OF less.prems(1) HB]
    have IH: "hb bv (ap \<rho> \<sigma> B) \<longleftrightarrow>
        (\<forall>us. pvals \<rho> (strip_params B) us \<longrightarrow> asem \<rho> \<sigma> (n - 1) bv us B)"
      using less.IH[OF _ ty(5) less.prems(2), of "n - 1"] ty(1) less.prems(3)
      by (simp add: implies_def)
    have "hb bv (ap \<rho> \<sigma> A) \<longleftrightarrow> (hb bv (ap \<rho> \<sigma> H) \<longrightarrow> hb bv (ap \<rho> \<sigma> B))"
      using hb_imp[OF \<rho> \<sigma> ty(4,5) less.prems(2)] ty(1) by simp
    also have "\<dots> \<longleftrightarrow> (\<forall>us. pvals \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n bv us A)"
      using IH less.prems(3) HB by (subst asem.simps) (auto simp: strip_params_imp)
    finally show ?thesis .
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
      note ty = typing_dest_all[OF less.prems(1) aTb]
      have IH: "hb (push u bv) (ap \<rho> \<sigma> b) \<longleftrightarrow>
          (\<forall>us. pvals \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (push u bv) us b)"
        if "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for u
        using less.IH[OF _ ty(5) bvals_ienv_push[OF less.prems(2) that], of n] ty(1) less.prems(3)
        by (simp add: all_const_def)
      have "hb bv (ap \<rho> \<sigma> A) \<longleftrightarrow> (\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow> hb (push u bv) (ap \<rho> \<sigma> b))"
        using hb_all[OF \<rho> \<sigma> ty(5) less.prems(2)] ty(1) by simp
      also have "\<dots> \<longleftrightarrow> (\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
          (\<forall>us. pvals \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (push u bv) us b))"
        using IH by blast
      also have "\<dots> \<longleftrightarrow> (\<forall>us. pvals \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n bv us A)"
      proof -
        have as: "asem \<rho> \<sigma> n bv (u # us) A = asem \<rho> \<sigma> n (push u bv) us b" for u us
          using None aTb by (subst asem.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b"
          using None aTb by (rule strip_params_all)
        show ?thesis
        proof
          assume H: "\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
            (\<forall>us. pvals \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (push u bv) us b)"
          show "\<forall>us. pvals \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n bv us A"
          proof (intro allI impI)
            fix us assume "pvals \<rho> (strip_params A) us"
            then obtain u us' where "us = u # us'" "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
              "pvals \<rho> (strip_params b) us'"
              by (auto simp: sp list_all2_Cons1)
            with H as show "asem \<rho> \<sigma> n bv us A" by simp
          qed
        next
          assume H: "\<forall>us. pvals \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n bv us A"
          show "\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
            (\<forall>us. pvals \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (push u bv) us b)"
          proof (intro allI impI)
            fix u us assume "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" "pvals \<rho> (strip_params b) us"
            then have "pvals \<rho> (strip_params A) (u # us)" by (simp add: sp)
            with H as show "asem \<rho> \<sigma> n (push u bv) us b" by metis
          qed
        qed
      qed
      finally show ?thesis .
    next
      case None': None
      with None show ?thesis by (subst asem.simps) (simp add: strip_params_other)
    qed
  qed
qed

text \<open>Ignoring an assumption weakens the spine semantics.\<close>

lemma asem_mono: "asem \<rho> \<sigma> n bv us A \<Longrightarrow> m \<le> 0 \<Longrightarrow> asem \<rho> \<sigma> m bv us A"
proof (induction \<rho> \<sigma> n bv us A arbitrary: m rule: asem.induct)
  case (1 \<rho> \<sigma> n bv us A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    from "1.prems"(1) HB have a: "(n \<noteq> 1 \<longrightarrow> hb bv (ap \<rho> \<sigma> H)) \<longrightarrow> asem \<rho> \<sigma> (n - 1) bv us B"
      by (subst (asm) asem.simps) simp
    have "asem \<rho> \<sigma> (m - 1) bv us B" if hH: "hb bv (ap \<rho> \<sigma> H)"
    proof -
      have ant: "n \<noteq> 1 \<longrightarrow> hb bv (ap \<rho> \<sigma> H)" using hH by simp
      with a have "asem \<rho> \<sigma> (n - 1) bv us B" by simp
      from "1.IH"(2)[OF HB refl ant this, of "m - 1"] "1.prems"(2) show ?thesis by simp
    qed
    with HB "1.prems"(2) show ?thesis by (subst asem.simps) simp
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
      show ?thesis
      proof (cases us)
        case Nil
        with None aTb show ?thesis by (subst asem.simps) simp
      next
        case (Cons u us')
        from "1.prems"(1) None aTb Cons have "asem \<rho> \<sigma> n (push u bv) us' b"
          by (subst (asm) asem.simps) simp
        from "1.IH"(1)[OF None aTb refl refl Cons this "1.prems"(2)] None aTb Cons
        show ?thesis by (subst asem.simps) simp
      qed
    next
      case None': None
      with None "1.prems"(1) show ?thesis by (subst (asm) asem.simps, subst asem.simps) simp
    qed
  qed
qed

text \<open>
  Removing the parameters of a proposition (\<^const>\<open>remove_params\<close>): if the result holds for
  values \<open>us\<close> of the parameters, the spine semantics holds for them, ignoring the \<open>n\<close>-th
  assumption.
\<close>

lemma remove_params_asem:
  assumes "ok (remove_params j n A) A'" "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> A : propT"
    "bvals \<eta> (ienv \<rho> e) bv" "ilength (strip_params A) = j"
    "pvals \<rho> (strip_params A) us" "hb (vpushes bv us) (ap \<rho> \<sigma> A')"
  shows "asem \<rho> \<sigma> n bv us A"
  using assms(1,4-)
proof (induction j n A arbitrary: A' bv us e rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp have A': "A' = A" by (subst (asm) remove_params.simps) simp
    have sp: "strip_params A = []"
      using True "1.prems"(4) by (cases "strip_params A") (auto simp: ilength_eq integer_eq_iff)
    with "1.prems"(5) have us: "us = []" by simp
    from holds_asem[OF assms(2,3) "1.prems"(2,3), where n = n] True "1.prems"(6) A' us sp
    show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      note ty = typing_dest_imp[OF "1.prems"(2) HB]
      have spB: "strip_params A = strip_params B" using HB by (rule strip_params_imp)
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have r: "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True r ty(5) "1.prems"(3)] "1.prems"(4-6) spB
        have "asem \<rho> \<sigma> (n - 1) bv us B" by simp
        with HB True show ?thesis by (subst asem.simps) simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits xres.splits)
        have lu: "ilength us = j"
          using "1.prems"(4) list_all2_lengthD[OF "1.prems"(5)] by (simp add: ilength_eq)
        have j0: "0 \<le> j" using lu ilength_nonneg by metis
        have bv': "bvals \<eta> (ienv \<rho> (pushes e (map snd (strip_params A)))) (vpushes bv us)"
          by (rule bvals_vpushes_p[OF "1.prems"(5,3)])
        have eqH: "sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> (incr_boundvars j H)) = sem \<eta> \<xi> bv (ap \<rho> \<sigma> H)"
        proof -
          have "ap \<rho> \<sigma> (incr_boundvars j H) = incr_bv j 0 (ap \<rho> \<sigma> H)"
            using gsubstD(1)[OF assms(3)] by (simp add: incr_boundvars_incr_bv ap_lift)
          moreover have "sem \<eta> \<xi> (vpushes bv us) (incr_bv j 0 (ap \<rho> \<sigma> H)) = sem \<eta> \<xi> bv (ap \<rho> \<sigma> H)"
            by (subst sem_incr_bv) (use j0 in simp, use j0 in simp, rule sem_bv_ext, use lu vpushes_shift in auto)
          ultimately show ?thesis by simp
        qed
        have bH: "sem \<eta> \<xi> bv (ap \<rho> \<sigma> H) \<in>\<^sub>u ubool" by (rule sem_ap_bool[OF assms(2,3) ty(4) "1.prems"(3)])
        have bB': "sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> B') \<in>\<^sub>u ubool"
        proof -
          have "pushes e (map snd (strip_params B)) \<turnstile> B' : propT"
            by (rule remove_params_typing[OF B' _ ty(5)]) (use "1.prems"(4) spB in simp)
          then show ?thesis using sem_ap_bool[OF assms(2,3) _ bv'] spB by simp
        qed
        from "1.prems"(6) A' have hi: "hb (vpushes bv us) (implies $ ap \<rho> \<sigma> (incr_boundvars j H) $ ap \<rho> \<sigma> B')"
          by simp
        have bX: "sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> (incr_boundvars j H)) \<in>\<^sub>u ubool" using eqH bH by simp
        have "hb (vpushes bv us) (ap \<rho> \<sigma> (incr_boundvars j H)) \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> B')"
          using sem_implies[OF bX bB'] hi by simp
        with eqH have h: "hb bv (ap \<rho> \<sigma> H) \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> B')" by simp
        have "hb bv (ap \<rho> \<sigma> H) \<longrightarrow> asem \<rho> \<sigma> (n - 1) bv us B"
          using "1.IH"(3)[OF False HB refl n1 B' ty(5) "1.prems"(3)] "1.prems"(4,5) spB h
          by simp
        with HB n1 show ?thesis by (subst asem.simps) simp
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTb)
        then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
        note ty = typing_dest_all[OF "1.prems"(2) aTb]
        with rp False None aTb have r: "ok (remove_params (j - 1) n b) A'"
          by (subst (asm) remove_params.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b" using None aTb by (rule strip_params_all)
        with "1.prems"(5) obtain u us' where us: "us = u # us'" and u: "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
          and us': "pvals \<rho> (strip_params b) us'"
          by (auto simp: list_all2_Cons1)
        have "asem \<rho> \<sigma> n (push u bv) us' b"
        proof (rule "1.IH"(1)[OF False None aTb refl refl r ty(5)])
          show "bvals \<eta> (ienv \<rho> (e\<langle>0:T\<rangle>)) (push u bv)" by (rule bvals_ienv_push[OF "1.prems"(3) u])
          show "ilength (strip_params b) = j - 1" using "1.prems"(4) sp by simp
          show "pvals \<rho> (strip_params b) us'" by (rule us')
          show "hb (vpushes (push u bv) us') (ap \<rho> \<sigma> A')" using "1.prems"(6) us by simp
        qed
        with None aTb us show ?thesis by (subst asem.simps) simp
      next
        case None': None
        with rp False None "1.prems"(4) show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits simp: strip_params_other)
      qed
    qed
  qed
qed

lemma holds_list_forall:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
  shows "bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow> pushes e (map snd ps) \<turnstile> X : propT \<Longrightarrow>
    \<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T \<Longrightarrow>
    hb bv (ap \<rho> \<sigma> (list_forall ps X)) \<longleftrightarrow> (\<forall>us. pvals \<rho> ps us \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> X))"
proof (induction ps arbitrary: bv e)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain a T where p: "p = (a, T)" by (cases p)
  have tY: "e\<langle>0:T\<rangle> \<turnstile> list_forall ps X : propT"
    using Cons.prems(2,3) p by (simp add: typing_list_forall)
  have "hb bv (ap \<rho> \<sigma> (list_forall (p # ps) X)) \<longleftrightarrow>
      (\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow> hb (push u bv) (ap \<rho> \<sigma> (list_forall ps X)))"
    using hb_all[OF \<rho> \<sigma> tY Cons.prems(1)] p by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. pvals \<rho> ps us \<longrightarrow> hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X)))"
  proof (intro iff_allI imp_cong[OF refl])
    fix u assume u: "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)"
    show "hb (push u bv) (ap \<rho> \<sigma> (list_forall ps X)) \<longleftrightarrow>
        (\<forall>us. pvals \<rho> ps us \<longrightarrow> hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X))"
      by (rule Cons.IH[OF bvals_ienv_push[OF Cons.prems(1) u]]) (use Cons.prems p in simp_all)
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>us. pvals \<rho> (p # ps) us \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> X))"
  proof
    assume H: "\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. pvals \<rho> ps us \<longrightarrow> hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X))"
    show "\<forall>us. pvals \<rho> (p # ps) us \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> X)"
    proof (intro allI impI)
      fix us assume "pvals \<rho> (p # ps) us"
      then obtain u us' where "us = u # us'" "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" "pvals \<rho> ps us'"
        by (auto simp: p list_all2_Cons1)
      with H show "hb (vpushes bv us) (ap \<rho> \<sigma> X)" by simp
    qed
  next
    assume H: "\<forall>us. pvals \<rho> (p # ps) us \<longrightarrow> hb (vpushes bv us) (ap \<rho> \<sigma> X)"
    show "\<forall>u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. pvals \<rho> ps us \<longrightarrow> hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X))"
    proof (intro allI impI)
      fix u us assume "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" "pvals \<rho> ps us"
      then have "pvals \<rho> (p # ps) (u # us)" by (simp add: p)
      with H show "hb (vpushes (push u bv) us) (ap \<rho> \<sigma> X)" by fastforce
    qed
  qed
  finally show ?case .
qed

text \<open>Flattening parameters (\<^const>\<open>flatten_params\<close>) strengthens a proposition.\<close>

lemma flatten_params_holds:
  assumes "ok (flatten_params vl n A) A'" "length (vl (map fst (strip_params A))) = length (strip_params A)"
    "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> A : propT" "closed A" "holds (ap \<rho> \<sigma> A')"
  shows "holds (ap \<rho> \<sigma> A)"
proof -
  let ?ps = "strip_params A"
  let ?vars = "zip (vl (map fst ?ps)) (map snd ?ps)"
  let ?e = "\<lambda>_::integer. propT"
  have tA: "?e \<turnstile> A : propT" by (rule typing_closed[OF assms(5,6)])
  obtain A'' where r: "ok (remove_params (ilength ?ps) n A) A''" and A': "A' = list_forall ?vars A''"
    and sv: "map snd ?vars = map snd ?ps"
    by (rule flatten_params_ok[OF assms(1,2)])
  have tA'': "pushes ?e (map snd ?vars) \<turnstile> A'' : propT"
    using remove_params_typing[OF r refl tA] sv by simp
  have cvars: "\<forall>(a, T)\<in>set ?vars. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
  proof (clarify)
    fix a T assume "(a, T) \<in> set ?vars"
    from set_zip_rightD[OF this] obtain a' where "(a', T) \<in> set ?ps" by auto
    then show "cert_typ alg ar (all_type T) \<and> cert_typ alg ar T" by (rule typing_strip_params[OF tA])
  qed
  have b0: "bvals \<eta> (ienv \<rho> ?e) bv0" by (rule bvals0)
  have h: "\<forall>us. pvals \<rho> ?vars us \<longrightarrow> hb (vpushes bv0 us) (ap \<rho> \<sigma> A'')"
    using holds_list_forall[OF assms(3,4) b0 tA'' cvars] assms(7) A' by (simp add: holds_hb)
  have "\<forall>us. pvals \<rho> ?ps us \<longrightarrow> asem \<rho> \<sigma> 0 bv0 us A"
  proof (intro allI impI)
    fix us assume t: "pvals \<rho> ?ps us"
    have "asem \<rho> \<sigma> n bv0 us A"
    proof (rule remove_params_asem[OF r assms(3,4) tA b0])
      show "hb (vpushes bv0 us) (ap \<rho> \<sigma> A'')" using h t pvals_snd[OF sv] by simp
    qed (use t in simp_all)
    then show "asem \<rho> \<sigma> 0 bv0 us A" by (rule asem_mono) simp
  qed
  with holds_asem[OF assms(3,4) tA b0, where n = 0] show ?thesis by (simp add: holds_hb)
qed


subsection \<open>Closures over parameters\<close>

lemma ienv_pushes: "ienv \<rho> (pushes e Ts) = pushes (ienv \<rho> e) (map (tsubst \<rho>) Ts)"
  by (induction Ts arbitrary: e) (simp_all add: tsubst_shift)

lemma typing_abs_list_ap:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "pushes e (map snd bs) \<turnstile> X : T" "\<forall>U\<in>snd ` set bs. cert_typ alg ar U"
  shows "ienv \<rho> e \<turnstile> ap \<rho> \<sigma> (abs_list bs X) : map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs) \<Rrightarrow> tsubst \<rho> T"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) bs"
  have ms: "map (tsubst \<rho>) (map snd bs) = map snd ?bs" by (induction bs) auto
  have "ienv \<rho> (pushes e (map snd bs)) \<turnstile> ap \<rho> \<sigma> X : tsubst \<rho> T"
    by (rule typing_ap_inst[OF assms(3,1) gsubstD(1)[OF assms(2)]])
  then have "pushes (ienv \<rho> e) (map snd ?bs) \<turnstile> ap \<rho> \<sigma> X : tsubst \<rho> T"
    unfolding ienv_pushes ms .
  moreover have "\<forall>U\<in>snd ` set ?bs. cert_typ alg ar U"
    using assms(1,4) by (auto simp: cert_typ_tsubst)
  ultimately have "ienv \<rho> e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> X) : map snd ?bs \<Rrightarrow> tsubst \<rho> T"
    by (rule typing_abs_list)
  then show ?thesis by (simp add: ap_abs_list)
qed

text \<open>
  The first premise of a rule is proved by the assumption \<open>asm\<close> (elim-resolution) if the
  closures of \<open>asm\<close> and of the conclusion of the premise are equivalent.
\<close>

lemma eres_holds:
  assumes ap: "assum_problems k A = (params, asms, concl)" and asm: "asm \<in> set asms"
    and cv: "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> (rlist_abs params asm)) = sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> (rlist_abs params concl))"
    and \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and tA: "e \<turnstile> A : propT" and cA: "closed A"
  shows "holds (ap \<rho> \<sigma> A)"
proof -
  let ?e = "\<lambda>_::integer. propT"
  have tA0: "?e \<turnstile> A : propT" by (rule typing_closed[OF tA cA])
  note st = assum_problems_struct[OF ap tA0]
  let ?ps = "rev params"
  let ?E = "pushes ?e (map snd ?ps)"
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) ?ps"
  have cps: "\<forall>(a, T)\<in>set ?ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tl: "?E \<turnstile> list_implies asms concl : propT"
    using tA0 st(1) by (simp_all add: typing_list_forall)
  have b0: "bvals \<eta> (ienv \<rho> ?e) bv0" by (rule bvals0)
  have cU: "\<forall>U\<in>snd ` set ?ps. cert_typ alg ar U" using cps by auto
  have aX: "ap \<rho> \<sigma> (rlist_abs params X) = abs_list ?bs (ap \<rho> \<sigma> X)" for X
    by (simp add: rlist_abs_abs_list ap_abs_list)
  have tX: "ienv \<rho> ?e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> X) : map snd ?bs \<Rrightarrow> tsubst \<rho> propT"
    if "X \<in> insert concl (set asms)" for X
    using typing_abs_list_ap[OF \<rho> \<sigma> _ cU, of ?e X propT] st(2,3) that by (auto simp: ap_abs_list)
  have eqc: "sem \<eta> \<xi> bv0 (abs_list ?bs (ap \<rho> \<sigma> asm)) = sem \<eta> \<xi> bv0 (abs_list ?bs (ap \<rho> \<sigma> concl))"
    using cv by (simp add: aX)
  have "\<forall>us. pvals \<rho> ?ps us \<longrightarrow> hb (vpushes bv0 us) (ap \<rho> \<sigma> (list_implies asms concl))"
  proof (intro allI impI)
    fix us assume pt: "pvals \<rho> ?ps us"
    have bvs: "bvals \<eta> (ienv \<rho> ?E) (vpushes bv0 us)" by (rule bvals_vpushes_p[OF pt b0])
    have bX: "sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> X) \<in>\<^sub>u ubool" if "X \<in> insert concl (set asms)" for X
      using sem_ap_bool[OF \<rho> \<sigma> _ bvs, of X] st(2,3) that by auto
    have eq: "sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> asm) = sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> concl)"
      using sem_abs_list[OF pvals_inst[OF pt], of \<xi> bv0 "ap \<rho> \<sigma> asm"]
        sem_abs_list[OF pvals_inst[OF pt], of \<xi> bv0 "ap \<rho> \<sigma> concl"] eqc by simp
    have "(\<forall>A\<in>set (map (ap \<rho> \<sigma>) asms). sem \<eta> \<xi> (vpushes bv0 us) A \<in>\<^sub>u ubool)"
      "sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> concl) \<in>\<^sub>u ubool"
      using bX by auto
    note li = sem_list_implies[OF this]
    have "(\<forall>A\<in>set asms. hb (vpushes bv0 us) (ap \<rho> \<sigma> A)) \<longrightarrow> hb (vpushes bv0 us) (ap \<rho> \<sigma> concl)"
      using asm eq by auto
    then show "hb (vpushes bv0 us) (ap \<rho> \<sigma> (list_implies asms concl))"
      by (simp add: ap_list_implies li)
  qed
  then have "hb bv0 (ap \<rho> \<sigma> (list_forall ?ps (list_implies asms concl)))"
    using holds_list_forall[OF \<rho> \<sigma> b0 tl cps] by blast
  then show ?thesis using st(1) by (simp add: holds_hb)
qed

text \<open>
  If the instances of \<open>X\<close> and \<open>Y\<close> are equal for all values of the parameters of a prefix,
  then \<open>Y\<close> under the prefix holds if \<open>X\<close> does.
\<close>

lemma holds_lift_pre_transfer:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
  shows "\<forall>i\<in>set p. litem_ok i \<Longrightarrow> e \<turnstile> lift_pre p X : propT \<Longrightarrow> e \<turnstile> lift_pre p Y : propT \<Longrightarrow>
    bvals \<eta> (ienv \<rho> e) bv \<Longrightarrow>
    (\<And>us. list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us \<Longrightarrow>
      sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> X) = sem \<eta> \<xi> (vpushes bv us) (ap \<rho> \<sigma> Y)) \<Longrightarrow>
    hb bv (ap \<rho> \<sigma> (lift_pre p X)) \<Longrightarrow> hb bv (ap \<rho> \<sigma> (lift_pre p Y))"
proof (induction p arbitrary: e bv)
  case Nil
  then show ?case using Nil.prems(5)[of "[]"] by simp
next
  case (Cons i p)
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    note iX = typing_lift_pre_imp[OF oki Cons.prems(2) LImp]
    note iY = typing_lift_pre_imp[OF oki Cons.prems(3) LImp]
    have hX: "hb bv (ap \<rho> \<sigma> H) \<longrightarrow> hb bv (ap \<rho> \<sigma> (lift_pre p X))"
      using Cons.prems(6) iX(1) hb_imp[OF \<rho> \<sigma> iX(2,3) Cons.prems(4)] by simp
    have "hb bv (ap \<rho> \<sigma> (lift_pre p X)) \<Longrightarrow> hb bv (ap \<rho> \<sigma> (lift_pre p Y))"
      by (rule Cons.IH[OF okp iX(3) iY(3) Cons.prems(4)]) (use Cons.prems(5) LImp in simp_all)
    with hX show ?thesis using iY(1) hb_imp[OF \<rho> \<sigma> iY(2,3) Cons.prems(4)] by simp
  next
    case (LAll c a T)
    note iX = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
    note iY = typing_lift_pre_all[OF oki Cons.prems(3) LAll]
    have "hb (push u bv) (ap \<rho> \<sigma> (lift_pre p Y))" if u: "u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)" for u
    proof (rule Cons.IH[OF okp iX(2) iY(2) bvals_ienv_push[OF Cons.prems(4) u]])
      show "sem \<eta> \<xi> (vpushes (push u bv) us) (ap \<rho> \<sigma> X) = sem \<eta> \<xi> (vpushes (push u bv) us) (ap \<rho> \<sigma> Y)"
        if "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us" for us
        using Cons.prems(5)[of "u # us"] that u LAll by simp
      show "hb (push u bv) (ap \<rho> \<sigma> (lift_pre p X))"
        using Cons.prems(6) hb_all[OF \<rho> \<sigma> iX(2) Cons.prems(4)] iX(1) u by simp
    qed
    then show ?thesis using hb_all[OF \<rho> \<sigma> iY(2) Cons.prems(4)] iY(1) by simp
  qed
qed

lemma holds_lift_pre_conv:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and ok: "\<forall>i\<in>set p. litem_ok i"
    and tX: "e \<turnstile> lift_pre p X : propT" and tY: "e \<turnstile> lift_pre p Y : propT"
    and cX: "closed (lift_pre p X)" and cY: "closed (lift_pre p Y)"
    and cv: "sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> (abs_pre p X)) = sem \<eta> \<xi> bv0 (ap \<rho> \<sigma> (abs_pre p Y))"
    and h: "holds (ap \<rho> \<sigma> (lift_pre p X))"
  shows "holds (ap \<rho> \<sigma> (lift_pre p Y))"
proof -
  let ?e = "\<lambda>_::integer. propT"
  have tX0: "?e \<turnstile> lift_pre p X : propT" and tY0: "?e \<turnstile> lift_pre p Y : propT"
    using typing_closed tX cX tY cY by blast+
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (lparams p)"
  have ms: "map snd ?bs = map (tsubst \<rho>) (ptys p)"
    by (induction p rule: lparams.induct) auto
  have "snd ` set (lparams p) = set (ptys p)" by (induction p rule: lparams.induct) auto
  then have cU: "\<forall>U\<in>snd ` set (lparams p). cert_typ alg ar U"
    using typing_lift_pre[OF ok tX0] by simp
  have tZ: "ienv \<rho> ?e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> Z) : map snd ?bs \<Rrightarrow> tsubst \<rho> propT"
    if "?e \<turnstile> lift_pre p Z : propT" for Z
  proof -
    have "pushes ?e (map snd (lparams p)) \<turnstile> Z : propT" using typing_lift_pre[OF ok that] by simp
    from typing_abs_list_ap[OF \<rho> \<sigma> this cU] show ?thesis by (simp add: ap_abs_list)
  qed
  have aZ: "ap \<rho> \<sigma> (abs_pre p Z) = abs_list ?bs (ap \<rho> \<sigma> Z)" for Z
    by (simp add: abs_pre_abs_list ap_abs_list)
  have b0: "bvals \<eta> (ienv \<rho> ?e) bv0" by (rule bvals0)
  have eq: "sem \<eta> \<xi> bv0 (abs_list ?bs (ap \<rho> \<sigma> X)) = sem \<eta> \<xi> bv0 (abs_list ?bs (ap \<rho> \<sigma> Y))"
    using cv by (simp add: aZ)
  have "hb bv0 (ap \<rho> \<sigma> (lift_pre p Y))"
  proof (rule holds_lift_pre_transfer[OF \<rho> \<sigma> ok tX0 tY0 b0])
    show "hb bv0 (ap \<rho> \<sigma> (lift_pre p X))" using h by (simp add: holds_hb)
    fix us assume us: "list_all2 (\<lambda>T u. u \<in>\<^sub>u tsem \<eta> (tsubst \<rho> T)) (ptys p) us"
    have "list_all2 (\<lambda>(x, T) u. u \<in>\<^sub>u tsem \<eta> T) ?bs us"
      unfolding list_all2_pairs[of "\<lambda>T u. u \<in>\<^sub>u tsem \<eta> T"] ms using us by (simp add: list_all2_map1)
    from sem_abs_list[OF this, of \<xi> bv0 "ap \<rho> \<sigma> X"] sem_abs_list[OF this, of \<xi> bv0 "ap \<rho> \<sigma> Y"] eq
    show "sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> X) = sem \<eta> \<xi> (vpushes bv0 us) (ap \<rho> \<sigma> Y)" by simp
  qed
  then show ?thesis by (simp add: holds_hb)
qed

end


subsection \<open>Validity\<close>

context pure_sig
begin

lemma conv_ap: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  unfolding ap_def by (rule conv_vsubst[OF conv_inst[OF _ cert_inst_inst_ok]])

end

context pure_model
begin

text \<open>Two closed terms denote the same value under a valuation:\<close>

definition eq_at :: "'u tval \<Rightarrow> 'u vval \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "eq_at \<eta> \<xi> t u \<longleftrightarrow> sem \<eta> \<xi> (\<lambda>_. utrue) t = sem \<eta> \<xi> (\<lambda>_. utrue) u"

lemma eq_at_conv:
  assumes "good \<eta> \<xi>" "gterm s T" "gterm t T" "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
  shows "eq_at \<eta> \<xi> s t"
  unfolding eq_at_def
  by (rule sem_conv[OF assms(1) gtermD(2)[OF assms(2), of "\<lambda>_. propT"]
      gtermD(2)[OF assms(3), of "\<lambda>_. propT"] assms(4)]) (simp add: bvals_def ubool_mem)

lemma eq_at_sym: "eq_at \<eta> \<xi> t u \<Longrightarrow> eq_at \<eta> \<xi> u t"
  and eq_at_trans: "eq_at \<eta> \<xi> t u \<Longrightarrow> eq_at \<eta> \<xi> u v \<Longrightarrow> eq_at \<eta> \<xi> t v"
  by (simp_all add: eq_at_def)

text \<open>
  Validity of a theorem with sort hypotheses \<open>Sh\<close>, hypotheses \<open>hs\<close>, flex-flex pairs \<open>tps\<close> and
  proposition \<open>P\<close>: if the sorts of \<open>Sh\<close> are inhabited, every instance whose flex-flex pairs hold
  as equations holds if its hypotheses do, for type instantiations that keep the inhabited sorts
  inhabited. For well-formed theorems, this is the semantic validity \<open>svalid\<close> below, where the
  variables are interpreted by valuations (lemma \<open>valid_svalid\<close>).
\<close>

definition valid :: "psort set \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid Sh hs tps P \<longleftrightarrow> (\<forall>S\<in>Sh. sinh S) \<longrightarrow> (\<forall>\<eta> \<xi> \<rho> \<sigma>. good \<eta> \<xi> \<longrightarrow> cinst \<rho> \<longrightarrow> inh_inst \<rho> \<longrightarrow>
    gsubst \<sigma> \<longrightarrow> (\<forall>(t, u)\<in>set tps. eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)) \<longrightarrow>
    (\<forall>h\<in>set hs. holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)) \<longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> P))"

lemma validI:
  "(\<And>\<eta> \<xi> \<rho> \<sigma>. (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow> cinst \<rho> \<Longrightarrow> inh_inst \<rho> \<Longrightarrow>
    gsubst \<sigma> \<Longrightarrow> (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)) \<Longrightarrow>
    (\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> P)) \<Longrightarrow>
    valid Sh hs tps P"
  unfolding valid_def by blast

lemma validD:
  "valid Sh hs tps P \<Longrightarrow> (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow> cinst \<rho> \<Longrightarrow> inh_inst \<rho> \<Longrightarrow>
    gsubst \<sigma> \<Longrightarrow> (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)) \<Longrightarrow>
    (\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> P)"
  unfolding valid_def by blast

lemma valid_mono: "valid Sh hs tps P \<Longrightarrow> Sh \<subseteq> Sh' \<Longrightarrow> valid Sh' hs tps P"
  unfolding valid_def by blast

text \<open>Validity is preserved by \<open>\<alpha>\<beta>\<eta>\<close>-conversion of the proposition, of the hypotheses and of the sides of the flex-flex pairs:\<close>

lemma valid_conv:
  assumes v: "valid Sh hs tps P"
    and P: "P \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> P'" "closed P" "e \<turnstile> P : propT" "closed P'" "e' \<turnstile> P' : propT"
    and hs: "list_all2 (\<lambda>h h'. h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h' \<and> closed h \<and> (\<exists>e. e \<turnstile> h : propT) \<and> closed h' \<and> (\<exists>e. e \<turnstile> h' : propT)) hs hs'"
    and tps: "list_all2 (\<lambda>(t, u) (t', u'). t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u' \<and>
      (\<exists>T e1 e2. closed t \<and> closed t' \<and> e1 \<turnstile> t : T \<and> e2 \<turnstile> t' : T) \<and>
      (\<exists>T e1 e2. closed u \<and> closed u' \<and> e1 \<turnstile> u : T \<and> e2 \<turnstile> u' : T)) tps tps'"
  shows "valid Sh hs' tps' P'"
proof (rule validI)
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps' \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
    and hh: "\<And>h. h \<in> set hs' \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  note c = conv_ap[OF _ cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]
  note g' = gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma>]
  have ce: "eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> t')"
    if "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "closed t" "closed t'" "e1 \<turnstile> t : T" "e2 \<turnstile> t' : T" for t t' e1 e2 T
    by (rule eq_at_conv[OF g g'[OF that(2,4)] g'[OF that(3,5)] c[OF that(1)]])
  have "holds_at \<eta> \<xi> (ap \<rho> \<sigma> P)"
  proof (rule validD[OF v sh g \<rho> \<rho>i \<sigma>])
    fix t u assume "(t, u) \<in> set tps"
    with tps obtain t' u' where "(t', u') \<in> set tps'" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
      and "\<exists>T e1 e2. closed t \<and> closed t' \<and> e1 \<turnstile> t : T \<and> e2 \<turnstile> t' : T"
      and "\<exists>T e1 e2. closed u \<and> closed u' \<and> e1 \<turnstile> u : T \<and> e2 \<turnstile> u' : T"
      by (auto simp: list_all2_conv_all_nth in_set_conv_nth split: prod.splits) (metis prod.collapse)
    with sol ce show "eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)" by (meson eq_at_sym eq_at_trans)
  next
    fix h assume "h \<in> set hs"
    from list_all2_ex1[OF hs this] obtain h' where h': "h' \<in> set hs'" "h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h'" "closed h" "closed h'"
      and t: "\<exists>e. e \<turnstile> h : propT" "\<exists>e. e \<turnstile> h' : propT"
      by blast
    from t obtain e1 e2 where "e1 \<turnstile> h : propT" "e2 \<turnstile> h' : propT" by blast
    with h' have "gterm (ap \<rho> \<sigma> h) propT" "gterm (ap \<rho> \<sigma> h') propT" using g' by fastforce+
    with h' hh[OF h'(1)] show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
      using holds_at_conv[OF g] conv_sym[OF c] by blast
  qed
  moreover have "gterm (ap \<rho> \<sigma> P) propT" "gterm (ap \<rho> \<sigma> P') propT" using g' P by fastforce+
  ultimately show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> P')" using holds_at_conv[OF g] c[OF P(1)] by blast
qed

text \<open>
  Validity is preserved by certified type instantiation, if the sorts of the instantiating types are
  added to the sort hypotheses (\<open>Thm.instantiate\<close>):
\<close>

lemma valid_tinst:
  assumes "valid Sh hs tps P" "cinst \<rho>0" and Sh: "Sh \<subseteq> Sh'" and S0: "sbound \<rho>0 Sh'"
  shows "valid Sh' (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) (inst \<rho>0 P)"
proof (rule validI)
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh' \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
    and hh: "\<And>h. h \<in> set (map (inst \<rho>0) hs) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  let ?\<rho> = "\<lambda>v S. tsubst \<rho> (\<rho>0 v S)"
  have a: "ap \<rho> \<sigma> (inst \<rho>0 t) = ap ?\<rho> \<sigma> t" for t by (simp add: ap_def inst_inst)
  have i0: "inh_inst \<rho>0" by (rule inh_inst_sbound[OF S0 sh])
  have "holds_at \<eta> \<xi> (ap ?\<rho> \<sigma> P)"
    by (rule validD[OF assms(1) _ g cinst_comp[OF \<rho> assms(2)] inh_inst_comp[OF \<rho>i assms(2) i0] \<sigma>])
      (use sol hh sh Sh in \<open>force simp: a\<close>)+
  then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (inst \<rho>0 P))" by (simp add: a)
qed

text \<open>
  Validity is preserved by the substitution of well-typed closed terms (which may contain schematic
  variables) for the schematic variables, provided that the variables of the theorem have certified
  types and variables with the same name have the same type
  (the substitution is keyed by name and type, an instance of the theorem by name and instantiated
  type).
\<close>

definition thm_vars :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "thm_vars hs tps P = vars P \<union> (\<Union>h\<in>set hs. vars h) \<union> (\<Union>(t, u)\<in>set tps. vars t \<union> vars u)"

lemma ap_vsubst:
  "(\<And>x T. (x, T) \<in> vars t \<Longrightarrow> \<sigma>1 x (tsubst \<rho> T) = ap \<rho> \<sigma> (\<sigma>0 x T)) \<Longrightarrow>
    ap \<rho> \<sigma>1 t = ap \<rho> \<sigma> (vsubst \<sigma>0 t)"
  by (induction t) auto

lemma valid_vsubst:
  assumes v: "valid Sh hs tps P" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> thm_vars hs tps P \<Longrightarrow> (x, U) \<in> thm_vars hs tps P \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> thm_vars hs tps P \<Longrightarrow> cert_typ alg ar T"
  shows "valid Sh (map (vsubst \<sigma>0) hs) (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) (vsubst \<sigma>0 P)"
proof (rule validI)
  let ?V = "thm_vars hs tps P"
  fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
    and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
    and hh: "\<And>h. h \<in> set (map (vsubst \<sigma>0) hs) \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
  define \<sigma>1 where "\<sigma>1 x T' = (if \<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T
    then ap \<rho> \<sigma> (\<sigma>0 x (SOME T. (x, T) \<in> ?V)) else \<sigma> x T')" for x T'
  have s1: "\<sigma>1 x (tsubst \<rho> T) = ap \<rho> \<sigma> (\<sigma>0 x T)" if "(x, T) \<in> ?V" for x T
  proof -
    have "(SOME T. (x, T) \<in> ?V) = T" using that uniq by (metis (mono_tags, lifting) someI)
    with that show ?thesis by (auto simp: \<sigma>1_def)
  qed
  have g1: "gsubst \<sigma>1"
  proof -
    have cv: "closed (\<sigma>1 x T')" for x T'
    proof (cases "\<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T")
      case True
      then obtain T where T: "(x, T) \<in> ?V" "T' = tsubst \<rho> T" by blast
      have "closed (\<sigma>0 x T)" using \<sigma>0 by (simp add: wt_subst_def closed_substD)
      then show ?thesis using s1[OF T(1)] T(2) \<sigma> by (simp add: closed_def gsubstD)
    next
      case False
      then have "\<sigma>1 x T' = \<sigma> x T'" unfolding \<sigma>1_def by (rule if_not_P)
      then show ?thesis using \<sigma> by (simp add: gsubstD closed_substD)
    qed
    moreover have "e \<turnstile> \<sigma>1 x T' : T'" if "cert_typ alg ar T'" for e x T'
    proof (cases "\<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T")
      case True
      then obtain T where T: "(x, T) \<in> ?V" "T' = tsubst \<rho> T" by blast
      have "(\<lambda>i. tsubst \<rho> (e i)) \<turnstile> ap \<rho> \<sigma> (\<sigma>0 x T) : tsubst \<rho> T"
        by (rule typing_ap_inst[OF wt_subst_typing[OF \<sigma>0 cert[OF T(1)]] cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]])
      with cv[of x T'] s1[OF T(1)] T(2) show ?thesis by (metis typing_closed)
    next
      case False
      then have "\<sigma>1 x T' = \<sigma> x T'" unfolding \<sigma>1_def by (rule if_not_P)
      then show ?thesis using wt_subst_typing[OF gsubstD(1)[OF \<sigma>] that] by simp
    qed
    ultimately show ?thesis by (auto simp: gsubst_def wt_subst_def closed_subst_def)
  qed
  have a: "ap \<rho> \<sigma>1 t = ap \<rho> \<sigma> (vsubst \<sigma>0 t)" if "vars t \<subseteq> ?V" for t
    by (rule ap_vsubst) (use s1 that in blast)
  have "holds_at \<eta> \<xi> (ap \<rho> \<sigma>1 P)"
  proof (rule validD[OF v sh g \<rho> \<rho>i g1])
    fix t u assume tu: "(t, u) \<in> set tps"
    then have "vars t \<subseteq> ?V" "vars u \<subseteq> ?V" by (auto simp: thm_vars_def)
    with tu sol show "eq_at \<eta> \<xi> (ap \<rho> \<sigma>1 t) (ap \<rho> \<sigma>1 u)" by (force simp: a)
  next
    fix h assume h: "h \<in> set hs"
    then have "vars h \<subseteq> ?V" by (auto simp: thm_vars_def)
    with h hh show "holds_at \<eta> \<xi> (ap \<rho> \<sigma>1 h)" by (simp add: a)
  qed
  moreover have "vars P \<subseteq> ?V" by (auto simp: thm_vars_def)
  ultimately show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> (vsubst \<sigma>0 P))" by (simp add: a)
qed


subsection \<open>Semantic validity\<close>

text \<open>
  A theorem is valid if its proposition holds under every valuation of its type variables and
  variables under which its flex-flex pairs hold as equations and its hypotheses hold. Variables
  are interpreted by name and type, type variables by name and sort.
\<close>

definition svalid :: "psort set \<Rightarrow> pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "svalid Sh hs tps P \<longleftrightarrow> (\<forall>S\<in>Sh. sinh S) \<longrightarrow> (\<forall>\<eta> \<xi>. good \<eta> \<xi> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. eq_at \<eta> \<xi> t u) \<longrightarrow> (\<forall>h\<in>set hs. holds_at \<eta> \<xi> h) \<longrightarrow> holds_at \<eta> \<xi> P)"

lemma svalidI:
  "(\<And>\<eta> \<xi>. (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> t u) \<Longrightarrow> (\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> h) \<Longrightarrow>
    holds_at \<eta> \<xi> P) \<Longrightarrow> svalid Sh hs tps P"
  unfolding svalid_def by blast

lemma svalidD:
  "svalid Sh hs tps P \<Longrightarrow> (\<And>S. S \<in> Sh \<Longrightarrow> sinh S) \<Longrightarrow> good \<eta> \<xi> \<Longrightarrow>
    (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> t u) \<Longrightarrow> (\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> h) \<Longrightarrow>
    holds_at \<eta> \<xi> P"
  unfolding svalid_def by blast

text \<open>The terms of a well-formed theorem are closed and well-typed:\<close>

definition wf_terms :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "wf_terms hs tps P \<longleftrightarrow> gterm P propT \<and> (\<forall>h\<in>set hs. gterm h propT) \<and>
    (\<forall>(t, u)\<in>set tps. \<exists>T. gterm t T \<and> gterm u T)"

lemma cinst_TVar: "cinst TVar"
  unfolding cinst_def wsinst_def cert_inst_def by (simp add: cert_typ_TVar del: has_sort.simps)

lemma eq_at_ap:
  "wt_subst \<sigma> \<Longrightarrow> e1 \<turnstile> t : T \<Longrightarrow> e2 \<turnstile> u : U \<Longrightarrow>
    eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u) \<longleftrightarrow> eq_at (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) t u"
  by (simp add: eq_at_def sem_ap)

lemma holds_at_ap:
  "wt_subst \<sigma> \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> t) \<longleftrightarrow> holds_at (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) t"
  by (simp add: holds_at_def sem_ap)

text \<open>For well-formed theorems, validity is semantic validity:\<close>

theorem valid_svalid:
  assumes wf: "wf_terms hs tps P"
  shows "valid Sh hs tps P \<longleftrightarrow> svalid Sh hs tps P"
proof
  assume v: "valid Sh hs tps P"
  show "svalid Sh hs tps P"
  proof (rule svalidI)
    fix \<eta> \<xi> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>"
      and tp: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> t u" and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> h"
    have gs: "gsubst (\<lambda>x T. Var x T)" using wt_subst_Var by (simp add: gsubst_def)
    have "holds_at \<eta> \<xi> (ap TVar (\<lambda>x T. Var x T) P)"
      by (rule validD[OF v sh g cinst_TVar inh_inst_TVar gs]) (simp_all add: ap_Var tp hh)
    then show "holds_at \<eta> \<xi> P" by (simp add: ap_Var)
  qed
next
  assume v: "svalid Sh hs tps P"
  show "valid Sh hs tps P"
  proof (rule validI)
    fix \<eta> \<xi> \<rho> \<sigma> assume sh: "\<And>S. S \<in> Sh \<Longrightarrow> sinh S" and g: "good \<eta> \<xi>" and \<rho>: "cinst \<rho>"
      and \<rho>i: "inh_inst \<rho>" and \<sigma>: "gsubst \<sigma>"
      and sol: "\<And>t u. (t, u) \<in> set tps \<Longrightarrow> eq_at \<eta> \<xi> (ap \<rho> \<sigma> t) (ap \<rho> \<sigma> u)"
      and hh: "\<And>h. h \<in> set hs \<Longrightarrow> holds_at \<eta> \<xi> (ap \<rho> \<sigma> h)"
    note ws = gsubstD(1)[OF \<sigma>]
    have tyP: "e \<turnstile> P : propT" for e using wf by (auto simp: wf_terms_def gterm_def)
    have "holds_at (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) P"
    proof (rule svalidD[OF v sh good_ap[OF g \<rho> \<rho>i ws]])
      fix t u assume tu: "(t, u) \<in> set tps"
      then obtain T where tt: "\<And>e. e \<turnstile> t : T" and tu': "\<And>e. e \<turnstile> u : T"
        using wf by (force simp: wf_terms_def gterm_def)
      from sol[OF tu] show "eq_at (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) t u" by (simp add: eq_at_ap[OF ws tt tu'])
    next
      fix h assume h: "h \<in> set hs"
      then have th: "e \<turnstile> h : propT" for e using wf by (auto simp: wf_terms_def gterm_def)
      from hh[OF h] show "holds_at (apv_t \<eta> \<rho>) (apv_v \<eta> \<xi> \<rho> \<sigma>) h" by (simp add: holds_at_ap[OF ws th])
    qed
    then show "holds_at \<eta> \<xi> (ap \<rho> \<sigma> P)" by (simp add: holds_at_ap[OF ws tyP])
  qed
qed

text \<open>Equational reasoning is sound in the models: equations that hold yield equal values.\<close>

theorem sem_eqv:
  assumes g: "good \<eta> \<xi>" and E: "\<And>l r bv. (l, r) \<in> E \<Longrightarrow> sem \<eta> \<xi> bv l = sem \<eta> \<xi> bv r"
  shows "eqv E e s t \<Longrightarrow> bvals \<eta> e bv \<Longrightarrow> sem \<eta> \<xi> bv s = sem \<eta> \<xi> bv t"
proof (induction arbitrary: bv rule: eqv.induct)
  case (eqv_ax s t e T)
  then show ?case using E by blast
next
  case (eqv_conv s t e T)
  then show ?case using sem_conv[OF g] by blast
next
  case (eqv_abs e T s t a b)
  from eqv_typing[OF eqv_abs.hyps(1)] obtain U where ts: "e\<langle>0:T\<rangle> \<turnstile> s : U" by blast
  have "sem \<eta> \<xi> bv (Abs a T s) = sem \<eta> \<xi> bv (Abs a T t)"
    by (rule sem_Abs_cong[OF g ts eqv_abs.prems]) (rule eqv_abs.IH[OF bvals_push[OF eqv_abs.prems]])
  then show ?case by simp
qed simp_all

lemma eq_at_eqv:
  assumes g: "good \<eta> \<xi>" and E: "\<And>l r. (l, r) \<in> E \<Longrightarrow> closed l \<and> closed r \<and> eq_at \<eta> \<xi> l r"
    and st: "eqv E e s t" "closed s" "closed t"
  shows "eq_at \<eta> \<xi> s t"
proof -
  have E': "sem \<eta> \<xi> bv l = sem \<eta> \<xi> bv r" if "(l, r) \<in> E" for l r bv
    using E[OF that] sem_closed[of l \<eta> \<xi> bv "\<lambda>_. utrue"] sem_closed[of r \<eta> \<xi> bv "\<lambda>_. utrue"]
    by (simp add: eq_at_def)
  have b: "bvals \<eta> e (\<lambda>i. SOME v. v \<in>\<^sub>u tsem \<eta> (e i))"
    unfolding bvals_def using tsem_ne[OF goodD(1)[OF g]] by (metis une_def someI_ex)
  from sem_eqv[OF g E' st(1) b] st(2,3) show ?thesis
    unfolding eq_at_def by (metis sem_closed)
qed

end

end
