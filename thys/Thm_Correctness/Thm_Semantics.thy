section \<open>A Semantics of Pure's Meta-Logic\<close>

theory Thm_Semantics
  imports Thm_Syntax
begin

text \<open>
  A model of the meta-logic is a predicate \<open>holds\<close> on closed propositions without schematic
  term variables (type variables are allowed). It respects \<open>\<alpha>\<beta>\<eta>\<close>-conversion of well-typed
  propositions, interprets \<open>\<Longrightarrow>\<close> as implication, \<open>\<And>x :: T\<close> as quantification over the closed
  terms of type \<open>T\<close> without schematic variables, and is closed under well-sorted certified type
  instantiation. These are the only properties of the meta-logic that the composition of
  theorems depends on. A theorem is valid if each of its instances holds whose flex-flex pairs
  are solved and whose hypotheses hold; an instance is given by a well-sorted certified type
  instantiation and a well-typed substitution of the schematic variables by closed terms without
  schematic variables.
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

text \<open>Closed terms without schematic variables, of a type, in every environment:\<close>

definition gterm :: "pterm \<Rightarrow> ptyp \<Rightarrow> bool" where
  "gterm t T \<longleftrightarrow> closed t \<and> vars t = {} \<and> (\<forall>e. e \<turnstile> t : T)"

text \<open>Substitutions of the schematic variables by such terms:\<close>

definition gsubst :: "vsubst \<Rightarrow> bool" where
  "gsubst \<sigma> \<longleftrightarrow> wt_subst \<sigma> \<and> (\<forall>x T. vars (\<sigma> x T) = {})"

text \<open>Well-sorted certified type instantiations:\<close>

definition cinst :: "tinst \<Rightarrow> bool" where
  "cinst \<rho> \<longleftrightarrow> wsinst alg \<rho> \<and> cert_inst \<rho>"

lemma gtermI: "closed t \<Longrightarrow> vars t = {} \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> gterm t T"
  unfolding gterm_def using typing_closed by blast

lemma gtermD: "gterm t T \<Longrightarrow> closed t" "gterm t T \<Longrightarrow> vars t = {}" "gterm t T \<Longrightarrow> e \<turnstile> t : T"
  unfolding gterm_def by blast+

lemma gsubstD: "gsubst \<sigma> \<Longrightarrow> wt_subst \<sigma>" "gsubst \<sigma> \<Longrightarrow> vars (\<sigma> x T) = {}"
  "gsubst \<sigma> \<Longrightarrow> closed_subst \<sigma>"
  unfolding gsubst_def wt_subst_def by blast+

lemma cinstD: "cinst \<rho> \<Longrightarrow> wsinst alg \<rho>" "cinst \<rho> \<Longrightarrow> cert_inst \<rho>"
  unfolding cinst_def by blast+

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

lemma vars_vsubst_gsubst [simp]: "gsubst \<sigma> \<Longrightarrow> vars (vsubst \<sigma> t) = {}"
  by (simp add: vars_vsubst gsubstD)

lemma vars_ap_gsubst [simp]: "gsubst \<sigma> \<Longrightarrow> vars (ap \<rho> \<sigma> t) = {}"
  by (simp add: ap_def)

lemma loose_bvar_ap [simp]: "gsubst \<sigma> \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar (ap \<rho> \<sigma> t) k \<longleftrightarrow> loose_bvar t k"
  by (simp add: ap_def gsubstD)

lemma typing_ap_inst:
  "e \<turnstile> t : T \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> (\<lambda>i. tsubst \<rho> (e i)) \<turnstile> ap \<rho> \<sigma> t : tsubst \<rho> T"
  by (rule typing_ap[OF typing_inst[OF _ cert_inst_inst_ok]])

lemma gterm_ap:
  "cert_inst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> closed t \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> gterm (ap \<rho> \<sigma> t) (tsubst \<rho> T)"
  by (rule gtermI[OF _ _ typing_ap_inst]) (auto simp: closed_def gsubstD)


subsection \<open>Simultaneous substitution of closed terms for loose bound variables\<close>

text \<open>\<open>substs k vs t\<close> replaces the loose bound variable \<open>k + i\<close> of \<open>t\<close> by \<open>vs ! i\<close>.\<close>

definition substs :: "integer \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> pterm" where
  "substs k vs t = foldl (\<lambda>t v. t[v/k]) t vs"

lemma substs_Nil [simp]: "substs k [] t = t"
  and substs_Cons: "substs k (v # vs) t = substs k vs (t[v/k])"
  by (simp_all add: substs_def)

lemma substs_append: "substs k (us @ vs) t = substs k vs (substs k us t)"
  by (simp add: substs_def)

lemma substs_App [simp]: "substs k vs (s $ t) = substs k vs s $ substs k vs t"
  by (induction vs arbitrary: s t) (simp_all add: substs_Cons)

lemma substs_atoms [simp]:
  "substs k vs (Const c T) = Const c T" "substs k vs (Free x T) = Free x T" "substs k vs (Var y T) = Var y T"
  by (induction vs) (simp_all add: substs_Cons)

lemma lift_closed: "closed v \<Longrightarrow> 0 \<le> k \<Longrightarrow> incr_bv n k v = v"
  by (rule incr_bv_no_loose) (rule closed_loose_bvar)

lemma subst_closed: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> t[v/k] = t"
  by (rule subst_no_loose) (rule closed_loose_bvar)

lemma substs_Abs [simp]:
  "\<forall>v\<in>set vs. closed v \<Longrightarrow> substs k vs (Abs a T t) = Abs a T (substs (k + 1) vs t)"
  by (induction vs arbitrary: t) (simp_all add: substs_Cons lift_closed)

lemma substs_implies [simp]: "substs k vs implies = implies"
  by (simp add: implies_def)

lemma substs_all_const [simp]: "substs k vs (all_const T) = all_const T"
  by (simp add: all_const_def)

lemma substs_closed: "closed t \<Longrightarrow> 0 \<le> k \<Longrightarrow> substs k vs t = t"
  by (induction vs) (simp_all add: substs_Cons subst_closed)

lemma substs_Suc_subst:
  assumes "closed u" "\<forall>v\<in>set vs. closed v"
  shows "(substs 1 vs t)[u/0] = substs 0 (u # vs) t"
  using assms(2)
proof (induction vs arbitrary: t)
  case (Cons v vs)
  have "t[v/1][u/0] = t[u/0][v/0]"
    using subst_subst[of 0 0 t v u] Cons.prems assms(1) by (simp add: lift_closed subst_closed)
  with Cons show ?case by (simp add: substs_Cons)
qed (simp add: substs_Cons)

lemma substs_incr_bv:
  assumes "\<forall>u\<in>set us. closed u"
  shows "substs 0 (us @ vs) (incr_bv (ilength us) 0 t) = substs 0 vs t"
  using assms
proof (induction us)
  case (Cons u us)
  have "incr_bv (ilength (u # us)) 0 t = lift (incr_bv (ilength us) 0 t) 0"
    by (simp add: incr_bv_Suc)
  with Cons show ?case by (simp add: substs_Cons)
qed simp

lemma loose_bvar_substs:
  assumes "\<forall>v\<in>set vs. closed v" "\<not> loose_bvar t (k + ilength vs)" "0 \<le> k"
  shows "\<not> loose_bvar (substs k vs t) k"
  using assms
proof (induction vs arbitrary: t)
  case (Cons v vs)
  have "\<not> loose_bvar (t[v/k]) (k + ilength vs)"
    by (rule loose_bvar_subst) (use Cons.prems in \<open>simp_all add: closed_loose_bvar algebra_simps\<close>)
  with Cons show ?case by (simp add: substs_Cons)
qed simp

lemma closed_substs:
  "\<forall>v\<in>set vs. closed v \<Longrightarrow> \<not> loose_bvar t (ilength vs) \<Longrightarrow> closed (substs 0 vs t)"
  using loose_bvar_substs[of vs t 0] by (simp add: closed_def)

lemma vars_substs: "vars (substs k vs t) \<subseteq> vars t \<union> (\<Union>v\<in>set vs. vars v)"
proof (induction vs arbitrary: t)
  case (Cons v vs)
  from Cons.IH[of "t[v/k]"] vars_subst[of t v k] show ?case by (auto simp: substs_Cons)
qed simp

text \<open>Values of the loose bound variables, innermost first, of the types given by \<open>e\<close>:\<close>

fun gvals :: "(integer \<Rightarrow> ptyp) \<Rightarrow> pterm list \<Rightarrow> bool" where
  "gvals e [] \<longleftrightarrow> True"
| "gvals e (v # vs) \<longleftrightarrow> gterm v (e 0) \<and> gvals (\<lambda>i. e (i + 1)) vs"

lemmas gvals_Cons = gvals.simps(2)

lemma gvals_Nil: "gvals e []"
  by simp

lemma gvals_cong: "(\<And>i. 0 \<le> i \<Longrightarrow> e' i = e i) \<Longrightarrow> gvals e' vs \<longleftrightarrow> gvals e vs"
proof (induction vs arbitrary: e e')
  case (Cons v vs)
  have "gvals (\<lambda>i. e' (i + 1)) vs \<longleftrightarrow> gvals (\<lambda>i. e (i + 1)) vs"
    by (rule Cons.IH) (use Cons.prems in simp)
  with Cons.prems[of 0] show ?case by simp
qed simp

lemma gvals_closed: "gvals e vs \<Longrightarrow> \<forall>v\<in>set vs. closed v"
  by (induction vs arbitrary: e) (auto dest: gtermD)

lemma gvals_vars: "gvals e vs \<Longrightarrow> \<forall>v\<in>set vs. vars v = {}"
  by (induction vs arbitrary: e) (auto dest: gtermD)

lemma typing_substs:
  assumes "e \<turnstile> t : T" "gvals e vs" "\<not> loose_bvar t (ilength vs)"
  shows "e' \<turnstile> substs 0 vs t : T"
  using assms
proof (induction vs arbitrary: e t)
  case Nil
  then show ?case by (simp add: typing_closed closed_def)
next
  case (Cons v vs)
  let ?e1 = "\<lambda>i. e (i + 1)"
  from Cons.prems(2) have v: "gterm v (e 0)" and vs: "gvals ?e1 vs" by (simp_all add: gvals_Cons)
  have "?e1\<langle>0:e 0\<rangle> \<turnstile> t : T"
    by (rule typing_env_nonneg[OF Cons.prems(1)]) (simp add: shift_def)
  from subst_lemma[OF this gtermD(3)[OF v] refl order_refl] have "?e1 \<turnstile> t[v/0] : T" .
  moreover have "\<not> loose_bvar (t[v/0]) (ilength vs)"
    by (rule loose_bvar_subst) (use Cons.prems(3) gtermD(1)[OF v] in \<open>simp_all add: closed_loose_bvar\<close>)
  ultimately show ?case using Cons.IH[OF _ vs] by (simp add: substs_Cons)
qed

lemma gterm_substs:
  "e \<turnstile> t : T \<Longrightarrow> gvals e vs \<Longrightarrow> \<not> loose_bvar t (ilength vs) \<Longrightarrow> vars t = {} \<Longrightarrow> gterm (substs 0 vs t) T"
  using gvals_closed gvals_vars vars_substs[of 0 vs t]
  by (auto simp: gterm_def closed_substs typing_substs)

text \<open>The instance of a term with loose bound variables:\<close>

abbreviation (input) ienv :: "tinst \<Rightarrow> (integer \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> ptyp" where
  "ienv \<rho> e \<equiv> \<lambda>i. tsubst \<rho> (e i)"

lemma gterm_substs_ap:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> t : T" "gvals (ienv \<rho> e) vs" "\<not> loose_bvar t (ilength vs)"
  shows "gterm (substs 0 vs (ap \<rho> \<sigma> t)) (tsubst \<rho> T)"
  by (rule gterm_substs[OF typing_ap_inst[OF assms(3,1) gsubstD(1)[OF assms(2)]] assms(4)])
    (use assms(2,5) in simp_all)

lemma gvals_shift_tail [simp]: "gvals (\<lambda>i. f ((e\<langle>0:T\<rangle>) (i + 1))) vs \<longleftrightarrow> gvals (\<lambda>i. f (e i)) vs"
  by (rule gvals_cong) (simp add: shift_def)

lemma gvals_shift: "gvals (ienv \<rho> (e\<langle>0:T\<rangle>)) (u # vs) \<longleftrightarrow> gterm u (tsubst \<rho> T) \<and> gvals (ienv \<rho> e) vs"
  by simp

text \<open>Values of parameters, outermost first:\<close>

abbreviation ptyped :: "tinst \<Rightarrow> binders \<Rightarrow> pterm list \<Rightarrow> bool" where
  "ptyped \<rho> ps us \<equiv> list_all2 (\<lambda>(a, T) u. gterm u (tsubst \<rho> T)) ps us"

lemma gvals_pushes:
  assumes "ptyped \<rho> ps us" "gvals (ienv \<rho> e) vs"
  shows "gvals (ienv \<rho> (pushes e (map snd ps))) (rev us @ vs)"
  using assms
proof (induction ps us arbitrary: e vs rule: list_all2_induct)
  case (Cons p ps u us)
  obtain a T where p: "p = (a, T)" by (cases p)
  have "gvals (ienv \<rho> (e\<langle>0:T\<rangle>)) (u # vs)"
    using Cons.hyps(1) Cons.prems p by (simp add: gvals_shift)
  from Cons.IH[OF this] show ?case by (simp add: p)
qed simp

lemma ap_implies [simp]: "ap \<rho> \<sigma> implies = implies"
  by (simp add: ap_def)

lemma ap_all_const [simp]: "ap \<rho> \<sigma> (all_const T) = all_const (tsubst \<rho> T)"
  by (simp add: ap_def)

lemma ap_list_implies: "ap \<rho> \<sigma> (list_implies As B) = list_implies (map (ap \<rho> \<sigma>) As) (ap \<rho> \<sigma> B)"
  by (induction As) auto

lemma substs_list_implies:
  "substs k vs (list_implies As B) = list_implies (map (substs k vs) As) (substs k vs B)"
  by (induction As) auto

lemma gterm_list_impliesD:
  "gterm (list_implies As B) propT \<Longrightarrow> (\<forall>A\<in>set As. gterm A propT) \<and> gterm B propT"
  using typing_list_impliesD[of _ As B]
  by (auto simp: gterm_def closed_def loose_bvar_list_implies vars_list_implies)

lemma ptyped_snd: "map snd ps = map snd qs \<Longrightarrow> ptyped \<rho> ps us \<longleftrightarrow> ptyped \<rho> qs us"
proof (induction ps arbitrary: qs us)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then obtain q qs' where "qs = q # qs'" "snd p = snd q" "map snd ps = map snd qs'" by (cases qs) auto
  with Cons.IH show ?case by (cases us) (auto split: prod.splits)
qed

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


subsection \<open>Models\<close>

locale pure_model = pure_sig alg ar ctab
  for alg :: algebra and ar :: "name \<Rightarrow> nat" and ctab :: "name \<Rightarrow> ptyp option" +
  fixes holds :: "pterm \<Rightarrow> bool"
  assumes holds_conv: "gterm A propT \<Longrightarrow> gterm B propT \<Longrightarrow> A \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> B \<Longrightarrow> holds A \<Longrightarrow> holds B"
    and holds_imp: "gterm A propT \<Longrightarrow> gterm B propT \<Longrightarrow> holds (implies $ A $ B) \<longleftrightarrow> (holds A \<longrightarrow> holds B)"
    and holds_all: "gterm (all_const T $ Abs a T P) propT \<Longrightarrow>
      holds (all_const T $ Abs a T P) \<longleftrightarrow> (\<forall>t. gterm t T \<longrightarrow> holds (P[t/0]))"
    and holds_inst: "cinst \<rho> \<Longrightarrow> gterm A propT \<Longrightarrow> holds A \<Longrightarrow> holds (inst \<rho> A)"

text \<open>The locale is consistent: every proposition holds in the trivial model.\<close>

lemma (in pure_sig) pure_model_trivial: "pure_model alg ar ctab (\<lambda>_. True)"
  by unfold_locales simp_all

context pure_model
begin

text \<open>Validity of a theorem with hypotheses \<open>hs\<close>, flex-flex pairs \<open>tps\<close> and proposition \<open>P\<close>:\<close>

definition valid :: "pterm list \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> bool" where
  "valid hs tps P \<longleftrightarrow> (\<forall>\<rho> \<sigma>. cinst \<rho> \<longrightarrow> gsubst \<sigma> \<longrightarrow>
    (\<forall>(t, u)\<in>set tps. ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) \<longrightarrow> (\<forall>h\<in>set hs. holds (ap \<rho> \<sigma> h)) \<longrightarrow>
    holds (ap \<rho> \<sigma> P))"

lemma validI:
  "(\<And>\<rho> \<sigma>. cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) \<Longrightarrow>
    (\<And>h. h \<in> set hs \<Longrightarrow> holds (ap \<rho> \<sigma> h)) \<Longrightarrow> holds (ap \<rho> \<sigma> P)) \<Longrightarrow> valid hs tps P"
  unfolding valid_def by blast

lemma validD:
  "valid hs tps P \<Longrightarrow> cinst \<rho> \<Longrightarrow> gsubst \<sigma> \<Longrightarrow> (\<And>t u. (t, u) \<in> set tps \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u) \<Longrightarrow>
    (\<And>h. h \<in> set hs \<Longrightarrow> holds (ap \<rho> \<sigma> h)) \<Longrightarrow> holds (ap \<rho> \<sigma> P)"
  unfolding valid_def by blast


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
  The semantics of the spine of a proposition \<open>A\<close>, for an instance \<open>(\<rho>, \<sigma>)\<close>, values \<open>vs\<close>
  of its loose bound variables (innermost first) and values \<open>us\<close> of its parameters (outermost
  first). The \<open>n\<close>-th assumption is ignored. The spine is that of \<open>A\<close>; the instance is applied to
  the hypotheses and the conclusion.
\<close>

function asem :: "tinst \<Rightarrow> vsubst \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm \<Rightarrow> bool" where
  "asem \<rho> \<sigma> n vs us A =
    (case dest_imp A of
      Some (H, B) \<Rightarrow> ((n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (ap \<rho> \<sigma> H))) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B)
    | None \<Rightarrow>
      (case dest_all A of
        Some (a, T, b) \<Rightarrow> (case us of [] \<Rightarrow> True | u # us' \<Rightarrow> asem \<rho> \<sigma> n (u # vs) us' b)
      | None \<Rightarrow> holds (substs 0 vs (ap \<rho> \<sigma> A))))"
  by auto
termination by (relation "measure (\<lambda>(_, _, _, _, _, A). size A)") (auto dest: dest_size)

declare asem.simps [simp del]

text \<open>A proposition holds iff its spine semantics holds for all values of its parameters.\<close>

lemma holds_asem:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "e \<turnstile> A : propT" "gvals (ienv \<rho> e) vs"
    "\<not> loose_bvar A (ilength vs)" "n \<le> 0"
  shows "holds (substs 0 vs (ap \<rho> \<sigma> A)) \<longleftrightarrow>
    (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
  using assms(3-6)
proof (induction A arbitrary: n vs e rule: measure_induct_rule[of size])
  case (less A)
  note g = gterm_substs_ap[OF assms(1,2)]
  have cv: "\<forall>v\<in>set vs. closed v" by (rule gvals_closed[OF less.prems(2)])
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    note ty = typing_dest_imp[OF less.prems(1) HB]
    have lHB: "\<not> loose_bvar H (ilength vs)" "\<not> loose_bvar B (ilength vs)"
      using less.prems(3) ty(1) by (simp_all add: implies_def)
    have IH: "holds (substs 0 vs (ap \<rho> \<sigma> B)) \<longleftrightarrow>
        (\<forall>us. ptyped \<rho> (strip_params B) us \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B)"
      using less.IH[OF _ ty(5) less.prems(2) lHB(2), of "n - 1"] ty(1) less.prems(4)
      by (simp add: implies_def)
    have gH: "gterm (substs 0 vs (ap \<rho> \<sigma> H)) propT" "gterm (substs 0 vs (ap \<rho> \<sigma> B)) propT"
      using g[OF ty(4) less.prems(2) lHB(1)] g[OF ty(5) less.prems(2) lHB(2)] by simp_all
    have "holds (substs 0 vs (ap \<rho> \<sigma> A)) \<longleftrightarrow>
        (holds (substs 0 vs (ap \<rho> \<sigma> H)) \<longrightarrow> holds (substs 0 vs (ap \<rho> \<sigma> B)))"
      using holds_imp[OF gH] ty(1) by simp
    also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
      using IH less.prems(4) HB by (subst asem.simps) (auto simp: strip_params_imp)
    finally show ?thesis .
  next
    case None
    show ?thesis
    proof (cases "dest_all A")
      case (Some aTb)
      then obtain a T b where aTb: "dest_all A = Some (a, T, b)" by (cases aTb) auto
      note ty = typing_dest_all[OF less.prems(1) aTb]
      have lb: "\<not> loose_bvar b (ilength vs + 1)" using less.prems(3) ty(1) by (simp add: all_const_def)
      have IH: "holds (substs 0 (u # vs) (ap \<rho> \<sigma> b)) \<longleftrightarrow>
          (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
        if "gterm u (tsubst \<rho> T)" for u
        using less.IH[OF _ ty(5), of "u # vs"] ty(1) less.prems(2,4) lb that
        by (simp add: all_const_def)
      have sA: "substs 0 vs (ap \<rho> \<sigma> A) =
          all_const (tsubst \<rho> T) $ Abs a (tsubst \<rho> T) (substs 1 vs (ap \<rho> \<sigma> b))"
        using ty(1) cv by simp
      have "holds (substs 0 vs (ap \<rho> \<sigma> A)) \<longleftrightarrow>
          (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds (substs 0 (u # vs) (ap \<rho> \<sigma> b)))"
      proof -
        have gA: "gterm (substs 0 vs (ap \<rho> \<sigma> A)) propT"
          using g[OF less.prems(1,2,3)] by simp
        have "holds (substs 0 vs (ap \<rho> \<sigma> A)) \<longleftrightarrow>
            (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds ((substs 1 vs (ap \<rho> \<sigma> b))[u/0]))"
          using holds_all[OF gA[unfolded sA]] sA by simp
        also have "\<dots> \<longleftrightarrow> (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds (substs 0 (u # vs) (ap \<rho> \<sigma> b)))"
          using substs_Suc_subst[OF gtermD(1) cv] by auto
        finally show ?thesis .
      qed
      also have "\<dots> \<longleftrightarrow> (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
          (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b))"
        using IH by blast
      also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A)"
      proof -
        have as: "asem \<rho> \<sigma> n vs (u # us) A = asem \<rho> \<sigma> n (u # vs) us b" for u us
          using None aTb by (subst asem.simps) simp
        have sp: "strip_params A = (a, T) # strip_params b"
          using None aTb by (rule strip_params_all)
        show ?thesis
        proof
          assume H: "\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
            (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
          show "\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A"
          proof (intro allI impI)
            fix us assume "ptyped \<rho> (strip_params A) us"
            then obtain u us' where "us = u # us'" "gterm u (tsubst \<rho> T)" "ptyped \<rho> (strip_params b) us'"
              by (auto simp: sp list_all2_Cons1)
            with H as show "asem \<rho> \<sigma> n vs us A" by simp
          qed
        next
          assume H: "\<forall>us. ptyped \<rho> (strip_params A) us \<longrightarrow> asem \<rho> \<sigma> n vs us A"
          show "\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
            (\<forall>us. ptyped \<rho> (strip_params b) us \<longrightarrow> asem \<rho> \<sigma> n (u # vs) us b)"
          proof (intro allI impI)
            fix u us assume "gterm u (tsubst \<rho> T)" "ptyped \<rho> (strip_params b) us"
            then have "ptyped \<rho> (strip_params A) (u # us)" by (simp add: sp)
            with H as show "asem \<rho> \<sigma> n (u # vs) us b" by metis
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

lemma asem_mono: "asem \<rho> \<sigma> n vs us A \<Longrightarrow> m \<le> 0 \<Longrightarrow> asem \<rho> \<sigma> m vs us A"
proof (induction \<rho> \<sigma> n vs us A arbitrary: m rule: asem.induct)
  case (1 \<rho> \<sigma> n vs us A)
  show ?case
  proof (cases "dest_imp A")
    case (Some HB)
    then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
    from "1.prems"(1) HB have a: "(n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (ap \<rho> \<sigma> H))) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B"
      by (subst (asm) asem.simps) simp
    have "asem \<rho> \<sigma> (m - 1) vs us B" if hH: "holds (substs 0 vs (ap \<rho> \<sigma> H))"
    proof -
      have ant: "n \<noteq> 1 \<longrightarrow> holds (substs 0 vs (ap \<rho> \<sigma> H))" using hH by simp
      with a have "asem \<rho> \<sigma> (n - 1) vs us B" by simp
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
        from "1.prems"(1) None aTb Cons have "asem \<rho> \<sigma> n (u # vs) us' b"
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
    "gvals (ienv \<rho> e) vs" "\<not> loose_bvar A (ilength vs)" "ilength (strip_params A) = j"
    "ptyped \<rho> (strip_params A) us" "holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> A'))"
  shows "asem \<rho> \<sigma> n vs us A"
  using assms(1,4-)
proof (induction j n A arbitrary: A' vs us e rule: remove_params.induct)
  case (1 j n A)
  note rp = "1.prems"(1)
  have j0: "0 \<le> j" using "1.prems"(5) ilength_nonneg by metis
  have cv: "\<forall>v\<in>set vs. closed v" by (rule gvals_closed[OF "1.prems"(3)])
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with rp have A': "A' = A" by (subst (asm) remove_params.simps) simp
    have sp: "strip_params A = []"
      using True "1.prems"(5) by (cases "strip_params A") (auto simp: ilength_eq integer_eq_iff)
    with "1.prems"(6) have us: "us = []" by simp
    from holds_asem[OF assms(2,3) "1.prems"(2,3,4), of n] True "1.prems"(7) A' us sp
    show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      then obtain H B where HB: "dest_imp A = Some (H, B)" by (cases HB) auto
      note ty = typing_dest_imp[OF "1.prems"(2) HB]
      have spB: "strip_params A = strip_params B" using HB by (rule strip_params_imp)
      have lHB: "\<not> loose_bvar H (ilength vs)" "\<not> loose_bvar B (ilength vs)"
        using "1.prems"(4) ty(1) by (simp_all add: implies_def)
      show ?thesis
      proof (cases "n = 1")
        case True
        with rp False HB have r: "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from "1.IH"(2)[OF False HB refl True r ty(5) "1.prems"(3) lHB(2)] "1.prems"(5-7) spB
        have "asem \<rho> \<sigma> (n - 1) vs us B" by simp
        with HB True show ?thesis by (subst asem.simps) simp
      next
        case n1: False
        with rp False HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          and A': "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: bindM_def split: option.splits res.splits)
        have lu: "ilength (rev us) = j"
          using "1.prems"(5,6) list_all2_lengthD[OF "1.prems"(6)] by (simp add: ilength_eq)
        have gv: "gvals (ienv \<rho> (pushes e (map snd (strip_params A)))) (rev us @ vs)"
          by (rule gvals_pushes[OF "1.prems"(6,3)])
        have cu: "\<forall>u\<in>set (rev us). closed u" using gvals_closed[OF gv] by simp
        have eqH: "substs 0 (rev us @ vs) (ap \<rho> \<sigma> (incr_boundvars j H)) = substs 0 vs (ap \<rho> \<sigma> H)"
          using substs_incr_bv[OF cu, of vs "ap \<rho> \<sigma> H"] lu gsubstD(1)[OF assms(3)]
          by (simp add: incr_boundvars_incr_bv ap_lift)
        have gH: "gterm (substs 0 vs (ap \<rho> \<sigma> H)) propT"
          using gterm_substs_ap[OF assms(2,3) ty(4) "1.prems"(3) lHB(1)] by simp
        have gB': "gterm (substs 0 (rev us @ vs) (ap \<rho> \<sigma> B')) propT"
        proof -
          have "pushes e (map snd (strip_params B)) \<turnstile> B' : propT"
            by (rule remove_params_typing[OF B' _ ty(5)]) (use "1.prems"(5) spB in simp)
          moreover have "\<not> loose_bvar B' (j + ilength vs)"
            by (rule remove_params_loose[OF B' _ lHB(2)]) (use "1.prems"(5) spB in simp_all)
          ultimately show ?thesis
            using gterm_substs_ap[OF assms(2,3) _ gv, of B' propT] lu spB by (simp add: add.commute)
        qed
        from "1.prems"(7) A' eqH have
          "holds (implies $ substs 0 vs (ap \<rho> \<sigma> H) $ substs 0 (rev us @ vs) (ap \<rho> \<sigma> B'))"
          by simp
        then have h: "holds (substs 0 vs (ap \<rho> \<sigma> H)) \<longrightarrow> holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> B'))"
          by (simp add: holds_imp[OF gH gB'])
        have "holds (substs 0 vs (ap \<rho> \<sigma> H)) \<longrightarrow> asem \<rho> \<sigma> (n - 1) vs us B"
          using "1.IH"(3)[OF False HB refl n1 B' ty(5) "1.prems"(3) lHB(2)] "1.prems"(5,6) spB h
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
        with "1.prems"(6) obtain u us' where us: "us = u # us'" and u: "gterm u (tsubst \<rho> T)"
          and us': "ptyped \<rho> (strip_params b) us'"
          by (auto simp: list_all2_Cons1)
        have "asem \<rho> \<sigma> n (u # vs) us' b"
        proof (rule "1.IH"(1)[OF False None aTb refl refl r ty(5)])
          show "gvals (ienv \<rho> (e\<langle>0:T\<rangle>)) (u # vs)" using u "1.prems"(3) by simp
          show "\<not> loose_bvar b (ilength (u # vs))" using "1.prems"(4) ty(1) by (simp add: all_const_def)
          show "ilength (strip_params b) = j - 1" using "1.prems"(5) sp by simp
          show "ptyped \<rho> (strip_params b) us'" by (rule us')
          show "holds (substs 0 (rev us' @ u # vs) (ap \<rho> \<sigma> A'))" using "1.prems"(7) us by simp
        qed
        with None aTb us show ?thesis by (subst asem.simps) simp
      next
        case None': None
        with rp False None "1.prems"(5) show ?thesis
          by (subst (asm) remove_params.simps) (auto split: if_splits simp: strip_params_other)
      qed
    qed
  qed
qed

lemma holds_list_forall:
  assumes "cert_inst \<rho>" "gsubst \<sigma>" "gvals (ienv \<rho> e) vs" "pushes e (map snd ps) \<turnstile> X : propT"
    "\<forall>(a, T)\<in>set ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    "\<not> loose_bvar X (ilength ps + ilength vs)"
  shows "holds (substs 0 vs (ap \<rho> \<sigma> (list_forall ps X))) \<longleftrightarrow>
    (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> X)))"
  using assms(3-)
proof (induction ps arbitrary: vs e)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain a T where p: "p = (a, T)" by (cases p)
  have cv: "\<forall>v\<in>set vs. closed v" by (rule gvals_closed[OF Cons.prems(1)])
  let ?Y = "ap \<rho> \<sigma> (list_forall ps X)"
  have tyA: "e \<turnstile> list_forall (p # ps) X : propT"
    using Cons.prems(2,3) by (simp add: typing_list_forall)
  have lA: "\<not> loose_bvar (list_forall (p # ps) X) (ilength vs)"
    using Cons.prems(4) by (simp add: loose_bvar_list_forall algebra_simps)
  have gA: "gterm (substs 0 vs (ap \<rho> \<sigma> (list_forall (p # ps) X))) propT"
    using gterm_substs_ap[OF assms(1,2) tyA Cons.prems(1) lA] by simp
  have sA: "substs 0 vs (ap \<rho> \<sigma> (list_forall (p # ps) X)) =
      all_const (tsubst \<rho> T) $ Abs a (tsubst \<rho> T) (substs 1 vs ?Y)"
    using cv by (simp add: p)
  have "holds (substs 0 vs (ap \<rho> \<sigma> (list_forall (p # ps) X))) \<longleftrightarrow>
      (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds ((substs 1 vs ?Y)[u/0]))"
    using holds_all[OF gA[unfolded sA]] sA by simp
  also have "\<dots> \<longleftrightarrow> (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds (substs 0 (u # vs) ?Y))"
    using substs_Suc_subst[OF gtermD(1) cv] by auto
  also have "\<dots> \<longleftrightarrow> (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (ap \<rho> \<sigma> X))))"
  proof (intro iff_allI imp_cong[OF refl])
    fix u assume u: "gterm u (tsubst \<rho> T)"
    show "holds (substs 0 (u # vs) ?Y) \<longleftrightarrow>
        (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (ap \<rho> \<sigma> X)))"
      by (rule Cons.IH) (use Cons.prems u p in \<open>simp_all add: algebra_simps\<close>)
  qed
  also have "\<dots> \<longleftrightarrow> (\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> X)))"
  proof
    assume H: "\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (ap \<rho> \<sigma> X)))"
    show "\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> X))"
    proof (intro allI impI)
      fix us assume "ptyped \<rho> (p # ps) us"
      then obtain u us' where "us = u # us'" "gterm u (tsubst \<rho> T)" "ptyped \<rho> ps us'"
        by (auto simp: p list_all2_Cons1)
      with H show "holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> X))" by simp
    qed
  next
    assume H: "\<forall>us. ptyped \<rho> (p # ps) us \<longrightarrow> holds (substs 0 (rev us @ vs) (ap \<rho> \<sigma> X))"
    show "\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow>
      (\<forall>us. ptyped \<rho> ps us \<longrightarrow> holds (substs 0 (rev us @ u # vs) (ap \<rho> \<sigma> X)))"
    proof (intro allI impI)
      fix u us assume "gterm u (tsubst \<rho> T)" "ptyped \<rho> ps us"
      then have "ptyped \<rho> (p # ps) (u # us)" by (simp add: p)
      with H show "holds (substs 0 (rev us @ u # vs) (ap \<rho> \<sigma> X))" by fastforce
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
  obtain A'' where r: "ok (remove_params (ilength ?ps) n A) A''" and A': "A' = list_forall ?vars A''"
    and sv: "map snd ?vars = map snd ?ps"
    by (rule flatten_params_ok[OF assms(1,2)])
  have lv: "ilength ?vars = ilength ?ps" using assms(2) by (simp add: ilength_eq)
  have cA: "\<not> loose_bvar A 0" using assms(6) by (simp add: closed_def)
  have tA'': "pushes e (map snd ?vars) \<turnstile> A'' : propT"
    using remove_params_typing[OF r refl assms(5)] sv by simp
  have lA'': "\<not> loose_bvar A'' (ilength ?vars + ilength ([] :: pterm list))"
    using remove_params_loose[OF r refl cA] lv by simp
  have cvars: "\<forall>(a, T)\<in>set ?vars. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
  proof (clarify)
    fix a T assume "(a, T) \<in> set ?vars"
    from set_zip_rightD[OF this] obtain a' where "(a', T) \<in> set ?ps" by auto
    then show "cert_typ alg ar (all_type T) \<and> cert_typ alg ar T" by (rule typing_strip_params[OF assms(5)])
  qed
  have h: "\<forall>us. ptyped \<rho> ?vars us \<longrightarrow> holds (substs 0 (rev us) (ap \<rho> \<sigma> A''))"
    using holds_list_forall[OF assms(3,4) gvals_Nil[of "ienv \<rho> e"] tA'' cvars lA''] assms(7) A' by simp
  have "\<forall>us. ptyped \<rho> ?ps us \<longrightarrow> asem \<rho> \<sigma> 0 [] us A"
  proof (intro allI impI)
    fix us assume t: "ptyped \<rho> ?ps us"
    have "asem \<rho> \<sigma> n [] us A"
    proof (rule remove_params_asem[OF r assms(3,4,5) gvals_Nil])
      show "holds (substs 0 (rev us @ []) (ap \<rho> \<sigma> A''))"
        using h t ptyped_snd[OF sv] by simp
    qed (use cA t in simp_all)
    then show "asem \<rho> \<sigma> 0 [] us A" by (rule asem_mono) simp
  qed
  with holds_asem[OF assms(3,4,5) gvals_Nil, of 0] cA show ?thesis by simp
qed


subsection \<open>Closures over parameters\<close>

lemma ienv_pushes: "ienv \<rho> (pushes e Ts) = pushes (ienv \<rho> e) (map (tsubst \<rho>) Ts)"
  by (induction Ts arbitrary: e) (simp_all add: tsubst_shift)

lemma beta_abs_list_substs:
  assumes "length bs = length us" "\<forall>u\<in>set us. closed u"
  shows "abs_list bs X \<degree>\<degree> us \<rightarrow>\<^sub>\<beta>\<^sup>* substs 0 (rev us) X"
  using assms
proof (induction us arbitrary: bs X rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc u us)
  then obtain bs' x T where bs: "bs = bs' @ [(x, T)]" and len: "length bs' = length us"
    by (cases bs rule: rev_cases) auto
  have cu: "closed u" "\<forall>v\<in>set (rev us). closed v" using snoc.prems(2) by auto
  have "abs_list bs X \<degree>\<degree> (us @ [u]) = (abs_list bs' (Abs x T X) \<degree>\<degree> us) $ u"
    by (simp add: bs)
  also have "\<dots> \<rightarrow>\<^sub>\<beta>\<^sup>* substs 0 (rev us) (Abs x T X) $ u"
  proof (rule rtrancl_beta_AppL)
    show "abs_list bs' (Abs x T X) \<degree>\<degree> us \<rightarrow>\<^sub>\<beta>\<^sup>* substs 0 (rev us) (Abs x T X)"
      using snoc.IH[OF len, of "Abs x T X"] snoc.prems(2) by simp
  qed
  also have "substs 0 (rev us) (Abs x T X) $ u = Abs x T (substs 1 (rev us) X) $ u"
    using cu by simp
  also have "\<dots> \<rightarrow>\<^sub>\<beta> (substs 1 (rev us) X)[u/0]" by simp
  also have "(substs 1 (rev us) X)[u/0] = substs 0 (rev (us @ [u])) X"
    using substs_Suc_subst[OF cu] by simp
  finally show ?case .
qed

lemma typings_gterms: "list_all2 gterm us Ts \<Longrightarrow> e \<tturnstile> us : Ts"
  by (induction rule: list_all2_induct) (auto dest: gtermD)

text \<open>If the closures of two terms are \<open>\<alpha>\<beta>\<eta>\<close>-equivalent, then so are the terms with the
  parameters replaced by closed terms.\<close>

lemma conv_abs_list_substs:
  assumes "e \<turnstile> abs_list bs X : map snd bs \<Rrightarrow> U" "e \<turnstile> abs_list bs Y : map snd bs \<Rrightarrow> U"
    "abs_list bs X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs Y" "list_all2 gterm us (map snd bs)"
  shows "substs 0 (rev us) X \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) Y"
proof -
  have ts: "e \<tturnstile> us : map snd bs" by (rule typings_gterms[OF assms(4)])
  have tX: "e \<turnstile> abs_list bs X \<degree>\<degree> us : U" and tY: "e \<turnstile> abs_list bs Y \<degree>\<degree> us : U"
    using list_app_typeI[OF assms(1) ts] list_app_typeI[OF assms(2) ts] .
  have len: "length bs = length us" using list_all2_lengthD[OF assms(4)] by simp
  have cu: "\<forall>u\<in>set us. closed u"
  proof
    fix u assume "u \<in> set us"
    then obtain i where i: "i < length us" "u = us ! i" by (auto simp: in_set_conv_nth)
    with assms(4) have "gterm u (map snd bs ! i)" unfolding list_all2_conv_all_nth by blast
    then show "closed u" by (rule gtermD)
  qed
  have "abs_list bs X \<degree>\<degree> us \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list bs Y \<degree>\<degree> us"
    by (rule conv_apps) (use tX tY assms(3) in \<open>auto simp: wt_def list.rel_refl\<close>)
  moreover have "abs_list bs X \<degree>\<degree> us \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) X"
    by (rule conv_beta_eta[OF _ beta_abs_list_substs[OF len cu]]) (use tX in \<open>auto simp: wt_def\<close>)
  moreover have "abs_list bs Y \<degree>\<degree> us \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) Y"
    by (rule conv_beta_eta[OF _ beta_abs_list_substs[OF len cu]]) (use tY in \<open>auto simp: wt_def\<close>)
  ultimately show ?thesis by (meson conv_sym conv_trans)
qed

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


lemma ptyped_gterms:
  "ptyped \<rho> ps us \<Longrightarrow> list_all2 gterm us (map snd (map (\<lambda>(x, T). (x, tsubst \<rho> T)) ps))"
  by (induction ps us rule: list_all2_induct) auto

text \<open>
  The first premise of a rule is proved by the assumption \<open>asm\<close> (elim-resolution) if the
  closures of \<open>asm\<close> and of the conclusion of the premise are equivalent.
\<close>

lemma eres_holds:
  assumes ap: "assum_problems k A = (params, asms, concl)" and asm: "asm \<in> set asms"
    and cv: "ap \<rho> \<sigma> (rlist_abs params asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (rlist_abs params concl)"
    and \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and tA: "e \<turnstile> A : propT" and cA: "closed A"
  shows "holds (ap \<rho> \<sigma> A)"
proof -
  note st = assum_problems_struct[OF ap tA]
  let ?ps = "rev params"
  let ?E = "pushes e (map snd ?ps)"
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) ?ps"
  have cps: "\<forall>(a, T)\<in>set ?ps. cert_typ alg ar (all_type T) \<and> cert_typ alg ar T"
    and tl: "?E \<turnstile> list_implies asms concl : propT"
    using tA st(1) by (simp_all add: typing_list_forall)
  have ll: "\<not> loose_bvar (list_implies asms concl) (ilength ?ps + ilength ([] :: pterm list))"
    using cA st(1) by (simp add: closed_def loose_bvar_list_forall)
  have "\<forall>us. ptyped \<rho> ?ps us \<longrightarrow> holds (substs 0 (rev us @ []) (ap \<rho> \<sigma> (list_implies asms concl)))"
  proof (intro allI impI)
    fix us assume pt: "ptyped \<rho> ?ps us"
    have gv: "gvals (ienv \<rho> ?E) (rev us @ [])" by (rule gvals_pushes[OF pt gvals_Nil])
    have lu: "ilength (rev us @ []) = ilength ?ps"
      using list_all2_lengthD[OF pt] by (simp add: ilength_eq)
    have gl: "gterm (substs 0 (rev us) (ap \<rho> \<sigma> (list_implies asms concl))) propT"
      using gterm_substs_ap[OF \<rho> \<sigma> tl gv] ll lu by simp
    have gX: "gterm (substs 0 (rev us) (ap \<rho> \<sigma> X)) propT" if "X \<in> insert concl (set asms)" for X
    proof -
      have t: "?E \<turnstile> X : propT" using that st(2,3) by auto
      have l: "\<not> loose_bvar X (ilength (rev us @ []))"
        using that ll lu by (auto simp: loose_bvar_list_implies)
      from gterm_substs_ap[OF \<rho> \<sigma> t gv l] show ?thesis by simp
    qed
    have conv: "substs 0 (rev us) (ap \<rho> \<sigma> asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (rev us) (ap \<rho> \<sigma> concl)"
    proof (rule conv_abs_list_substs)
      have cU: "\<forall>U\<in>snd ` set ?ps. cert_typ alg ar U" using cps by auto
      have aX: "ap \<rho> \<sigma> (rlist_abs params X) = abs_list ?bs (ap \<rho> \<sigma> X)" for X
        by (simp add: rlist_abs_abs_list ap_abs_list)
      show "ienv \<rho> e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> asm) : map snd ?bs \<Rrightarrow> tsubst \<rho> propT"
        using typing_abs_list_ap[OF \<rho> \<sigma> _ cU, of e asm propT] st(2) asm by (simp add: ap_abs_list)
      show "ienv \<rho> e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> concl) : map snd ?bs \<Rrightarrow> tsubst \<rho> propT"
        using typing_abs_list_ap[OF \<rho> \<sigma> _ cU, of e concl propT] st(3) by (simp add: ap_abs_list)
      show "abs_list ?bs (ap \<rho> \<sigma> asm) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> abs_list ?bs (ap \<rho> \<sigma> concl)" using cv by (simp only: aX)
      show "list_all2 gterm us (map snd ?bs)" by (rule ptyped_gterms[OF pt])
    qed
    have "holds (list_implies (map (substs 0 (rev us)) (map (ap \<rho> \<sigma>) asms)) (substs 0 (rev us) (ap \<rho> \<sigma> concl)))"
    proof (rule holds_list_impliesI)
      show "gterm (list_implies (map (substs 0 (rev us)) (map (ap \<rho> \<sigma>) asms)) (substs 0 (rev us) (ap \<rho> \<sigma> concl))) propT"
        using gl by (simp add: ap_list_implies substs_list_implies)
      assume "\<And>A. A \<in> set (map (substs 0 (rev us)) (map (ap \<rho> \<sigma>) asms)) \<Longrightarrow> holds A"
      then have "holds (substs 0 (rev us) (ap \<rho> \<sigma> asm))" using asm by auto
      from holds_conv[OF gX gX conv this] asm show "holds (substs 0 (rev us) (ap \<rho> \<sigma> concl))" by simp
    qed
    then show "holds (substs 0 (rev us @ []) (ap \<rho> \<sigma> (list_implies asms concl)))"
      by (simp add: ap_list_implies substs_list_implies)
  qed
  then have "holds (substs 0 [] (ap \<rho> \<sigma> (list_forall ?ps (list_implies asms concl))))"
    using holds_list_forall[OF \<rho> \<sigma> gvals_Nil tl cps ll] by blast
  then show ?thesis using st(1) by simp
qed

text \<open>
  If the instances of \<open>X\<close> and \<open>Y\<close> are equivalent for all values of the parameters of a prefix,
  then \<open>Y\<close> under the prefix holds if \<open>X\<close> does.
\<close>

lemma holds_lift_pre_transfer:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and ok: "\<forall>i\<in>set p. litem_ok i"
    and tX: "e \<turnstile> lift_pre p X : propT" and tY: "e \<turnstile> lift_pre p Y : propT"
    and ws: "gvals (ienv \<rho> e) ws"
    and lX: "\<not> loose_bvar (lift_pre p X) (ilength ws)" and lY: "\<not> loose_bvar (lift_pre p Y) (ilength ws)"
    and cv: "\<And>vs. list_all2 gterm vs (map (tsubst \<rho>) (rev (ptys p))) \<Longrightarrow>
      substs 0 (vs @ ws) (ap \<rho> \<sigma> X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (vs @ ws) (ap \<rho> \<sigma> Y)"
    and h: "holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre p X)))"
  shows "holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre p Y)))"
  using ok tX tY ws lX lY cv h
proof (induction p arbitrary: e ws)
  case Nil
  have g: "gterm (substs 0 ws (ap \<rho> \<sigma> Z)) propT"
    if "e \<turnstile> Z : propT" "\<not> loose_bvar Z (ilength ws)" for Z
    using gterm_substs_ap[OF \<rho> \<sigma> that(1) Nil.prems(4) that(2)] by simp
  have "substs 0 ws (ap \<rho> \<sigma> X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 ws (ap \<rho> \<sigma> Y)"
    using Nil.prems(7)[of "[]"] by simp
  moreover have "gterm (substs 0 ws (ap \<rho> \<sigma> X)) propT" "gterm (substs 0 ws (ap \<rho> \<sigma> Y)) propT"
    using g[of X] g[of Y] Nil.prems(2,3,5,6) by simp_all
  ultimately show ?case using holds_conv Nil.prems(8) by simp
next
  case (Cons i p)
  have cw: "\<forall>v\<in>set ws. closed v" by (rule gvals_closed[OF Cons.prems(4)])
  have oki: "litem_ok i" and okp: "\<forall>i\<in>set p. litem_ok i" using Cons.prems(1) by simp_all
  show ?case
  proof (cases i)
    case (LImp c H)
    note iX = typing_lift_pre_imp[OF oki Cons.prems(2) LImp]
    note iY = typing_lift_pre_imp[OF oki Cons.prems(3) LImp]
    have lH: "\<not> loose_bvar H (ilength ws)" using Cons.prems(5) iX(1) by (simp add: implies_def)
    have lX': "\<not> loose_bvar (lift_pre p X) (ilength ws)" using Cons.prems(5) iX(1) by (simp add: implies_def)
    have lY': "\<not> loose_bvar (lift_pre p Y) (ilength ws)" using Cons.prems(6) iY(1) by (simp add: implies_def)
    have g: "gterm (substs 0 ws (ap \<rho> \<sigma> Z)) propT"
      if "e \<turnstile> Z : propT" "\<not> loose_bvar Z (ilength ws)" for Z
      using gterm_substs_ap[OF \<rho> \<sigma> that(1) Cons.prems(4) that(2)] by simp
    note gH = g[OF iX(2) lH] and gX = g[OF iX(3) lX'] and gY = g[OF iY(3) lY']
    have hX: "holds (substs 0 ws (ap \<rho> \<sigma> H)) \<longrightarrow> holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre p X)))"
      using Cons.prems(8) iX(1) holds_imp[OF gH gX] by simp
    have "holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre p X))) \<Longrightarrow> holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre p Y)))"
      by (rule Cons.IH[OF okp iX(3) iY(3) Cons.prems(4) lX' lY']) (use Cons.prems(7) LImp in simp_all)
    with hX show ?thesis using iY(1) holds_imp[OF gH gY] by simp
  next
    case (LAll c a T)
    note iX = typing_lift_pre_all[OF oki Cons.prems(2) LAll]
    note iY = typing_lift_pre_all[OF oki Cons.prems(3) LAll]
    have g: "gterm (substs 0 ws (ap \<rho> \<sigma> Z)) propT"
      if "e \<turnstile> Z : propT" "\<not> loose_bvar Z (ilength ws)" for Z
      using gterm_substs_ap[OF \<rho> \<sigma> that(1) Cons.prems(4) that(2)] by simp
    have hall: "holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre (i # p) Z))) \<longleftrightarrow>
        (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds (substs 0 (u # ws) (ap \<rho> \<sigma> (lift_pre p Z))))"
      if "e \<turnstile> lift_pre (i # p) Z : propT" "\<not> loose_bvar (lift_pre (i # p) Z) (ilength ws)"
        "lift_pre (i # p) Z = all_const T $ Abs a T (lift_pre p Z)" for Z
    proof -
      have sA: "substs 0 ws (ap \<rho> \<sigma> (lift_pre (i # p) Z)) =
          all_const (tsubst \<rho> T) $ Abs a (tsubst \<rho> T) (substs 1 ws (ap \<rho> \<sigma> (lift_pre p Z)))"
        using cw that(3) by simp
      have "holds (substs 0 ws (ap \<rho> \<sigma> (lift_pre (i # p) Z))) \<longleftrightarrow>
          (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds ((substs 1 ws (ap \<rho> \<sigma> (lift_pre p Z)))[u/0]))"
        using holds_all[OF g[OF that(1,2), unfolded sA]] sA by simp
      also have "\<dots> \<longleftrightarrow> (\<forall>u. gterm u (tsubst \<rho> T) \<longrightarrow> holds (substs 0 (u # ws) (ap \<rho> \<sigma> (lift_pre p Z))))"
        using substs_Suc_subst[OF gtermD(1) cw] by auto
      finally show ?thesis .
    qed
    have "holds (substs 0 (u # ws) (ap \<rho> \<sigma> (lift_pre p Y)))" if u: "gterm u (tsubst \<rho> T)" for u
    proof (rule Cons.IH[OF okp iX(2) iY(2)])
      show "gvals (ienv \<rho> (e\<langle>0:T\<rangle>)) (u # ws)" using u Cons.prems(4) by simp
      show "\<not> loose_bvar (lift_pre p X) (ilength (u # ws))"
        using Cons.prems(5) iX(1) by (simp add: all_const_def)
      show "\<not> loose_bvar (lift_pre p Y) (ilength (u # ws))"
        using Cons.prems(6) iY(1) by (simp add: all_const_def)
      show "substs 0 (vs @ u # ws) (ap \<rho> \<sigma> X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 (vs @ u # ws) (ap \<rho> \<sigma> Y)"
        if "list_all2 gterm vs (map (tsubst \<rho>) (rev (ptys p)))" for vs
        using Cons.prems(7)[of "vs @ [u]"] that u LAll by (simp add: list_all2_appendI)
      show "holds (substs 0 (u # ws) (ap \<rho> \<sigma> (lift_pre p X)))"
        using Cons.prems(8) hall[OF Cons.prems(2,5) iX(1)] u by blast
    qed
    then show ?thesis using hall[OF Cons.prems(3,6) iY(1)] by blast
  qed
qed

lemma holds_lift_pre_conv:
  assumes \<rho>: "cert_inst \<rho>" and \<sigma>: "gsubst \<sigma>" and ok: "\<forall>i\<in>set p. litem_ok i"
    and tX: "e \<turnstile> lift_pre p X : propT" and tY: "e \<turnstile> lift_pre p Y : propT"
    and cX: "closed (lift_pre p X)" and cY: "closed (lift_pre p Y)"
    and cv: "ap \<rho> \<sigma> (abs_pre p X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> (abs_pre p Y)"
    and h: "holds (ap \<rho> \<sigma> (lift_pre p X))"
  shows "holds (ap \<rho> \<sigma> (lift_pre p Y))"
proof -
  let ?bs = "map (\<lambda>(x, T). (x, tsubst \<rho> T)) (lparams p)"
  have ms: "map snd ?bs = map (tsubst \<rho>) (ptys p)"
    by (induction p rule: lparams.induct) auto
  have "snd ` set (lparams p) = set (ptys p)" by (induction p rule: lparams.induct) auto
  then have cU: "\<forall>U\<in>snd ` set (lparams p). cert_typ alg ar U"
    using typing_lift_pre[OF ok tX] by simp
  have tZ: "ienv \<rho> e \<turnstile> abs_list ?bs (ap \<rho> \<sigma> Z) : map snd ?bs \<Rrightarrow> tsubst \<rho> propT"
    if "e \<turnstile> lift_pre p Z : propT" for Z
  proof -
    have "pushes e (map snd (lparams p)) \<turnstile> Z : propT" using typing_lift_pre[OF ok that] by simp
    from typing_abs_list_ap[OF \<rho> \<sigma> this cU] show ?thesis by (simp add: ap_abs_list)
  qed
  have aZ: "ap \<rho> \<sigma> (abs_pre p Z) = abs_list ?bs (ap \<rho> \<sigma> Z)" for Z
    by (simp add: abs_pre_abs_list ap_abs_list)
  show ?thesis
  proof (rule holds_lift_pre_transfer[OF \<rho> \<sigma> ok tX tY gvals_Nil, simplified])
    show "\<not> loose_bvar (lift_pre p X) 0" "\<not> loose_bvar (lift_pre p Y) 0"
      using cX cY by (simp_all add: closed_def)
    show "holds (ap \<rho> \<sigma> (lift_pre p X))" by (rule h)
    fix vs assume vs: "list_all2 gterm vs (map (tsubst \<rho>) (rev (ptys p)))"
    have "list_all2 gterm (rev vs) (map snd ?bs)"
      unfolding ms using vs by (simp add: list_all2_rev1 rev_map)
    from conv_abs_list_substs[OF tZ[OF tX] tZ[OF tY] cv[unfolded aZ] this]
    show "substs 0 vs (ap \<rho> \<sigma> X) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> substs 0 vs (ap \<rho> \<sigma> Y)" by simp
  qed
qed


subsection \<open>Validity under conversion and instantiation\<close>

text \<open>Validity is preserved by \<open>\<alpha>\<beta>\<eta>\<close>-conversion of the proposition, of the hypotheses and of the sides of the flex-flex pairs:\<close>

lemma conv_ap: "s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t \<Longrightarrow> cert_inst \<rho> \<Longrightarrow> wt_subst \<sigma> \<Longrightarrow> ap \<rho> \<sigma> s \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> t"
  unfolding ap_def by (rule conv_vsubst[OF conv_inst[OF _ cert_inst_inst_ok]])

lemma valid_conv:
  assumes v: "valid hs tps P"
    and P: "P \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> P'" "closed P" "e \<turnstile> P : propT" "closed P'" "e' \<turnstile> P' : propT"
    and hs: "list_all2 (\<lambda>h h'. h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h' \<and> closed h \<and> (\<exists>e. e \<turnstile> h : propT) \<and> closed h' \<and> (\<exists>e. e \<turnstile> h' : propT)) hs hs'"
    and tps: "list_all2 (\<lambda>(t, u) (t', u'). t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t' \<and> u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u') tps tps'"
  shows "valid hs' tps' P'"
proof (rule validI)
  fix \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set tps' \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set hs' \<Longrightarrow> holds (ap \<rho> \<sigma> h)"
  note c = conv_ap[OF _ cinstD(2)[OF \<rho>] gsubstD(1)[OF \<sigma>]]
  note g = gterm_ap[OF cinstD(2)[OF \<rho>] \<sigma>]
  have "holds (ap \<rho> \<sigma> P)"
  proof (rule validD[OF v \<rho> \<sigma>])
    fix t u assume "(t, u) \<in> set tps"
    with tps obtain t' u' where "(t', u') \<in> set tps'" "t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t'" "u \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
      by (auto simp: list_all2_conv_all_nth in_set_conv_nth split: prod.splits) (metis prod.collapse)
    with sol c show "ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u" by (meson conv_sym conv_trans)
  next
    fix h assume "h \<in> set hs"
    from list_all2_ex1[OF hs this] obtain h' where h': "h' \<in> set hs'" "h \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> h'" "closed h" "closed h'"
      and t: "\<exists>e. e \<turnstile> h : propT" "\<exists>e. e \<turnstile> h' : propT"
      by blast
    from t obtain e1 e2 where "e1 \<turnstile> h : propT" "e2 \<turnstile> h' : propT" by blast
    with h' have "gterm (ap \<rho> \<sigma> h) propT" "gterm (ap \<rho> \<sigma> h') propT" using g by fastforce+
    with h' hh[OF h'(1)] show "holds (ap \<rho> \<sigma> h)"
      using holds_conv conv_sym[OF c] by blast
  qed
  moreover have "gterm (ap \<rho> \<sigma> P) propT" "gterm (ap \<rho> \<sigma> P') propT" using g P by fastforce+
  ultimately show "holds (ap \<rho> \<sigma> P')" using holds_conv c[OF P(1)] by blast
qed

text \<open>Validity is preserved by certified type instantiation:\<close>

lemma valid_tinst:
  assumes "valid hs tps P" "cinst \<rho>0"
  shows "valid (map (inst \<rho>0) hs) (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) (inst \<rho>0 P)"
proof (rule validI)
  fix \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (inst \<rho>0 t, inst \<rho>0 u)) tps) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set (map (inst \<rho>0) hs) \<Longrightarrow> holds (ap \<rho> \<sigma> h)"
  let ?\<rho> = "\<lambda>v S. tsubst \<rho> (\<rho>0 v S)"
  have a: "ap \<rho> \<sigma> (inst \<rho>0 t) = ap ?\<rho> \<sigma> t" for t by (simp add: ap_def inst_inst)
  have "holds (ap ?\<rho> \<sigma> P)"
    by (rule validD[OF assms(1) cinst_comp[OF \<rho> assms(2)] \<sigma>]) (use sol hh in \<open>force simp: a\<close>)+
  then show "holds (ap \<rho> \<sigma> (inst \<rho>0 P))" by (simp add: a)
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
  assumes v: "valid hs tps P" and \<sigma>0: "wt_subst \<sigma>0"
    and uniq: "\<And>x T U. (x, T) \<in> thm_vars hs tps P \<Longrightarrow> (x, U) \<in> thm_vars hs tps P \<Longrightarrow> T = U"
    and cert: "\<And>x T. (x, T) \<in> thm_vars hs tps P \<Longrightarrow> cert_typ alg ar T"
  shows "valid (map (vsubst \<sigma>0) hs) (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) (vsubst \<sigma>0 P)"
proof (rule validI)
  let ?V = "thm_vars hs tps P"
  fix \<rho> \<sigma> assume \<rho>: "cinst \<rho>" and \<sigma>: "gsubst \<sigma>"
    and sol: "\<And>t u. (t, u) \<in> set (map (\<lambda>(t, u). (vsubst \<sigma>0 t, vsubst \<sigma>0 u)) tps) \<Longrightarrow> ap \<rho> \<sigma> t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma> u"
    and hh: "\<And>h. h \<in> set (map (vsubst \<sigma>0) hs) \<Longrightarrow> holds (ap \<rho> \<sigma> h)"
  define \<sigma>1 where "\<sigma>1 x T' = (if \<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T
    then ap \<rho> \<sigma> (\<sigma>0 x (SOME T. (x, T) \<in> ?V)) else \<sigma> x T')" for x T'
  have s1: "\<sigma>1 x (tsubst \<rho> T) = ap \<rho> \<sigma> (\<sigma>0 x T)" if "(x, T) \<in> ?V" for x T
  proof -
    have "(SOME T. (x, T) \<in> ?V) = T" using that uniq by (metis (mono_tags, lifting) someI)
    with that show ?thesis by (auto simp: \<sigma>1_def)
  qed
  have g1: "gsubst \<sigma>1"
  proof -
    have cv: "closed (\<sigma>1 x T') \<and> vars (\<sigma>1 x T') = {}" for x T'
    proof (cases "\<exists>T. (x, T) \<in> ?V \<and> T' = tsubst \<rho> T")
      case True
      then obtain T where T: "(x, T) \<in> ?V" "T' = tsubst \<rho> T" by blast
      have "closed (\<sigma>0 x T)" using \<sigma>0 by (simp add: wt_subst_def closed_substD)
      then show ?thesis using s1[OF T(1)] T(2) \<sigma> by (simp add: closed_def)
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
  have "holds (ap \<rho> \<sigma>1 P)"
  proof (rule validD[OF v \<rho> g1])
    fix t u assume tu: "(t, u) \<in> set tps"
    then have "vars t \<subseteq> ?V" "vars u \<subseteq> ?V" by (auto simp: thm_vars_def)
    with tu sol show "ap \<rho> \<sigma>1 t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ap \<rho> \<sigma>1 u" by (force simp: a)
  next
    fix h assume h: "h \<in> set hs"
    then have "vars h \<subseteq> ?V" by (auto simp: thm_vars_def)
    with h hh show "holds (ap \<rho> \<sigma>1 h)" by (simp add: a)
  qed
  moreover have "vars P \<subseteq> ?V" by (auto simp: thm_vars_def)
  ultimately show "holds (ap \<rho> \<sigma> (vsubst \<sigma>0 P))" by (simp add: a)
qed

end

end
