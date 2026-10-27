section \<open>Completeness of Matching\<close>

theory Match_Complete
  imports Match_Termination Poly_Unif
begin

declare sup_apply[simp del]

subsection \<open>Equivalence of de Bruijn terms\<close>

lemma subst_lift_Suc: "(lift t (Suc k))[BVar k/k] = t"
  by (induction t arbitrary: k) auto

lemma Abs_equiv_Abs: "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t \<Longrightarrow> s \<equiv>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  assume "dB.Abs s \<equiv>\<^sub>\<beta>\<^sub>\<eta> dB.Abs t"
  then have "s \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (dB.Abs t) 0 \<degree> BVar 0" by (simp add: fact6)
  moreover have "lift (dB.Abs t) 0 \<degree> BVar 0 \<rightarrow>\<^sub>\<beta> t"
    using beta.beta[of "lift t (Suc 0)" "BVar 0"] by (simp add: subst_lift_Suc)
  then have "lift (dB.Abs t) 0 \<degree> BVar 0 \<equiv>\<^sub>\<beta>\<^sub>\<eta> t" by (intro beta_into_equiv r_into_rtranclp)
  ultimately show ?thesis by (rule equiv_trans)
qed

text \<open>A term without \<open>\<beta>\<close>-redexes only depends on the bound variables it contains:\<close>

lemma rfree_dep_on: "rfree t \<Longrightarrow> proper t \<Longrightarrow> dep_on Z (tr t) \<Longrightarrow> loose_BVars (tr t) \<subseteq> Z"
proof (induction t arbitrary: Z rule: measure_induct_rule[of size])
  case (less t)
  show ?case
  proof (cases "Pure_Term.is_Abs t")
    case True
    then obtain a T u where t: "t = pterm.Abs a T u" by (cases t) auto
    from less.prems(3) have "dep_on (insert 0 (Suc ` Z)) (tr u)" by (simp add: t Abs_dep_on)
    with less.IH[of u] less.prems(1,2) have "loose_BVars (tr u) \<subseteq> insert 0 (Suc ` Z)" by (simp add: t)
    then show ?thesis by (auto simp: t)
  next
    case False
    obtain h ts where s: "strip_comb t = (h, ts)" by force
    have tc: "t = list_comb h ts" by (rule strip_comb_list_comb[OF s])
    have h: "\<not> (\<exists>f u. h = f $ u)" by (rule strip_comb_head[OF s])
    have rf: "\<forall>u\<in>set ts. rfree u" "ts \<noteq> [] \<longrightarrow> \<not> Pure_Term.is_Abs h"
      using less.prems(1) by (simp_all add: tc rfree_list_comb)
    have pr: "proper h" "\<forall>u\<in>set ts. proper u" using less.prems(2) by (simp_all add: tc proper_list_comb)
    have "\<not> Pure_Term.is_Abs h" using False rf(2) by (cases ts) (auto simp: tc)
    then have at: "is_atom (tr h)" using h pr(1) by (cases h) auto
    have dep: "dep_on Z (tr h \<degree>\<degree> map tr ts)" using less.prems(3) by (simp add: tc tr_list_comb)
    note ad = atom_apps_dep_on[OF at dep]
    have "loose_BVars (tr u) \<subseteq> Z" if "u \<in> set ts" for u
      using less.IH[OF strip_comb_arg(2)[OF s that]] rf(1) pr(2) ad(2) that by simp
    with ad(1) show ?thesis by (auto simp: tc tr_list_comb)
  qed
qed


subsection \<open>Successful auxiliary computations\<close>

lemma integer_of_nat_nat: "0 \<le> i \<Longrightarrow> integer_of_nat (nat_of_integer i) = i"
  by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq)

lemma mapM_ok_ex: "(\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. ok (f x) y) \<Longrightarrow> \<exists>ys. ok (mapM f xs) ys"
  by (induction xs) auto

lemma subst_type_ok:
  assumes "\<forall>(v, S)\<in>tvars T. \<forall>S' U. vt_lookup tye v = Some (S', U) \<longrightarrow> S' = S"
  shows "\<exists>T'. ok (subst_type tye T) T'"
proof -
  have "\<exists>T'. ok (subst_type_aux tye T) T'" using assms
  proof (induction tye T rule: subst_type_aux.induct)
    case (1 tye a Ts)
    then have "\<exists>Ts'. ok (mapM (subst_type_aux tye) Ts) Ts'" by (intro mapM_ok_ex) auto
    then show ?case by auto
  qed (auto simp: type_lookup_def split: option.splits)
  then show ?thesis by (auto simp: subst_type_def)
qed

lemma mapbnd_ok:
  assumes "proper t" "0 \<le> d"
    "\<forall>k\<in>loose_BVars (tr t). nat_of_integer d \<le> k \<longrightarrow> (\<exists>j. ok (f (integer_of_nat (k - nat_of_integer d))) j)"
  shows "\<exists>t'. ok (mapbnd f d t) t'"
  using assms
proof (induction f d t rule: mapbnd.induct)
  case (1 f d i)
  show ?case
  proof (cases "i < d")
    case False
    with "1.prems" have "nat_of_integer d \<le> nat_of_integer i"
      by (simp add: nat_of_integer_less_iff flip: not_less)
    with "1.prems" obtain j where "ok (f (integer_of_nat (nat_of_integer i - nat_of_integer d))) j" by auto
    with False "1.prems"(2) show ?thesis by (auto simp: integer_of_nat_diff)
  qed simp
next
  case (2 f d s T t)
  have d1: "0 \<le> d + 1" using add_nonneg_nonneg[OF "2.prems"(2) zero_le_one] .
  have n: "nat_of_integer (d + 1) = Suc (nat_of_integer d)"
    using "2.prems"(2) nat_of_integer_add[of d 1] by simp
  have "\<exists>j. ok (f (integer_of_nat (k - nat_of_integer (d + 1)))) j"
    if "k \<in> loose_BVars (tr t)" "nat_of_integer (d + 1) \<le> k" for k
  proof -
    from that(2) n obtain k' where k: "k = Suc k'" "nat_of_integer d \<le> k'" by (cases k) auto
    with that(1) "2.prems"(3) show ?thesis by (auto simp: n)
  qed
  then have "\<forall>k\<in>loose_BVars (tr t). nat_of_integer (d + 1) \<le> k \<longrightarrow>
      (\<exists>j. ok (f (integer_of_nat (k - nat_of_integer (d + 1)))) j)"
    by blast
  from "2.IH"[OF _ d1 this] "2.prems"(1) show ?case by auto
next
  case (3 f d u1 u2)
  from "3.IH"(1) "3.prems" obtain v1 where v1: "ok (mapbnd f d u1) v1" by auto
  from "3.IH"(2)[OF v1[folded return_def]] "3.prems" obtain v2 where "ok (mapbnd f d u2) v2" by auto
  with v1 show ?case by auto
qed auto

lemma mkabs_ok: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders \<Longrightarrow> \<exists>u. ok (mkabs binders is t) u"
  by (induction "is") (auto simp: ok_nth split: prod.splits)

lemma match_bind_ok:
  assumes "proper t" "loose_BVars (tr t) \<subseteq> set (nats is)"
    "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" "vt_lookup itms ixn = None"
  shows "\<exists>itms'. ok (match_bind itms binders ixn T is t) itms'"
proof -
  have lb: "set (loose_bnos t) = integer_of_nat ` loose_BVars (tr t)" by (rule set_loose_bnos[OF assms(1)])
  have up: "\<exists>itms'. ok (update_new (ixn, (T, u)) itms) itms'" for u
    using assms(4) by (simp add: update_new_def vt_defined_lookup)
  have inis: "integer_of_nat k \<in> set is" if "k \<in> loose_BVars (tr t)" for k
  proof -
    from that assms(2) obtain i where "i \<in> set is" "k = nat_of_integer i" by auto
    with assms(3) show ?thesis by (simp add: integer_of_nat_nat)
  qed
  show ?thesis
  proof (cases "is = []")
    case True
    with assms(2) have "loose_bnos t = []" using lb by auto
    with True up show ?thesis by (simp add: match_bind_def)
  next
    case False
    have sub: "subset (loose_bnos t) is" using inis lb by (auto simp: subset_def list_all_iff)
    have "\<exists>t'. ok (if downto0 is (ilength binders - 1) then return t else mapbnd (idx is) 0 t) t'"
    proof (cases "downto0 is (ilength binders - 1)")
      case False
      have "\<exists>j. ok (idx is (integer_of_nat k)) j" if "k \<in> loose_BVars (tr t)" for k
        using inis[OF that] idx_None_iff[of "is" "integer_of_nat k"] by (cases "Unification.idx is (integer_of_nat k)") (auto simp: ok_idx)
      then have "\<exists>t'. ok (mapbnd (idx is) 0 t) t'" by (intro mapbnd_ok[OF assms(1)]) auto
      with False show ?thesis by simp
    qed simp
    then obtain t' where t': "ok (if downto0 is (ilength binders - 1) then return t else mapbnd (idx is) 0 t) t'" ..
    obtain u where u: "ok (mkabs binders is t') u" using mkabs_ok[OF assms(3)] by blast
    from t' u up[of u] False sub show ?thesis by (auto simp: match_bind_def Let_def simp del: mapbnd.simps)
  qed
qed


subsection \<open>Linear patterns\<close>

text \<open>The variables of a term in order of occurrence; a term is \<^emph>\<open>linear\<close> if no variable repeats.\<close>

fun vlist :: "pterm \<Rightarrow> indexname list" where
  "vlist (pterm.Var x _) = [x]"
| "vlist (pterm.Abs _ _ t) = vlist t"
| "vlist (s $ t) = vlist s @ vlist t"
| "vlist _ = []"

definition linear :: "pterm \<Rightarrow> bool" where
  "linear t \<longleftrightarrow> distinct (vlist t)"

lemma set_vlist[simp]: "set (vlist t) = vars t"
  by (induction t) auto

lemma vlist_list_comb: "vlist (list_comb h ts) = vlist h @ concat (map vlist ts)"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def)

lemma vlist_incr: "vlist (incr t) = vlist t"
proof -
  have "vlist (incr_aux d t) = vlist t" for d by (induction d t rule: incr_aux.induct) auto
  then show ?thesis by (simp add: incr_def)
qed

text \<open>The type variables of all types in a term:\<close>

definition tvs :: "pterm \<Rightarrow> (indexname \<times> psort) set" where
  "tvs t = \<Union> (tvars ` tys t)"

lemma tvs_simps[simp]:
  "tvs (s $ t) = tvs s \<union> tvs t" "tvs (pterm.Abs a T t) = tvars T \<union> tvs t"
  "tvs (Const a T) = tvars T" "tvs (Free a T) = tvars T" "tvs (pterm.Var x T) = tvars T" "tvs (Bound i) = {}"
  "tvs (incr t) = tvs t"
  by (auto simp: tvs_def)

lemma tvs_list_comb: "tvs (list_comb h ts) = tvs h \<union> \<Union> (tvs ` set ts)"
  by (auto simp: tvs_def tys_list_comb)

lemma ctys_tvs: "T \<in> ctys t \<Longrightarrow> tvars T \<subseteq> tvs t"
  by (induction t) (auto simp: tvs_def)

lemma is_Abs_incr_aux: "Pure_Term.is_Abs (incr_aux d t) \<longleftrightarrow> Pure_Term.is_Abs t"
  by (cases t) auto

lemma rfree_incr: "rfree (incr t) \<longleftrightarrow> rfree t" and is_Abs_incr: "Pure_Term.is_Abs (incr t) \<longleftrightarrow> Pure_Term.is_Abs t"
proof -
  have "rfree (incr_aux d t) \<longleftrightarrow> rfree t" for d
    by (induction d t rule: incr_aux.induct) (auto simp: is_Abs_incr_aux)
  then show "rfree (incr t) \<longleftrightarrow> rfree t" "Pure_Term.is_Abs (incr t) \<longleftrightarrow> Pure_Term.is_Abs t"
    by (simp_all add: incr_def is_Abs_incr_aux)
qed

lemma code_eq_iff: "code a = code b \<longleftrightarrow> a = b"
  by (metis atom_of_code)


subsection \<open>Higher-order matching\<close>

context wf_algebra
begin

text \<open>
  If some environment \<open>(tye, te)\<close> instantiates a linear pattern to a term equivalent to an object
  without \<open>\<beta>\<close>-redexes, matching succeeds; the type environment stays in agreement with \<open>tye\<close>.
\<close>

lemma mtch_complete:
  assumes "ppat pt" "linear pt" "rfree ob" "proper ob" "no_loose_bound (tr pt) (length binders)"
    "\<forall>T\<in>ctys pt. wft ar T" "\<forall>T\<in>ctys ob. wft ar T" "tvs pt \<subseteq> A" "scons A"
    "tagrees (fst env) (mtinst tye) A" "\<forall>x\<in>vars pt. vt_lookup (snd env) x = None"
    "mte_ok te" "minst (tye, te) pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  shows "\<exists>env'. ok (mtch alg binders pt ob env) env' \<and> tagrees (fst env') (mtinst tye) A \<and>
    (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow> vt_lookup (snd env) x \<noteq> None \<or> x \<in> vars pt)"
  using assms(1-8,10-11,13)
proof (induction "(pt, ob)" arbitrary: binders pt ob env
    rule: wf_induct[OF wf_measures[of "[\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"]])
  case 1
  let ?\<rho> = "mtinst tye" and ?E = "(tye, te)"
  have IH: "\<exists>env'. ok (mtch alg binders' p q e) env' \<and> tagrees (fst env') ?\<rho> A \<and>
      (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow> vt_lookup (snd e) x \<noteq> None \<or> x \<in> vars p)"
    if "nabs p + nabs q < nabs pt + nabs ob \<or>
        nabs p + nabs q \<le> nabs pt + nabs ob \<and> size p + size q < size pt + size ob"
      "ppat p" "linear p" "rfree q" "proper q" "no_loose_bound (tr p) (length binders')"
      "\<forall>T\<in>ctys p. wft ar T" "\<forall>T\<in>ctys q. wft ar T" "tvs p \<subseteq> A" "tagrees (fst e) ?\<rho> A"
      "\<forall>x\<in>vars p. vt_lookup (snd e) x = None" "minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q"
    for binders' p q e
  proof -
    have "((p, q), (pt, ob)) \<in> measures [\<lambda>(pt, ob). nabs pt + nabs ob, \<lambda>(pt, ob). size pt + size ob]"
      using that(1) by (auto simp: order.order_iff_strict)
    with "1.hyps" that(2-12) show ?thesis by blast
  qed
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have ppt: "proper pt" by (rule ppat_proper[OF prems(1)])
  show ?case
  proof (cases "Pure_Term.is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = pterm.Abs ns Ts ts" by (cases pt) auto
    have ts: "ppat ts" "linear ts" "no_loose_bound (tr ts) (Suc (length binders))"
      "\<forall>T\<in>ctys ts. wft ar T" "tvs ts \<subseteq> A" "\<forall>x\<in>vars ts. vt_lookup (snd env) x = None"
      using prems ppat_AbsD[of ns Ts ts] by (auto simp: pt linear_def)
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      have eq: "mtch alg binders pt ob env = mtch alg ((nt, Tt) # binders) ts tt env"
        by (subst mtch.simps) (simp add: e pt ob)
      have q: "rfree tt" "proper tt" "\<forall>T\<in>ctys tt. wft ar T" using prems(3,4,7) by (simp_all add: ob)
      have "minst ?E ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr tt"
        using Abs_equiv_Abs[of "minst ?E ts" "tr tt"] prems(11) by (simp add: pt ob minst_simps)
      note eqv = this
      have "\<exists>env'. ok (mtch alg ((nt, Tt) # binders) ts tt env) env' \<and> tagrees (fst env') ?\<rho> A \<and>
          (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow> vt_lookup (snd env) x \<noteq> None \<or> x \<in> vars ts)"
        by (rule IH) (use eqv ts q prems(9) in \<open>simp_all add: pt ob\<close>)
      then show ?thesis unfolding eq by (simp add: pt)
    next
      case oA: False
      have "\<forall>(v, S)\<in>tvars Ts. \<forall>S' U. vt_lookup iTs v = Some (S', U) \<longrightarrow> S' = S"
        using prems(8,9) by (fastforce simp: pt e tagrees_def)
      then obtain Tt where st: "ok (subst_type iTs Ts) Tt" using subst_type_ok by blast
      have eq: "mtch alg binders pt ob env = mtch alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env"
        by (subst mtch.simps) (simp add: e pt oA st)
      have q: "rfree (incr ob $ Bound 0)" "proper (incr ob $ Bound 0)"
        "\<forall>T\<in>ctys (incr ob $ Bound 0). wft ar T"
        using prems(3,4,7) oA by (simp_all add: rfree_incr is_Abs_incr proper_incr ctys_incr)
      have "minst ?E ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (incr ob $ Bound 0)"
        using prems(11) by (simp add: pt minst_simps fact6 tr_incr[OF prems(4)])
      note eqv = this
      have "\<exists>env'. ok (mtch alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env) env' \<and>
          tagrees (fst env') ?\<rho> A \<and>
          (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow> vt_lookup (snd env) x \<noteq> None \<or> x \<in> vars ts)"
        by (rule IH) (use eqv ts q prems(9) in \<open>simp_all add: pt nabs_incr\<close>)
      then show ?thesis unfolding eq by (simp add: pt)
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      have eq: "mtch alg binders pt ob env = mtch alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env"
        by (subst mtch.simps) (simp add: e pA ob)
      have p: "ppat (incr pt $ Bound 0)" "linear (incr pt $ Bound 0)"
        "no_loose_bound (tr (incr pt $ Bound 0)) (Suc (length binders))"
        "\<forall>T\<in>ctys (incr pt $ Bound 0). wft ar T" "tvs (incr pt $ Bound 0) \<subseteq> A"
        "\<forall>x\<in>vars (incr pt $ Bound 0). vt_lookup (snd env) x = None"
        using ppat_incr_Bound0[OF prems(1) pA] prems(2,6,8,10) no_loose_bound_lift[OF prems(5) le0]
        by (simp_all add: linear_def vlist_incr tr_incr[OF ppt] ctys_incr vars_incr)
      have q: "rfree tt" "proper tt" "\<forall>T\<in>ctys tt. wft ar T" using prems(3,4,7) by (simp_all add: ob)
      have "minst ?E (incr pt $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr tt"
      proof -
        have "minst ?E (incr pt $ Bound 0) = lift (minst ?E pt) 0 \<degree> BVar 0"
          by (simp add: minst_simps minst_incr[OF _ ppt] assms(12))
        moreover have "tr tt \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (minst ?E pt) 0 \<degree> BVar 0"
          using equiv_sym[OF prems(11)] by (simp add: ob fact6)
        ultimately show ?thesis by (simp add: equiv_sym)
      qed
      note eqv = this
      have "\<exists>env'. ok (mtch alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env) env' \<and>
          tagrees (fst env') ?\<rho> A \<and> (\<forall>x. vt_lookup (snd env') x \<noteq> None \<longrightarrow>
            vt_lookup (snd env) x \<noteq> None \<or> x \<in> vars (incr pt $ Bound 0))"
        by (rule IH) (use eqv p q prems(9) in \<open>simp_all add: ob nabs_incr\<close>)
      then show ?thesis unfolding eq by (simp add: vars_incr)
    next
      case oA: False
      obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
      have obc: "ob = list_comb oh oargs" by (rule strip_comb_list_comb[OF so])
      have ohh: "\<not> (\<exists>f u. oh = f $ u)" by (rule strip_comb_head[OF so])
      have orf: "\<forall>q\<in>set oargs. rfree q" "oargs \<noteq> [] \<longrightarrow> \<not> Pure_Term.is_Abs oh"
        using prems(3) by (simp_all add: obc rfree_list_comb)
      have opr: "proper oh" "\<forall>q\<in>set oargs. proper q" using prems(4) by (simp_all add: obc proper_list_comb)
      have "\<not> Pure_Term.is_Abs oh" using oA orf(2) by (cases oargs) (auto simp: obc)
      then have oat: "is_atom (tr oh)" using ohh opr(1) by (cases oh) auto
      have ow: "\<forall>q\<in>set oargs. \<forall>T\<in>ctys q. wft ar T" "\<forall>T\<in>ctys oh. wft ar T"
        using prems(7) by (auto simp: obc ctys_list_comb)
      show ?thesis
      proof (cases rule: ppat_nonAbsE[OF prems(1) pA, case_names rigid flex])
        case (flex x T iss)
        have sp: "strip_comb pt = (pterm.Var x T, map Bound iss)"
          by (simp add: flex app_list_comb strip_comb_list_comb_eq)
        have io: "ok (ints_of (map Bound iss)) iss" using flex(2) by (simp add: ok_ints_of)
        have none: "vt_lookup itms x = None" using prems(10) by (simp add: e flex app_list_comb vars_list_comb)
        then have lk: "ok (lookup1 itms x T) None" by (simp add: lookup1_def)
        have lt: "\<forall>i\<in>set iss. 0 \<le> i \<and> nat_of_integer i < length binders"
          using prems(5) flex(3) no_loose_bound_BVars[of "tr pt" "length binders"]
          by (auto simp: flex loose_BVars_tr_app)
        have mi: "minst ?E pt = msub te (code (AVar x)) \<degree>\<degree> map BVar (nats iss)"
          by (simp add: flex app_list_comb minst_list_comb minst_simps comp_def)
        have "no_loose_bound (msub te (code (AVar x))) 0"
          by (rule closed_onD[OF closed_msub[OF assms(12), of UNIV] UNIV_I])
        then have "loose_BVars (minst ?E pt) \<subseteq> set (nats iss)" by (auto simp: mi no_loose_bound_loose_BVars)
        then have "dep_on (set (nats iss)) (tr ob)" by (rule dep_onI[OF equiv_sym[OF prems(11)]])
        then have "loose_BVars (tr ob) \<subseteq> set (nats iss)" by (rule rfree_dep_on[OF prems(3,4)])
        then obtain itms' where mb: "ok (match_bind itms binders x T iss ob) itms'"
          using match_bind_ok[OF prems(4) _ lt none] by blast
        obtain u where u: "itms' = vt_update (x, (T, u)) itms"
          using match_bind_sound[OF mb prems(4) flex(3)] by blast
        have "ok (mtch alg binders pt ob env) (iTs, itms')"
          by (subst mtch.simps) (simp add: e pA oA sp io lk mb)
        moreover have "x \<in> vars pt" by (simp add: flex app_list_comb vars_list_comb)
        ultimately show ?thesis using prems(9) by (auto simp: e u)
      next
        case (rigid h ts)
        have hh: "\<not> (\<exists>f u. h = f $ u)" by (rule is_rigid_not_App[OF rigid(1)])
        have sp: "strip_comb pt = (h, ts)" by (simp add: rigid(2) strip_comb_list_comb_eq[OF hh])
        have hnv: "\<not> is_Var h" using rigid(1) by (auto simp: is_rigid_def)
        have hat: "is_atom (minst ?E h)" using rigid(1) by (auto simp: is_rigid_def minst_simps)
        have "minst ?E h \<degree>\<degree> map (minst ?E) ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr oh \<degree>\<degree> map tr oargs"
          using prems(11) by (simp add: rigid(2) obc minst_list_comb tr_list_comb)
        from atom_apps_equiv[OF hat oat this]
        have hd: "minst ?E h = tr oh" and l2: "list_all2 (\<lambda>p q. minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ts oargs"
          by (simp_all add: list_all2_map1 list_all2_map2)
        have len: "length ts = length oargs" using l2 by (rule list_all2_lengthD)
        have vh: "vlist h = []" using rigid(1) by (auto simp: is_rigid_def)
        have dts: "distinct (concat (map vlist ts))" using prems(2) by (simp add: linear_def rigid(2) vlist_list_comb vh)
        have pts: "ppat p" "linear p" "no_loose_bound (tr p) (length binders)" "\<forall>T\<in>ctys p. wft ar T"
          "tvs p \<subseteq> A" "vars p \<subseteq> vars pt" if "p \<in> set ts" for p
          using that rigid(3) prems(5,6,8) dts
          by (auto simp: rigid(2) linear_def tr_list_comb no_loose_bound_list_app ctys_list_comb
            tvs_list_comb vars_list_comb distinct_concat_iff)
        text \<open>The arguments are matched from left to right:\<close>
        have args: "\<exists>e'. ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ps qs) e) e' \<and> tagrees (fst e') ?\<rho> A \<and>
            (\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup (snd e) x \<noteq> None \<or> x \<in> vars pt)"
          if "list_all2 (\<lambda>p q. minst ?E p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ps qs" "set ps \<subseteq> set ts" "set qs \<subseteq> set oargs"
            "distinct (concat (map vlist ps))" "tagrees (fst e) ?\<rho> A"
            "\<forall>x\<in>\<Union> (vars ` set ps). vt_lookup (snd e) x = None"
          for ps qs e
          using that
        proof (induction ps qs arbitrary: e rule: list_all2_induct)
          case (Cons p ps q qs)
          have p: "p \<in> set ts" "q \<in> set oargs" using Cons.prems(1,2) by auto
          note ap = strip_comb_arg[OF sp p(1)] and aq = strip_comb_arg[OF so p(2)]
          have "\<exists>e1. ok (mtch alg binders p q e) e1 \<and> tagrees (fst e1) ?\<rho> A \<and>
              (\<forall>x. vt_lookup (snd e1) x \<noteq> None \<longrightarrow> vt_lookup (snd e) x \<noteq> None \<or> x \<in> vars p)"
            by (rule IH) (use pts[OF p(1)] orf(1) opr(2) ow(1) p Cons.hyps(1) Cons.prems(4,5) ap aq in auto)
          then obtain e1 where e1: "ok (mtch alg binders p q e) e1" "tagrees (fst e1) ?\<rho> A"
            "\<forall>x. vt_lookup (snd e1) x \<noteq> None \<longrightarrow> vt_lookup (snd e) x \<noteq> None \<or> x \<in> vars p"
            by blast
          have disj: "vars p \<inter> \<Union> (vars ` set ps) = {}" using Cons.prems(3) by simp
          have "\<forall>x\<in>\<Union> (vars ` set ps). vt_lookup (snd e1) x = None"
          proof
            fix x assume x: "x \<in> \<Union> (vars ` set ps)"
            with Cons.prems(5) have "vt_lookup (snd e) x = None" by simp
            moreover have "x \<notin> vars p" using disj x by blast
            ultimately show "vt_lookup (snd e1) x = None" using e1(3) by blast
          qed
          from Cons.IH[OF _ _ _ e1(2) this] Cons.prems(1-3) obtain e' where
            e': "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ps qs) e1) e'" "tagrees (fst e') ?\<rho> A"
              "\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup (snd e1) x \<noteq> None \<or> x \<in> vars pt"
            by auto
          have "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip (p # ps) (q # qs)) e) e'"
            using e1(1) e'(1) by auto
          with e1(3) e'(2,3) pts(6)[OF p(1)] show ?case by blast
        qed simp
        have args0: "\<exists>e'. ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) e) e' \<and>
            tagrees (fst e') ?\<rho> A \<and>
            (\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup (snd e) x \<noteq> None \<or> x \<in> vars pt)"
          if "tagrees (fst e) ?\<rho> A" "snd e = itms" for e
          using args[OF l2 order.refl order.refl dts that(1)] prems(10) that(2) pts(6)
          by (fastforce simp: e)
        have hdl: "ok (handle (zip_eq ts oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). mtch alg binders p q) pqs e))
            (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) e'"
          if "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) e) e'" for e e'
          using that len by (simp add: ok_handle ok_zip_eq)
        show ?thesis
        proof (cases h)
          case h: (Const a Ta)
          with hd obtain Tb where oh: "oh = Const a Tb" and tb: "Tb = tsubst ?\<rho> Ta"
            by (cases oh) (auto simp: minst_simps)
          have wa: "wft ar Ta" "wft ar Tb"
            using prems(6) ow(2) by (simp_all add: rigid(2) h oh ctys_list_comb)
          have ta: "tvars Ta \<subseteq> A" using prems(8) by (auto simp: rigid(2) h tvs_list_comb)
          have "tmatcher alg iTs ?\<rho> Ta Tb"
            using tb tagrees_mono[OF prems(9) ta] by (simp add: e tmatcher_tagrees)
          moreover have "scons (tvars Ta)" using assms(9) ta unfolding scons_def by blast
          ultimately obtain iTs' where tm: "typ_match alg Ta Tb iTs = return iTs'"
            and "textends iTs iTs'" "\<forall>(v, S)\<in>tvars Ta. vt_lookup iTs' v = Some (S, ?\<rho> v S)"
            "\<forall>v. vt_lookup iTs' v \<noteq> None \<longrightarrow> vt_lookup iTs v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars Ta)"
            using typ_match_complete[OF wa] by blast
          then have tmc: "tmcomplete ?\<rho> Ta iTs iTs'" by (simp add: tmcomplete_def)
          note tm = tm[unfolded return_def]
          have ag: "tagrees iTs' ?\<rho> A"
            by (rule tagrees_step[OF _ assms(9) ta tmc]) (use prems(9) in \<open>simp add: e\<close>)
          from args0[of "(iTs', itms)"] ag obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e'"
            and r: "tagrees (fst e') ?\<rho> A"
              "\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup itms x \<noteq> None \<or> x \<in> vars pt"
            by auto
          have "ok (mtch alg binders pt ob env) e'"
            by (subst mtch.simps) (simp add: e pA oA sp so h oh hnv tm hdl[OF f])
          with r show ?thesis by (auto simp: e)
        next
          case h: (Free a Ta)
          with hd obtain Tb where oh: "oh = Free a Tb" and tb: "Tb = tsubst ?\<rho> Ta"
            by (cases oh) (auto simp: minst_simps)
          have wa: "wft ar Ta" "wft ar Tb"
            using prems(6) ow(2) by (simp_all add: rigid(2) h oh ctys_list_comb)
          have ta: "tvars Ta \<subseteq> A" using prems(8) by (auto simp: rigid(2) h tvs_list_comb)
          have "tmatcher alg iTs ?\<rho> Ta Tb"
            using tb tagrees_mono[OF prems(9) ta] by (simp add: e tmatcher_tagrees)
          moreover have "scons (tvars Ta)" using assms(9) ta unfolding scons_def by blast
          ultimately obtain iTs' where tm: "typ_match alg Ta Tb iTs = return iTs'"
            and "textends iTs iTs'" "\<forall>(v, S)\<in>tvars Ta. vt_lookup iTs' v = Some (S, ?\<rho> v S)"
            "\<forall>v. vt_lookup iTs' v \<noteq> None \<longrightarrow> vt_lookup iTs v \<noteq> None \<or> (\<exists>S. (v, S) \<in> tvars Ta)"
            using typ_match_complete[OF wa] by blast
          then have tmc: "tmcomplete ?\<rho> Ta iTs iTs'" by (simp add: tmcomplete_def)
          note tm = tm[unfolded return_def]
          have ag: "tagrees iTs' ?\<rho> A"
            by (rule tagrees_step[OF _ assms(9) ta tmc]) (use prems(9) in \<open>simp add: e\<close>)
          from args0[of "(iTs', itms)"] ag obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) (iTs', itms)) e'"
            and r: "tagrees (fst e') ?\<rho> A"
              "\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup itms x \<noteq> None \<or> x \<in> vars pt"
            by auto
          have "ok (mtch alg binders pt ob env) e'"
            by (subst mtch.simps) (simp add: e pA oA sp so h oh hnv tm hdl[OF f])
          with r show ?thesis by (auto simp: e)
        next
          case h: (Bound i)
          have i0: "0 \<le> i" using rigid(1) by (simp add: h is_rigid_def)
          from hd h opr(1) i0 have oh: "oh = Bound i"
            by (cases oh) (auto simp: minst_simps nat_of_integer_eq_iff)
          from args0[of env] prems(9) obtain e' where
            f: "ok (foldM (\<lambda>(p, q). mtch alg binders p q) (zip ts oargs) env) e'"
            and r: "tagrees (fst e') ?\<rho> A"
              "\<forall>x. vt_lookup (snd e') x \<noteq> None \<longrightarrow> vt_lookup itms x \<noteq> None \<or> x \<in> vars pt"
            by (auto simp: e)
          have "ok (mtch alg binders pt ob env) e'"
            using hdl[OF f] by (subst mtch.simps) (simp add: e pA oA sp so h oh)
          with r show ?thesis by (auto simp: e)
        qed (use rigid(1) hh in \<open>auto simp: is_rigid_def\<close>)
      qed
    qed
  qed
qed

end

declare sup_apply[simp]

end
