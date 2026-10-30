section \<open>Exceptions of Matching\<close>

theory Match_Exceptions
  imports Match_Termination Poly_Unif
begin

context csig
begin

text \<open>
  On well-formed inputs, matching fails only with \<open>Match\<close> or \<open>Pattern\<close>, and \<open>Pattern\<close> only if the
  pattern is not a higher-order pattern or the object contains a \<open>\<beta>\<close>-redex.
\<close>

subsection \<open>Terms\<close>

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


subsection \<open>Well-formedness\<close>

text \<open>Variables and their types in a term:\<close>

fun vtys :: "pterm \<Rightarrow> (indexname \<times> ptyp) set" where
  "vtys (pterm.Var x T) = {(x, T)}"
| "vtys (pterm.Abs _ _ t) = vtys t"
| "vtys (s $ t) = vtys s \<union> vtys t"
| "vtys _ = {}"

text \<open>Each variable has a unique type, also in the bindings of an environment:\<close>

definition vfun :: "(indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vfun V \<longleftrightarrow> (\<forall>x T T'. (x, T) \<in> V \<longrightarrow> (x, T') \<in> V \<longrightarrow> T = T')"

definition vagree :: "tenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vagree te V \<longleftrightarrow> (\<forall>(x, T)\<in>V. \<forall>U u. vt_lookup te x = Some (U, u) \<longrightarrow> U = T)"

text \<open>Each type variable has a unique sort, also in the bindings of a type environment:\<close>

definition tsorts :: "tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tsorts tye A \<longleftrightarrow> (\<forall>(v, S)\<in>A. \<forall>S' U. vt_lookup tye v = Some (S', U) \<longrightarrow> S' = S)"

lemma vtys_simps[simp]:
  "vtys (incr t) = vtys t" "vtys (Const a T) = {}" "vtys (Free a T) = {}" "vtys (Bound i) = {}"
proof -
  have "vtys (incr_aux d t) = vtys t" for d by (induction d t rule: incr_aux.induct) auto
  then show "vtys (incr t) = vtys t" by (simp add: incr_def)
qed simp_all

lemma vtys_list_comb: "vtys (list_comb h ts) = vtys h \<union> \<Union> (vtys ` set ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)

lemma ppat_rfree: "ppat t \<Longrightarrow> rfree t"
  by (induction rule: ppat.induct)
    (auto simp: rfree_list_comb is_rigid_def app_list_comb)


lemma vagree_update:
  assumes "vagree te V" "vfun V" "(x, T) \<in> V"
  shows "vagree (vt_update (x, (T, u)) te) V"
  unfolding vagree_def
proof clarify
  fix y T' U u' assume yT: "(y, T') \<in> V" and l: "vt_lookup (vt_update (x, (T, u)) te) y = Some (U, u')"
  show "U = T'"
  proof (cases "y = x")
    case True
    with l have "U = T" by simp
    moreover have "T' = T" using assms(2,3) yT True unfolding vfun_def by blast
    ultimately show ?thesis by simp
  next
    case False
    with l have "vt_lookup te y = Some (U, u')" by simp
    with yT assms(1) show ?thesis by (auto simp: vagree_def)
  qed
qed


subsection \<open>Auxiliary functions\<close>

lemma ints_of_exn: "ints_of ts = Some r \<Longrightarrow> (\<exists>is. r = Ok is) \<or> r = Err Pattern"
  by (induction ts arbitrary: r rule: ints_of.induct)
    (auto simp: return_def raise_def bindM_def split: option.splits res.splits if_splits)

lemma red_other_ok:
  assumes "\<not> (Pure_Term.is_Abs t \<and> is \<noteq> [])" "proper t" "no_loose_bound (tr t) (length js)"
  shows "\<exists>u. ok (red t is js) u"
proof -
  have "\<exists>j. ok (nth js (integer_of_nat k)) j" if "k \<in> loose_BVars (tr t)" for k
    using that no_loose_bound_BVars[OF assms(3)] by (auto simp: ok_nth less_eq_integer.rep_eq)
  then have "\<exists>t'. ok (mapbnd (nth js) 0 t) t'" by (intro mapbnd_ok[OF assms(2)]) auto
  then show ?thesis by (auto simp: red_other[OF assms(1)] simp del: mapbnd.simps)
qed

lemma red_ok:
  "proper t \<Longrightarrow> no_loose_bound (tr t) (length js) \<Longrightarrow> \<exists>u. ok (red t is js) u"
proof (induction t arbitrary: "is" js)
  case (Abs a T s)
  show ?case
  proof (cases "is")
    case Nil
    with Abs.prems show ?thesis by (intro red_other_ok) simp_all
  next
    case (Cons i is')
    with Abs.IH[of "i # js" is'] Abs.prems show ?thesis by simp
  qed
qed (rule red_other_ok; simp)+

lemma match_bind_exn:
  assumes "match_bind itms binders ixn T is t = Some r" "proper t"
    "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders" "vt_lookup itms ixn = None"
  shows "(\<exists>itms'. r = Ok itms') \<or> r = Err Match"
proof (cases "loose_BVars (tr t) \<subseteq> set (nats is)")
  case True
  obtain itms' where "ok (match_bind itms binders ixn T is t) itms'"
    using match_bind_ok[OF assms(2) True assms(3,4)] by blast
  with assms(1) show ?thesis by auto
next
  case False
  then obtain k where k: "k \<in> loose_BVars (tr t)" "k \<notin> set (nats is)" by blast
  have "integer_of_nat k \<notin> set is"
  proof
    assume "integer_of_nat k \<in> set is"
    moreover have "nat_of_integer (integer_of_nat k) = k" by (simp add: nat_of_integer.rep_eq)
    ultimately have "k \<in> set (nats is)" by (metis image_eqI set_map)
    with k(2) show False by simp
  qed
  with k set_loose_bnos[OF assms(2)] have "\<not> subset (loose_bnos t) is" "loose_bnos t \<noteq> []"
    by (auto simp: subset_def list_all_iff)
  with assms(1) show ?thesis by (auto simp: match_bind_def Let_def raise_def split: if_splits)
qed

lemma foldM_exn:
  assumes "foldM f xs e = Some r" "I e"
    "\<And>x e r. x \<in> set xs \<Longrightarrow> f x e = Some r \<Longrightarrow> I e \<Longrightarrow> (\<exists>e'. r = Ok e' \<and> I e') \<or> (\<exists>ex. r = Err ex \<and> P ex)"
  shows "(\<exists>e'. r = Ok e' \<and> I e') \<or> (\<exists>ex. r = Err ex \<and> P ex)"
  using assms
proof (induction xs arbitrary: e)
  case Nil
  then show ?case by (auto simp: return_def)
next
  case (Cons x xs)
  from Cons.prems(1) obtain r1 where r1: "f x e = Some r1"
    and rest: "(case r1 of Ok e1 \<Rightarrow> foldM f xs e1 | Err ex \<Rightarrow> Some (Err ex)) = Some r"
    by (auto simp: bindM_def split: option.splits res.splits)
  have step: "(\<exists>e'. r = Ok e' \<and> I e') \<or> (\<exists>ex. r = Err ex \<and> P ex)"
    if "y \<in> set xs" "f y e = Some r" "I e" for y e r
    using that by (intro Cons.prems(3)) auto
  have "(\<exists>e'. r1 = Ok e' \<and> I e') \<or> (\<exists>ex. r1 = Err ex \<and> P ex)"
    by (rule Cons.prems(3)[OF _ r1 Cons.prems(2)]) simp
  then show ?case
  proof (elim disjE exE conjE)
    fix e1 assume "r1 = Ok e1" "I e1"
    with rest Cons.IH[OF _ _ step] show ?thesis by auto
  next
    fix ex assume "r1 = Err ex" "P ex"
    with rest show ?thesis by auto
  qed
qed

lemma zip_eq_exn:
  "zip_eq xs ys = Some r \<Longrightarrow>
    length xs = length ys \<and> r = Ok (zip xs ys) \<or> length xs \<noteq> length ys \<and> r = Err Unequal_Lengths"
  by (induction xs ys arbitrary: r rule: zip_eq.induct)
    (auto simp: return_def raise_def bindM_def split: option.splits res.splits)


subsection \<open>Types of terms\<close>

lemma fastype_of_bound_typed:
  "0 \<le> i \<Longrightarrow> nat_of_integer i < length Ts \<Longrightarrow> fastype_of_bound Ts i = return (Ts ! nat_of_integer i)"
proof (induction Ts arbitrary: i)
  case (Cons T Ts)
  show ?case
  proof (cases "i = 0")
    case False
    with Cons.prems have "0 < i" by simp
    then have "0 \<le> i - 1" "nat_of_integer (i - 1) = nat_of_integer i - 1" "nat_of_integer i \<noteq> 0"
      by (simp_all add: integer_reps nat_of_integer_minus_1)
    then obtain k where k: "nat_of_integer i = Suc k" "nat_of_integer (i - 1) = k" by (cases "nat_of_integer i") auto
    with Cons.prems Cons.IH[of "i - 1"] False \<open>0 \<le> i - 1\<close> show ?thesis by simp
  qed simp
qed simp

lemma fastype_of_typed:
  "(\<forall>T. has_type W Ts t T \<longrightarrow> fastype_of_term Ts t = return T) \<and>
    (\<forall>A B. has_type W Ts t (A \<rightarrow>\<^sub>T B) \<longrightarrow> range_type_of Ts t = return B)"
proof (induction t arbitrary: Ts)
  case (Bound i)
  have "fastype_of_term Ts (Bound i) = return T" if "has_type W Ts (Bound i) T" for T
    using that by (auto simp: has_type_Bound_iff fastype_of_bound_typed)
  moreover have "range_type_of Ts (Bound i) = return B" if "has_type W Ts (Bound i) (A \<rightarrow>\<^sub>T B)" for A B
  proof -
    from that have "0 \<le> i" "nat_of_integer i < length Ts" "Ts ! nat_of_integer i = A \<rightarrow>\<^sub>T B"
      by (simp_all add: has_type_Bound_iff)
    then show ?thesis by (simp add: fastype_of_bound_typed return_def)
  qed
  ultimately show ?case by blast
next
  case (Abs x T0 u)
  then show ?case by (auto elim: has_type_elims simp: return_def)
next
  case (App s u)
  then show ?case by (auto elim!: has_type_elims simp: return_def)
qed (auto elim: has_type_elims)

lemma fastype_of_closed: "has_type W [] t T \<Longrightarrow> fastype_of t = return T"
  using fastype_of_typed[of W "[]" t] by (simp add: fastype_of_def)

lemma has_type_strengthen:
  "has_type W (Ts @ Us) t T \<Longrightarrow> no_loose_bound (tr t) (length Ts) \<Longrightarrow> has_type W Ts t T"
proof (induction t arbitrary: Ts T)
  case (Bound i)
  then show ?case by (auto simp: has_type_Bound_iff nth_append nat_of_integer_less_iff)
next
  case (Abs x T0 u)
  from Abs.prems(1) obtain U where "T = T0 \<rightarrow>\<^sub>T U" "has_type W ((T0 # Ts) @ Us) u U"
    by (auto elim: has_type_elims)
  with Abs.prems(2) Abs.IH[of "T0 # Ts" U] show ?case by (auto intro: has_type.Abs)
next
  case (App s u)
  from App.prems(1) obtain T' where s: "has_type W (Ts @ Us) s (T' \<rightarrow>\<^sub>T T)"
    and u: "has_type W (Ts @ Us) u T'"
    by (auto elim: has_type_elims)
  from App.prems(2) have "no_loose_bound (tr s) (length Ts)" "no_loose_bound (tr u) (length Ts)"
    by simp_all
  then have "has_type W Ts s (T' \<rightarrow>\<^sub>T T)" "has_type W Ts u T'"
    using App.IH(1)[OF s] App.IH(2)[OF u] by simp_all
  then show ?case by (rule has_type.App)
qed (auto elim!: has_type_elims intro: has_type.intros)

lemma has_type_wft: "has_type W Ts t T \<Longrightarrow> \<forall>U\<in>tys t \<union> set Ts. wft ar U \<Longrightarrow> wft ar T"
  by (induction rule: has_type.induct) (auto simp: tarity_def)


subsection \<open>Higher-order matching\<close>

end

context wf_csig
begin

text \<open>Type matching fails only with \<open>Match\<close> and keeps the sorts consistent:\<close>

lemma typ_match_m_exn:
  assumes "wft ar T" "wft ar U" "tvars T \<subseteq> A" "scons A" "tsorts tye A"
  shows "(\<exists>tye'. typ_match_m alg T U tye = Some (Ok tye') \<and> tsorts tye' A) \<or>
    typ_match_m alg T U tye = Some (Err Match)"
proof -
  have "scons (tvars T)" using assms(3,4) unfolding scons_def by blast
  moreover have "tcons tye T" using assms(5) assms(3) unfolding tcons_def tsorts_def by fastforce
  ultimately have "mcons tye T" by (simp add: mcons_def)
  from typ_match_exn[OF assms(1,2) this] show ?thesis
  proof (elim disjE exE)
    fix tye' assume tm: "typ_match alg T U tye = return tye'"
    note s = typ_match_sound[OF assms(1,2) tm]
    have "tsorts tye' A"
      unfolding tsorts_def
    proof (intro ballI allI impI, clarify)
      fix v S S' V assume vS: "(v, S) \<in> A" and l: "vt_lookup tye' v = Some (S', V)"
      show "S' = S"
      proof (cases "vt_lookup tye v")
        case None
        with s(4)[OF l] have "(v, S') \<in> tvars T" by blast
        with vS assms(3,4) show ?thesis unfolding scons_def by blast
      next
        case (Some b)
        have "vt_lookup tye' v = Some b" using s(1) Some unfolding textends_def by blast
        with l Some have "vt_lookup tye v = Some (S', V)" by simp
        with vS assms(5) show ?thesis by (auto simp: tsorts_def)
      qed
    qed
    with tm show ?thesis by (simp add: typ_match_m_def return_def)
  qed (simp add: typ_match_m_def raise_def)
qed

lemma mtch_exn:
  assumes "mtch alg' binders pt ob env = Some r"
  shows "alg' = alg \<Longrightarrow> proper pt \<Longrightarrow> proper ob \<Longrightarrow> no_loose_bound (tr pt) (length binders) \<Longrightarrow>
    \<forall>T\<in>ctys pt. wft ar T \<Longrightarrow> \<forall>T\<in>ctys ob. wft ar T \<Longrightarrow> tvs pt \<subseteq> A \<Longrightarrow> scons A \<Longrightarrow>
    tsorts (fst env) A \<Longrightarrow> vtys pt \<subseteq> V \<Longrightarrow> vfun V \<Longrightarrow> vagree (snd env) V \<Longrightarrow> mte_ok (snd env) \<Longrightarrow>
    (\<exists>env'. r = Ok env' \<and> tsorts (fst env') A \<and> vagree (snd env') V \<and> mte_ok (snd env')) \<or>
    (\<exists>ex. r = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)))"
  using assms
proof (induction alg' binders pt ob env r rule: mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' binders pt ob env r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" using prems by simp
  note h = "1.hyps"[unfolded alg']
  note IH = "1.IH"[OF _ refl]
  show ?case
  proof (cases "Pure_Term.is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = pterm.Abs ns Ts ts" by (cases pt) auto
    have ts: "proper ts" "no_loose_bound (tr ts) (length (b # binders))" "\<forall>T\<in>ctys ts. wft ar T"
      "tvs ts \<subseteq> A" "vtys ts \<subseteq> V" for b
      using prems by (simp_all add: pt)
    have pat: "ppat pt \<Longrightarrow> ppat ts" by (simp add: pt ppat_AbsD)
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from h have m: "fm alg ((nt, Tt) # binders) ts tt env = Some r" by (simp add: e pt ob)
      from IH[OF m ts(1)] prems ts pat show ?thesis by (auto simp: ob)
    next
      case oA: False
      have "\<forall>(v, S)\<in>tvars Ts. \<forall>S' U. vt_lookup iTs v = Some (S', U) \<longrightarrow> S' = S"
        using prems(7,9) by (fastforce simp: pt e tsorts_def)
      then obtain Tt where st: "ok (subst_type iTs Ts) Tt" using subst_type_ok by blast
      from h oA have m: "fm alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env = Some r"
        by (simp add: e pt st)
      have q: "proper (incr ob $ Bound 0)" "\<forall>T\<in>ctys (incr ob $ Bound 0). wft ar T"
        "rfree ob \<Longrightarrow> rfree (incr ob $ Bound 0)"
        using prems(3,6) oA by (simp_all add: proper_incr ctys_incr rfree_incr is_Abs_incr)
      from IH[OF m ts(1) q(1)] prems ts q pat show ?thesis by auto
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from h pA have m: "fm alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env = Some r"
        by (simp add: e ob)
      have p: "proper (incr pt $ Bound 0)" "no_loose_bound (tr (incr pt $ Bound 0)) (length ((nt, Tt) # binders))"
        "\<forall>T\<in>ctys (incr pt $ Bound 0). wft ar T" "tvs (incr pt $ Bound 0) \<subseteq> A"
        "vtys (incr pt $ Bound 0) \<subseteq> V" "ppat pt \<Longrightarrow> ppat (incr pt $ Bound 0)"
        using prems(2,4,5,7,10) no_loose_bound_lift[OF prems(4) le0] ppat_incr_Bound0[OF _ pA]
        by (simp_all add: proper_incr tr_incr[OF prems(2)] ctys_incr)
      from IH[OF m p(1)] prems p show ?thesis by (auto simp: ob)
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      have ptc: "pt = list_comb ph pargs" by (rule strip_comb_list_comb[OF sp])
      have phh: "\<not> (\<exists>f u. ph = f $ u)" by (rule strip_comb_head[OF sp])
      have pa: "\<forall>p\<in>set pargs. proper p \<and> no_loose_bound (tr p) (length binders) \<and> (\<forall>T\<in>ctys p. wft ar T) \<and>
          tvs p \<subseteq> A \<and> vtys p \<subseteq> V"
        using prems(2,4,5,7,10)
        by (auto simp: ptc proper_list_comb tr_list_comb no_loose_bound_list_app ctys_list_comb
          tvs_list_comb vtys_list_comb)
      have php: "\<forall>T\<in>ctys ph. wft ar T" "tvs ph \<subseteq> A" "vtys ph \<subseteq> V"
        using prems(5,7,10) by (auto simp: ptc ctys_list_comb tvs_list_comb vtys_list_comb)
      note h = h[unfolded e, simplified pA oA if_False sp Let_def prod.case]
      show ?thesis
      proof (cases "is_Var ph")
        case True
        then obtain ixn T where ph: "ph = pterm.Var ixn T" by (cases ph) auto
        obtain ri where io: "ints_of pargs = Some ri" using ints_of_term by blast
        from ints_of_exn[OF io] show ?thesis
        proof (elim disjE exE)
          assume ri: "ri = Err Pattern"
          have "\<not> ppat pt"
          proof
            assume "ppat pt"
            then obtain iss where "pargs = map Bound iss" "distinct iss"
              using ppat_strip_flex[OF sp[unfolded ph]] by blast
            then have "ok (ints_of pargs) iss" by (simp add: ok_ints_of)
            with io ri show False by simp
          qed
          with h ph io ri show ?thesis by auto
        next
          fix "is" assume ri: "ri = Ok is"
          then have pargs: "pargs = map Bound is" using io by (simp add: ok_ints_of)
          have lt: "\<forall>i\<in>set is. 0 \<le> i \<and> nat_of_integer i < length binders"
            using pa by (simp add: pargs)
          have tV: "(ixn, T) \<in> V" using php(3) by (simp add: ph)
          show ?thesis
          proof (cases "vt_lookup itms ixn")
            case None
            then have lk: "lookup1 itms ixn T = Some (Ok None)" by (simp add: lookup1_def return_def)
            obtain rm where mb: "match_bind itms binders ixn T is ob = Some rm" using match_bind_term by blast
            from match_bind_exn[OF mb prems(3) lt None] show ?thesis
            proof (elim disjE exE)
              fix itms' assume rm: "rm = Ok itms'"
              obtain u where u: "itms' = vt_update (ixn, (T, u)) itms" "proper u" "no_loose_bound (tr u) 0"
                using match_bind_sound[OF mb[unfolded rm] prems(3)] lt by blast
              have "vagree itms' V"
                using vagree_update[OF prems(12)[unfolded e snd_conv] prems(11) tV] by (simp add: u(1))
              moreover have "mte_ok itms'" using prems(13) u(2,3) by (auto simp: u(1) e mte_ok_def)
              moreover have "r = Ok (iTs, itms')" using h ph io ri lk mb rm by (simp add: return_def)
              ultimately show ?thesis using prems(9) by (auto simp: e)
            next
              assume "rm = Err Match"
              with h ph io ri lk mb have "r = Err Match" by simp
              then show ?thesis by auto
            qed
          next
            case (Some b)
            then obtain U u where b: "vt_lookup itms ixn = Some (U, u)" by (cases b) auto
            with prems(12) tV have "U = T" by (auto simp: e vagree_def)
            with b have lk: "lookup1 itms ixn T = Some (Ok (Some u))" by (simp add: lookup1_def return_def)
            have "proper u" "no_loose_bound (tr u) 0" using mte_okD[OF prems(13)[unfolded e snd_conv] b] by simp_all
            then obtain u' where rd: "red u is [] = Some (Ok u')" using red_ok[of u "[]" "is"] by auto
            show ?thesis
            proof (cases "aeconv ob u'")
              case True
              with h ph io ri lk rd have "r = Ok (iTs, itms)" by (simp add: return_def)
              with prems(9,12,13) show ?thesis by (auto simp: e)
            next
              case False
              with h ph io ri lk rd have "r = Err Match" by (simp add: raise_def)
              then show ?thesis by auto
            qed
          qed
        qed
      next
        case nV: False
        obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
        have obc: "ob = list_comb oh oargs" by (rule strip_comb_list_comb[OF so])
        have oa: "\<forall>q\<in>set oargs. proper q \<and> (\<forall>T\<in>ctys q. wft ar T)" "\<forall>T\<in>ctys oh. wft ar T"
          using prems(3,6) by (auto simp: obc proper_list_comb ctys_list_comb)
        have pat_args: "\<forall>p\<in>set pargs. ppat p" if "ppat pt"
          using ppat_spine[OF that[unfolded ptc] phh] oA nV pA by (auto simp: ptc)
        have rf_args: "\<forall>q\<in>set oargs. rfree q" if "rfree ob" using that by (simp add: obc rfree_list_comb)
        note h = h[simplified nV if_False so Let_def prod.case]
        text \<open>The arguments, after a successful comparison of the heads:\<close>
        have args: "(\<exists>env'. r = Ok env' \<and> tsorts (fst env') A \<and> vagree (snd env') V \<and> mte_ok (snd env')) \<or>
            (\<exists>ex. r = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)))"
          if hd: "handle (zip_eq pargs oargs \<bind> (\<lambda>ps. foldM (\<lambda>(p, q). fm alg binders p q) ps e0))
              (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) = Some r"
            and inv: "tsorts (fst e0) A \<and> vagree (snd e0) V \<and> mte_ok (snd e0)"
          for e0
        proof -
          obtain rz where z: "zip_eq pargs oargs = Some rz" using zip_eq_term by blast
          from zip_eq_exn[OF z] show ?thesis
          proof (elim disjE conjE)
            assume rz: "rz = Ok (zip pargs oargs)"
            from hd z rz obtain rf where f: "foldM (\<lambda>(p, q). fm alg binders p q) (zip pargs oargs) e0 = Some rf"
              and hr: "handle (Some rf) (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) = Some r"
              by (cases "foldM (\<lambda>(p, q). fm alg binders p q) (zip pargs oargs) e0") (auto simp: handle_def)
            have "(\<exists>e'. rf = Ok e' \<and> (tsorts (fst e') A \<and> vagree (snd e') V \<and> mte_ok (snd e'))) \<or>
                (\<exists>ex. rf = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)))"
            proof (rule foldM_exn[where I="\<lambda>e. tsorts (fst e) A \<and> vagree (snd e) V \<and> mte_ok (snd e)"
                and P="\<lambda>ex. ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)", OF f inv])
              fix x e r' assume x: "x \<in> set (zip pargs oargs)" and m: "(\<lambda>(p, q). fm alg binders p q) x e = Some r'"
                and ie: "tsorts (fst e) A \<and> vagree (snd e) V \<and> mte_ok (snd e)"
              obtain p q where xpq: "x = (p, q)" by force
              with x have pq: "p \<in> set pargs" "q \<in> set oargs" by (auto dest: set_zip_leftD set_zip_rightD)
              have m': "fm alg binders p q e = Some r'" using m by (simp add: xpq)
              have "(\<exists>e'. r' = Ok e' \<and> tsorts (fst e') A \<and> vagree (snd e') V \<and> mte_ok (snd e')) \<or>
                  (\<exists>ex. r' = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat p \<and> rfree q)))"
                by (rule IH[OF m']) (use pa oa(1) pq ie prems(8,11) in auto)
              with pat_args rf_args pq
              show "(\<exists>e'. r' = Ok e' \<and> (tsorts (fst e') A \<and> vagree (snd e') V \<and> mte_ok (snd e'))) \<or>
                  (\<exists>ex. r' = Err ex \<and> (ex = Match \<or> ex = Pattern \<and> \<not> (ppat pt \<and> rfree ob)))"
                by blast
            qed
            with hr show ?thesis by (auto simp: raise_def)
          next
            assume rz: "rz = Err Unequal_Lengths"
            with hd z have "r = Err Match" by (simp add: raise_def)
            then show ?thesis by auto
          qed
        qed
        note typed = typ_match_m_exn[OF _ _ _ prems(8) prems(9)[unfolded e fst_conv]]
        show ?thesis
        proof (cases ph)
          case ph: (Const a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Const b Tb)
            have w: "wft ar Ta" "wft ar Tb" "tvars Ta \<subseteq> A" using php oa(2) by (simp_all add: ph oh)
            show ?thesis
            proof (cases "a = b")
              case True
              from typed[OF w] show ?thesis
              proof (elim disjE exE conjE)
                fix iTs' assume "typ_match_m alg Ta Tb iTs = Some (Ok iTs')" "tsorts iTs' A"
                with h ph oh True prems(12,13) show ?thesis by (intro args[of "(iTs', itms)"]) (simp_all add: e)
              qed (use h ph oh True in auto)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
          next
            case oh: (Abs b U u)
            have "\<not> rfree ob" using oA by (cases oargs) (auto simp: obc oh rfree_list_comb)
            with h ph oh show ?thesis by (auto simp: raise_def)
          qed (use h ph in \<open>auto simp: raise_def\<close>)
        next
          case ph: (Free a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Free b Tb)
            have w: "wft ar Ta" "wft ar Tb" "tvars Ta \<subseteq> A" using php oa(2) by (simp_all add: ph oh)
            show ?thesis
            proof (cases "a = b")
              case True
              from typed[OF w] show ?thesis
              proof (elim disjE exE conjE)
                fix iTs' assume "typ_match_m alg Ta Tb iTs = Some (Ok iTs')" "tsorts iTs' A"
                with h ph oh True prems(12,13) show ?thesis by (intro args[of "(iTs', itms)"]) (simp_all add: e)
              qed (use h ph oh True in auto)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
          next
            case oh: (Abs b U u)
            have "\<not> rfree ob" using oA by (cases oargs) (auto simp: obc oh rfree_list_comb)
            with h ph oh show ?thesis by (auto simp: raise_def)
          qed (use h ph in \<open>auto simp: raise_def\<close>)
        next
          case ph: (Bound i)
          show ?thesis
          proof (cases oh)
            case oh: (Bound j)
            show ?thesis
            proof (cases "i = j")
              case True
              with h ph oh prems(9,12,13) show ?thesis by (intro args[of env]) (simp_all add: e)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
          next
            case oh: (Abs b U u)
            have "\<not> rfree ob" using oA by (cases oargs) (auto simp: obc oh rfree_list_comb)
            with h ph oh show ?thesis by (auto simp: raise_def)
          qed (use h ph in \<open>auto simp: raise_def\<close>)
        next
          case ph: (Abs a T t)
          have "\<not> rfree pt" using pA by (cases pargs) (auto simp: ptc ph rfree_list_comb)
          with h ph ppat_rfree show ?thesis by (auto simp: raise_def)
        qed (use nV phh in auto)
      qed
    qed
  qed
qed



subsection \<open>First-order matching\<close>

lemma fo_mtch_exn:
  assumes "fo_mtch alg' inAbs env pt ob = Some r"
  shows "\<And>Ts U. alg' = alg \<Longrightarrow> \<forall>T\<in>tys pt. wft ar T \<Longrightarrow> has_type W Ts ob U \<Longrightarrow>
    \<forall>T\<in>tys ob \<union> set Ts. wft ar T \<Longrightarrow> (\<not> inAbs \<longrightarrow> no_loose_bound (tr ob) 0) \<Longrightarrow>
    tvs pt \<subseteq> A \<Longrightarrow> scons A \<Longrightarrow> tsorts (fst env) A \<Longrightarrow> vtys pt \<subseteq> V \<Longrightarrow> vfun V \<Longrightarrow>
    vagree (snd env) V \<Longrightarrow>
    (\<exists>env'. r = Ok env' \<and> tsorts (fst env') A \<and> vagree (snd env') V) \<or> r = Err Match"
  using assms
proof (induction alg' inAbs env pt ob r rule: fo_mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' inAbs env pt ob r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" using prems by simp
  note h = "1.hyps"[unfolded alg' e Let_def prod.case]
  note IH = "1.IH"[OF _ refl]
  note typed = typ_match_m_exn[OF _ _ _ prems(7) prems(8)[unfolded e fst_conv]]
  have pob: "proper ob" by (rule has_type_proper[OF prems(3)])
  have e0: "tsorts iTs A" "vagree itms V" using prems(8,11) by (simp_all add: e)
  show ?case
  proof (cases "is_Var pt")
    case True
    then obtain ixn T where pt: "pt = pterm.Var ixn T" by (cases pt) auto
    show ?thesis
    proof (cases "inAbs \<and> is_open ob")
      case True
      with h pt show ?thesis by (simp add: raise_def)
    next
      case False
      with prems(5) closed_iff[OF pob] have clo: "no_loose_bound (tr ob) 0" by blast
      have tV: "(ixn, T) \<in> V" using prems(9) by (simp add: pt)
      show ?thesis
      proof (cases "vt_lookup itms ixn")
        case None
        then have lk: "lookup1 itms ixn T = Some (Ok None)" by (simp add: lookup1_def return_def)
        have "has_type W [] ob U" using has_type_strengthen[of W "[]" Ts ob U] prems(3) clo by simp
        then have ft: "fastype_of ob = Some (Ok U)" and wU: "wft ar U"
          using fastype_of_typed[of W "[]" ob] has_type_wft[of W "[]" ob U] prems(4)
          by (auto simp: fastype_of_def return_def)
        have wT: "wft ar T" "tvars T \<subseteq> A" using prems(2,6) by (simp_all add: pt)
        from typed[OF wT(1) wU wT(2)] show ?thesis
        proof (elim disjE exE conjE)
          fix iTs' assume tm: "typ_match_m alg T U iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
          have up: "update_new (ixn, (T, ob)) itms = Some (Ok (vt_update (ixn, (T, ob)) itms))"
            using None by (simp add: update_new_def vt_defined_lookup return_def)
          have "r = Ok (iTs', vt_update (ixn, (T, ob)) itms)"
            using h pt False lk ft tm up by (simp add: return_def)
          moreover have "vagree (vt_update (ixn, (T, ob)) itms) V"
            using vagree_update[OF prems(11)[unfolded e snd_conv] prems(10) tV] .
          ultimately show ?thesis using ts by simp
        next
          assume "typ_match_m alg T U iTs = Some (Err Match)"
          with h pt False lk ft show ?thesis by simp
        qed
      next
        case (Some b)
        then obtain U' u where b: "vt_lookup itms ixn = Some (U', u)" by (cases b) auto
        with prems(11) tV have "U' = T" by (auto simp: e vagree_def)
        with b have lk: "lookup1 itms ixn T = Some (Ok (Some u))" by (simp add: lookup1_def return_def)
        show ?thesis
          using h pt False lk prems(8,11) by (cases "aeconv ob u") (auto simp: e return_def raise_def)
      qed
    qed
  next
    case nV: False
    note h = h[simplified nV if_False]
    have Abs_ob: "?thesis" if ob: "ob = pterm.Abs b U' u" and
      m: "fm alg True (iTs, itms) (incr pt $ Bound 0) u = Some r" for b U' u
    proof -
      from prems(3) obtain U'' where "has_type W (U' # Ts) u U''" by (auto simp: ob elim: has_type_elims)
      from IH[OF m _ this] prems e0 show ?thesis by (simp add: ob)
    qed
    show ?thesis
    proof (cases pt)
      case pt: (Const a T)
      show ?thesis
      proof (cases ob)
        case ob: (Const b U')
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,4,6) by (simp_all add: pt ob)
        show ?thesis
        proof (cases "a = b")
          case True
          from typed[OF w] show ?thesis
          proof (elim disjE exE conjE)
            fix iTs' assume tm: "typ_match_m alg T U' iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
            with h pt ob True have "r = Ok (iTs', itms)" by (simp del: ok_typ_match_m add: return_def)
            with ts prems(11) show ?thesis by (simp add: e)
          next
            assume "typ_match_m alg T U' iTs = Some (Err Match)"
            with h pt ob True show ?thesis by (simp del: ok_typ_match_m)
          qed
        qed (use h pt ob in \<open>simp add: raise_def\<close>)
      next
        case ob: (Abs b U' u)
        with h pt show ?thesis by (intro Abs_ob[OF ob]) simp
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    next
      case pt: (Free a T)
      show ?thesis
      proof (cases ob)
        case ob: (Free b U')
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,4,6) by (simp_all add: pt ob)
        show ?thesis
        proof (cases "a = b")
          case True
          from typed[OF w] show ?thesis
          proof (elim disjE exE conjE)
            fix iTs' assume tm: "typ_match_m alg T U' iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
            with h pt ob True have "r = Ok (iTs', itms)" by (simp del: ok_typ_match_m add: return_def)
            with ts prems(11) show ?thesis by (simp add: e)
          next
            assume "typ_match_m alg T U' iTs = Some (Err Match)"
            with h pt ob True show ?thesis by (simp del: ok_typ_match_m)
          qed
        qed (use h pt ob in \<open>simp add: raise_def\<close>)
      next
        case ob: (Abs b U' u)
        with h pt show ?thesis by (intro Abs_ob[OF ob]) simp
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    next
      case pt: (Bound i)
      show ?thesis
      proof (cases ob)
        case ob: (Bound j)
        show ?thesis using h pt ob prems(8,11) by (auto simp: e return_def raise_def split: if_splits)
      next
        case ob: (Abs b U' u)
        with h pt show ?thesis by (intro Abs_ob[OF ob]) simp
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    next
      case pt: (Abs a T t)
      show ?thesis
      proof (cases ob)
        case ob: (Abs b U' u)
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,4,6) by (simp_all add: pt ob)
        from prems(3) obtain U'' where tu: "has_type W (U' # Ts) u U''" by (auto simp: ob elim: has_type_elims)
        from typed[OF w] show ?thesis
        proof (elim disjE exE conjE)
          fix iTs' assume tm: "typ_match_m alg T U' iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
          with h pt ob have m: "fm alg True (iTs', itms) t u = Some r" by (simp del: ok_typ_match_m)
          from IH[OF m _ tu] prems ts e0 show ?thesis by (simp add: pt ob)
        qed (use h pt ob in \<open>simp del: ok_typ_match_m\<close>)
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    next
      case pt: (App f t)
      show ?thesis
      proof (cases ob)
        case ob: (App g u)
        from prems(3) obtain T' where tg: "has_type W Ts g (T' \<rightarrow>\<^sub>T U)" and tu: "has_type W Ts u T'"
          by (auto simp: ob elim: has_type_elims)
        from h pt ob obtain r1 where m1: "fm alg inAbs (iTs, itms) f g = Some r1"
          and rest: "(case r1 of Ok e1 \<Rightarrow> fm alg inAbs e1 t u | Err ex \<Rightarrow> Some (Err ex)) = Some r"
          by (auto simp: bindM_def split: option.splits)
        from IH[OF m1 _ tg] prems have "(\<exists>e1. r1 = Ok e1 \<and> tsorts (fst e1) A \<and> vagree (snd e1) V) \<or> r1 = Err Match"
          by (auto simp: pt ob e)
        then show ?thesis
        proof (elim disjE exE conjE)
          fix e1 assume r1: "r1 = Ok e1" and ts: "tsorts (fst e1) A" "vagree (snd e1) V"
          with rest have m2: "fm alg inAbs e1 t u = Some r" by simp
          from IH[OF m2 _ tu] prems ts show ?thesis by (auto simp: pt ob)
        qed (use rest in simp)
      next
        case ob: (Abs b U' u)
        with h pt show ?thesis by (intro Abs_ob[OF ob]) simp
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    qed (use nV in simp)
  qed
qed
end

end
