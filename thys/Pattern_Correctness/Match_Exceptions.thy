section \<open>Exceptions of Matching\<close>

theory Match_Exceptions
  imports Match_Termination
begin

context pure_sig
begin

text \<open>
  On well-formed inputs, higher-order matching fails only with \<open>Match\<close> or \<open>Pattern\<close>, and
  first-order matching only with \<open>Match\<close>.
\<close>

lemma bindM_Ok [simp]: "bindM (Some (Ok x)) f = f x" and bindM_Err [simp]: "bindM (Some (Err ex)) f = Some (Err ex)"
  and handle_Ok [simp]: "handle (Some (Ok x)) h = Some (Ok x)" and handle_Err [simp]: "handle (Some (Err ex)) h = h ex"
  by (simp_all add: bindM_def handle_def)

subsection \<open>Terms\<close>

text \<open>The type variables of all types in a term:\<close>

definition ptvs :: "pterm \<Rightarrow> (indexname \<times> psort) set" where
  "ptvs t = \<Union> (tvars ` typs t)"

lemma ptvs_simps [simp]:
  "ptvs (s $ t) = ptvs s \<union> ptvs t" "ptvs (Abs a T t) = tvars T \<union> ptvs t"
  "ptvs (Const c T) = tvars T" "ptvs (Free y T) = tvars T" "ptvs (Var x T) = tvars T" "ptvs (Bound i) = {}"
  "ptvs (incr t) = ptvs t"
  by (auto simp: ptvs_def typs_incr)

lemma ptvs_apps: "ptvs (s \<degree>\<degree> ts) = ptvs s \<union> \<Union> (ptvs ` set ts)"
  by (auto simp: ptvs_def typs_apps_m)

text \<open>Bound variables have nonnegative indices:\<close>

fun nbounds :: "pterm \<Rightarrow> bool" where
  "nbounds (Bound i) \<longleftrightarrow> 0 \<le> i"
| "nbounds (Abs _ _ t) \<longleftrightarrow> nbounds t"
| "nbounds (s $ t) \<longleftrightarrow> nbounds s \<and> nbounds t"
| "nbounds _ \<longleftrightarrow> True"

lemma nbounds_incr: "nbounds (incr t) \<longleftrightarrow> nbounds t"
proof -
  have "0 \<le> d \<Longrightarrow> nbounds (incr_aux d t) \<longleftrightarrow> nbounds t" for d
    by (induction d t rule: incr_aux.induct) (auto simp: integer_arith)
  then show ?thesis by (simp add: incr_def)
qed

lemma nbounds_apps: "nbounds (s \<degree>\<degree> ts) \<longleftrightarrow> nbounds s \<and> (\<forall>t\<in>set ts. nbounds t)"
  by (induction ts arbitrary: s) auto

lemma typing_nbounds: "e \<turnstile> t : T \<Longrightarrow> nbounds t"
  by (induction rule: typing.induct) auto

lemma typing_tvars:
  "e \<turnstile> t : T \<Longrightarrow> tvars T \<subseteq> ptvs t \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 t i}. tvars (e i))"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  have "tvars ((e\<langle>0:T\<rangle>) i) \<subseteq> tvars T \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 (Abs a T t) i}. tvars (e i))"
    if "0 \<le> i" "loose_bvar1 t i" for i
  proof (cases "i = 0")
    case False
    with that have "0 \<le> i - 1" "loose_bvar1 (Abs a T t) (i - 1)" by (simp_all add: integer_arith)
    with False that(1) show ?thesis by (auto simp: integer_arith)
  qed simp
  with Abs.IH show ?case by fastforce
qed auto

text \<open>Each variable has a unique type, also in the bindings of an environment:\<close>

definition vfun :: "(indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vfun V \<longleftrightarrow> (\<forall>x T T'. (x, T) \<in> V \<longrightarrow> (x, T') \<in> V \<longrightarrow> T = T')"

definition vagree :: "tenv \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> bool" where
  "vagree te V \<longleftrightarrow> (\<forall>x T U u. (x, T) \<in> V \<longrightarrow> vt_lookup te x = Some (U, u) \<longrightarrow> U = T)"

text \<open>Each type variable has a unique sort, also in the bindings of a type environment:\<close>

definition tsorts :: "tyenv \<Rightarrow> (indexname \<times> psort) set \<Rightarrow> bool" where
  "tsorts tye A \<longleftrightarrow> (\<forall>v S S' U. (v, S) \<in> A \<longrightarrow> vt_lookup tye v = Some (S', U) \<longrightarrow> S' = S)"

text \<open>The bindings are closed:\<close>

definition bclosed :: "tenv \<Rightarrow> bool" where
  "bclosed te \<longleftrightarrow> (\<forall>x U u. vt_lookup te x = Some (U, u) \<longrightarrow> closed u)"

lemma vagree_update:
  assumes "vagree te V" "vfun V" "(x, T) \<in> V"
  shows "vagree (vt_update (x, (T, u)) te) V"
  unfolding vagree_def
proof (intro allI impI)
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
    with yT assms(1) show ?thesis unfolding vagree_def by blast
  qed
qed


subsection \<open>Auxiliary functions\<close>

lemma ints_of_exn: "ints_of ts = Some r \<Longrightarrow> (\<exists>is. r = Ok is) \<or> r = Err Pattern"
  by (induction ts arbitrary: r rule: ints_of.induct)
    (auto simp: return_def raise_def bindM_def split: option.splits res.splits if_splits)

lemma zip_eq_exn:
  "zip_eq xs ys = Some r \<Longrightarrow>
    length xs = length ys \<and> r = Ok (zip xs ys) \<or> length xs \<noteq> length ys \<and> r = Err Unequal_Lengths"
  by (induction xs ys arbitrary: r rule: zip_eq.induct)
    (auto simp: return_def raise_def bindM_def split: option.splits res.splits)

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

lemma closed_bind:
  assumes "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is"
  shows "closed (abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 t))"
proof (rule closed_abs_list)
  show "\<not> loose_bvar (rename (bidx is) 0 t) (ilength (map (\<lambda>i. bs ! nat_of_integer i) is))"
  proof
    assume "loose_bvar (rename (bidx is) 0 t) (ilength (map (\<lambda>i. bs ! nat_of_integer i) is))"
    then obtain j where j: "j \<ge> ilength is" "loose_bvar1 (rename (bidx is) 0 t) j"
      by (auto simp: loose_bvar_iff)
    have "0 \<le> j" using ilength_nonneg[of "is"] j(1) by (rule order_trans)
    then obtain k where "0 \<le> k" "loose_bvar1 t k" "j = bidx is k"
      using loose_bvar1_rename[OF nonneg_bidx, of "is" 0 t j] j(2) by auto
    with assms bidx_less j(1) show False by force
  qed
qed

lemma match_bind_exn:
  assumes "match_bind itms bs x T is t = Some r" "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    "vt_lookup itms x = None"
  shows "(\<exists>itms'. r = Ok itms') \<or> r = Err Match"
proof (cases "\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k \<in> set is")
  case True
  have up: "ok (update_new (x, (T, u)) itms) (vt_update (x, (T, u)) itms)" for u
    using assms(3) by (simp add: ok_update_new)
  show ?thesis
  proof (cases "is = []")
    case True
    with \<open>\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k \<in> set is\<close> have "set (loose_bnos t) = {}"
      using set_loose_bnos[of t] by auto
    then have "loose_bnos t = []" by simp
    with True assms(1) up[of t] show ?thesis by (auto simp: match_bind_def)
  next
    case False
    have sb: "subset (loose_bnos t) is" using True by (auto simp: subset_iff_set set_loose_bnos)
    have "\<exists>t'. ok (if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) t'"
      using ok_mapbnd_idx[of t 0 "is"] True by auto
    then obtain t' where t': "ok (if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) t'" ..
    have mk: "ok (mkabs bs is t') (abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t')"
      using assms(2) by (simp add: ok_mkabs)
    have "ok (match_bind itms bs x T is t) (vt_update (x, (T, abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) t')) itms)"
      using t' mk up False sb by (simp add: match_bind_def Let_def del: mapbnd.simps)
    with assms(1) show ?thesis by auto
  qed
next
  case False
  then obtain k where k: "0 \<le> k" "loose_bvar1 t k" "k \<notin> set is" by blast
  then have "k \<in> set (loose_bnos t)" by (simp add: set_loose_bnos)
  with k(3) have "\<not> subset (loose_bnos t) is" "loose_bnos t \<noteq> []"
    by (auto simp: subset_iff_set)
  with assms(1) show ?thesis by (auto simp: match_bind_def Let_def raise_def split: if_splits)
qed

lemma red_other:
  "\<not> (is_Abs t \<and> is \<noteq> []) \<Longrightarrow>
    red t is js = (if is = [] \<and> js = [] then return t else do {t' \<leftarrow> mapbnd (nth js) 0 t; return (app t' is)})"
  by (cases t; cases "is"; cases js) simp_all

lemma red_other_ok:
  assumes "\<not> (is_Abs t \<and> is \<noteq> [])" "\<not> loose_bvar t (ilength js)"
  shows "\<exists>u. ok (red t is js) u"
proof -
  have "ok (mapbnd (nth js) 0 t) (rename (bren js) 0 t)"
  proof (rule mapbnd_rename)
    fix k assume "0 \<le> k" "loose_bvar1 t (k + 0)"
    moreover from this assms(2) have "k < ilength js" using loose_bvar1_less by simp
    ultimately show "ok (nth js k) (bren js k)" by (simp add: ok_nth bren_nth)
  qed
  then show ?thesis by (auto simp: red_other[OF assms(1)] simp del: mapbnd.simps)
qed

lemma red_ok: "\<not> loose_bvar t (ilength js) \<Longrightarrow> \<exists>u. ok (red t is js) u"
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
    proof (intro allI impI)
      fix v S S' V assume vS: "(v, S) \<in> A" and l: "vt_lookup tye' v = Some (S', V)"
      show "S' = S"
      proof (cases "vt_lookup tye v")
        case None
        with s(4)[OF l] have "(v, S') \<in> tvars T" by blast
        with vS assms(3,4) show ?thesis unfolding scons_def by blast
      next
        case (Some b)
        have "vt_lookup tye' v = Some b" using s(1) Some unfolding textends_def by (cases b, cases v) blast
        with l Some have "vt_lookup tye v = Some (S', V)" by simp
        with vS assms(5) show ?thesis unfolding tsorts_def by blast
      qed
    qed
    with tm show ?thesis by (simp add: typ_match_m_def return_def)
  qed (simp add: typ_match_m_def raise_def)
qed


subsection \<open>Higher-order matching\<close>

lemma mtch_exn:
  assumes "mtch alg' bs pt ob env = Some r"
  shows "alg' = alg \<Longrightarrow> nbounds pt \<Longrightarrow> \<not> loose_bvar pt (ilength bs) \<Longrightarrow>
    \<forall>T\<in>typs pt. wft ar T \<Longrightarrow> \<forall>T\<in>typs ob. wft ar T \<Longrightarrow> ptvs pt \<subseteq> A \<Longrightarrow> scons A \<Longrightarrow>
    tsorts (fst env) A \<Longrightarrow> vars pt \<subseteq> V \<Longrightarrow> vfun V \<Longrightarrow> vagree (snd env) V \<Longrightarrow> bclosed (snd env) \<Longrightarrow>
    (\<exists>env'. r = Ok env' \<and> tsorts (fst env') A \<and> vagree (snd env') V \<and> bclosed (snd env')) \<or>
    (\<exists>ex. r = Err ex \<and> (ex = Match \<or> ex = Pattern))"
  using assms
proof (induction alg' bs pt ob env r rule: mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' bs pt ob env r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" using prems by simp
  note h = "1.hyps"[unfolded alg']
  note IH = "1.IH"[OF _ refl]
  show ?case
  proof (cases "is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = Abs ns Ts ts" by (cases pt) auto
    have ts: "nbounds ts" "\<not> loose_bvar ts (ilength (b # bs))" "\<forall>T\<in>typs ts. wft ar T"
      "ptvs ts \<subseteq> A" "vars ts \<subseteq> V" for b
      using prems by (simp_all add: pt)
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from h have m: "fm alg ((nt, Tt) # bs) ts tt env = Some r" by (simp add: e pt ob)
      from IH[OF m ts(1,2)] prems ts show ?thesis by (simp add: ob)
    next
      case oA: False
      have "\<forall>(v, S)\<in>tvars Ts. \<forall>S' U. vt_lookup iTs v = Some (S', U) \<longrightarrow> S' = S"
        using prems(6,8) unfolding pt e tsorts_def by auto
      then obtain Tt where st: "ok (subst_type iTs Ts) Tt" using subst_type_ok by blast
      from h oA have m: "fm alg ((ns, Tt) # bs) ts (incr ob $ Bound 0) env = Some r"
        by (simp add: e pt st)
      have q: "\<forall>T\<in>typs (incr ob $ Bound 0). wft ar T" using prems(5) by (simp add: typs_incr)
      from IH[OF m ts(1,2) ts(3) q] prems ts show ?thesis by simp
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from h pA have m: "fm alg ((nt, Tt) # bs) (incr pt $ Bound 0) tt env = Some r"
        by (simp add: e ob)
      have il: "incr pt = lift pt 0" by (simp add: incr_def incr_aux_lift)
      have p: "nbounds (incr pt $ Bound 0)" "\<not> loose_bvar (incr pt $ Bound 0) (ilength ((nt, Tt) # bs))"
        "\<forall>T\<in>typs (incr pt $ Bound 0). wft ar T" "ptvs (incr pt $ Bound 0) \<subseteq> A"
        "vars (incr pt $ Bound 0) \<subseteq> V"
        using prems(2,3,4,6,9) loose_bvar_lift[of 0 "ilength bs" pt] ilength_nonneg[of bs]
        by (simp_all add: nbounds_incr il typs_incr vars_incr integer_arith)
      from IH[OF m p(1,2)] prems p show ?thesis by (simp add: ob)
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      have ptc: "pt = ph \<degree>\<degree> pargs" by (rule mt_strip_comb_apps[OF sp])
      have phh: "\<not> (\<exists>f u. ph = f $ u)" by (rule strip_comb_head[OF sp])
      have pa: "\<forall>p\<in>set pargs. nbounds p \<and> \<not> loose_bvar p (ilength bs) \<and> (\<forall>T\<in>typs p. wft ar T) \<and>
          ptvs p \<subseteq> A \<and> vars p \<subseteq> V"
        using prems(2,3,4,6,9)
        by (auto simp: ptc nbounds_apps loose_bvar_apps typs_apps_m ptvs_apps vars_apps)
      have php: "\<forall>T\<in>typs ph. wft ar T" "ptvs ph \<subseteq> A" "vars ph \<subseteq> V"
        using prems(4,6,9) by (auto simp: ptc typs_apps_m ptvs_apps vars_apps)
      note h = h[unfolded e, simplified pA oA if_False sp Let_def prod.case]
      show ?thesis
      proof (cases "is_Var ph")
        case True
        then obtain ixn T where ph: "ph = Var ixn T" by (cases ph) auto
        obtain ri where io: "ints_of pargs = Some ri" using mt_ints_of by blast
        from ints_of_exn[OF io] show ?thesis
        proof (elim disjE exE)
          assume ri: "ri = Err Pattern"
          with h ph io show ?thesis by auto
        next
          fix "is" assume ri: "ri = Ok is"
          then have pargs: "pargs = map Bound is" and dis: "distinct is" using io by (simp_all add: ok_ints_of)
          have lt: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
            using pa by (auto simp: pargs)
          have tV: "(ixn, T) \<in> V" using php(3) by (simp add: ph)
          show ?thesis
          proof (cases "vt_lookup itms ixn")
            case None
            then have lk: "lookup1 itms ixn T = Some (Ok None)" by (simp add: lookup1_def return_def)
            obtain rm where mb: "match_bind itms bs ixn T is ob = Some rm" using match_bind_term by blast
            from match_bind_exn[OF mb lt None] show ?thesis
            proof (elim disjE exE)
              fix itms' assume rm: "rm = Ok itms'"
              note b = ok_match_bind[OF mb[unfolded rm] dis]
              have "vagree itms' V"
                using vagree_update[OF prems(11)[unfolded e snd_conv] prems(10) tV] by (simp add: b(2))
              moreover have "bclosed itms'"
                using prems(12) closed_bind[OF b(3)] by (auto simp: b(2) e bclosed_def)
              moreover have "r = Ok (iTs, itms')" using h ph io ri lk mb rm by (simp add: return_def)
              ultimately show ?thesis using prems(8) by (auto simp: e)
            next
              assume "rm = Err Match"
              with h ph io ri lk mb have "r = Err Match" by simp
              then show ?thesis by auto
            qed
          next
            case (Some b)
            then obtain U u where b: "vt_lookup itms ixn = Some (U, u)" by (cases b) auto
            with prems(11) tV have "U = T" unfolding e vagree_def by blast
            with b have lk: "lookup1 itms ixn T = Some (Ok (Some u))" by (simp add: lookup1_def return_def)
            have "closed u" using prems(12) b unfolding e bclosed_def by blast
            then obtain u' where rd: "red u is [] = Some (Ok u')" using red_ok[of u "[]" "is"]
              by (auto simp: closed_def)
            show ?thesis
            proof (cases "aeconv ob u'")
              case True
              with h ph io ri lk rd have "r = Ok (iTs, itms)" by (simp add: return_def)
              with prems(8,11,12) show ?thesis by (auto simp: e)
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
        have obc: "ob = oh \<degree>\<degree> oargs" by (rule mt_strip_comb_apps[OF so])
        have oa: "\<forall>q\<in>set oargs. \<forall>T\<in>typs q. wft ar T" "\<forall>T\<in>typs oh. wft ar T"
          using prems(5) by (auto simp: obc typs_apps_m)
        note h = h[simplified nV if_False so Let_def prod.case]
        text \<open>The arguments, after a successful comparison of the heads:\<close>
        have args: "(\<exists>env'. r = Ok env' \<and> tsorts (fst env') A \<and> vagree (snd env') V \<and> bclosed (snd env')) \<or>
            (\<exists>ex. r = Err ex \<and> (ex = Match \<or> ex = Pattern))"
          if hd: "handle (zip_eq pargs oargs \<bind> (\<lambda>ps. foldM (\<lambda>(p, q). fm alg bs p q) ps e0))
              (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) = Some r"
            and inv: "tsorts (fst e0) A \<and> vagree (snd e0) V \<and> bclosed (snd e0)"
          for e0
        proof -
          obtain rz where z: "zip_eq pargs oargs = Some rz" using zip_eq_term by blast
          from zip_eq_exn[OF z] show ?thesis
          proof (elim disjE conjE)
            assume rz: "rz = Ok (zip pargs oargs)"
            from hd z rz obtain rf where f: "foldM (\<lambda>(p, q). fm alg bs p q) (zip pargs oargs) e0 = Some rf"
              and hr: "handle (Some rf) (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) = Some r"
              by (cases "foldM (\<lambda>(p, q). fm alg bs p q) (zip pargs oargs) e0") (auto simp: handle_def)
            have "(\<exists>e'. rf = Ok e' \<and> (tsorts (fst e') A \<and> vagree (snd e') V \<and> bclosed (snd e'))) \<or>
                (\<exists>ex. rf = Err ex \<and> (ex = Match \<or> ex = Pattern))"
            proof (rule foldM_exn[where I="\<lambda>e. tsorts (fst e) A \<and> vagree (snd e) V \<and> bclosed (snd e)"
                and P="\<lambda>ex. ex = Match \<or> ex = Pattern", OF f inv])
              fix x e r' assume x: "x \<in> set (zip pargs oargs)" and m: "(\<lambda>(p, q). fm alg bs p q) x e = Some r'"
                and ie: "tsorts (fst e) A \<and> vagree (snd e) V \<and> bclosed (snd e)"
              obtain p q where xpq: "x = (p, q)" by force
              with x have pq: "p \<in> set pargs" "q \<in> set oargs" by (auto dest: set_zip_leftD set_zip_rightD)
              have m': "fm alg bs p q e = Some r'" using m by (simp add: xpq)
              show "(\<exists>e'. r' = Ok e' \<and> (tsorts (fst e') A \<and> vagree (snd e') V \<and> bclosed (snd e'))) \<or>
                  (\<exists>ex. r' = Err ex \<and> (ex = Match \<or> ex = Pattern))"
                by (rule IH[OF m']) (use pa oa(1) pq ie prems(7,10) in auto)
            qed
            with hr show ?thesis by (auto simp: raise_def)
          next
            assume rz: "rz = Err Unequal_Lengths"
            with hd z have "r = Err Match" by (simp add: raise_def)
            then show ?thesis by auto
          qed
        qed
        note typed = typ_match_m_exn[OF _ _ _ prems(7) prems(8)[unfolded e fst_conv]]
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
                with h ph oh True prems(11,12) show ?thesis by (intro args[of "(iTs', itms)"]) (simp_all add: e)
              qed (use h ph oh True in auto)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
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
                with h ph oh True prems(11,12) show ?thesis by (intro args[of "(iTs', itms)"]) (simp_all add: e)
              qed (use h ph oh True in auto)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
          qed (use h ph in \<open>auto simp: raise_def\<close>)
        next
          case ph: (Bound i)
          show ?thesis
          proof (cases oh)
            case oh: (Bound j)
            show ?thesis
            proof (cases "i = j")
              case True
              with h ph oh prems(8,11,12) show ?thesis by (intro args[of env]) (simp_all add: e)
            qed (use h ph oh in \<open>auto simp: raise_def\<close>)
          qed (use h ph in \<open>auto simp: raise_def\<close>)
        next
          case ph: (Abs a T t)
          with h show ?thesis by (auto simp: raise_def)
        qed (use nV phh in auto)
      qed
    qed
  qed
qed


subsection \<open>First-order matching\<close>

lemma fo_mtch_exn:
  assumes "fo_mtch alg' inAbs env pt ob = Some r"
  shows "\<And>e U. alg' = alg \<Longrightarrow> \<forall>T\<in>typs pt. wft ar T \<Longrightarrow> e \<turnstile> ob : U \<Longrightarrow> (\<not> inAbs \<longrightarrow> closed ob) \<Longrightarrow>
    ptvs pt \<subseteq> A \<Longrightarrow> scons A \<Longrightarrow> tsorts (fst env) A \<Longrightarrow> vars pt \<subseteq> V \<Longrightarrow> vfun V \<Longrightarrow>
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
  note typed = typ_match_m_exn[OF _ _ _ prems(6) prems(7)[unfolded e fst_conv]]
  have wo: "\<forall>T\<in>typs ob. wft ar T" using typing_typs_cert[OF prems(3)] by (auto simp: cert_wft)
  have e0: "tsorts iTs A" "vagree itms V" using prems(7,10) by (simp_all add: e)
  show ?case
  proof (cases "is_Var pt")
    case True
    then obtain ixn T where pt: "pt = Var ixn T" by (cases pt) auto
    show ?thesis
    proof (cases "inAbs \<and> is_open ob")
      case True
      with h pt show ?thesis by (simp add: raise_def)
    next
      case False
      with prems(4) have clo: "closed ob" by (auto simp: is_open_closed)
      have tV: "(ixn, T) \<in> V" using prems(8) by (simp add: pt)
      show ?thesis
      proof (cases "vt_lookup itms ixn")
        case None
        then have lk: "lookup1 itms ixn T = Some (Ok None)" by (simp add: lookup1_def return_def)
        have ft: "fastype_of ob = Some (Ok U)" using fastype_of_closed[OF prems(3) clo] by (simp add: return_def)
        have wU: "wft ar U" using typing_cert_closed[OF prems(3) clo] by (rule cert_wft)
        have wT: "wft ar T" "tvars T \<subseteq> A" using prems(2,5) by (simp_all add: pt)
        from typed[OF wT(1) wU wT(2)] show ?thesis
        proof (elim disjE exE conjE)
          fix iTs' assume tm: "typ_match_m alg T U iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
          have up: "update_new (ixn, (T, ob)) itms = Some (Ok (vt_update (ixn, (T, ob)) itms))"
            using None by (simp add: update_new_def vt_defined_lookup return_def)
          have "r = Ok (iTs', vt_update (ixn, (T, ob)) itms)"
            using h pt False lk ft tm up by (simp add: return_def)
          moreover have "vagree (vt_update (ixn, (T, ob)) itms) V"
            using vagree_update[OF prems(10)[unfolded e snd_conv] prems(9) tV] .
          ultimately show ?thesis using ts by simp
        next
          assume "typ_match_m alg T U iTs = Some (Err Match)"
          with h pt False lk ft show ?thesis by simp
        qed
      next
        case (Some b)
        then obtain U' u where b: "vt_lookup itms ixn = Some (U', u)" by (cases b) auto
        with prems(10) tV have "U' = T" unfolding e vagree_def by blast
        with b have lk: "lookup1 itms ixn T = Some (Ok (Some u))" by (simp add: lookup1_def return_def)
        show ?thesis
          using h pt False lk prems(7,10) by (cases "aeconv ob u") (auto simp: e return_def raise_def)
      qed
    qed
  next
    case nV: False
    note h = h[simplified nV if_False]
    have Abs_ob: "?thesis" if ob: "ob = Abs b U' u" and
      m: "fm alg True (iTs, itms) (incr pt $ Bound 0) u = Some r" for b U' u
    proof -
      from prems(3) obtain U'' where "e\<langle>0:U'\<rangle> \<turnstile> u : U''" by (auto simp: ob)
      from IH[OF m _ this] prems e0 show ?thesis by (simp add: ob typs_incr vars_incr)
    qed
    show ?thesis
    proof (cases pt)
      case pt: (Const a T)
      show ?thesis
      proof (cases ob)
        case ob: (Const b U')
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,5) wo by (simp_all add: pt ob)
        show ?thesis
        proof (cases "a = b")
          case True
          from typed[OF w] show ?thesis
          proof (elim disjE exE conjE)
            fix iTs' assume tm: "typ_match_m alg T U' iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
            with h pt ob True have "r = Ok (iTs', itms)" by (simp del: ok_typ_match_m add: return_def)
            with ts prems(10) show ?thesis by (simp add: e)
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
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,5) wo by (simp_all add: pt ob)
        show ?thesis
        proof (cases "a = b")
          case True
          from typed[OF w] show ?thesis
          proof (elim disjE exE conjE)
            fix iTs' assume tm: "typ_match_m alg T U' iTs = Some (Ok iTs')" and ts: "tsorts iTs' A"
            with h pt ob True have "r = Ok (iTs', itms)" by (simp del: ok_typ_match_m add: return_def)
            with ts prems(10) show ?thesis by (simp add: e)
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
        show ?thesis using h pt ob prems(7,10) by (auto simp: e return_def raise_def split: if_splits)
      next
        case ob: (Abs b U' u)
        with h pt show ?thesis by (intro Abs_ob[OF ob]) simp
      qed (use h pt in \<open>auto simp: raise_def\<close>)
    next
      case pt: (Abs a T t)
      show ?thesis
      proof (cases ob)
        case ob: (Abs b U' u)
        have w: "wft ar T" "wft ar U'" "tvars T \<subseteq> A" using prems(2,5) wo by (simp_all add: pt ob)
        from prems(3) obtain U'' where tu: "e\<langle>0:U'\<rangle> \<turnstile> u : U''" by (auto simp: ob)
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
        from prems(3) obtain T' where tg: "e \<turnstile> g : T' \<rightarrow>\<^sub>T U" and tu: "e \<turnstile> u : T'"
          by (auto simp: ob)
        from h pt ob obtain r1 where m1: "fm alg inAbs (iTs, itms) f g = Some r1"
          and rest: "(case r1 of Ok e1 \<Rightarrow> fm alg inAbs e1 t u | Err ex \<Rightarrow> Some (Err ex)) = Some r"
          by (auto simp: bindM_def split: option.splits)
        have cl: "\<not> inAbs \<longrightarrow> closed g" "\<not> inAbs \<longrightarrow> closed u" using prems(4) by (auto simp: ob closed_def)
        from IH[OF m1 _ tg] prems cl have "(\<exists>e1. r1 = Ok e1 \<and> tsorts (fst e1) A \<and> vagree (snd e1) V) \<or> r1 = Err Match"
          by (auto simp: pt ob e)
        then show ?thesis
        proof (elim disjE exE conjE)
          fix e1 assume r1: "r1 = Ok e1" and ts: "tsorts (fst e1) A" "vagree (snd e1) V"
          with rest have m2: "fm alg inAbs e1 t u = Some r" by simp
          from IH[OF m2 _ tu] prems ts cl show ?thesis by (auto simp: pt ob)
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
