section \<open>The Range of the Bindings of a Match\<close>

theory Match_Range
  imports "Pattern_Correctness.Match_Sound"
begin

text \<open>
  \<open>Thm.match\<close> turns the bindings of \<open>Pattern.match\<close> into certified types and terms with the
  maximal index and the sorts of the object (and the sorts of the pattern). This needs more than
  \<^theory>\<open>Pattern_Correctness.Match_Sound\<close> states: the variables and type variables of the
  bindings are those of the object, their free type variables are those of the object or the
  pattern, the bound type variables and variables are those of the pattern, and the types bound
  to type variables are certified.
\<close>

fun tfrees :: "ptyp \<Rightarrow> (name \<times> psort) set" where
  "tfrees (Type a Ts) = (\<Union>T\<in>set Ts. tfrees T)"
| "tfrees (TFree a S) = {(a, S)}"
| "tfrees (TVar v S) = {}"

definition ttfrees :: "pterm \<Rightarrow> (name \<times> psort) set" where
  "ttfrees t = (\<Union>U\<in>typs t. tfrees U)"

lemma ttfrees_simps [simp]:
  "ttfrees (s $ t) = ttfrees s \<union> ttfrees t" "ttfrees (Abs a T t) = tfrees T \<union> ttfrees t"
  "ttfrees (Bound i) = {}" "ttfrees (Var x T) = tfrees T" "ttfrees (Const c T) = tfrees T"
  "ttfrees (Free f T) = tfrees T"
  by (auto simp: ttfrees_def)

lemma tvars_tsubst_sub: "(v, S) \<in> tvars T \<Longrightarrow> tvars (\<rho> v S) \<subseteq> tvars (tsubst \<rho> T)"
  by (induction T) auto

lemma tfrees_tsubst_sub: "(v, S) \<in> tvars T \<Longrightarrow> tfrees (\<rho> v S) \<subseteq> tfrees (tsubst \<rho> T)"
  by (induction T) auto

lemma tfrees_tsubst: "tfrees (tsubst \<rho> T) = tfrees T \<union> (\<Union>(v, S)\<in>tvars T. tfrees (\<rho> v S))"
  by (induction T) auto

text \<open>The type of a term is built from the types in it and the types of its loose bound variables:\<close>

context signature
begin

lemma typing_tvars:
  "e \<turnstile> t : T \<Longrightarrow> tvars T \<subseteq> ttvars t \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 t i}. tvars (e i))"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  show ?case
  proof
    fix w assume "w \<in> tvars (T \<rightarrow>\<^sub>T U)"
    then consider "w \<in> tvars T" | "w \<in> tvars U" by auto
    then show "w \<in> ttvars (Abs a T t) \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 (Abs a T t) i}. tvars (e i))"
    proof cases
      case 2
      with Abs.IH obtain i where "w \<in> ttvars t \<or> (0 \<le> i \<and> loose_bvar1 t i \<and> w \<in> tvars ((e\<langle>0:T\<rangle>) i))" by auto
      then show ?thesis by (cases "i = 0") (auto simp: shift_def integer_arith intro: exI[of _ "i - 1"])
    qed simp
  qed
qed auto

lemma typing_tfrees:
  "e \<turnstile> t : T \<Longrightarrow> tfrees T \<subseteq> ttfrees t \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 t i}. tfrees (e i))"
proof (induction rule: typing.induct)
  case (Abs T e t U a)
  show ?case
  proof
    fix w assume "w \<in> tfrees (T \<rightarrow>\<^sub>T U)"
    then consider "w \<in> tfrees T" | "w \<in> tfrees U" by auto
    then show "w \<in> ttfrees (Abs a T t) \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 (Abs a T t) i}. tfrees (e i))"
    proof cases
      case 2
      with Abs.IH obtain i where "w \<in> ttfrees t \<or> (0 \<le> i \<and> loose_bvar1 t i \<and> w \<in> tfrees ((e\<langle>0:T\<rangle>) i))" by auto
      then show ?thesis by (cases "i = 0") (auto simp: shift_def integer_arith intro: exI[of _ "i - 1"])
    qed simp
  qed
qed auto

end

context pure_sig
begin

lemma typing_closed_tvars: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> tvars T \<subseteq> ttvars t"
  using typing_tvars[of e t T] by (auto simp: closed_iff_loose_bvar1)

lemma typing_closed_tfrees: "e \<turnstile> t : T \<Longrightarrow> closed t \<Longrightarrow> tfrees T \<subseteq> ttfrees t"
  using typing_tfrees[of e t T] by (auto simp: closed_iff_loose_bvar1)

end


subsection \<open>The invariant\<close>

locale match_range = pure_sig alg ar ctab for alg ar ctab +
  fixes V :: "(indexname \<times> ptyp) set" and A :: "(indexname \<times> psort) set" and F :: "(name \<times> psort) set"
    and Dx :: "indexname set" and Dv :: "indexname set"
begin

definition trange :: "tyenv \<Rightarrow> bool" where
  "trange tye \<longleftrightarrow> tye_cert tye \<and>
    (\<forall>v S U. vt_lookup tye v = Some (S, U) \<longrightarrow> v \<in> Dv \<and> tvars U \<subseteq> A \<and> tfrees U \<subseteq> F)"

definition mrange :: "match_env \<Rightarrow> bool" where
  "mrange env \<longleftrightarrow> trange (fst env) \<and>
    (\<forall>x T u. vt_lookup (snd env) x = Some (T, u) \<longrightarrow> x \<in> Dx \<and> vars u \<subseteq> V \<and> ttvars u \<subseteq> A \<and> ttfrees u \<subseteq> F)"

lemma typ_match_range:
  assumes m: "ok (typ_match alg T U tye) tye'" and w: "wft ar T" and c: "cert_typ alg ar U"
    and r: "trange tye" and U: "tvars U \<subseteq> A" "tfrees U \<subseteq> F" and T: "fst ` tvars T \<subseteq> Dv"
  shows "trange tye'"
proof -
  note s = typ_match_sound[OF w cert_wft[OF c] m[folded return_def]]
  have "tye_cert tye'" by (rule typ_match_cert[OF m w cert_wft[OF c] c]) (use r in \<open>simp add: trange_def\<close>)
  moreover have "v \<in> Dv \<and> tvars U' \<subseteq> A \<and> tfrees U' \<subseteq> F" if b: "vt_lookup tye' v = Some (S, U')" for v S U'
  proof (cases "vt_lookup tye v")
    case None
    from s(4)[OF b None] have vT: "(v, S) \<in> tvars T" by simp
    have "mtinst tye' v S = U'" using b by (simp add: mtinst_def)
    with tvars_tsubst_sub[OF vT, of "mtinst tye'"] tfrees_tsubst_sub[OF vT, of "mtinst tye'"] s(2) U
    have "tvars U' \<subseteq> A" "tfrees U' \<subseteq> F" by auto
    with vT T show ?thesis by force
  next
    case (Some x)
    from s(1)[unfolded textends_def, rule_format, OF Some] b have "vt_lookup tye v = Some (S, U')"
      by (simp add: Some)
    with r show ?thesis unfolding trange_def by blast
  qed
  ultimately show ?thesis by (auto simp: trange_def)
qed

lemma mrange_update:
  "mrange (tye, te) \<Longrightarrow> trange tye' \<Longrightarrow> x \<in> Dx \<Longrightarrow> vars u \<subseteq> V \<Longrightarrow> ttvars u \<subseteq> A \<Longrightarrow> ttfrees u \<subseteq> F \<Longrightarrow>
    mrange (tye', vt_update (x, (T, u)) te)"
  by (auto simp: mrange_def vt_lookup_update split: if_splits)

lemma mrange_tye: "mrange (tye, te) \<Longrightarrow> trange tye' \<Longrightarrow> mrange (tye', te)"
  by (auto simp: mrange_def)


subsection \<open>First-order matching\<close>

lemma fo_mtch_range:
  assumes "fo_mtch alg' inAbs env pt ob = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env1 \<Longrightarrow> (\<not> inAbs \<longrightarrow> closed ob) \<Longrightarrow> \<forall>T\<in>typs pt. wft ar T \<Longrightarrow>
    e \<turnstile> ob : Ty \<Longrightarrow> vars ob \<subseteq> V \<Longrightarrow> ttvars ob \<subseteq> A \<Longrightarrow> ttfrees ob \<subseteq> F \<Longrightarrow>
    fst ` vars pt \<subseteq> Dx \<Longrightarrow> fst ` ttvars pt \<subseteq> Dv \<Longrightarrow> mrange env \<Longrightarrow> mrange env1"
  using assms
proof (induction alg' inAbs env pt ob r arbitrary: env1 e Ty rule: fo_mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' inAbs instsp pt ob r)
  obtain tyinsts insts where e: "instsp = (tyinsts, insts)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" and r: "r = Ok env1" using prems by simp_all
  have h: "ok (if is_Var pt then
      (case pt of
        Var ixn T \<Rightarrow>
          if inAbs \<and> is_open ob then raise Match
          else do {
            r \<leftarrow> lookup1 insts ixn T;
            case r of
              None \<Rightarrow> do {
                tT \<leftarrow> fastype_of ob;
                tyinsts' \<leftarrow> typ_match_m alg T tT tyinsts;
                insts' \<leftarrow> update_new (ixn, (T, ob)) insts;
                return (tyinsts', insts')}
            | Some u \<Rightarrow> if aeconv ob u then return (tyinsts, insts) else raise Match}
      | _ \<Rightarrow> raise (Failure (STR ''fo_mtch'')))
    else
      (case (pt, ob) of
        (Free a T, Free b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Const a T, Const b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Bound i, Bound j) \<Rightarrow> if i = j then return (tyinsts, insts) else raise Match
      | (Abs _ T t, Abs _ U u) \<Rightarrow> do {
          tyinsts' \<leftarrow> typ_match_m alg T U tyinsts;
          fm alg True (tyinsts', insts) t u}
      | (f $ t, g $ u) \<Rightarrow> do {instsp' \<leftarrow> fm alg inAbs (tyinsts, insts) f g; fm alg inAbs instsp' t u}
      | (_, Abs _ U u) \<Rightarrow> fm alg True (tyinsts, insts) (incr pt $ Bound 0) u
      | _ \<Rightarrow> raise Match)) env1"
    using "1.hyps" unfolding alg' r e Let_def prod.case .
  note IH = "1.IH"[OF _ refl refl]
  have cl: "\<not> inAbs \<longrightarrow> closed ob" and wp: "\<forall>T\<in>typs pt. wft ar T" and ty: "e \<turnstile> ob : Ty"
    and ob: "vars ob \<subseteq> V" "ttvars ob \<subseteq> A" "ttfrees ob \<subseteq> F"
    and pt: "fst ` vars pt \<subseteq> Dx" "fst ` ttvars pt \<subseteq> Dv" and mr: "mrange (tyinsts, insts)"
    using prems by (simp_all add: e)
  have tr: "trange tyinsts" using mr by (simp add: mrange_def)
  have tyo: "\<forall>U\<in>typs ob. cert_typ alg ar U" by (rule typing_typs_cert[OF ty])
  text \<open>A step of type matching against a type of the object:\<close>
  have tmr: "trange tyinsts'"
    if "ok (typ_match alg T U tyinsts) tyinsts'" "T \<in> typs pt" "U \<in> typs ob" for T U tyinsts'
  proof (rule typ_match_range[OF that(1) _ _ tr])
    show "wft ar T" using wp that(2) by blast
    show "cert_typ alg ar U" using tyo that(3) by blast
    show "tvars U \<subseteq> A" "tfrees U \<subseteq> F" using ob(2,3) that(3) by (auto simp: ttvars_def ttfrees_def)
    show "fst ` tvars T \<subseteq> Dv" using pt(2) that(2) by (auto simp: ttvars_def)
  qed
  text \<open>The pattern is \<open>\<eta>\<close>-expanded against an abstraction:\<close>
  have eta: "mrange env1"
    if ob': "ob = Abs b U u" and m: "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" for b U u
  proof -
    from ty obtain Ty' where tu: "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" by (auto simp: ob')
    show ?thesis
      by (rule IH[OF m _ _ tu])
        (use wp ob pt mr in \<open>auto simp: ob' e typs_incr vars_incr ttvars_def\<close>)
  qed
  show ?case
  proof (cases "is_Var pt")
    case True
    then obtain ixn T where ptv: "pt = Var ixn T" by (cases pt) auto
    from h have nopen: "\<not> (inAbs \<and> is_open ob)" by (auto simp: ptv split: if_splits)
    with cl have clo: "closed ob" by (auto simp: is_open_closed)
    have wT: "wft ar T" using wp by (simp add: ptv)
    from h nopen obtain lr where lk: "ok (lookup1 insts ixn T) lr"
      and h2: "ok (case lr of
          None \<Rightarrow> do {
            tT \<leftarrow> fastype_of ob;
            tyinsts' \<leftarrow> typ_match_m alg T tT tyinsts;
            insts' \<leftarrow> update_new (ixn, (T, ob)) insts;
            return (tyinsts', insts')}
        | Some u \<Rightarrow> if aeconv ob u then return (tyinsts, insts) else raise Match) env1"
      by (auto simp: ptv)
    from ok_lookup1[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume lr: "lr = None" and none: "vt_lookup insts ixn = None"
      from h2[unfolded lr] obtain tT tyinsts' where ft: "ok (fastype_of ob) tT"
        and tm: "ok (typ_match alg T tT tyinsts) tyinsts'"
        and env1: "env1 = (tyinsts', vt_update (ixn, (T, ob)) insts)"
        by (auto simp: ok_update_new)
      have tT: "tT = Ty" using ft fastype_of_closed[OF ty clo] by (simp add: return_def)
      have cT: "cert_typ alg ar Ty" by (rule typing_cert_closed[OF ty clo])
      have "trange tyinsts'"
        by (rule typ_match_range[OF tm[unfolded tT] wT cT tr])
          (use typing_closed_tvars[OF ty clo] typing_closed_tfrees[OF ty clo] ob pt in \<open>auto simp: ptv\<close>)
      then show ?thesis unfolding env1 by (rule mrange_update[OF mr]) (use ob pt in \<open>auto simp: ptv\<close>)
    next
      fix u assume lr: "lr = Some u"
      from h2[unfolded lr] have "env1 = instsp" by (auto simp: e split: if_splits)
      then show ?thesis using mr by (simp add: e)
    qed
  next
    case nv: False
    with h have h': "ok (case (pt, ob) of
        (Free a T, Free b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Const a T, Const b U) \<Rightarrow>
          if a = b then do {tyinsts' \<leftarrow> typ_match_m alg T U tyinsts; return (tyinsts', insts)}
          else raise Match
      | (Bound i, Bound j) \<Rightarrow> if i = j then return (tyinsts, insts) else raise Match
      | (Abs _ T t, Abs _ U u) \<Rightarrow> do {
          tyinsts' \<leftarrow> typ_match_m alg T U tyinsts;
          fm alg True (tyinsts', insts) t u}
      | (f $ t, g $ u) \<Rightarrow> do {instsp' \<leftarrow> fm alg inAbs (tyinsts, insts) f g; fm alg inAbs instsp' t u}
      | (_, Abs _ U u) \<Rightarrow> fm alg True (tyinsts, insts) (incr pt $ Bound 0) u
      | _ \<Rightarrow> raise Match) env1" by simp
    show ?thesis
    proof (cases pt)
      case (Const a T)
      show ?thesis
      proof (cases ob)
        case (Const b U)
        from h' obtain tyinsts' where tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env1: "env1 = (tyinsts', insts)"
          by (auto simp: \<open>pt = Const a T\<close> Const split: if_splits)
        from tmr[OF tm] show ?thesis unfolding env1 by (intro mrange_tye[OF mr]) (simp_all add: \<open>pt = Const a T\<close> Const)
      next
        case (Abs b U u)
        from h' show ?thesis by (intro eta[OF Abs]) (simp add: \<open>pt = Const a T\<close> Abs e)
      qed (use h' Const in auto)
    next
      case (Free a T)
      show ?thesis
      proof (cases ob)
        case (Free b U)
        from h' obtain tyinsts' where tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env1: "env1 = (tyinsts', insts)"
          by (auto simp: \<open>pt = Free a T\<close> Free split: if_splits)
        from tmr[OF tm] show ?thesis unfolding env1 by (intro mrange_tye[OF mr]) (simp_all add: \<open>pt = Free a T\<close> Free)
      next
        case (Abs b U u)
        from h' show ?thesis by (intro eta[OF Abs]) (simp add: \<open>pt = Free a T\<close> Abs e)
      qed (use h' Free in auto)
    next
      case (Var x T)
      with nv show ?thesis by simp
    next
      case (Bound i)
      show ?thesis
      proof (cases ob)
        case (Bound j)
        from h' have "env1 = instsp" by (auto simp: \<open>pt = Bound i\<close> Bound e split: if_splits)
        then show ?thesis using mr by (simp add: e)
      next
        case (Abs b U u)
        from h' show ?thesis by (intro eta[OF Abs]) (simp add: \<open>pt = Bound i\<close> Abs e)
      qed (use h' Bound in auto)
    next
      case pa: (Abs a T t)
      show ?thesis
      proof (cases ob)
        case (Abs b U u)
        from h' obtain tyinsts' where tm: "ok (typ_match alg T U tyinsts) tyinsts'"
          and m: "ok (fm alg True (tyinsts', insts) t u) env1"
          by (auto simp: pa Abs)
        from ty obtain Ty' where tu: "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" by (auto simp: Abs)
        have "mrange (tyinsts', insts)" by (rule mrange_tye[OF mr tmr[OF tm]]) (simp_all add: pa Abs)
        then show ?thesis
          by (intro IH[OF m _ _ tu]) (use wp ob pt in \<open>auto simp: pa Abs\<close>)
      qed (use h' pa in auto)
    next
      case pa: (App f t)
      show ?thesis
      proof (cases ob)
        case (App g u)
        from h' obtain env' where m1: "ok (fm alg inAbs (tyinsts, insts) f g) env'"
          and m2: "ok (fm alg inAbs env' t u) env1"
          by (auto simp: pa App)
        from ty obtain T' where tg: "e \<turnstile> g : T' \<rightarrow>\<^sub>T Ty" and tu: "e \<turnstile> u : T'" by (auto simp: App)
        have c: "\<not> inAbs \<longrightarrow> closed g \<and> closed u" using cl by (auto simp: App closed_def)
        have "mrange env'"
          by (rule IH[OF m1 _ _ tg]) (use wp ob pt mr c in \<open>auto simp: pa App\<close>)
        then show ?thesis
          by (intro IH[OF m2 _ _ tu]) (use wp ob pt c in \<open>auto simp: pa App\<close>)
      next
        case (Abs b U u)
        from h' show ?thesis by (intro eta[OF Abs]) (simp add: pa Abs e)
      qed (use h' pa in auto)
    qed
  qed
qed


subsection \<open>Matching of higher-order patterns\<close>

lemma typs_abs_list: "typs (abs_list bs t) = snd ` set bs \<union> typs t"
  by (induction bs) (force simp: abs_list_def)+

lemma typs_rename [simp]: "typs (rename f d t) = typs t"
  by (induction f d t rule: rename.induct) auto

lemma mtch_range:
  assumes "mtch alg' bs pt ob env = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env1 \<Longrightarrow> \<forall>T\<in>typs pt. wft ar T \<Longrightarrow> \<forall>T\<in>typs ob. cert_typ alg ar T \<Longrightarrow>
    abs_bound (tbnd (fst env)) pt \<Longrightarrow> vars ob \<subseteq> V \<Longrightarrow> ttvars ob \<subseteq> A \<Longrightarrow> ttfrees ob \<subseteq> F \<Longrightarrow>
    fst ` vars pt \<subseteq> Dx \<Longrightarrow> fst ` ttvars pt \<subseteq> Dv \<Longrightarrow> ttfrees pt \<subseteq> F \<Longrightarrow>
    \<forall>b\<in>set bs. tvars (snd b) \<subseteq> A \<and> tfrees (snd b) \<subseteq> F \<Longrightarrow> mrange env \<Longrightarrow>
    mrange env1 \<and> textends (fst env) (fst env1)"
  using assms
proof (induction alg' bs pt ob env r arbitrary: env1 rule: mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' bs pt ob env r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" and r: "r = Ok env1" using prems by simp_all
  note h = "1.hyps"[unfolded alg' r]
  note IH = "1.IH"[OF _ refl refl]
  have wp: "\<forall>T\<in>typs pt. wft ar T" and wo: "\<forall>T\<in>typs ob. cert_typ alg ar T"
    and ab: "abs_bound (tbnd iTs) pt"
    and ob: "vars ob \<subseteq> V" "ttvars ob \<subseteq> A" "ttfrees ob \<subseteq> F"
    and pt: "fst ` vars pt \<subseteq> Dx" "fst ` ttvars pt \<subseteq> Dv" "ttfrees pt \<subseteq> F"
    and bsr: "\<forall>b\<in>set bs. tvars (snd b) \<subseteq> A \<and> tfrees (snd b) \<subseteq> F" and mr: "mrange (iTs, itms)"
    using prems e by simp_all
  have tr: "trange iTs" using mr by (simp add: mrange_def)
  define pre where "pre p q \<longleftrightarrow> (\<forall>T\<in>typs p. wft ar T) \<and> (\<forall>T\<in>typs q. cert_typ alg ar T) \<and>
    vars q \<subseteq> V \<and> ttvars q \<subseteq> A \<and> ttfrees q \<subseteq> F \<and> fst ` vars p \<subseteq> Dx \<and> fst ` ttvars p \<subseteq> Dv \<and> ttfrees p \<subseteq> F"
    for p q
  text \<open>Arguments of rigid heads are matched from left to right:\<close>
  have args: "mrange env1 \<and> textends (fst e0) (fst env1)"
    if m: "ok (handle (zip_eq ps qs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs e0))
      (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
      and ps: "\<forall>p\<in>set ps. abs_bound (tbnd (fst e0)) p" and pq: "\<forall>x\<in>set (zip ps qs). pre (fst x) (snd x)"
      and me: "mrange e0"
    for e0 ps qs
  proof -
    have nh: "\<not> ok (case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) y" for e and y :: match_env
      by (cases e) simp_all
    from m nh have len: "length ps = length qs"
      and f: "ok (foldM (\<lambda>(p, q). fm alg bs p q) (zip ps qs) e0) env1"
      by (auto simp: ok_handle ok_zip_eq)
    define Q where "Q xs b b' \<longleftrightarrow> (\<forall>x\<in>set xs. abs_bound (tbnd (fst b)) (fst x) \<and> pre (fst x) (snd x)) \<longrightarrow>
      mrange b \<longrightarrow> mrange b' \<and> textends (fst b) (fst b')" for xs and b b' :: match_env
    have "Q (zip ps qs) e0 env1"
      using f
    proof (induction rule: ok_foldM_induct)
      case (Nil b)
      then show ?case by (simp add: Q_def)
    next
      case (Cons x xs b b1 b')
      obtain p q where x: "x = (p, q)" by force
      show ?case unfolding Q_def
      proof (intro impI)
        assume pr: "\<forall>y\<in>set (x # xs). abs_bound (tbnd (fst b)) (fst y) \<and> pre (fst y) (snd y)" and mb: "mrange b"
        from Cons(1) have m1: "ok (fm alg bs p q b) b1" by (simp add: x)
        have i: "mrange b1 \<and> textends (fst b) (fst b1)"
          by (rule IH[OF m1]) (use pr mb bsr in \<open>simp_all add: x pre_def\<close>)
        then have "tbnd (fst b) \<subseteq> tbnd (fst b1)" by (simp add: tbnd_mono)
        with pr have "\<forall>y\<in>set xs. abs_bound (tbnd (fst b1)) (fst y) \<and> pre (fst y) (snd y)"
          by (auto intro: abs_bound_mono)
        with Cons(3) i show "mrange b' \<and> textends (fst b) (fst b')"
          unfolding Q_def by (auto intro: textends_trans)
      qed
    qed
    moreover have "\<forall>x\<in>set (zip ps qs). abs_bound (tbnd (fst e0)) (fst x)"
      using ps by (auto dest: set_zip_leftD)
    ultimately show ?thesis using pq me unfolding Q_def by blast
  qed
  show ?case
  proof (cases "is_Abs pt")
    case pA: True
    then obtain ns Ts ts where ptA: "pt = Abs ns Ts ts" by (cases pt) auto
    have pre1: "\<forall>T\<in>typs ts. wft ar T" "abs_bound (tbnd (fst env)) ts" and tvT: "tvars Ts \<subseteq> tbnd iTs"
      using wp ab by (simp_all add: ptA e)
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where obA: "ob = Abs nt Tt tt" by (cases ob) auto
      from h have m: "ok (fm alg ((nt, Tt) # bs) ts tt env) env1" by (simp add: e ptA obA)
      show ?thesis
        by (rule IH[OF m]) (use pre1 wo ob pt bsr mr in \<open>simp_all add: ptA obA e image_Un\<close>)
    next
      case oA: False
      from h oA obtain Tt where st: "ok (subst_type iTs Ts) Tt"
        and m: "ok (fm alg ((ns, Tt) # bs) ts (incr ob $ Bound 0) env) env1"
        by (auto simp: e ptA)
      have Tt: "Tt = tsubst (mtinst iTs) Ts" by (rule ok_subst_type[OF st])
      have bnd: "tvars (mtinst iTs v S) \<subseteq> A" "tfrees (mtinst iTs v S) \<subseteq> F" if "(v, S) \<in> tvars Ts" for v S
      proof -
        from that tvT obtain S' U where l: "vt_lookup iTs v = Some (S', U)" by (auto simp: tbnd_def)
        with tr have "tvars U \<subseteq> A" "tfrees U \<subseteq> F" unfolding trange_def by blast+
        with l show "tvars (mtinst iTs v S) \<subseteq> A" "tfrees (mtinst iTs v S) \<subseteq> F" by (simp_all add: mtinst_def)
      qed
      have rT: "tvars Tt \<subseteq> A" "tfrees Tt \<subseteq> F"
      proof -
        show "tvars Tt \<subseteq> A" unfolding Tt tvars_tsubst using bnd(1) by auto
        have "x \<in> F" if "(v, S) \<in> tvars Ts" "x \<in> tfrees (mtinst iTs v S)" for v S x
          using bnd(2)[OF that(1)] that(2) by blast
        moreover have "tfrees Ts \<subseteq> F" using pt(3) by (simp add: ptA)
        ultimately show "tfrees Tt \<subseteq> F" unfolding Tt tfrees_tsubst by auto
      qed
      show ?thesis
        by (rule IH[OF m])
          (use pre1 wo ob pt bsr mr rT in \<open>simp_all add: ptA e typs_incr vars_incr ttvars_def ttfrees_def image_Un\<close>)
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where obA: "ob = Abs nt Tt tt" by (cases ob) auto
      from h pA have m: "ok (fm alg ((nt, Tt) # bs) (incr pt $ Bound 0) tt env) env1"
        by (simp add: e obA)
      show ?thesis
        by (rule IH[OF m])
          (use wp wo abs_bound_incr_Bound0[OF pA ab] ob pt bsr mr in
            \<open>simp_all add: obA e typs_incr vars_incr ttvars_def ttfrees_def\<close>)
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      have ptc: "pt = ph \<degree>\<degree> pargs" by (rule strip_comb_apps[OF sp])
      note h = h[unfolded e, simplified pA oA if_False sp Let_def prod.case]
      show ?thesis
      proof (cases "is_Var ph")
        case True
        then obtain ixn T where ph: "ph = Var ixn T" by (cases ph) auto
        from h obtain "is" lr where io: "ok (ints_of pargs) is" and lk: "ok (lookup1 itms ixn T) lr"
          and h2: "ok (case lr of
              None \<Rightarrow> match_bind itms bs ixn T is ob \<bind> (\<lambda>itms'. return (iTs, itms'))
            | Some u \<Rightarrow> red u is [] \<bind> (\<lambda>u'. if aeconv ob u' then return (iTs, itms) else raise Match)) env1"
          by (auto simp: ph)
        from io have pargs: "pargs = map Bound is" and dis: "distinct is" by (simp_all add: ok_ints_of)
        have vpt: "(ixn, T) \<in> vars pt" by (simp add: ptc ph vars_apps)
        from ok_lookup1[OF lk] show ?thesis
        proof (elim disjE exE conjE)
          assume lr: "lr = None"
          from h2 lr obtain itms' where mb: "ok (match_bind itms bs ixn T is ob) itms'"
            and env1: "env1 = (iTs, itms')" by auto
          note b = ok_match_bind[OF mb dis]
          define u where "u = abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 ob)"
          have sub: "tvars T' \<subseteq> A \<and> tfrees T' \<subseteq> F" if "T' \<in> snd ` set (map (\<lambda>i. bs ! nat_of_integer i) is)" for T'
          proof -
            from that obtain i where i: "i \<in> set is" and T': "T' = snd (bs ! nat_of_integer i)" by auto
            from b(4) i have "0 \<le> i" "i < ilength bs" by auto
            then have "nat_of_integer i < length bs"
              by (simp add: ilength_eq integer_less_iff integer_less_eq_iff integer_of_nat.rep_eq nat_of_integer.rep_eq)
            then have "bs ! nat_of_integer i \<in> set bs" by simp
            with bsr show ?thesis unfolding T' by blast
          qed
          have "vars u \<subseteq> V" using ob(1) by (simp add: u_def)
          moreover have "tvars T' \<subseteq> A \<and> tfrees T' \<subseteq> F" if "T' \<in> typs u" for T'
          proof -
            from that consider "T' \<in> snd ` set (map (\<lambda>i. bs ! nat_of_integer i) is)" | "T' \<in> typs ob"
              unfolding u_def typs_abs_list typs_rename by blast
            then show ?thesis
            proof cases
              case 1
              then show ?thesis by (rule sub)
            next
              case 2
              then show ?thesis using ob(2,3) unfolding ttvars_def ttfrees_def by blast
            qed
          qed
          then have "ttvars u \<subseteq> A" "ttfrees u \<subseteq> F" unfolding ttvars_def ttfrees_def by blast+
          ultimately have ru: "vars u \<subseteq> V" "ttvars u \<subseteq> A" "ttfrees u \<subseteq> F" .
          have "mrange (iTs, vt_update (ixn, (T, u)) itms)"
            by (rule mrange_update[OF mr tr _ ru]) (use pt(1) vpt in force)
          then show ?thesis by (simp add: env1 b(2) u_def e)
        next
          fix u assume lr: "lr = Some u"
          from h2 lr have "env1 = (iTs, itms)" by (auto split: if_splits)
          then show ?thesis using mr by (simp add: e)
        qed
      next
        case False
        obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
        have obc: "ob = oh \<degree>\<degree> oargs" by (rule strip_comb_apps[OF so])
        note h = h[simplified False if_False so Let_def prod.case]
        text \<open>A rigid head matched against an object head, followed by the arguments:\<close>
        have rig: "mrange env1 \<and> textends (fst env) (fst env1)"
          if m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
              (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
            and te: "textends iTs iTs'" and tr': "trange iTs'"
            and ab': "\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p"
          for iTs'
        proof -
          have pq: "\<forall>x\<in>set (zip pargs oargs). pre (fst x) (snd x)"
          proof
            fix x assume x: "x \<in> set (zip pargs oargs)"
            obtain p q where xp: "x = (p, q)" by force
            from x have "p \<in> set pargs" "q \<in> set oargs"
              unfolding xp by (auto dest: set_zip_leftD set_zip_rightD)
            then have s: "typs p \<subseteq> typs pt" "vars p \<subseteq> vars pt" "typs q \<subseteq> typs ob" "vars q \<subseteq> vars ob"
              by (auto simp: ptc obc typs_apps vars_apps)
            then have t: "ttvars p \<subseteq> ttvars pt" "ttfrees p \<subseteq> ttfrees pt" "ttvars q \<subseteq> ttvars ob" "ttfrees q \<subseteq> ttfrees ob"
              unfolding ttvars_def ttfrees_def by blast+
            have 1: "\<forall>T\<in>typs p. wft ar T" "\<forall>T\<in>typs q. cert_typ alg ar T" using wp wo s(1,3) by blast+
            have 2: "vars q \<subseteq> V" "ttvars q \<subseteq> A" "ttfrees q \<subseteq> F"
              by (rule subset_trans[OF s(4) ob(1)], rule subset_trans[OF t(3) ob(2)], rule subset_trans[OF t(4) ob(3)])
            have 3: "fst ` vars p \<subseteq> Dx" "fst ` ttvars p \<subseteq> Dv" "ttfrees p \<subseteq> F"
              by (rule subset_trans[OF image_mono[OF s(2)] pt(1)], rule subset_trans[OF image_mono[OF t(1)] pt(2)],
                rule subset_trans[OF t(2) pt(3)])
            show "pre (fst x) (snd x)" by (simp add: xp pre_def 1 2 3)
          qed
          have "mrange env1 \<and> textends (fst (iTs', itms)) (fst env1)"
            by (rule args[OF m _ pq]) (use ab' mr tr' in \<open>auto simp: mrange_def\<close>)
          with te show ?thesis by (auto simp: e intro: textends_trans)
        qed
        text \<open>Constants and free variables: their types are matched first.\<close>
        have typed: "trange iTs' \<and> (\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p)"
          if tm: "ok (typ_match alg Ta Tb iTs) iTs'" and wa: "Ta \<in> typs pt" and cb: "Tb \<in> typs ob"
            and abh: "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
          for Ta Tb iTs'
        proof (intro conjI ballI)
          have wa': "wft ar Ta" and cb': "cert_typ alg ar Tb" using wp wo wa cb by blast+
          show "trange iTs'"
          proof (rule typ_match_range[OF tm wa' cb' tr])
            show "tvars Tb \<subseteq> A" "tfrees Tb \<subseteq> F" using ob(2,3) cb by (auto simp: ttvars_def ttfrees_def)
            show "fst ` tvars Ta \<subseteq> Dv" using pt(2) wa by (auto simp: ttvars_def)
          qed
          have "tbnd iTs \<union> tvars Ta \<subseteq> tbnd iTs'"
            using tbnd_mono[OF typ_match_ext[OF tm]] typ_match_tbnd[OF tm wa' cert_wft[OF cb']] by blast
          then show "abs_bound (tbnd iTs') p" if "p \<in> set pargs" for p
            using abh that abs_bound_mono by blast
        qed
        show ?thesis
        proof (cases ph)
          case ph: (Const a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Const b Tb)
            from h ph oh obtain iTs' where tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            from typed[OF tm _ _ this] have "trange iTs' \<and> (\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p)"
              by (simp add: ptc obc ph oh typs_apps)
            then show ?thesis using rig[OF m typ_match_ext[OF tm]] by blast
          qed (use h ph in auto)
        next
          case ph: (Free a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Free b Tb)
            from h ph oh obtain iTs' where tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            from typed[OF tm _ _ this] have "trange iTs' \<and> (\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p)"
              by (simp add: ptc obc ph oh typs_apps)
            then show ?thesis using rig[OF m typ_match_ext[OF tm]] by blast
          qed (use h ph in auto)
        next
          case ph: (Bound i)
          show ?thesis
          proof (cases oh)
            case oh: (Bound j)
            from h ph oh have m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs, itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            then show ?thesis using rig[OF m textends_refl tr] by blast
          qed (use h ph in auto)
        qed (use False h strip_comb_head[OF sp] in auto)
      qed
    qed
  qed
qed

end


subsection \<open>The bindings of a match\<close>

context pure_sig
begin

text \<open>
  A successful match of a closed, typed pattern against a closed, typed object, from the empty
  environment: the types bound to type variables are certified; the bound type variables and
  variables are those of the pattern; the variables and type variables of the bindings are
  those of the object, and their free type variables those of the object or the pattern.
\<close>

theorem match_range:
  assumes m: "ok ((if fo then first_order_match else match) alg pt ob (vt_empty, vt_empty)) (tye, te)"
    and cl: "closed pt" "closed ob" and ty: "e \<turnstile> pt : pT" "e \<turnstile> ob : oT"
  shows "tye_cert tye"
    and "vt_lookup tye v = Some (S, U) \<Longrightarrow>
      v \<in> fst ` ttvars pt \<and> tvars U \<subseteq> ttvars ob \<and> tfrees U \<subseteq> ttfrees ob \<union> ttfrees pt"
    and "vt_lookup te x = Some (T, u) \<Longrightarrow>
      x \<in> fst ` vars pt \<and> vars u \<subseteq> vars ob \<and> ttvars u \<subseteq> ttvars ob \<and> ttfrees u \<subseteq> ttfrees ob \<union> ttfrees pt"
proof -
  interpret R: match_range alg ar ctab "vars ob" "ttvars ob" "ttfrees ob \<union> ttfrees pt" "fst ` vars pt" "fst ` ttvars pt"
    by unfold_locales
  have wp: "\<forall>T\<in>typs pt. wft ar T" using typing_typs_cert[OF ty(1)] by (auto simp: cert_wft)
  have wo: "\<forall>T\<in>typs ob. cert_typ alg ar T" using typing_typs_cert[OF ty(2)] .
  have r0: "R.mrange (vt_empty, vt_empty)"
    by (simp add: R.mrange_def R.trange_def tye_cert_def)
  have fo: "R.mrange env'" if "ok (first_order_match alg pt ob env) env'" "R.mrange env" for env env'
    by (rule R.fo_mtch_range[OF that(1)[unfolded first_order_match_def] refl refl _ wp ty(2)])
      (use cl that(2) in auto)
  have "R.mrange (tye, te)"
  proof (cases fo)
    case True
    with m show ?thesis by (intro fo[OF _ r0]) simp
  next
    case False
    with m obtain iTs where tm: "ok (typ_match alg pT oT vt_empty) iTs"
      and h: "ok (handle (mtch alg [] pt ob (iTs, vt_empty))
        (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, vt_empty) | _ \<Rightarrow> raise e)) (tye, te)"
      by (auto simp: match_def Let_def fastype_of_closed[OF ty(1) cl(1)] fastype_of_closed[OF ty(2) cl(2)])
    have cp: "cert_typ alg ar pT" "cert_typ alg ar oT"
      using typing_cert_closed[OF ty(1) cl(1)] typing_cert_closed[OF ty(2) cl(2)] .
    have tr: "R.trange iTs"
    proof (rule R.typ_match_range[OF tm cert_wft[OF cp(1)] cp(2)])
      show "R.trange vt_empty" using r0 by (simp add: R.mrange_def)
      show "tvars oT \<subseteq> ttvars ob" by (rule typing_closed_tvars[OF ty(2) cl(2)])
      show "tfrees oT \<subseteq> ttfrees ob \<union> ttfrees pt" using typing_closed_tfrees[OF ty(2) cl(2)] by blast
      show "fst ` tvars pT \<subseteq> fst ` ttvars pt" by (rule image_mono[OF typing_closed_tvars[OF ty(1) cl(1)]])
    qed
    have r1: "R.mrange (iTs, vt_empty)" using r0 tr by (simp add: R.mrange_def)
    have pat: "ok (case ex of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, vt_empty) | _ \<Rightarrow> raise ex) env' \<Longrightarrow>
        ok (first_order_match alg pt ob (iTs, vt_empty)) env'" for ex and env' :: match_env
      by (cases ex) simp_all
    from h consider (m) "ok (mtch alg [] pt ob (iTs, vt_empty)) (tye, te)"
      | (f) "ok (first_order_match alg pt ob (iTs, vt_empty)) (tye, te)"
      using pat by (auto simp: ok_handle)
    then show ?thesis
    proof cases
      case m
      have "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 pt i \<longrightarrow> tvars (e i) \<subseteq> tbnd iTs"
        using cl(1) by (simp add: closed_iff_loose_bvar1)
      moreover have "tvars pT \<subseteq> tbnd iTs" by (rule typ_match_tbnd[OF tm]) (simp_all add: cp cert_wft)
      ultimately have ab: "abs_bound (tbnd iTs) pt" using typing_abs_bound[OF ty(1)] by blast
      have "R.mrange (tye, te) \<and> textends (fst (iTs, vt_empty :: tenv)) (fst (tye, te))"
        using R.mtch_range[OF m refl refl wp wo] ab r1 by auto
      then show ?thesis by simp
    next
      case f
      then show ?thesis by (rule fo[OF _ r1])
    qed
  qed
  then have *: "tye_cert tye"
    "\<forall>v S U. vt_lookup tye v = Some (S, U) \<longrightarrow>
      v \<in> fst ` ttvars pt \<and> tvars U \<subseteq> ttvars ob \<and> tfrees U \<subseteq> ttfrees ob \<union> ttfrees pt"
    "\<forall>x T u. vt_lookup te x = Some (T, u) \<longrightarrow>
      x \<in> fst ` vars pt \<and> vars u \<subseteq> vars ob \<and> ttvars u \<subseteq> ttvars ob \<and> ttfrees u \<subseteq> ttfrees ob \<union> ttfrees pt"
    unfolding R.mrange_def R.trange_def by simp_all
  show "tye_cert tye" by (rule *(1))
  show "vt_lookup tye v = Some (S, U) \<Longrightarrow>
      v \<in> fst ` ttvars pt \<and> tvars U \<subseteq> ttvars ob \<and> tfrees U \<subseteq> ttfrees ob \<union> ttfrees pt"
    using *(2) by blast
  show "vt_lookup te x = Some (T, u) \<Longrightarrow>
      x \<in> fst ` vars pt \<and> vars u \<subseteq> vars ob \<and> ttvars u \<subseteq> ttvars ob \<and> ttfrees u \<subseteq> ttfrees ob \<union> ttfrees pt"
    using *(3) by blast
qed

end

end
