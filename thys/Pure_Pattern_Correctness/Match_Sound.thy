section \<open>Soundness of Matching\<close>

theory Match_Sound
  imports Match_Types Match_Pattern Poly_Inst
begin

text \<open>
  A matching environment \<open>(tye, te)\<close> instantiates the type variables of a pattern by the
  one-pass instantiation \<^term>\<open>mtinst tye\<close> and its term variables by the bindings of \<open>te\<close>
  (\<open>Envir.subst_term\<close>). The object is not instantiated: its variables behave like constants.
\<close>

lemma ok_typ_match_m[simp]: "ok (typ_match_m alg T U tye) tye' \<longleftrightarrow> ok (typ_match alg T U tye) tye'"
  by (auto simp: typ_match_m_def handle_def return_def raise_def split: option.splits res.splits exn.splits)

text \<open>\<open>\<equiv>\<^sub>\<beta>\<^sub>\<eta>\<close> is the closure of \<^term>\<open>sup beta eta\<close>; unfolding the supremum only obscures it.\<close>

declare sup_apply[simp del]

subsection \<open>Matchers\<close>

definition msub :: "tenv \<Rightarrow> nat \<Rightarrow> dB" where
  "msub te n = (case atom_of n of
     AVar x \<Rightarrow> (case vt_lookup te x of
       Some (_, u) \<Rightarrow> if n = code (AVar x) then tr u else dB.Var n
     | None \<Rightarrow> dB.Var n)
   | _ \<Rightarrow> dB.Var n)"

lemma msub_simps[simp]:
  "msub te (code (AVar x)) = (case vt_lookup te x of Some (_, u) \<Rightarrow> tr u | None \<Rightarrow> dB.Var (code (AVar x)))"
  "msub te (code (AConst a T)) = dB.Var (code (AConst a T))"
  "msub te (code (AFree a T)) = dB.Var (code (AFree a T))"
  by (simp_all add: msub_def split: option.splits)

text \<open>The instance of a term under a matching environment:\<close>

definition minst :: "match_env \<Rightarrow> pterm \<Rightarrow> dB" where
  "minst env t = mk_subst (msub (snd env)) (tr (inst (mtinst (fst env)) t))"

text \<open>Bindings are proper and closed:\<close>

definition mte_ok :: "tenv \<Rightarrow> bool" where
  "mte_ok te \<longleftrightarrow> (\<forall>x U u. vt_lookup te x = Some (U, u) \<longrightarrow> proper u \<and> no_loose_bound (tr u) 0)"

lemma mte_okD: "mte_ok te \<Longrightarrow> vt_lookup te x = Some (U, u) \<Longrightarrow> proper u \<and> no_loose_bound (tr u) 0"
  unfolding mte_ok_def by blast

lemma closed_msub: "mte_ok te \<Longrightarrow> closed_on V (msub te)"
  unfolding closed_on_def msub_def
  by (auto split: atom.splits option.splits dest: mte_okD)

definition mextends :: "match_env \<Rightarrow> match_env \<Rightarrow> bool" where
  "mextends env env' \<longleftrightarrow> textends (fst env) (fst env') \<and>
    (\<forall>x b. vt_lookup (snd env) x = Some b \<longrightarrow> vt_lookup (snd env') x = Some b)"

lemma mextends_refl[simp]: "mextends env env"
  by (simp add: mextends_def)

lemma mextends_trans: "mextends env1 env2 \<Longrightarrow> mextends env2 env3 \<Longrightarrow> mextends env1 env3"
  by (auto simp: mextends_def intro: textends_trans)

text \<open>The types that matter for the translation: those of constants and free variables.\<close>

fun ctys :: "pterm \<Rightarrow> ptyp set" where
  "ctys (Const _ T) = {T}"
| "ctys (Free _ T) = {T}"
| "ctys (pterm.Abs _ _ t) = ctys t"
| "ctys (s $ t) = ctys s \<union> ctys t"
| "ctys _ = {}"

text \<open>The environment binds the relevant type variables and the variables of a term:\<close>

definition mbound :: "match_env \<Rightarrow> pterm \<Rightarrow> bool" where
  "mbound env t \<longleftrightarrow> (\<forall>T\<in>ctys t. \<forall>(v, S)\<in>tvars T. vt_lookup (fst env) v \<noteq> None) \<and>
    (\<forall>x\<in>vars t. vt_lookup (snd env) x \<noteq> None)"

lemma mbound_mono: "mextends env env' \<Longrightarrow> mbound env t \<Longrightarrow> mbound env' t"
  unfolding mbound_def mextends_def textends_def by fastforce

lemma tsubst_mtinst_mono:
  "textends tye tye' \<Longrightarrow> \<forall>(v, S)\<in>tvars T. vt_lookup tye v \<noteq> None \<Longrightarrow>
    tsubst (mtinst tye') T = tsubst (mtinst tye) T"
  by (rule tsubst_cong) (auto simp: mtinst_def textends_def)

lemma minst_simps:
  "minst env (s $ t) = minst env s \<degree> minst env t" "minst env (pterm.Abs a T t) = dB.Abs (minst env t)"
  "minst env (Bound i) = BVar (nat_of_integer i)"
  "minst env (Const a T) = dB.Var (code (AConst a (tsubst (mtinst (fst env)) T)))"
  "minst env (Free a T) = dB.Var (code (AFree a (tsubst (mtinst (fst env)) T)))"
  "minst env (pterm.Var x T) = msub (snd env) (code (AVar x))"
  by (simp_all add: minst_def)

lemma mbound_simps:
  "mbound env (s $ t) \<longleftrightarrow> mbound env s \<and> mbound env t"
  "mbound env (pterm.Abs a T t) \<longleftrightarrow> mbound env t"
  by (auto simp: mbound_def)

lemma minst_mono: "mextends env env' \<Longrightarrow> mbound env t \<Longrightarrow> minst env' t = minst env t"
proof (induction t)
  case (Const a T)
  then show ?case by (auto simp: minst_def mbound_def mextends_def intro!: tsubst_mtinst_mono)
next
  case (Free a T)
  then show ?case by (auto simp: minst_def mbound_def mextends_def intro!: tsubst_mtinst_mono)
next
  case (Var x T)
  then obtain U u where b: "vt_lookup (snd env) x = Some (U, u)" by (auto simp: mbound_def)
  with Var.prems(1) have "vt_lookup (snd env') x = Some (U, u)" unfolding mextends_def by blast
  with b show ?case by (simp add: minst_simps)
qed (simp_all add: minst_simps mbound_simps)


subsection \<open>Terms\<close>

lemma aconv_tr: "aconv_term t u \<Longrightarrow> tr t = tr u"
  by (induction t u rule: aconv_term.induct) auto

lemma aconv_proper: "aconv_term t u \<Longrightarrow> proper t \<longleftrightarrow> proper u"
  by (induction t u rule: aconv_term.induct) auto

lemma loose_bvar_tr:
  "proper t \<Longrightarrow> 0 \<le> k \<Longrightarrow> loose_bvar t k \<longleftrightarrow> \<not> no_loose_bound (tr t) (nat_of_integer k)"
proof (induction t arbitrary: k)
  case (Bound i)
  then show ?case by (auto simp: nat_of_integer_less_iff)
next
  case (Abs a T t)
  have "nat_of_integer (k + 1) = Suc (nat_of_integer k)"
    using Abs.prems(2) nat_of_integer_add[of k 1] by simp
  with Abs show ?case by simp
qed auto

lemma closed_iff: "proper t \<Longrightarrow> \<not> is_open t \<longleftrightarrow> no_loose_bound (tr t) 0"
  using loose_bvar_tr[of t 0] by (simp add: is_open_def)

lemma tr_decr:
  "proper f \<Longrightarrow> 0 \<le> lev \<Longrightarrow> \<not> loose_bvar1 f lev \<Longrightarrow>
    proper (Pure_Term.decr lev f) \<and> lift (tr (Pure_Term.decr lev f)) (nat_of_integer lev) = tr f"
proof (induction f arbitrary: lev)
  case (Bound i)
  show ?case
  proof (cases "lev \<le> i")
    case True
    with Bound.prems have "lev < i" by simp
    with Bound.prems(2) have "0 < i" by (rule order.strict_trans1)
    with Bound.prems(2) \<open>lev < i\<close> have "nat_of_integer lev < nat_of_integer i"
      by (simp add: nat_of_integer_less_iff)
    moreover have "0 \<le> i - 1" using \<open>0 < i\<close> by (simp add: integer_reps)
    ultimately show ?thesis using True \<open>0 < i\<close> by (simp add: nat_of_integer_minus_1)
  next
    case False
    with Bound.prems have "nat_of_integer i < nat_of_integer lev"
      by (simp add: nat_of_integer_less_iff)
    with False Bound.prems show ?thesis by simp
  qed
next
  case (Abs a T t)
  have l: "0 \<le> lev + 1" using add_nonneg_nonneg[OF Abs.prems(2) zero_le_one] .
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)"
    using Abs.prems(2) nat_of_integer_add[of lev 1] by simp
  with Abs.IH[OF _ l] Abs.prems show ?case by simp
qed auto

lemma tr_eta_contract: "proper t \<Longrightarrow> proper (eta_contract t) \<and> tr (eta_contract t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t"
proof (induction t)
  case (Abs a T body)
  let ?b = "eta_contract body"
  have "proper body" using Abs.prems by simp
  note ih = Abs.IH[OF this]
  have pb: "proper ?b" and abs: "dB.Abs (tr ?b) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (pterm.Abs a T body)"
    using ih equiv_Abs[OF ih[THEN conjunct2]] by simp_all
  show ?case
  proof (cases "\<exists>f. ?b = f $ Bound 0 \<and> \<not> is_dependent f")
    case True
    then obtain f where b: "?b = f $ Bound 0" and nd: "\<not> is_dependent f" by blast
    have pf: "proper f" using pb by (simp add: b)
    have d: "proper (Pure_Term.decr 0 f)" "lift (tr (Pure_Term.decr 0 f)) 0 = tr f"
      using tr_decr[of f 0] pf nd by (simp_all add: is_dependent_def)
    have e: "eta_contract (pterm.Abs a T body) = Pure_Term.decr 0 f" using b nd by simp
    have "dB.Abs (tr ?b) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Pure_Term.decr 0 f)"
      using eta_lift_equiv[of "tr (Pure_Term.decr 0 f)"] by (simp add: b d(2)[symmetric])
    from equiv_trans[OF equiv_sym[OF this] abs] d(1) e show ?thesis by simp
  next
    case False
    then have "eta_contract (pterm.Abs a T body) = pterm.Abs a T ?b"
      by (cases ?b) (auto simp: Let_def split: pterm.splits)
    with abs pb show ?thesis by (simp del: eta_contract.simps)
  qed
next
  case (App s t)
  then have "proper (eta_contract s)" "tr (eta_contract s) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr s"
    "proper (eta_contract t)" "tr (eta_contract t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t" by simp_all
  then show ?case using equiv_App by simp
qed auto

lemma aeconv_tr: "proper t \<Longrightarrow> proper u \<Longrightarrow> aeconv t u \<Longrightarrow> tr t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
  unfolding aeconv_def
proof (elim disjE)
  assume "proper t" "proper u" "aconv_term (eta_contract t) (eta_contract u)"
  with tr_eta_contract[of t] tr_eta_contract[of u] aconv_tr show "tr t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
    by (metis equiv_sym equiv_trans)
qed (simp add: aconv_tr)

lemma tr_incr: "proper t \<Longrightarrow> tr (incr t) = lift (tr t) 0"
  using tr_incr_aux[of t 0] by (simp add: incr_def)

lemma proper_incr: "proper t \<Longrightarrow> proper (incr t)"
  by (simp add: incr_def proper_incr_aux)

lemma minst_incr: "mte_ok (snd env) \<Longrightarrow> proper t \<Longrightarrow> minst env (incr t) = lift (minst env t) 0"
  by (simp add: minst_def inst_incr tr_incr mk_subst_lift_on closed_msub)

lemma ctys_incr_aux: "ctys (incr_aux d t) = ctys t"
  by (induction d t rule: incr_aux.induct) auto

lemma ctys_incr: "ctys (incr t) = ctys t"
  by (simp add: incr_def ctys_incr_aux)

lemma mbound_incr: "mbound env (incr t) \<longleftrightarrow> mbound env t"
  by (simp add: mbound_def ctys_incr vars_incr)

lemma ok_update_new:
  "update_new (x, b) te = return te' \<Longrightarrow> vt_lookup te x = None \<and> te' = vt_update (x, b) te"
  by (simp add: update_new_def vt_defined_lookup return_def raise_def split: if_splits)

lemma bindM_returnE: "bindM m f = return y \<Longrightarrow> \<exists>x. m = return x \<and> f x = return y"
  by (auto simp: bindM_def return_def split: option.splits res.splits)

lemma lookup1_cases:
  "lookup1 te x T = return r \<Longrightarrow>
    (r = None \<and> vt_lookup te x = None) \<or> (\<exists>u. r = Some u \<and> vt_lookup te x = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def return_def raise_def split: option.splits if_splits)


subsection \<open>First-order matching\<close>

context wf_algebra
begin

lemma fo_mtch_sound:
  assumes "fo_mtch alg' inAbs env pt ob = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env' \<Longrightarrow> proper pt \<Longrightarrow> proper ob \<Longrightarrow>
    (\<not> inAbs \<longrightarrow> no_loose_bound (tr ob) 0) \<Longrightarrow> mte_ok (snd env) \<Longrightarrow>
    \<forall>T\<in>ctys pt. wft ar T \<Longrightarrow> \<forall>T\<in>ctys ob. wft ar T \<Longrightarrow>
    mextends env env' \<and> mte_ok (snd env') \<and> mbound env' pt \<and> minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  using assms
proof (induction alg' inAbs env pt ob r arbitrary: env' rule: fo_mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' inAbs instsp pt ob r)
  obtain tyinsts insts where e: "instsp = (tyinsts, insts)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" and r: "r = Ok env'" using prems by simp_all
  have h: "ok (if is_Var pt then
      (case pt of
        pterm.Var ixn T \<Rightarrow>
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
      | (pterm.Abs _ T t, pterm.Abs _ U u) \<Rightarrow> do {
          tyinsts' \<leftarrow> typ_match_m alg T U tyinsts;
          fm alg True (tyinsts', insts) t u}
      | (f $ t, g $ u) \<Rightarrow> do {instsp' \<leftarrow> fm alg inAbs (tyinsts, insts) f g; fm alg inAbs instsp' t u}
      | (_, pterm.Abs _ U u) \<Rightarrow> fm alg True (tyinsts, insts) (incr pt $ Bound 0) u
      | _ \<Rightarrow> raise Match)) env'"
    using "1.hyps" unfolding alg' r e Let_def prod.case .
  note IH = "1.IH"[OF _ refl refl]
  have pp: "proper pt" "proper ob" and cl: "\<not> inAbs \<longrightarrow> no_loose_bound (tr ob) 0"
    and ok: "mte_ok insts" and wp: "\<forall>T\<in>ctys pt. wft ar T" and wo: "\<forall>T\<in>ctys ob. wft ar T"
    using prems e by simp_all
  have tm_sound: "textends tyinsts tyinsts'" if "ok (typ_match_m alg T U tyinsts) tyinsts'" for T U tyinsts'
    using that typ_match_textends[unfolded return_def] by simp
  text \<open>The pattern is \<open>\<eta>\<close>-expanded against an abstraction:\<close>
  have eta: "mextends instsp env' \<and> mte_ok (snd env') \<and> mbound env' pt \<and> minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
    if ob: "ob = pterm.Abs b U u" and m: "ok (fm alg True instsp (incr pt $ Bound 0) u) env'" for b U u
  proof -
    have "proper (incr pt $ Bound 0)" "proper u" "\<forall>T\<in>ctys (incr pt $ Bound 0). wft ar T"
      "\<forall>T\<in>ctys u. wft ar T"
      using pp wp wo by (simp_all add: ob proper_incr ctys_incr)
    from IH[OF m this(1,2) _ _ this(3,4)] ok e
    have i: "mextends instsp env'" "mte_ok (snd env')" "mbound env' (incr pt $ Bound 0)"
      "minst env' (incr pt $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
      by simp_all
    have mb: "mbound env' pt" using i(3) by (simp add: mbound_simps mbound_incr)
    have "minst env' (incr pt $ Bound 0) = lift (minst env' pt) 0 \<degree> BVar 0"
      by (simp add: minst_simps minst_incr[OF i(2) pp(1)])
    with equiv_Abs[OF i(4)] have "dB.Abs (lift (minst env' pt) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
      by (simp add: ob)
    then have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
      using eta_lift_equiv[of "minst env' pt"] equiv_sym equiv_trans by blast
    with i(1,2) mb show ?thesis by simp
  qed
  show ?case
  proof (cases "is_Var pt")
    case True
    then obtain ixn T where pt: "pt = pterm.Var ixn T" by (cases pt) auto
    from h have nopen: "\<not> (inAbs \<and> is_open ob)" by (auto simp: pt split: if_splits)
    with h obtain lr where lk: "ok (lookup1 insts ixn T) lr"
      and h2: "ok (case lr of
          None \<Rightarrow> do {
            tT \<leftarrow> fastype_of ob;
            tyinsts' \<leftarrow> typ_match_m alg T tT tyinsts;
            insts' \<leftarrow> update_new (ixn, (T, ob)) insts;
            return (tyinsts', insts')}
        | Some u \<Rightarrow> if aeconv ob u then return (tyinsts, insts) else raise Match) env'"
      by (auto simp: pt)
    from lookup1_cases[OF lk[folded return_def]] show ?thesis
    proof (elim disjE exE conjE)
      assume lr: "lr = None" and none: "vt_lookup insts ixn = None"
      from h2[unfolded lr] obtain tT tyinsts' insts' where
        tm: "ok (typ_match_m alg T tT tyinsts) tyinsts'"
        and un: "ok (update_new (ixn, (T, ob)) insts) insts'" and env': "env' = (tyinsts', insts')"
        by auto
      have te: "textends tyinsts tyinsts'" by (rule tm_sound[OF tm])
      have ins: "insts' = vt_update (ixn, (T, ob)) insts" using ok_update_new[OF un[folded return_def]] by simp
      have clo: "no_loose_bound (tr ob) 0" using cl nopen closed_iff[OF pp(2)] by blast
      have "mextends instsp env'" using te none by (auto simp: e env' ins mextends_def)
      moreover have "mte_ok insts'" using ok pp(2) clo by (auto simp: ins mte_ok_def)
      moreover have "mbound env' pt" by (simp add: env' ins pt mbound_def)
      moreover have "minst env' pt = tr ob" by (simp add: env' ins pt minst_simps)
      ultimately show ?thesis by (simp add: env')
    next
      fix u assume lr: "lr = Some u" and some: "vt_lookup insts ixn = Some (T, u)"
      from h2[unfolded lr] have ae: "aeconv ob u" and env': "env' = instsp"
        by (auto simp: e split: if_splits)
      have pu: "proper u" using mte_okD[OF ok some] by simp
      have "minst env' pt = tr u" using some by (simp add: env' e pt minst_simps)
      moreover have "tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob" using aeconv_tr[OF pp(2) pu ae] by (rule equiv_sym)
      moreover have "mbound env' pt" using some by (simp add: env' e pt mbound_def)
      ultimately show ?thesis using ok by (simp add: env' e)
    qed
  next
    case False
    note h = h[simplified False if_False]
    show ?thesis
    proof (cases pt)
      case pt: (Const a T)
      show ?thesis
      proof (cases ob)
        case ob: (Const b U)
        with h pt obtain tyinsts' where ab: "a = b"
          and tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env': "env' = (tyinsts', insts)"
          by (auto split: if_splits)
        have "wft ar T" "wft ar U" using wp wo pt ob by simp_all
        note s = typ_match_sound[OF this tm[folded return_def]]
        show ?thesis using s(1-3) ok
          by (simp add: env' e pt ob ab minst_simps mextends_def mbound_def)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env'" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    next
      case pt: (Free a T)
      show ?thesis
      proof (cases ob)
        case ob: (Free b U)
        with h pt obtain tyinsts' where ab: "a = b"
          and tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env': "env' = (tyinsts', insts)"
          by (auto split: if_splits)
        have "wft ar T" "wft ar U" using wp wo pt ob by simp_all
        note s = typ_match_sound[OF this tm[folded return_def]]
        show ?thesis using s(1-3) ok
          by (simp add: env' e pt ob ab minst_simps mextends_def mbound_def)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env'" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    next
      case (Var x T)
      with False show ?thesis by simp
    next
      case pt: (Bound i)
      show ?thesis
      proof (cases ob)
        case ob: (Bound j)
        with h pt have "i = j" "env' = instsp" by (auto simp: e split: if_splits)
        with ok pt ob show ?thesis by (simp add: e minst_simps mbound_def)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env'" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    next
      case pt: (Abs a T t)
      show ?thesis
      proof (cases ob)
        case ob: (Abs b U u)
        with h pt obtain tyinsts' where tm: "ok (typ_match_m alg T U tyinsts) tyinsts'"
          and m: "ok (fm alg True (tyinsts', insts) t u) env'"
          by auto
        have "proper t" "proper u" "\<forall>T\<in>ctys t. wft ar T" "\<forall>T\<in>ctys u. wft ar T"
          using pp wp wo pt ob by simp_all
        from IH[OF m this(1,2) _ _ this(3,4)] ok
        have i: "mextends (tyinsts', insts) env'" "mte_ok (snd env')" "mbound env' t" "minst env' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
          by simp_all
        have "mextends instsp env'" using tm_sound[OF tm] i(1) by (auto simp: e mextends_def intro: textends_trans)
        moreover have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob" using equiv_Abs[OF i(4)] by (simp add: pt ob minst_simps)
        ultimately show ?thesis using i(2,3) by (simp add: pt mbound_simps)
      qed (use h pt in auto)
    next
      case pt: (App f t)
      show ?thesis
      proof (cases ob)
        case ob: (App g u)
        with h pt obtain env1 where m1: "ok (fm alg inAbs instsp f g) env1"
          and m2: "ok (fm alg inAbs env1 t u) env'"
          by (auto simp: e)
        have pr: "proper f" "proper g" "proper t" "proper u" using pp pt ob by simp_all
        have cl': "\<not> inAbs \<longrightarrow> no_loose_bound (tr g) 0" "\<not> inAbs \<longrightarrow> no_loose_bound (tr u) 0"
          using cl ob by auto
        have w: "\<forall>T\<in>ctys f. wft ar T" "\<forall>T\<in>ctys g. wft ar T" "\<forall>T\<in>ctys t. wft ar T" "\<forall>T\<in>ctys u. wft ar T"
          using wp wo pt ob by simp_all
        from IH[OF m1 pr(1,2) cl'(1) _ w(1,2)] ok
        have i1: "mextends instsp env1" "mte_ok (snd env1)" "mbound env1 f" "minst env1 f \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr g"
          by (simp_all add: e)
        from IH[OF m2 pr(3,4) cl'(2) i1(2) w(3,4)]
        have i2: "mextends env1 env'" "mte_ok (snd env')" "mbound env' t" "minst env' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u"
          by simp_all
        have "minst env' f = minst env1 f" by (rule minst_mono[OF i2(1) i1(3)])
        with i1(4) i2(4) have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
          using equiv_App by (simp add: pt ob minst_simps)
        moreover have "mbound env' f" by (rule mbound_mono[OF i2(1) i1(3)])
        ultimately show ?thesis using i2(2,3) mextends_trans[OF i1(1) i2(1)]
          by (simp add: pt mbound_simps)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env'" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    qed
  qed
qed

end


subsection \<open>Bindings of higher-order matching\<close>

text \<open>\<^term>\<open>mapbnd f d\<close> renames the loose bound variables \<open>k \<ge> d\<close> by \<open>f\<close>:\<close>

definition bmap :: "(integer \<Rightarrow> integer M) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bmap f d k = (if k < d then k else
    case f (integer_of_nat (k - d)) of Some (Ok j) \<Rightarrow> nat_of_integer j + d | _ \<Rightarrow> k)"

lemma bmap_Suc: "(\<lambda>x. case x of 0 \<Rightarrow> 0 | Suc a \<Rightarrow> Suc (bmap f d a)) = bmap f (Suc d)"
  by (auto simp: fun_eq_iff bmap_def split: nat.split option.split res.split)

lemma integer_of_nat_diff:
  "0 \<le> d \<Longrightarrow> d \<le> i \<Longrightarrow> integer_of_nat (nat_of_integer i - nat_of_integer d) = i - d"
  by (simp add: integer_eq_iff nat_of_integer.rep_eq less_eq_integer.rep_eq)
lemma mapbnd_sound:
  assumes "ok (mapbnd f d t) t'" "proper t" "0 \<le> d" "\<forall>i j. 0 \<le> i \<longrightarrow> ok (f i) j \<longrightarrow> 0 \<le> j"
  shows "proper t' \<and> tr t' = map_BVars (bmap f (nat_of_integer d)) (tr t) \<and>
    (\<forall>k\<in>loose_BVars (tr t). nat_of_integer d \<le> k \<longrightarrow> (\<exists>j. ok (f (integer_of_nat (k - nat_of_integer d))) j))"
  using assms
proof (induction f d t arbitrary: t' rule: mapbnd.induct)
  case (1 f d i)
  show ?case
  proof (cases "i < d")
    case True
    moreover have "0 \<le> i" using "1.prems"(2) by simp
    ultimately have "t' = Bound i" "nat_of_integer i < nat_of_integer d"
      using "1.prems" by (simp_all add: nat_of_integer_less_iff)
    with "1.prems" show ?thesis by (simp add: bmap_def)
  next
    case False
    with "1.prems" obtain j where j: "ok (f (i - d)) j" "t' = Bound (j + d)" by auto
    have id: "0 \<le> i - d" using False by (simp add: integer_reps)
    have j0: "0 \<le> j" using "1.prems"(4) id j(1) by blast
    have e1: "integer_of_nat (nat_of_integer i - nat_of_integer d) = i - d"
      using False "1.prems"(3) by (simp add: integer_of_nat_diff)
    have e2: "nat_of_integer (j + d) = nat_of_integer j + nat_of_integer d"
      using j0 "1.prems"(3) by (simp add: nat_of_integer_add)
    have e3: "\<not> nat_of_integer i < nat_of_integer d"
      using False "1.prems" by (simp add: nat_of_integer_less_iff)
    show ?thesis using j j0 "1.prems"(3) by (simp add: bmap_def e1 e2 e3)
  qed
next
  case (2 f d s T t)
  from "2.prems" obtain t'' where m: "ok (mapbnd f (d + 1) t) t''" and t': "t' = pterm.Abs s T t''"
    by auto
  have d1: "0 \<le> d + 1" using add_nonneg_nonneg[OF "2.prems"(3) zero_le_one] .
  have n: "nat_of_integer (d + 1) = Suc (nat_of_integer d)"
    using "2.prems"(3) nat_of_integer_add[of d 1] by simp
  from "2.IH"[OF m _ d1 "2.prems"(4)] "2.prems"(2) n show ?case
    by (auto simp: t' bmap_Suc)
next
  case (3 f d u1 u2)
  from "3.prems" obtain v1 v2 where m: "ok (mapbnd f d u1) v1" "ok (mapbnd f d u2) v2"
    and t': "t' = v1 $ v2"
    by auto
  from "3.IH"(1)[OF m(1) _ _ "3.prems"(4)] "3.IH"(2)[OF m(1)[folded return_def] m(2) _ _ "3.prems"(4)]
    "3.prems"(2,3)
  show ?case by (auto simp: t')
qed auto

lemma bmap_0: "ok (f (integer_of_nat k)) j \<Longrightarrow> bmap f 0 k = nat_of_integer j"
  by (simp add: bmap_def)

lemma Abs_m_Abs: "Abs_m n (dB.Abs t) = Abs_m (Suc n) t"
  by (induction n) simp_all

text \<open>
  \<^term>\<open>red u is js\<close> computes a \<open>\<beta>\<close>-reduct of \<open>u\<close> applied to the bound variables \<open>is\<close>; the
  abstractions of \<open>u\<close> already consumed by \<open>js\<close> (in reverse order) are kept in the accumulator.
\<close>

lemma red_other:
  "\<not> (Pure_Term.is_Abs t \<and> is \<noteq> []) \<Longrightarrow>
    red t is js = (if is = [] \<and> js = [] then return t else do {t' \<leftarrow> mapbnd (nth js) 0 t; return (app t' is)})"
  by (cases t; cases "is"; cases js) simp_all

lemma red_mapbnd_sound:
  assumes "ok (mapbnd (nth js) 0 t) t'" "proper t" "\<forall>i\<in>set is \<union> set js. 0 \<le> i"
    "no_loose_bound (tr t) (length js)"
  shows "proper (app t' is) \<and>
    tr (app t' is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length js) (tr t) \<degree>\<degree> map BVar (rev (nats js)) \<degree>\<degree> map BVar (nats is)"
proof -
  have f: "\<forall>i j. 0 \<le> i \<longrightarrow> ok (nth js i) j \<longrightarrow> 0 \<le> j" using assms(3) by (auto simp: ok_nth)
  note m = mapbnd_sound[OF assms(1,2) order.refl f]
  have "map_BVars (bmap (nth js) 0) (tr t) = map_BVars (ren (rev (nats js))) (tr t)"
  proof (rule map_BVars_cong)
    fix k assume k: "k \<in> loose_BVars (tr t)"
    then have "k < length js" using no_loose_bound_BVars[OF assms(4)] by auto
    then have "ok (nth js (integer_of_nat k)) (js ! k)" by (simp add: ok_nth less_eq_integer.rep_eq)
    with \<open>k < length js\<close> show "bmap (nth js) 0 k = ren (rev (nats js)) k"
      by (simp add: bmap_0 ren_def rev_nth)
  qed
  moreover have "Abs_m (length js) (tr t) \<degree>\<degree> map BVar (rev (nats js)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (rev (nats js))) (tr t)"
    using Abs_m_apps_equiv[of "rev (nats js)" "tr t"] by simp
  ultimately show ?thesis using m assms(3)
    by (auto simp: proper_app tr_app' intro!: equiv_list_app list_all2_refl intro: equiv_sym)
qed

lemma red_other_sound:
  assumes "\<not> (Pure_Term.is_Abs t \<and> is \<noteq> [])" "ok (red t is js) u" "proper t"
    "\<forall>i\<in>set is \<union> set js. 0 \<le> i" "no_loose_bound (tr t) (length js)"
  shows "proper u \<and>
    tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length js) (tr t) \<degree>\<degree> map BVar (rev (nats js)) \<degree>\<degree> map BVar (nats is)"
proof (cases "is = [] \<and> js = []")
  case True
  with assms(2,3) show ?thesis by (simp add: red_other[OF assms(1)])
next
  case False
  with assms(2) obtain t' where "ok (mapbnd (nth js) 0 t) t'" "u = app t' is"
    by (auto simp: red_other[OF assms(1)] simp del: mapbnd.simps)
  with red_mapbnd_sound[OF this(1) assms(3-5)] show ?thesis by simp
qed

lemma red_sound:
  "ok (red t is js) u \<Longrightarrow> proper t \<Longrightarrow> \<forall>i\<in>set is \<union> set js. 0 \<le> i \<Longrightarrow>
    no_loose_bound (tr t) (length js) \<Longrightarrow>
    proper u \<and> tr u \<equiv>\<^sub>\<beta>\<^sub>\<eta> Abs_m (length js) (tr t) \<degree>\<degree> map BVar (rev (nats js)) \<degree>\<degree> map BVar (nats is)"
proof (induction t arbitrary: "is" js u)
  case (Abs a T s)
  show ?case
  proof (cases "is")
    case Nil
    with Abs.prems show ?thesis by (intro red_other_sound) simp_all
  next
    case (Cons i is')
    with Abs.prems(1) have "ok (red s is' (i # js)) u" by simp
    from Abs.IH[OF this] Abs.prems Cons show ?thesis by (simp add: Abs_m_Abs)
  qed
qed (rule red_other_sound; simp)+

lemma set_add_loose_bnos:
  "proper t \<Longrightarrow> 0 \<le> lev \<Longrightarrow> set (add_loose_bnos t lev js) =
    set js \<union> integer_of_nat ` {k. k + nat_of_integer lev \<in> loose_BVars (tr t)}"
proof (induction t lev js rule: add_loose_bnos.induct)
  case (1 i lev js)
  show ?case
  proof (cases "i < lev")
    case True
    with "1.prems" have "nat_of_integer i < nat_of_integer lev" by (simp add: nat_of_integer_less_iff)
    with True show ?thesis by auto
  next
    case False
    with "1.prems" have le: "nat_of_integer lev \<le> nat_of_integer i"
      by (simp add: nat_of_integer_less_iff flip: not_less)
    then have "{k. k + nat_of_integer lev \<in> loose_BVars (tr (Bound i))} = {nat_of_integer i - nat_of_integer lev}"
      by auto
    with False "1.prems" show ?thesis by (simp add: integer_of_nat_diff)
  qed
next
  case (2 a T t lev js)
  have l: "0 \<le> lev + 1" using add_nonneg_nonneg[OF "2.prems"(2) zero_le_one] .
  have "nat_of_integer (lev + 1) = Suc (nat_of_integer lev)"
    using "2.prems"(2) nat_of_integer_add[of lev 1] by simp
  with "2.IH"[OF _ l] "2.prems" show ?case by simp
qed auto

lemma set_loose_bnos: "proper t \<Longrightarrow> set (loose_bnos t) = integer_of_nat ` loose_BVars (tr t)"
  using set_add_loose_bnos[of t 0 "[]"] by (simp add: loose_bnos_def)

text \<open>A new binding \<open>F := \<lambda>is. t\<close>:\<close>

lemma match_bind_sound:
  assumes "ok (match_bind itms binders ixn T is t) itms'" "proper t" "\<forall>i\<in>set is. 0 \<le> i"
  obtains u where "vt_lookup itms ixn = None" "itms' = vt_update (ixn, (T, u)) itms" "proper u"
    "no_loose_bound (tr u) 0" "tr u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr t"
proof (cases "is = []")
  case True
  with assms(1) have "loose_bnos t = []" and up: "ok (update_new (ixn, (T, t)) itms) itms'"
    by (auto simp: match_bind_def split: if_splits)
  then have "no_loose_bound (tr t) 0"
    using set_loose_bnos[OF assms(2)] loose_BVars_no_loose_bound[of "tr t" 0] by auto
  with ok_update_new[OF up[folded return_def]] True assms(2) that show ?thesis by simp
next
  case False
  have sub: "\<forall>k\<in>loose_BVars (tr t). integer_of_nat k \<in> set is"
    using assms(1) False set_loose_bnos[OF assms(2)]
    by (auto simp: match_bind_def subset_def list_all_iff split: if_splits)
  from assms(1) False obtain t' u
    where t': "ok (if downto0 is (ilength binders - 1) then return t else mapbnd (idx is) 0 t) t'"
      and u: "ok (mkabs binders is t') u" and up: "ok (update_new (ixn, (T, u)) itms) itms'"
    by (auto simp: match_bind_def Let_def simp del: mapbnd.simps split: if_splits)
  have nat_k: "k \<in> set (nats is)" if "k \<in> loose_BVars (tr t)" for k
    using sub that by (force simp: image_iff)
  have key: "proper t' \<and> no_loose_bound (tr t') (length is) \<and> map_BVars (ren (nats is)) (tr t') = tr t"
  proof (cases "downto0 is (ilength binders - 1)")
    case True
    with t' have tt: "t' = t" by simp
    obtain m where m: "nats is = downs m" using downto0_nats[OF True] by blast
    have "map_BVars (ren (nats is)) (tr t) = map_BVars id (tr t)"
      by (rule map_BVars_cong) (use nat_k in \<open>auto simp: m ren_downs\<close>)
    moreover have "no_loose_bound (tr t) (length is)"
      by (rule loose_BVars_no_loose_bound) (use nat_k m in \<open>fastforce dest: arg_cong[of _ _ length]\<close>)
    ultimately show ?thesis using assms(2) by (simp add: tt map_BVars_id)
  next
    case False
    with t' have mb: "ok (mapbnd (idx is) 0 t) t'" by simp
    have f: "\<forall>i j. 0 \<le> i \<longrightarrow> ok (idx is i) j \<longrightarrow> 0 \<le> j" by (auto simp: ok_idx less_eq_integer.rep_eq)
    note m = mapbnd_sound[OF mb assms(2) order.refl f]
    have r: "ren (nats is) (bmap (idx is) 0 k) = k \<and> bmap (idx is) 0 k < length is"
      if "k \<in> loose_BVars (tr t)" for k
    proof -
      from m that obtain j where j: "ok (idx is (integer_of_nat k)) j" by auto
      from ok_idx_ren[OF j assms(3)] bmap_0[of "idx is" k j, OF j] show ?thesis by (simp add: less_eq_integer.rep_eq)
    qed
    have "map_BVars (ren (nats is)) (tr t') = map_BVars id (tr t)"
      using m r by (auto simp: map_BVars_comp intro!: map_BVars_cong)
    moreover have "no_loose_bound (tr t') (length is)"
      using m r by (auto simp: loose_BVars_map_BVars intro!: loose_BVars_no_loose_bound)
    ultimately show ?thesis using m by (simp add: map_BVars_id)
  qed
  have tu: "tr u = Abs_m (length is) (tr t')" "proper u" using ok_mkabs[OF u] key by simp_all
  have "tr u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> map_BVars (ren (nats is)) (tr t')"
    using Abs_m_apps_equiv[of "nats is" "tr t'"] by (simp add: tu)
  with key tu ok_update_new[OF up[folded return_def]] that show ?thesis
    by (simp add: loose_bound_Abs_m)
qed

declare sup_apply[simp]

end
