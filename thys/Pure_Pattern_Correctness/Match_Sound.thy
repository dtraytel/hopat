section \<open>Soundness of Matching\<close>

theory Match_Sound
  imports Match_Types Match_Pattern Poly_Inst
begin

context csig
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

end

context wf_csig
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


context csig
begin

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

lemma minst_list_comb: "minst env (list_comb h ts) = minst env h \<degree>\<degree> map (minst env) ts"
  by (induction ts arbitrary: h) (simp_all add: list_comb_def minst_simps)

lemma mbound_list_comb: "mbound env (list_comb h ts) \<longleftrightarrow> mbound env h \<and> (\<forall>t\<in>set ts. mbound env t)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def mbound_simps)

lemma ctys_list_comb: "ctys (list_comb h ts) = ctys h \<union> \<Union> (ctys ` set ts)"
  by (induction ts arbitrary: h) (auto simp: list_comb_def)


subsection \<open>Higher-order matching\<close>

end

context wf_csig
begin

lemma mtch_sound:
  assumes "mtch alg' binders pt ob env = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env' \<Longrightarrow> proper pt \<Longrightarrow> proper ob \<Longrightarrow> mte_ok (snd env) \<Longrightarrow>
    \<forall>T\<in>ctys pt. wft ar T \<Longrightarrow> \<forall>T\<in>ctys ob. wft ar T \<Longrightarrow>
    mextends env env' \<and> mte_ok (snd env') \<and> mbound env' pt \<and> minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  using assms
proof (induction alg' binders pt ob env r arbitrary: env' rule: mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' binders pt ob env r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" and r: "r = Ok env'" using prems by simp_all
  note h = "1.hyps"[unfolded alg' r]
  note IH = "1.IH"[OF _ refl refl]
  have pp: "proper pt" "proper ob" and ok: "mte_ok itms" and wp: "\<forall>T\<in>ctys pt. wft ar T"
    and wo: "\<forall>T\<in>ctys ob. wft ar T"
    using prems e by simp_all
  text \<open>Arguments of rigid heads are matched from left to right:\<close>
  have args: "mextends e0 env' \<and> mte_ok (snd env') \<and> (\<forall>p\<in>set ps. mbound env' p) \<and>
      list_all2 (\<lambda>p q. minst env' p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ps qs"
    if m: "ok (handle (zip_eq ps qs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg binders p q) pqs e0))
      (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env'"
      and e0: "mte_ok (snd e0)" and ps: "\<forall>p\<in>set ps. proper p \<and> (\<forall>T\<in>ctys p. wft ar T)"
      and qs: "\<forall>q\<in>set qs. proper q \<and> (\<forall>T\<in>ctys q. wft ar T)"
    for e0 ps qs
  proof -
    have nh: "\<not> ok (case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) y" for e and y :: match_env
      by (cases e) simp_all
    from m nh have len: "length ps = length qs"
      and f: "ok (foldM (\<lambda>(p, q). fm alg binders p q) (zip ps qs) e0) env'"
      by (auto simp: ok_handle ok_zip_eq)
    have "mte_ok (snd env') \<and> mextends e0 env' \<and>
      (\<forall>x\<in>set (zip ps qs). mbound env' (fst x) \<and> minst env' (fst x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (snd x))"
    proof (rule foldM_ok[OF f, where P="\<lambda>e. mte_ok (snd e)" and R="\<lambda>e' e. mextends e e'"
        and Q="\<lambda>x e. mbound e (fst x) \<and> minst e (fst x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (snd x)"])
      fix x e e1 assume x: "x \<in> set (zip ps qs)" and m1: "ok ((\<lambda>(p, q). fm alg binders p q) x e) e1"
        and ok1: "mte_ok (snd e)"
      obtain p q where xpq: "x = (p, q)" by force
      with x have "p \<in> set ps" "q \<in> set qs" by (auto dest: set_zip_leftD set_zip_rightD)
      with IH[of binders p q e e1] m1 ok1 ps qs xpq
      show "mte_ok (snd e1) \<and> mextends e e1 \<and> mbound e1 (fst x) \<and> minst e1 (fst x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (snd x)"
        by simp
    next
      fix x e1 e2 assume "mbound e1 (fst x) \<and> minst e1 (fst x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (snd x)" "mextends e1 e2"
      then show "mbound e2 (fst x) \<and> minst e2 (fst x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (snd x)"
        by (simp add: mbound_mono minst_mono)
    qed (auto intro: mextends_trans e0)
    then have "mte_ok (snd env')" "mextends e0 env'"
      and l2: "list_all2 (\<lambda>p q. mbound env' p \<and> minst env' p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ps qs"
      using len by (auto simp: list_all2_iff)
    moreover from l2 have "\<forall>p\<in>set ps. mbound env' p" by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
    moreover from l2 have "list_all2 (\<lambda>p q. minst env' p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) ps qs"
      by (rule list_all2_mono) simp
    ultimately show ?thesis by simp
  qed
  show ?case
  proof (cases "Pure_Term.is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = pterm.Abs ns Ts ts" by (cases pt) auto
    have ts: "proper ts" "\<forall>T\<in>ctys ts. wft ar T" using pp wp by (simp_all add: pt)
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from h have m: "ok (fm alg ((nt, Tt) # binders) ts tt env) env'" by (simp add: e pt ob)
      have "proper tt" "\<forall>T\<in>ctys tt. wft ar T" using pp wo by (simp_all add: ob)
      from IH[OF m ts(1) this(1) prems(5) ts(2) this(2)]
      show ?thesis by (simp add: pt ob minst_simps mbound_simps equiv_Abs)
    next
      case False
      from h False obtain Tt where m: "ok (fm alg ((ns, Tt) # binders) ts (incr ob $ Bound 0) env) env'"
        by (auto simp: e pt)
      have "proper (incr ob $ Bound 0)" "\<forall>T\<in>ctys (incr ob $ Bound 0). wft ar T"
        using pp wo by (simp_all add: proper_incr ctys_incr)
      from IH[OF m ts(1) this(1) prems(5) ts(2) this(2)]
      have i: "mextends env env'" "mte_ok (snd env')" "mbound env' ts"
        "minst env' ts \<equiv>\<^sub>\<beta>\<^sub>\<eta> lift (tr ob) 0 \<degree> BVar 0"
        by (simp_all add: tr_incr[OF pp(2)])
      have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
        using equiv_trans[OF equiv_Abs[OF i(4)] eta_lift_equiv] by (simp add: pt minst_simps)
      with i show ?thesis by (simp add: pt mbound_simps)
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "Pure_Term.is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = pterm.Abs nt Tt tt" by (cases ob) auto
      from h pA have m: "ok (fm alg ((nt, Tt) # binders) (incr pt $ Bound 0) tt env) env'"
        by (simp add: e ob)
      have "proper (incr pt $ Bound 0)" "proper tt" "\<forall>T\<in>ctys (incr pt $ Bound 0). wft ar T"
        "\<forall>T\<in>ctys tt. wft ar T"
        using pp wp wo by (simp_all add: ob proper_incr ctys_incr)
      from IH[OF m this(1,2) prems(5) this(3,4)]
      have i: "mextends env env'" "mte_ok (snd env')" "mbound env' (incr pt $ Bound 0)"
        "minst env' (incr pt $ Bound 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr tt"
        by simp_all
      have mb: "mbound env' pt" using i(3) by (simp add: mbound_simps mbound_incr)
      have "minst env' (incr pt $ Bound 0) = lift (minst env' pt) 0 \<degree> BVar 0"
        by (simp add: minst_simps minst_incr[OF i(2) pp(1)])
      with equiv_Abs[OF i(4)] have "dB.Abs (lift (minst env' pt) 0 \<degree> BVar 0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
        by (simp add: ob)
      then have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
        using eta_lift_equiv[of "minst env' pt"] equiv_sym equiv_trans by blast
      with i(1,2) mb show ?thesis by simp
    next
      case oA: False
      obtain ph pargs where sp: "strip_comb pt = (ph, pargs)" by force
      have ptc: "pt = list_comb ph pargs" by (rule strip_comb_list_comb[OF sp])
      have pa: "proper ph" "\<forall>p\<in>set pargs. proper p \<and> (\<forall>T\<in>ctys p. wft ar T)" "\<forall>T\<in>ctys ph. wft ar T"
        using pp(1) wp by (auto simp: ptc proper_list_comb ctys_list_comb)
      note h = h[unfolded e, simplified pA oA if_False sp Let_def prod.case]
      show ?thesis
      proof (cases "is_Var ph")
        case True
        then obtain ixn T where ph: "ph = pterm.Var ixn T" by (cases ph) auto
        from h obtain "is" lr where io: "ok (ints_of pargs) is" and lk: "ok (lookup1 itms ixn T) lr"
          and h2: "ok (case lr of
              None \<Rightarrow> match_bind itms binders ixn T is ob \<bind> (\<lambda>itms'. return (iTs, itms'))
            | Some u \<Rightarrow> red u is [] \<bind> (\<lambda>u'. if aeconv ob u' then return (iTs, itms) else raise Match)) env'"
          by (auto simp: ph)
        from io have pargs: "pargs = map Bound is" by (simp add: ok_ints_of)
        have is0: "\<forall>i\<in>set is. 0 \<le> i" using pa(2) by (auto simp: pargs)
        have mi: "minst env'' pt = msub (snd env'') (code (AVar ixn)) \<degree>\<degree> map BVar (nats is)" for env''
          by (simp add: ptc ph pargs minst_list_comb minst_simps comp_def)
        have mb: "mbound env'' pt \<longleftrightarrow> vt_lookup (snd env'') ixn \<noteq> None" for env''
          unfolding ptc ph pargs mbound_list_comb by (simp add: mbound_def)
        from lookup1_cases[OF lk[folded return_def]] show ?thesis
        proof (elim disjE exE conjE)
          assume lr: "lr = None" and none: "vt_lookup itms ixn = None"
          from h2 lr obtain itms' where mt: "ok (match_bind itms binders ixn T is ob) itms'"
            and env': "env' = (iTs, itms')"
            by auto
          obtain u where u: "itms' = vt_update (ixn, (T, u)) itms" "proper u" "no_loose_bound (tr u) 0"
            "tr u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
            by (rule match_bind_sound[OF mt pp(2) is0])
          have "mextends env env'" using none by (auto simp: e env' u(1) mextends_def)
          moreover have "mte_ok itms'" using ok u(2,3) by (auto simp: u(1) mte_ok_def)
          ultimately show ?thesis using u(4) by (simp add: env' mi mb u(1))
        next
          fix u assume lr: "lr = Some u" and some: "vt_lookup itms ixn = Some (T, u)"
          from h2 lr obtain u' where rd: "ok (red u is []) u'" and ae: "aeconv ob u'"
            and env': "env' = (iTs, itms)"
            by (auto split: if_splits)
          have pu: "proper u" "no_loose_bound (tr u) 0" using mte_okD[OF ok some] by simp_all
          from red_sound[OF rd pu(1)] is0 pu(2)
          have r: "proper u'" "tr u' \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr u \<degree>\<degree> map BVar (nats is)" by simp_all
          have "tr u \<degree>\<degree> map BVar (nats is) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
            using equiv_trans[OF equiv_sym[OF r(2)] equiv_sym[OF aeconv_tr[OF pp(2) r(1) ae]]] .
          with some ok show ?thesis by (simp add: env' e mi mb)
        qed
      next
        case False
        obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
        have obc: "ob = list_comb oh oargs" by (rule strip_comb_list_comb[OF so])
        have oa: "\<forall>q\<in>set oargs. proper q \<and> (\<forall>T\<in>ctys q. wft ar T)" "\<forall>T\<in>ctys oh. wft ar T"
          using pp(2) wo by (auto simp: obc proper_list_comb ctys_list_comb)
        note h = h[simplified False if_False so Let_def prod.case]
        text \<open>A rigid head matched against an object head, followed by the arguments:\<close>
        have rig: "mextends env env' \<and> mte_ok (snd env') \<and> mbound env' pt \<and> minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
          if m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg binders p q) pqs (iTs', itms)))
              (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env'"
            and te: "textends iTs iTs'"
            and hd: "\<And>env''. mextends (iTs', itms) env'' \<Longrightarrow> mbound env'' ph \<and> minst env'' ph = tr oh"
          for iTs'
        proof -
          from args[OF m _ pa(2) oa(1)] ok
          have a: "mextends (iTs', itms) env'" "mte_ok (snd env')" "\<forall>p\<in>set pargs. mbound env' p"
            "list_all2 (\<lambda>p q. minst env' p \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr q) pargs oargs"
            by simp_all
          note hd' = hd[OF a(1)]
          have "mextends env env'" using te a(1) by (auto simp: e mextends_def intro: textends_trans)
          moreover have "list_all2 (\<equiv>\<^sub>\<beta>\<^sub>\<eta>) (map (minst env') pargs) (map tr oargs)"
            using a(4) by (simp add: list_all2_map1 list_all2_map2)
          then have "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
            using equiv_list_app[OF equiv_refl] hd' by (simp add: ptc obc minst_list_comb tr_list_comb)
          ultimately show ?thesis using a(2,3) hd' by (simp add: ptc mbound_list_comb)
        qed
        text \<open>Constants and free variables: their types are matched first.\<close>
        have typed: "tsubst (mtinst (fst env'')) Ta = Tb \<and> (\<forall>(v, S)\<in>tvars Ta. vt_lookup (fst env'') v \<noteq> None)"
          if "ok (typ_match alg Ta Tb iTs) iTs'" "mextends (iTs', itms) env''" "wft ar Ta" "wft ar Tb"
          for Ta Tb iTs' env''
        proof -
          note s = typ_match_sound[OF that(3,4) that(1)[folded return_def]]
          have te: "textends iTs' (fst env'')" using that(2) by (simp add: mextends_def)
          have "tsubst (mtinst (fst env'')) Ta = Tb"
            using tsubst_mtinst_mono[OF te s(3)] s(2) by simp
          moreover have "\<forall>(v, S)\<in>tvars Ta. vt_lookup (fst env'') v \<noteq> None"
            using s(3) te by (fastforce simp: textends_def)
          ultimately show ?thesis by simp
        qed
        show ?thesis
        proof (cases ph)
          case ph: (Const a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Const b Tb)
            from h ph oh obtain iTs' where ab: "a = b" and tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg binders p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env'"
              by (auto split: if_splits)
            have te: "textends iTs iTs'" using tm typ_match_textends[unfolded return_def] by simp
            have w: "wft ar Ta" "wft ar Tb" using pa(3) oa(2) by (simp_all add: ph oh)
            show ?thesis
              by (rule rig[OF m te]) (use typed[OF tm _ w] in \<open>simp add: ph oh ab minst_simps mbound_def\<close>)
          qed (use h ph in auto)
        next
          case ph: (Free a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Free b Tb)
            from h ph oh obtain iTs' where ab: "a = b" and tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg binders p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env'"
              by (auto split: if_splits)
            have te: "textends iTs iTs'" using tm typ_match_textends[unfolded return_def] by simp
            have w: "wft ar Ta" "wft ar Tb" using pa(3) oa(2) by (simp_all add: ph oh)
            show ?thesis
              by (rule rig[OF m te]) (use typed[OF tm _ w] in \<open>simp add: ph oh ab minst_simps mbound_def\<close>)
          qed (use h ph in auto)
        next
          case ph: (Bound i)
          show ?thesis
          proof (cases oh)
            case oh: (Bound j)
            from h ph oh have ij: "i = j"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg binders p q) pqs (iTs, itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env'"
              by (auto split: if_splits)
            show ?thesis
              by (rule rig[OF m textends_refl]) (simp add: ph oh ij minst_simps mbound_def)
          qed (use h ph in auto)
        qed (use False h strip_comb_head[OF sp] in auto)
      qed
    qed
  qed
qed



subsection \<open>Soundness\<close>

text \<open>
  A successful match extends the environment by bindings for the variables of the pattern
  such that the instance of the pattern is \<open>\<beta>\<eta>\<close>-equivalent to the object.
\<close>

theorem first_order_match_sound:
  assumes "ok (first_order_match alg pt ob env) env'" "proper pt" "proper ob"
    "no_loose_bound (tr ob) 0" "mte_ok (snd env)" "\<forall>T\<in>ctys pt. wft ar T" "\<forall>T\<in>ctys ob. wft ar T"
  shows "mextends env env'" "mte_ok (snd env')" "mbound env' pt" "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  using fo_mtch_sound[OF assms(1)[unfolded first_order_match_def] refl refl assms(2-3) _ assms(5-7)] assms(4)
  by simp_all

theorem match_sound:
  assumes "ok (match alg pt ob env) env'" "proper pt" "proper ob"
    "no_loose_bound (tr ob) 0" "mte_ok (snd env)" "\<forall>T\<in>ctys pt. wft ar T" "\<forall>T\<in>ctys ob. wft ar T"
  shows "mextends env env'" "mte_ok (snd env')" "mbound env' pt" "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
proof -
  from assms(1) obtain pT oT iTs where tm: "ok (typ_match alg pT oT (fst env)) iTs"
    and m: "ok (handle (mtch alg [] pt ob (iTs, snd env))
      (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise e)) env'"
    by (auto simp: match_def Let_def)
  have e1: "mextends env (iTs, snd env)"
    using tm typ_match_textends[unfolded return_def] by (simp add: mextends_def)
  have ok1: "mte_ok (snd (iTs, snd env))" using assms(5) by simp
  have nh: "ok (case e of Pattern \<Rightarrow> m' | _ \<Rightarrow> raise e) y \<Longrightarrow> e = Pattern \<and> ok m' y"
    for e and m' :: "match_env M" and y by (cases e) simp_all
  from m have "mextends (iTs, snd env) env' \<and> mte_ok (snd env') \<and> mbound env' pt \<and> minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
  proof (auto simp: ok_handle dest!: nh)
    assume "ok (mtch alg [] pt ob (iTs, snd env)) env'"
    from mtch_sound[OF this refl refl assms(2,3) ok1 assms(6,7)]
    show "mextends (iTs, snd env) env'" "mte_ok (snd env')" "mbound env' pt" "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
      by simp_all
  next
    assume "ok (first_order_match alg pt ob (iTs, snd env)) env'"
    from first_order_match_sound[OF this assms(2-4) ok1 assms(6,7)]
    show "mextends (iTs, snd env) env'" "mte_ok (snd env')" "mbound env' pt" "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
      by simp_all
  qed
  with e1 show "mextends env env'" "mte_ok (snd env')" "mbound env' pt" "minst env' pt \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr ob"
    by (auto intro: mextends_trans)
qed

end

context csig
begin

declare sup_apply[simp]

end

end
