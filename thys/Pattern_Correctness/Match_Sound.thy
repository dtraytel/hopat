section \<open>Soundness of Matching\<close>

theory Match_Sound
  imports Match_Lemmas
begin

context pure_sig
begin

text \<open>
  A matching environment \<open>(tye, te)\<close> instantiates the type variables of a pattern by the
  one-pass instantiation \<^term>\<open>mtinst tye\<close> (\<open>Envir.subst_type\<close>) and then its variables by the
  bindings of \<open>te\<close> (\<open>Envir.subst_term\<close>): a variable is identified by its name and its
  instantiated type. The object is not instantiated: its variables behave like constants.
\<close>

lemma ok_typ_match_m [simp]: "ok (typ_match_m alg' T U tye) tye' \<longleftrightarrow> ok (typ_match alg' T U tye) tye'"
  by (auto simp: typ_match_m_def handle_def return_def raise_def split: option.splits res.splits exn.splits)

definition msubst :: "tyenv \<Rightarrow> tenv \<Rightarrow> vsubst" where
  "msubst tye te x T = (case vt_lookup te x of
     Some (U, u) \<Rightarrow> if tsubst (mtinst tye) U = T then u else Var x T
   | None \<Rightarrow> Var x T)"

definition minst :: "match_env \<Rightarrow> pterm \<Rightarrow> pterm" where
  "minst env = ap (mtinst (fst env)) (msubst (fst env) (snd env))"

text \<open>The bindings are closed terms of the instantiated types:\<close>

definition btyped :: "tyenv \<Rightarrow> tenv \<Rightarrow> bool" where
  "btyped tye te \<longleftrightarrow> (\<forall>x U u. vt_lookup te x = Some (U, u) \<longrightarrow>
    closed u \<and> (\<forall>e. e \<turnstile> u : tsubst (mtinst tye) U))"

definition mextends :: "match_env \<Rightarrow> match_env \<Rightarrow> bool" where
  "mextends env env' \<longleftrightarrow> textends (fst env) (fst env') \<and>
    (\<forall>x b. vt_lookup (snd env) x = Some b \<longrightarrow> vt_lookup (snd env') x = Some b)"

text \<open>The variables of a term are bound, with their types:\<close>

definition mvars :: "match_env \<Rightarrow> pterm \<Rightarrow> bool" where
  "mvars env t \<longleftrightarrow> (\<forall>x T. (x, T) \<in> vars t \<longrightarrow> (\<exists>u. vt_lookup (snd env) x = Some (T, u)))"

lemma mextends_refl [simp]: "mextends env env"
  by (simp add: mextends_def textends_def)

lemma mextends_trans: "mextends env1 env2 \<Longrightarrow> mextends env2 env3 \<Longrightarrow> mextends env1 env3"
  by (auto simp: mextends_def intro: textends_trans)

lemma mvars_mono: "mextends env env' \<Longrightarrow> mvars env t \<Longrightarrow> mvars env' t"
  unfolding mvars_def mextends_def by fast

lemma btyped_update:
  "btyped tye te \<Longrightarrow> closed u \<Longrightarrow> (\<And>e. e \<turnstile> u : tsubst (mtinst tye) U) \<Longrightarrow>
    btyped tye (vt_update (x, (U, u)) te)"
  unfolding btyped_def by auto

lemma wt_subst_msubst: "btyped tye te \<Longrightarrow> wt_subst (msubst tye te)"
  unfolding wt_subst_def closed_subst_def btyped_def msubst_def
  by (auto simp: closed_def split: option.splits)

lemma minst_simps [simp]:
  "minst env (Const c T) = Const c (tsubst (mtinst (fst env)) T)"
  "minst env (Free y T) = Free y (tsubst (mtinst (fst env)) T)"
  "minst env (Bound i) = Bound i"
  "minst env (Abs a T t) = Abs a (tsubst (mtinst (fst env)) T) (minst env t)"
  "minst env (s $ t) = minst env s $ minst env t"
  by (simp_all add: minst_def)

lemma minst_Var: "vt_lookup (snd env) x = Some (T, u) \<Longrightarrow> minst env (Var x T) = u"
  by (simp add: minst_def msubst_def)

lemma minst_apps: "minst env (s \<degree>\<degree> ts) = minst env s \<degree>\<degree> map (minst env) ts"
  by (simp add: minst_def ap_apps)

lemma minst_incr: "btyped (fst env) (snd env) \<Longrightarrow> minst env (incr t) = lift (minst env t) 0"
  by (simp add: minst_def incr_def incr_aux_lift ap_lift wt_subst_msubst)

lemma typing_minst: "e \<turnstile> inst (mtinst tye) t : T \<Longrightarrow> btyped tye te \<Longrightarrow> e \<turnstile> minst (tye, te) t : T"
  by (simp add: minst_def typing_ap wt_subst_msubst)

lemma typs_incr: "typs (incr t) = typs t"
proof -
  have "typs (incr_aux d t) = typs t" for d by (induction d t rule: incr_aux.induct) auto
  then show ?thesis by (simp add: incr_def)
qed

lemma vars_incr: "vars (incr t) = vars t"
  by (simp add: incr_def)

lemma mvars_simps:
  "mvars env (s $ t) \<longleftrightarrow> mvars env s \<and> mvars env t"
  "mvars env (Abs a T t) \<longleftrightarrow> mvars env t"
  "mvars env (incr t) \<longleftrightarrow> mvars env t"
  by (auto simp: mvars_def vars_incr)

lemma mvars_apps: "mvars env (s \<degree>\<degree> ts) \<longleftrightarrow> mvars env s \<and> (\<forall>t\<in>set ts. mvars env t)"
  unfolding mvars_def vars_apps by blast

lemma lookup1_cases:
  "ok (lookup1 te x T) r \<Longrightarrow>
    (r = None \<and> vt_lookup te x = None) \<or> (\<exists>u. r = Some u \<and> vt_lookup te x = Some (T, u))"
  by (auto simp: lookup1_def var_clash_def split: option.splits if_splits)

lemma typ_match_ext: "ok (typ_match alg' T U tye) tye' \<Longrightarrow> textends tye tye'"
  using typ_match_textends[of alg' T U tye tye'] by (simp add: return_def)

lemma typ_match_inst:
  assumes "ok (typ_match alg T U tye) tye'" "wft ar T" "wft ar U" "textends tye' tye''"
  shows "tsubst (mtinst tye'') T = U"
proof -
  note s = typ_match_sound[OF assms(2,3) assms(1)[folded return_def]]
  show ?thesis using mtinst_textends[OF assms(4) s(3)] s(2) by simp
qed

lemma cert_wft: "cert_typ alg ar T \<Longrightarrow> wft ar T"
  by (simp add: cert_typ_def)

lemma wt_closedI: "e \<turnstile> t : T \<Longrightarrow> wt t"
  unfolding wt_def by blast


text \<open>The type variables bound by a type environment:\<close>

definition tbnd :: "tyenv \<Rightarrow> (indexname \<times> psort) set" where
  "tbnd tye = {(v, S). vt_lookup tye v \<noteq> None}"

lemma tbnd_mono: "textends tye tye' \<Longrightarrow> tbnd tye \<subseteq> tbnd tye'"
  unfolding tbnd_def textends_def by fastforce

lemma mtinst_tbnd: "textends tye tye' \<Longrightarrow> tvars T \<subseteq> tbnd tye \<Longrightarrow> tsubst (mtinst tye') T = tsubst (mtinst tye) T"
  by (rule mtinst_textends) (auto simp: tbnd_def)

lemma typ_match_tbnd: "ok (typ_match alg T U tye) tye' \<Longrightarrow> wft ar T \<Longrightarrow> wft ar U \<Longrightarrow> tvars T \<subseteq> tbnd tye'"
  using typ_match_sound(3)[of T U tye tye'] by (auto simp: tbnd_def return_def)

text \<open>Bindings whose types have bound type variables remain typed in extensions:\<close>

definition bstable :: "match_env \<Rightarrow> bool" where
  "bstable env \<longleftrightarrow> (\<forall>x U u. vt_lookup (snd env) x = Some (U, u) \<longrightarrow> tvars U \<subseteq> tbnd (fst env))"

lemma btyped_textends:
  "btyped tye te \<Longrightarrow> bstable (tye, te) \<Longrightarrow> textends tye tye' \<Longrightarrow> btyped tye' te"
  unfolding btyped_def bstable_def using mtinst_tbnd by fastforce

lemma bstable_textends: "bstable (tye, te) \<Longrightarrow> textends tye tye' \<Longrightarrow> bstable (tye', te)"
  unfolding bstable_def using tbnd_mono by fastforce

lemma bstable_update: "bstable (tye, te) \<Longrightarrow> tvars U \<subseteq> tbnd tye \<Longrightarrow> bstable (tye, vt_update (x, (U, u)) te)"
  unfolding bstable_def by auto


subsection \<open>First-order matching\<close>

text \<open>
  The postcondition of first-order matching: the environment is extended, the variables of the
  pattern are bound, and for every extension of the result to a final environment and every
  typing of the object, the new bindings are typed, and the instance of the pattern under the
  final environment has the type of the object and is equivalent to it.
\<close>

definition fo_post :: "match_env \<Rightarrow> match_env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "fo_post env env1 pt ob \<longleftrightarrow> mextends env env1 \<and> mvars env1 pt \<and>
    (\<forall>e Ty. e \<turnstile> ob : Ty \<longrightarrow> bstable env \<longrightarrow> bstable env1) \<and>
    (\<forall>tye te e Ty. mextends env1 (tye, te) \<longrightarrow> e \<turnstile> ob : Ty \<longrightarrow> btyped tye (snd env) \<longrightarrow>
      btyped tye (snd env1) \<and>
      (btyped tye te \<longrightarrow> e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob))"

lemma fo_postI:
  assumes "mextends env env1" "mvars env1 pt"
    and "\<And>tye te e Ty. mextends env1 (tye, te) \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow>
      btyped tye (snd env1)"
    and "\<And>tye te e Ty. mextends env1 (tye, te) \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow>
      btyped tye te \<Longrightarrow> e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
    and "\<And>e Ty. e \<turnstile> ob : Ty \<Longrightarrow> bstable env \<Longrightarrow> bstable env1"
  shows "fo_post env env1 pt ob"
  using assms unfolding fo_post_def by blast

lemma fo_postD:
  assumes "fo_post env env1 pt ob"
  shows "mextends env env1" "mvars env1 pt"
    and "mextends env1 (tye, te) \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow> btyped tye (snd env1)"
    and "mextends env1 (tye, te) \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow> btyped tye te \<Longrightarrow>
      e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
  using assms unfolding fo_post_def by blast+

lemma fo_postD_bstable: "fo_post env env1 pt ob \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> bstable env \<Longrightarrow> bstable env1"
  unfolding fo_post_def by blast

text \<open>\<open>\<eta>\<close>-expansion of the instance of a pattern against an abstraction:\<close>

lemma eta_expand_conv:
  assumes "e\<langle>0:U\<rangle> \<turnstile> lift p 0 $ Bound 0 : Ty'" "lift p 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u"
    "e \<turnstile> Abs b U u : U \<rightarrow>\<^sub>T Ty'"
  shows "e \<turnstile> p : U \<rightarrow>\<^sub>T Ty'" "p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b U u"
proof -
  from assms(1) obtain A where a: "e\<langle>0:U\<rangle> \<turnstile> lift p 0 : A \<rightarrow>\<^sub>T Ty'" "e\<langle>0:U\<rangle> \<turnstile> Bound 0 : A"
    by blast
  from a(2) have "A = U" by (rule typing_elims(1)) simp
  with a(1) have tl: "e\<langle>0:U\<rangle> \<turnstile> lift p 0 : U \<rightarrow>\<^sub>T Ty'" by simp
  then show tp: "e \<turnstile> p : U \<rightarrow>\<^sub>T Ty'" by (rule typing_lift0D)
  have U: "cert_typ alg ar U" using assms(3) by blast
  have ta: "e \<turnstile> Abs b U (lift p 0 $ Bound 0) : U \<rightarrow>\<^sub>T Ty'"
    by (rule typing.Abs[OF U], rule typing.App[OF tl]) auto
  have "p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b U (lift p 0 $ Bound 0)"
    by (rule conv_sym, rule beta_eta_conv[OF eta_reds_beta_eta_reds[OF r_into_rtranclp[of eta, OF eta_lift_Bound0]]])
      (rule wt_closedI[OF ta])
  also have "Abs b U (lift p 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b U u"
    using wt_closedI[OF ta] wt_closedI[OF assms(3)] assms(2) by (rule conv_Abs)
  finally show "p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs b U u" .
qed

lemma fo_mtch_sound:
  assumes "fo_mtch alg' inAbs env pt ob = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env1 \<Longrightarrow> (\<not> inAbs \<longrightarrow> closed ob) \<Longrightarrow> \<forall>T\<in>typs pt. wft ar T \<Longrightarrow>
    fo_post env env1 pt ob"
  using assms
proof (induction alg' inAbs env pt ob r arbitrary: env1 rule: fo_mtch.raw_induct[rotated, consumes 1])
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
  have cl: "\<not> inAbs \<longrightarrow> closed ob" and wp: "\<forall>T\<in>typs pt. wft ar T" using prems by simp_all
  text \<open>The pattern is \<open>\<eta>\<close>-expanded against an abstraction:\<close>
  have eta: "fo_post instsp env1 pt ob"
    if ob: "ob = Abs b U u" and m: "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" for b U u
  proof -
    have "\<forall>T\<in>typs (incr pt $ Bound 0). wft ar T" using wp by (simp add: typs_incr)
    from IH[OF m _ this] have i: "fo_post instsp env1 (incr pt $ Bound 0) u" by simp
    note ib = fo_postD_bstable[OF i] and i = fo_postD[OF i]
    show ?thesis
    proof (rule fo_postI)
      show "mextends instsp env1" by (rule i(1))
      show "mvars env1 pt" using i(2) by (simp add: mvars_simps)
    next
      fix tye te e Ty assume ex: "mextends env1 (tye, te)" and ty: "e \<turnstile> ob : Ty"
        and bt: "btyped tye (snd instsp)"
      from ty obtain Ty' where Ty: "Ty = U \<rightarrow>\<^sub>T Ty'" and tu: "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" by (auto simp: ob)
      show "btyped tye (snd env1)" by (rule i(3)[OF ex tu bt])
      assume bf: "btyped tye te"
      let ?p = "minst (tye, te) pt"
      have mi: "minst (tye, te) (incr pt $ Bound 0) = lift ?p 0 $ Bound 0"
        using bf by (simp add: minst_incr)
      from i(4)[OF ex tu bt bf] mi have "e\<langle>0:U\<rangle> \<turnstile> lift ?p 0 $ Bound 0 : Ty'"
        and "lift ?p 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" by simp_all
      from eta_expand_conv[OF this] ty show "e \<turnstile> ?p : Ty \<and> ?p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by (simp add: ob Ty)
    next
      fix e Ty assume ty: "e \<turnstile> ob : Ty" and bs: "bstable instsp"
      from ty obtain Ty' where "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" by (auto simp: ob)
      from ib[OF this bs] show "bstable env1" .
    qed
  qed
  show ?case
  proof (cases "is_Var pt")
    case True
    then obtain ixn T where pt: "pt = Var ixn T" by (cases pt) auto
    from h have nopen: "\<not> (inAbs \<and> is_open ob)" by (auto simp: pt split: if_splits)
    with cl have clo: "closed ob" by (auto simp: is_open_closed)
    have wT: "wft ar T" using wp by (simp add: pt)
    from h nopen obtain lr where lk: "ok (lookup1 insts ixn T) lr"
      and h2: "ok (case lr of
          None \<Rightarrow> do {
            tT \<leftarrow> fastype_of ob;
            tyinsts' \<leftarrow> typ_match_m alg T tT tyinsts;
            insts' \<leftarrow> update_new (ixn, (T, ob)) insts;
            return (tyinsts', insts')}
        | Some u \<Rightarrow> if aeconv ob u then return (tyinsts, insts) else raise Match) env1"
      by (auto simp: pt)
    from lookup1_cases[OF lk] show ?thesis
    proof (elim disjE exE conjE)
      assume lr: "lr = None" and none: "vt_lookup insts ixn = None"
      from h2[unfolded lr] obtain tT tyinsts' where ft: "ok (fastype_of ob) tT"
        and tm: "ok (typ_match alg T tT tyinsts) tyinsts'"
        and env1: "env1 = (tyinsts', vt_update (ixn, (T, ob)) insts)"
        by (auto simp: ok_update_new)
      show ?thesis
      proof (rule fo_postI)
        show "mextends instsp env1" using typ_match_ext[OF tm] none by (auto simp: e env1 mextends_def)
        show "mvars env1 pt" by (simp add: env1 pt mvars_def)
      next
        fix tye te e Ty assume ex: "mextends env1 (tye, te)" and ty: "e \<turnstile> ob : Ty"
          and bt: "btyped tye (snd instsp)"
        have tT: "tT = Ty" using ft fastype_of_closed[OF ty clo] by (simp add: return_def)
        have wO: "wft ar Ty" using typing_cert_closed[OF ty clo] by (rule cert_wft)
        have te: "textends tyinsts' tye" using ex by (simp add: env1 mextends_def)
        have T: "tsubst (mtinst tye) T = Ty" using typ_match_inst[OF tm[unfolded tT] wT wO te] .
        show "btyped tye (snd env1)"
          using bt clo typing_closed[OF ty clo] by (simp add: e env1 T btyped_update)
        have "vt_lookup te ixn = Some (T, ob)" using ex unfolding env1 mextends_def by (cases ixn) auto
        then have "minst (tye, te) pt = ob" by (simp add: pt minst_Var)
        with ty show "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by simp
      next
        fix e Ty assume ty: "e \<turnstile> ob : Ty" and bs: "bstable instsp"
        have tT: "tT = Ty" using ft fastype_of_closed[OF ty clo] by (simp add: return_def)
        have wO: "wft ar Ty" using typing_cert_closed[OF ty clo] by (rule cert_wft)
        have "tvars T \<subseteq> tbnd tyinsts'" by (rule typ_match_tbnd[OF tm[unfolded tT] wT wO])
        with bstable_textends[OF bs[unfolded e] typ_match_ext[OF tm]] show "bstable env1"
          by (simp add: env1 bstable_update)
      qed
    next
      fix u assume lr: "lr = Some u" and some: "vt_lookup insts ixn = Some (T, u)"
      from h2[unfolded lr] have ae: "aeconv ob u" and env1: "env1 = instsp"
        by (auto simp: e split: if_splits)
      show ?thesis
      proof (rule fo_postI)
        show "mextends instsp env1" by (simp add: env1)
        show "mvars env1 pt" using some by (simp add: env1 e pt mvars_def)
      next
        fix tye te e Ty assume ex: "mextends env1 (tye, te)" and ty: "e \<turnstile> ob : Ty"
          and bt: "btyped tye (snd instsp)"
        show "btyped tye (snd env1)" using bt by (simp add: env1)
        have tu: "e \<turnstile> u : tsubst (mtinst tye) T" using bt some unfolding e btyped_def by (cases ixn) auto
        have "vt_lookup te ixn = Some (T, u)" using ex some unfolding env1 e mextends_def by (cases ixn) auto
        then have mi: "minst (tye, te) pt = u" by (simp add: pt minst_Var)
        have cv: "ob \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" using aeconv_conv[OF ae wt_closedI[OF ty] wt_closedI[OF tu]] .
        have "Ty = tsubst (mtinst tye) T" by (rule conv_typing_eq[OF ty tu cv])
        with tu cv show "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
          by (simp add: mi conv_sym)
      next
        show "bstable instsp \<Longrightarrow> bstable env1" for e Ty by (simp add: env1)
      qed
    qed
  next
    case False
    note h = h[simplified False if_False]
    text \<open>Atoms whose types are matched:\<close>
    have atom: "fo_post instsp env1 pt ob"
      if tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env1: "env1 = (tyinsts', insts)"
        and wT: "wft ar T" and vs: "vars pt = {}"
        and mi: "\<And>env'. tsubst (mtinst (fst env')) T = U \<Longrightarrow> minst env' pt = ob"
        and ty: "\<And>e Ty. e \<turnstile> ob : Ty \<Longrightarrow> Ty = U \<and> cert_typ alg ar U"
      for T U tyinsts'
    proof (rule fo_postI)
      show "mextends instsp env1" using typ_match_ext[OF tm] by (simp add: e env1 mextends_def)
      show "mvars env1 pt" by (simp add: mvars_def vs)
    next
      fix tye te e Ty assume ex: "mextends env1 (tye, te)" and to: "e \<turnstile> ob : Ty"
        and bt: "btyped tye (snd instsp)"
      show "btyped tye (snd env1)" using bt by (simp add: e env1)
      have wU: "wft ar U" using ty[OF to] by (simp add: cert_wft)
      have "tsubst (mtinst tye) T = U"
        by (rule typ_match_inst[OF tm wT wU]) (use ex in \<open>simp add: env1 mextends_def\<close>)
      with mi[of "(tye, te)"] to show "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
        by simp
    next
      show "bstable instsp \<Longrightarrow> bstable env1" for e Ty
        using bstable_textends[OF _ typ_match_ext[OF tm]] by (simp add: e env1)
    qed
    show ?thesis
    proof (cases pt)
      case pt: (Const a T)
      show ?thesis
      proof (cases ob)
        case ob: (Const b U)
        with h pt obtain tyinsts' where ab: "a = b"
          and tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env1: "env1 = (tyinsts', insts)"
          by (auto split: if_splits)
        show ?thesis
          by (rule atom[OF tm env1]) (use wp in \<open>auto simp: pt ob ab\<close>)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    next
      case pt: (Free a T)
      show ?thesis
      proof (cases ob)
        case ob: (Free b U)
        with h pt obtain tyinsts' where ab: "a = b"
          and tm: "ok (typ_match alg T U tyinsts) tyinsts'" and env1: "env1 = (tyinsts', insts)"
          by (auto split: if_splits)
        show ?thesis
          by (rule atom[OF tm env1]) (use wp in \<open>auto simp: pt ob ab\<close>)
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" by (simp add: e)
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
        with h pt have ij: "i = j" and env1: "env1 = instsp" by (auto simp: e split: if_splits)
        show ?thesis
        proof (rule fo_postI)
          show "mextends instsp env1" by (simp add: env1)
          show "mvars env1 pt" by (simp add: pt mvars_def)
        next
          fix tye te e Ty assume "e \<turnstile> ob : Ty" "btyped tye (snd instsp)"
          then show "btyped tye (snd env1)" "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            by (simp_all add: env1 pt ob ij)
        next
          show "bstable instsp \<Longrightarrow> bstable env1" for e Ty by (simp add: env1)
        qed
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    next
      case pt: (Abs a T t)
      show ?thesis
      proof (cases ob)
        case ob: (Abs b U u)
        with h pt obtain tyinsts' where tm: "ok (typ_match alg T U tyinsts) tyinsts'"
          and m: "ok (fm alg True (tyinsts', insts) t u) env1"
          by auto
        have wT: "wft ar T" and wt: "\<forall>T\<in>typs t. wft ar T" using wp by (simp_all add: pt)
        from IH[OF m _ wt] have i: "fo_post (tyinsts', insts) env1 t u" by simp
        note ib = fo_postD_bstable[OF i] and i = fo_postD[OF i]
        show ?thesis
        proof (rule fo_postI)
          show "mextends instsp env1"
            using typ_match_ext[OF tm] i(1) by (auto simp: e mextends_def intro: textends_trans)
          show "mvars env1 pt" using i(2) by (simp add: pt mvars_simps)
        next
          fix tye te e Ty assume ex: "mextends env1 (tye, te)" and to: "e \<turnstile> ob : Ty"
            and bt: "btyped tye (snd instsp)"
          from to obtain Ty' where Ty: "Ty = U \<rightarrow>\<^sub>T Ty'" and tu: "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" and U: "cert_typ alg ar U"
            by (auto simp: ob)
          have bt': "btyped tye (snd (tyinsts', insts))" using bt by (simp add: e)
          show "btyped tye (snd env1)" by (rule i(3)[OF ex tu bt'])
          assume bf: "btyped tye te"
          have T: "tsubst (mtinst tye) T = U"
          proof (rule typ_match_inst[OF tm wT])
            show "wft ar U" using U by (simp add: cert_wft)
            show "textends tyinsts' tye" using i(1) ex by (auto simp: mextends_def intro: textends_trans)
          qed
          from i(4)[OF ex tu bt' bf] have b: "e\<langle>0:U\<rangle> \<turnstile> minst (tye, te) t : Ty'"
            "minst (tye, te) t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" by simp_all
          have ta: "e \<turnstile> minst (tye, te) pt : Ty" using b(1) U by (auto simp: pt T Ty)
          have "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            using conv_Abs[OF wt_closedI[OF ta[unfolded pt minst_simps fst_conv T]] wt_closedI[OF to[unfolded ob]] b(2)]
            by (simp add: pt ob T)
          with ta show "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by simp
        next
          fix e Ty assume to: "e \<turnstile> ob : Ty" and bs: "bstable instsp"
          from to obtain Ty' where "e\<langle>0:U\<rangle> \<turnstile> u : Ty'" by (auto simp: ob)
          moreover have "bstable (tyinsts', insts)"
            using bstable_textends[OF bs[unfolded e] typ_match_ext[OF tm]] .
          ultimately show "bstable env1" by (rule ib)
        qed
      qed (use h pt in auto)
    next
      case pt: (App f t)
      show ?thesis
      proof (cases ob)
        case ob: (App g u)
        with h pt obtain env2 where m1: "ok (fm alg inAbs instsp f g) env2"
          and m2: "ok (fm alg inAbs env2 t u) env1"
          by (auto simp: e)
        have cl': "\<not> inAbs \<longrightarrow> closed g" "\<not> inAbs \<longrightarrow> closed u"
          using cl ob by (auto simp: closed_def)
        have w: "\<forall>T\<in>typs f. wft ar T" "\<forall>T\<in>typs t. wft ar T" using wp pt by simp_all
        from IH[OF m1 cl'(1) w(1)] have i1: "fo_post instsp env2 f g" .
        from IH[OF m2 cl'(2) w(2)] have i2: "fo_post env2 env1 t u" .
        note ib1 = fo_postD_bstable[OF i1] and ib2 = fo_postD_bstable[OF i2]
        note i1 = fo_postD[OF i1] and i2 = fo_postD[OF i2]
        show ?thesis
        proof (rule fo_postI)
          show "mextends instsp env1" using i1(1) i2(1) by (rule mextends_trans)
          show "mvars env1 pt" using mvars_mono[OF i2(1) i1(2)] i2(2) by (simp add: pt mvars_simps)
        next
          fix tye te e Ty assume ex: "mextends env1 (tye, te)" and to: "e \<turnstile> ob : Ty"
            and bt: "btyped tye (snd instsp)"
          from to obtain A where tg: "e \<turnstile> g : A \<rightarrow>\<^sub>T Ty" and tu: "e \<turnstile> u : A" by (auto simp: ob)
          have ex1: "mextends env2 (tye, te)" using i2(1) ex by (rule mextends_trans)
          have b2: "btyped tye (snd env2)" by (rule i1(3)[OF ex1 tg bt])
          show "btyped tye (snd env1)" by (rule i2(3)[OF ex tu b2])
          assume bf: "btyped tye te"
          from i1(4)[OF ex1 tg bt bf] i2(4)[OF ex tu b2 bf]
          have c: "e \<turnstile> minst (tye, te) f : A \<rightarrow>\<^sub>T Ty" "minst (tye, te) f \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> g"
            "e \<turnstile> minst (tye, te) t : A" "minst (tye, te) t \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u" by simp_all
          have ta: "e \<turnstile> minst (tye, te) pt : Ty" using c(1,3) by (auto simp: pt)
          have "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            using conv_App[OF wt_closedI[OF ta[unfolded pt minst_simps]] wt_closedI[OF to[unfolded ob]] c(2,4)]
            by (simp add: pt ob)
          with ta show "e \<turnstile> minst (tye, te) pt : Ty \<and> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by simp
        next
          fix e Ty assume to: "e \<turnstile> ob : Ty" and bs: "bstable instsp"
          from to obtain A where tg: "e \<turnstile> g : A \<rightarrow>\<^sub>T Ty" and tu: "e \<turnstile> u : A" by (auto simp: ob)
          show "bstable env1" by (rule ib2[OF tu ib1[OF tg bs]])
        qed
      next
        case ob: (Abs b U u)
        with h pt have "ok (fm alg True instsp (incr pt $ Bound 0) u) env1" by (simp add: e)
        from eta[OF ob this] show ?thesis .
      qed (use h pt in auto)
    qed
  qed
qed


subsection \<open>Bindings of higher-order matching\<close>

lemma downto0_set: "downto0 is n \<Longrightarrow> k \<in> set is \<Longrightarrow> 0 \<le> k \<and> k \<le> n"
proof -
  have "downto0 is n \<Longrightarrow> (k \<in> set is \<longrightarrow> 0 \<le> k \<and> k \<le> n) \<and> -1 \<le> n"
  proof (induction "is" arbitrary: n)
    case (Cons i "is")
    then have "i = n" "downto0 is (n - 1)" by simp_all
    from Cons.IH[OF this(2)] this(1) show ?case by (auto simp: integer_arith)
  qed (simp add: integer_arith)
  then show "downto0 is n \<Longrightarrow> k \<in> set is \<Longrightarrow> 0 \<le> k \<and> k \<le> n" by blast
qed

lemma ok_match_bind:
  assumes "ok (match_bind itms bs x T is t) itms'" "distinct is"
  shows "vt_lookup itms x = None"
    and "itms' = vt_update (x, (T, abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 t))) itms"
    and "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is"
    and "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
proof -
  let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 t)"
  have "vt_lookup itms x = None \<and> itms' = vt_update (x, (T, ?u)) itms \<and>
    (\<forall>k. 0 \<le> k \<longrightarrow> loose_bvar1 t k \<longrightarrow> k \<in> set is) \<and> (\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs)"
  proof (cases "is = []")
    case True
    with assms(1) have lb: "loose_bnos t = []" and u: "ok (update_new (x, (T, t)) itms) itms'"
      by (auto simp: match_bind_def Let_def split: if_splits)
    from lb have nl: "\<not> loose_bvar1 t k" if "0 \<le> k" for k
      using that set_loose_bnos[of t] by auto
    have "rename (bidx is) 0 t = rename (\<lambda>k. k) 0 t" by (rule rename_cong) (simp add: nl)
    with u True nl show ?thesis by (simp add: ok_update_new rename_id)
  next
    case False
    with assms(1) have sb: "subset (loose_bnos t) is" and
      m: "ok ((if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) \<bind>
        (\<lambda>t'. mkabs bs is t' \<bind> (\<lambda>u. update_new (x, (T, u)) itms))) itms'"
      by (auto simp: match_bind_def Let_def split: if_splits)
    have lb: "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is"
      using sb by (auto simp: subset_iff_set set_loose_bnos)
    from m obtain t' u where t': "ok (if downto0 is (ilength bs - 1) then return t else mapbnd (idx is) 0 t) t'"
      and mk: "ok (mkabs bs is t') u" and up: "ok (update_new (x, (T, u)) itms) itms'"
      by auto
    have "t' = rename (bidx is) 0 t"
    proof (cases "downto0 is (ilength bs - 1)")
      case True
      with t' have "t' = t" by simp
      note dt = downto0_bren[OF True]
      have "rename (bidx is) 0 t = rename (\<lambda>k. k) 0 t"
      proof (rule rename_cong)
        fix k assume k: "0 \<le> k" "loose_bvar1 t (k + 0)"
        then have "k \<in> set is" using lb by simp
        then have kn: "0 \<le> k" "k \<le> ilength bs - 1" using downto0_set[OF True] by blast+
        then have "bren (rev is) k = k" using dt by blast
        moreover have "k < ilength is" using kn dt by (simp add: integer_arith)
        ultimately show "bidx is k = k" using bidx_bren[OF assms(2) kn(1)] by simp
      qed
      with \<open>t' = t\<close> show ?thesis by (simp add: rename_id)
    next
      case False
      with t' ok_mapbnd_idx[of t 0 "is"] lb show ?thesis by simp
    qed
    with mk up lb show ?thesis by (simp add: ok_mkabs ok_update_new)
  qed
  then show "vt_lookup itms x = None" "itms' = vt_update (x, (T, ?u)) itms"
    "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is" "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
    by blast+
qed

lemma aconv_term_sym: "aconv_term s t \<Longrightarrow> aconv_term t s"
  by (simp add: aconv_term_unname)

lemma aconv_abs_list_names: "map snd bs = map snd bs' \<Longrightarrow> aconv_term (abs_list bs t) (abs_list bs' t)"
proof (induction bs arbitrary: bs')
  case (Cons b bs)
  then obtain b' bs'' where "bs' = b' # bs''" "snd b = snd b'" "map snd bs = map snd bs''" by auto
  with Cons.IH show ?case by (cases b, cases b') simp
qed simp

text \<open>A new binding is a closed term of the type of the variable, which, applied to the bound
  variables, is equivalent to the object:\<close>

lemma match_binding:
  assumes bs: "bs_env TVar e bs" and t: "e \<turnstile> t : Ty"
    and lb: "\<And>k. 0 \<le> k \<Longrightarrow> loose_bvar1 t k \<Longrightarrow> k \<in> set is"
    and iss: "\<forall>i\<in>set is. 0 \<le> i \<and> i < ilength bs"
  defines "u \<equiv> abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 t)"
  shows "closed u" "e' \<turnstile> u : map e is \<Rrightarrow> Ty" "u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
proof -
  have ty: "\<forall>k\<in>set is. cert_typ alg ar (e k)"
  proof
    fix k assume k: "k \<in> set is"
    with iss have k': "0 \<le> k" "k < ilength bs" by auto
    then have "e k = snd (bs ! nat_of_integer k)" using bs by (simp add: bs_env_def)
    moreover have "bs ! nat_of_integer k \<in> set bs" using nat_of_integer_less_ilength[OF k'] by simp
    ultimately show "cert_typ alg ar (e k)" using bs by (auto simp: bs_env_def case_prod_unfold)
  qed
  note st = strengthen[OF t lb ty]
  have sn: "map snd (map (\<lambda>i. bs ! nat_of_integer i) is) = map snd (map (\<lambda>k. (STR '''', e k)) is)"
    using bs_types(1)[OF bs iss] by (simp add: case_prod_unfold)
  have ac: "aconv_term u (sabs e is t)"
    unfolding u_def sabs_def by (rule aconv_abs_list_names[OF sn])
  show "closed u" using st(1) loose_bvar1_aconv[OF ac] by (simp add: closed_iff_loose_bvar1)
  show tu: "e' \<turnstile> u : map e is \<Rrightarrow> Ty" for e'
    using typing_aconv[OF aconv_term_sym[OF ac] st(2)] .
  have tb: "e \<tturnstile> map Bound is : map e is" using iss by (intro typings_Bounds) simp
  have ta: "e \<turnstile> u \<degree>\<degree> map Bound is : Ty" "e \<turnstile> sabs e is t \<degree>\<degree> map Bound is : Ty"
    using list_app_typeI[OF tu tb] list_app_typeI[OF st(2) tb] by simp_all
  have "u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> sabs e is t \<degree>\<degree> map Bound is"
    by (rule conv_apps[OF _ wt_closedI[OF ta(1)] wt_closedI[OF ta(2)] aconv_term_conv[OF ac]])
      (simp add: list_all2_refl)
  also have "sabs e is t \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t"
    using st(3)[of "is"] iss rename_bren_bidx[OF lb]
    by (intro beta_eta_conv[OF _ wt_closedI[OF ta(2)]]) (simp add: beta_reds_beta_eta_reds)
  finally show "u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> t" .
qed

subsection \<open>Binder and variable types of patterns\<close>

text \<open>
  When a pattern abstraction is matched against an object that is no abstraction, the binder type
  is instantiated by the current type environment; when a flexible pattern \<open>?F x\<^sub>1 \<dots> x\<^sub>n\<close> is
  matched, \<open>?F\<close> is bound at its type. The type variables of these types are bound: they occur in
  the types of the enclosing heads (which are matched first) or of the enclosing pattern.
\<close>

fun rhd :: "pterm \<Rightarrow> bool" where
  "rhd (s $ t) = rhd s"
| "rhd t = rigid t"

fun htv :: "pterm \<Rightarrow> (indexname \<times> psort) set" where
  "htv (Const _ T) = tvars T"
| "htv (Free _ T) = tvars T"
| "htv (s $ t) = htv s"
| "htv _ = {}"

text \<open>The type of the head of a flexible term with bound variables as arguments:\<close>

fun fty :: "pterm \<Rightarrow> ptyp option" where
  "fty (Var x T) = Some T"
| "fty (s $ Bound i) = fty s"
| "fty _ = None"

lemma fty_App: "fty (s $ t) = (if is_Bound t then fty s else None)"
  by (cases t) auto

lemma fty_flex: "fty (Var x T \<degree>\<degree> map Bound is) = Some T"
  by (induction "is" rule: rev_induct) (simp_all add: app_last[symmetric])

lemma fty_typing:
  "e \<turnstile> t : T \<Longrightarrow> fty t = Some A \<Longrightarrow>
    tvars A \<subseteq> tvars T \<union> (\<Union>i\<in>{i. 0 \<le> i \<and> loose_bvar1 t i}. tvars (e i))"
proof (induction arbitrary: A rule: typing.induct)
  case (App e s T U t)
  then obtain i where t: "t = Bound i" and fs: "fty s = Some A" by (cases t) auto
  from App.hyps(2) t have "0 \<le> i" "e i = T" by auto
  with App.IH(1)[OF fs] t show ?case by auto
qed auto

fun abs_bound :: "(indexname \<times> psort) set \<Rightarrow> pterm \<Rightarrow> bool" where
  "abs_bound V (Abs _ T t) \<longleftrightarrow> tvars T \<subseteq> V \<and> abs_bound V t"
| "abs_bound V (s $ t) \<longleftrightarrow> (if rhd s then abs_bound V s \<and> abs_bound (V \<union> htv s) t
    else (\<forall>A. fty (s $ t) = Some A \<longrightarrow> tvars A \<subseteq> V))"
| "abs_bound V (Var x T) \<longleftrightarrow> tvars T \<subseteq> V"
| "abs_bound V _ \<longleftrightarrow> True"

lemma abs_bound_mono: "abs_bound V t \<Longrightarrow> V \<subseteq> V' \<Longrightarrow> abs_bound V' t"
proof (induction t arbitrary: V V')
  case (App s t)
  show ?case
  proof (cases "rhd s")
    case True
    with App show ?thesis by (auto intro: App.IH(2)[of "V \<union> htv s" "V' \<union> htv s"])
  next
    case False
    with App.prems show ?thesis by (simp del: fty.simps) blast
  qed
qed auto

lemma rhd_incr_aux: "rhd (incr_aux d t) = rhd t" and htv_incr_aux: "htv (incr_aux d t) = htv t"
  by (induction d t rule: incr_aux.induct) auto

lemma is_Bound_incr_aux: "is_Bound (incr_aux d t) = is_Bound t"
  by (cases t) auto

lemma fty_incr_aux: "fty (incr_aux d t) = fty t"
  by (induction d t rule: incr_aux.induct) (simp_all add: fty_App is_Bound_incr_aux)

lemma abs_bound_incr: "abs_bound V (incr t) \<longleftrightarrow> abs_bound V t"
proof -
  have "abs_bound V (incr_aux d t) \<longleftrightarrow> abs_bound V t" for d
  proof (induction d t arbitrary: V rule: incr_aux.induct)
    case (3 d u1 u2)
    have "fty (incr_aux d u1 $ incr_aux d u2) = fty (u1 $ u2)" using fty_incr_aux[of d "u1 $ u2"] by simp
    with 3 show ?case by (simp add: rhd_incr_aux htv_incr_aux del: fty.simps)
  qed simp_all
  then show ?thesis by (simp add: incr_def)
qed

lemma abs_bound_incr_Bound0:
  assumes "\<not> is_Abs t" "abs_bound V t"
  shows "abs_bound V (incr t $ Bound 0)"
proof (cases "rhd t")
  case True
  then have "rhd (incr t)" by (simp add: incr_def rhd_incr_aux)
  with assms(2) show ?thesis by (simp add: abs_bound_incr)
next
  case False
  have "rhd (incr t) = rhd t" by (simp add: incr_def rhd_incr_aux)
  moreover have "fty (incr t $ Bound 0) = fty t" by (simp add: incr_def fty_incr_aux)
  moreover have "tvars A \<subseteq> V" if "fty t = Some A" for A
    using assms that False by (cases t) (auto simp: fty_App split: if_splits)
  ultimately show ?thesis using False by (simp del: fty.simps)
qed

lemma rhd_apps: "rhd (h \<degree>\<degree> ts) = rhd h" and htv_apps: "htv (h \<degree>\<degree> ts) = htv h"
  by (induction ts rule: rev_induct) auto

lemma abs_bound_flex: "abs_bound V (Var x T \<degree>\<degree> map Bound is) \<Longrightarrow> tvars T \<subseteq> V"
proof (cases "is" rule: rev_cases)
  case (snoc js j)
  have "rhd (Var x T \<degree>\<degree> map Bound js) = False" by (simp add: rhd_apps)
  moreover have "fty (Var x T \<degree>\<degree> map Bound is) = Some T" by (rule fty_flex)
  moreover assume "abs_bound V (Var x T \<degree>\<degree> map Bound is)"
  ultimately show ?thesis by (simp add: snoc app_last[symmetric] del: fty.simps)
qed simp

lemma abs_bound_apps: "rigid h \<Longrightarrow> abs_bound V (h \<degree>\<degree> ts) \<longleftrightarrow> (\<forall>t\<in>set ts. abs_bound (V \<union> htv h) t)"
proof (induction ts rule: rev_induct)
  case Nil
  then show ?case by (cases h) simp_all
next
  case (snoc t ts)
  have "rhd h" using snoc.prems by (cases h) simp_all
  with snoc show ?case by (auto simp: rhd_apps htv_apps)
qed

lemma rhd_typing:
  "e \<turnstile> s : S \<Longrightarrow> rhd s \<Longrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 s i \<longrightarrow> tvars (e i) \<subseteq> V) \<Longrightarrow>
    tvars S \<subseteq> V \<union> htv s"
  by (induction rule: typing.induct) auto

lemma typing_abs_bound:
  "e \<turnstile> t : T \<Longrightarrow> (\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> tvars (e i) \<subseteq> V) \<Longrightarrow>
    (\<not> rhd t \<longrightarrow> tvars T \<subseteq> V) \<Longrightarrow> abs_bound V t"
proof (induction arbitrary: V rule: typing.induct)
  case (Abs T e t U a)
  have "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> tvars ((e\<langle>0:T\<rangle>) i) \<subseteq> V"
  proof (intro allI impI)
    fix i assume i: "0 \<le> i" "loose_bvar1 t i"
    show "tvars ((e\<langle>0:T\<rangle>) i) \<subseteq> V"
    proof (cases "i = 0")
      case False
      with i have "0 \<le> i - 1" "loose_bvar1 (Abs a T t) (i - 1)" by (simp_all add: integer_arith)
      with Abs.prems False i(1) show ?thesis by (simp add: integer_arith)
    qed (use Abs.prems in simp)
  qed
  with Abs show ?case by simp
next
  case (App e s T U t)
  have l: "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 s i \<longrightarrow> tvars (e i) \<subseteq> V"
    "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 t i \<longrightarrow> tvars (e i) \<subseteq> V \<union> htv s"
    using App.prems by auto
  show ?case
  proof (cases "rhd s")
    case r: True
    from App.IH(1)[OF l(1)] r have "abs_bound V s" by simp
    moreover have "tvars (T \<rightarrow>\<^sub>T U) \<subseteq> V \<union> htv s" using rhd_typing[OF App.hyps(1) r l(1)] .
    then have "abs_bound (V \<union> htv s) t" using App.IH(2)[OF l(2)] by auto
    ultimately show ?thesis using r by simp
  next
    case False
    have "tvars A \<subseteq> V" if "fty (s $ t) = Some A" for A
      using fty_typing[OF typing.App[OF App.hyps] that] App.prems False by fastforce
    with False show ?thesis by (simp del: fty.simps)
  qed
qed auto

lemma typing_typs_cert: "e \<turnstile> t : T \<Longrightarrow> \<forall>U\<in>typs t. cert_typ alg ar U"
  by (induction rule: typing.induct) auto

lemma typs_apps_m: "typs (s \<degree>\<degree> ts) = typs s \<union> \<Union> (typs ` set ts)"
  by (induction ts arbitrary: s) auto

lemma minst_rigid: "rigid h \<Longrightarrow> minst env h = inst (mtinst (fst env)) h"
  by (cases h) simp_all


subsection \<open>Higher-order matching\<close>

text \<open>
  The postcondition of higher-order matching: for every extension of the result to a final
  environment, if the pattern instantiated by the final type environment has the type of the
  object in the environment of the binders, the new bindings are typed, and the instance of the
  pattern is equivalent to the object.
\<close>

definition m_post :: "binders \<Rightarrow> match_env \<Rightarrow> match_env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "m_post bs env env1 pt ob \<longleftrightarrow> mextends env env1 \<and> mvars env1 pt \<and>
    (tye_cert (fst env) \<longrightarrow> tye_cert (fst env1)) \<and> (bstable env \<longrightarrow> bstable env1) \<and>
    (\<forall>tye te e Ty. mextends env1 (tye, te) \<longrightarrow> bs_env TVar e bs \<longrightarrow>
      e \<turnstile> inst (mtinst tye) pt : Ty \<longrightarrow> e \<turnstile> ob : Ty \<longrightarrow> btyped tye (snd env) \<longrightarrow>
      btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob))"

lemma m_postI:
  assumes "mextends env env1" "mvars env1 pt" "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)"
    and "bstable env \<Longrightarrow> bstable env1"
    and "\<And>tye te e Ty. mextends env1 (tye, te) \<Longrightarrow> bs_env TVar e bs \<Longrightarrow>
      e \<turnstile> inst (mtinst tye) pt : Ty \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow>
      btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
  shows "m_post bs env env1 pt ob"
  using assms unfolding m_post_def by blast

lemma m_postD:
  assumes "m_post bs env env1 pt ob"
  shows "mextends env env1" "mvars env1 pt" "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)"
    and "mextends env1 (tye, te) \<Longrightarrow> bs_env TVar e bs \<Longrightarrow>
      e \<turnstile> inst (mtinst tye) pt : Ty \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow>
      btyped tye (snd env1)"
    and "mextends env1 (tye, te) \<Longrightarrow> bs_env TVar e bs \<Longrightarrow>
      e \<turnstile> inst (mtinst tye) pt : Ty \<Longrightarrow> e \<turnstile> ob : Ty \<Longrightarrow> btyped tye (snd env) \<Longrightarrow>
      btyped tye te \<Longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
  using assms unfolding m_post_def by blast+

lemma m_postD_bstable: "m_post bs env env1 pt ob \<Longrightarrow> bstable env \<Longrightarrow> bstable env1"
  unfolding m_post_def by blast

lemma bs_env_TVar_Cons:
  "bs_env TVar e bs \<Longrightarrow> cert_typ alg ar T \<Longrightarrow> bs_env TVar (e\<langle>0:T\<rangle>) ((a, T) # bs)"
  using bs_env_Cons[of TVar e bs T a] by simp


lemma rename_bren_Nil: "rename (bren []) d t = t"
proof -
  have "bren [] = (\<lambda>k. k)" by (rule ext) simp
  then show ?thesis by (simp add: rename_id)
qed

lemma mtch_sound:
  assumes "mtch alg' bs pt ob env = Some r"
  shows "alg' = alg \<Longrightarrow> r = Ok env1 \<Longrightarrow> \<forall>T\<in>typs pt. wft ar T \<Longrightarrow> \<forall>T\<in>typs ob. cert_typ alg ar T \<Longrightarrow>
    abs_bound (tbnd (fst env)) pt \<Longrightarrow> m_post bs env env1 pt ob"
  using assms
proof (induction alg' bs pt ob env r arbitrary: env1 rule: mtch.raw_induct[rotated, consumes 1])
  case (1 fm alg' bs pt ob env r)
  obtain iTs itms where e: "env = (iTs, itms)" by force
  note prems = "1.prems"
  have alg': "alg' = alg" and r: "r = Ok env1" using prems by simp_all
  note h = "1.hyps"[unfolded alg' r]
  note IH = "1.IH"[OF _ refl refl]
  have wp: "\<forall>T\<in>typs pt. wft ar T" and wo: "\<forall>T\<in>typs ob. cert_typ alg ar T"
    and ab: "abs_bound (tbnd iTs) pt" using prems e by simp_all
  text \<open>Arguments of rigid heads are matched from left to right:\<close>
  have args: "length ps = length qs \<and> mextends e0 env1 \<and> (\<forall>p\<in>set ps. mvars env1 p) \<and>
      (tye_cert (fst e0) \<longrightarrow> tye_cert (fst env1)) \<and> (bstable e0 \<longrightarrow> bstable env1) \<and>
      (\<forall>tye te e. mextends env1 (tye, te) \<longrightarrow> bs_env TVar e bs \<longrightarrow>
        list_all2 (\<lambda>p q. \<exists>Ty. e \<turnstile> inst (mtinst tye) p : Ty \<and> e \<turnstile> q : Ty) ps qs \<longrightarrow>
        btyped tye (snd e0) \<longrightarrow>
        btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> list_all2 (\<lambda>p q. minst (tye, te) p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q) ps qs))"
    if m: "ok (handle (zip_eq ps qs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs e0))
      (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
      and ps: "\<forall>p\<in>set ps. (\<forall>T\<in>typs p. wft ar T) \<and> abs_bound (tbnd (fst e0)) p"
      and qs: "\<forall>q\<in>set qs. \<forall>T\<in>typs q. cert_typ alg ar T"
    for e0 ps qs
  proof -
    have nh: "\<not> ok (case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e) y" for e and y :: match_env
      by (cases e) simp_all
    from m nh have len: "length ps = length qs"
      and f: "ok (foldM (\<lambda>(p, q). fm alg bs p q) (zip ps qs) e0) env1"
      by (auto simp: ok_handle ok_zip_eq)
    define pre where "pre b x \<longleftrightarrow> (\<forall>T\<in>typs (fst x). wft ar T) \<and> abs_bound (tbnd (fst b)) (fst x) \<and>
      (\<forall>T\<in>typs (snd x). cert_typ alg ar T)" for b :: match_env and x :: "pterm \<times> pterm"
    define Q where "Q xs b b' \<longleftrightarrow> (\<forall>x\<in>set xs. pre b x) \<longrightarrow>
        mextends b b' \<and> (\<forall>x\<in>set xs. mvars b' (fst x)) \<and> (tye_cert (fst b) \<longrightarrow> tye_cert (fst b')) \<and>
        (bstable b \<longrightarrow> bstable b') \<and> (\<forall>tye te e. mextends b' (tye, te) \<longrightarrow> bs_env TVar e bs \<longrightarrow>
          (\<forall>x\<in>set xs. \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty) \<longrightarrow>
          btyped tye (snd b) \<longrightarrow>
          btyped tye (snd b') \<and> (btyped tye te \<longrightarrow> (\<forall>x\<in>set xs. minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x)))"
      for xs b b'
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
        assume pr: "\<forall>y\<in>set (x # xs). pre b y"
        from Cons(1) have m1: "ok (fm alg bs p q b) b1" by (simp add: x)
        have "m_post bs b b1 p q" using IH[OF m1] pr by (simp add: x pre_def)
        note mp = m_postD[OF this]
        have tb: "tbnd (fst b) \<subseteq> tbnd (fst b1)" using mp(1) by (simp add: mextends_def tbnd_mono)
        have "\<forall>y\<in>set xs. pre b1 y" using pr tb by (auto simp: pre_def intro: abs_bound_mono)
        with Cons(3) have r: "mextends b1 b'" "\<forall>x\<in>set xs. mvars b' (fst x)"
          "tye_cert (fst b1) \<Longrightarrow> tye_cert (fst b')" "bstable b1 \<Longrightarrow> bstable b'"
          and rt: "\<And>tye te e. mextends b' (tye, te) \<Longrightarrow> bs_env TVar e bs \<Longrightarrow>
            (\<forall>x\<in>set xs. \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty) \<Longrightarrow>
            btyped tye (snd b1) \<Longrightarrow>
            btyped tye (snd b') \<and> (btyped tye te \<longrightarrow> (\<forall>x\<in>set xs. minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x))"
          unfolding Q_def by blast+
        show "mextends b b' \<and> (\<forall>x\<in>set (x # xs). mvars b' (fst x)) \<and> (tye_cert (fst b) \<longrightarrow> tye_cert (fst b')) \<and>
          (bstable b \<longrightarrow> bstable b') \<and>
          (\<forall>tye te e. mextends b' (tye, te) \<longrightarrow> bs_env TVar e bs \<longrightarrow>
            (\<forall>x\<in>set (x # xs). \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty) \<longrightarrow>
            btyped tye (snd b) \<longrightarrow>
            btyped tye (snd b') \<and> (btyped tye te \<longrightarrow> (\<forall>x\<in>set (x # xs). minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x)))"
        proof (intro conjI allI impI)
          show "mextends b b'" using mp(1) r(1) by (rule mextends_trans)
          show "\<forall>x\<in>set (x # xs). mvars b' (fst x)" using r(2) mvars_mono[OF r(1) mp(2)] by (simp add: x)
          show "tye_cert (fst b) \<Longrightarrow> tye_cert (fst b')" using mp(3) r(3) by blast
          show "bstable b \<Longrightarrow> bstable b'" using m_postD_bstable[OF \<open>m_post bs b b1 p q\<close>] r(4) by blast
        next
          fix tye te e assume ex: "mextends b' (tye, te)" and bse: "bs_env TVar e bs"
            and ty: "\<forall>x\<in>set (x # xs). \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty"
            and bt: "btyped tye (snd b)"
          have ex1: "mextends b1 (tye, te)" using r(1) ex by (rule mextends_trans)
          from ty obtain Ty where tp: "e \<turnstile> inst (mtinst tye) p : Ty" and tq: "e \<turnstile> q : Ty" by (auto simp: x)
          have bt1: "btyped tye (snd b1)" by (rule mp(4)[OF ex1 bse tp tq bt])
          from rt[OF ex bse _ bt1] ty
          have r2: "btyped tye (snd b')" "btyped tye te \<Longrightarrow> \<forall>x\<in>set xs. minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x"
            by simp_all
          show "btyped tye (snd b')" by (rule r2(1))
          assume bf: "btyped tye te"
          show "\<forall>x\<in>set (x # xs). minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x"
            using r2(2)[OF bf] mp(5)[OF ex1 bse tp tq bt bf] by (simp add: x)
        qed
      qed
    qed
    moreover have "\<forall>x\<in>set (zip ps qs). pre e0 x"
      using ps qs by (auto simp: pre_def dest: set_zip_leftD set_zip_rightD)
    ultimately have q: "mextends e0 env1" "\<forall>x\<in>set (zip ps qs). mvars env1 (fst x)"
      "tye_cert (fst e0) \<Longrightarrow> tye_cert (fst env1)" "bstable e0 \<Longrightarrow> bstable env1"
      and qt: "\<And>tye te e. mextends env1 (tye, te) \<Longrightarrow> bs_env TVar e bs \<Longrightarrow>
        (\<forall>x\<in>set (zip ps qs). \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty) \<Longrightarrow>
        btyped tye (snd e0) \<Longrightarrow>
        btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> (\<forall>x\<in>set (zip ps qs). minst (tye, te) (fst x) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> snd x))"
      unfolding Q_def by blast+
    have "\<forall>p\<in>set ps. mvars env1 p"
      using q(2) len by (auto simp: in_set_conv_nth set_zip) metis
    moreover have "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> list_all2 (\<lambda>p q. minst (tye, te) p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q) ps qs)"
      if "mextends env1 (tye, te)" "bs_env TVar e bs"
        "list_all2 (\<lambda>p q. \<exists>Ty. e \<turnstile> inst (mtinst tye) p : Ty \<and> e \<turnstile> q : Ty) ps qs" "btyped tye (snd e0)"
      for tye te e
    proof -
      have "\<forall>x\<in>set (zip ps qs). \<exists>Ty. e \<turnstile> inst (mtinst tye) (fst x) : Ty \<and> e \<turnstile> snd x : Ty"
        using that(3) by (auto simp: list_all2_iff)
      from qt[OF that(1,2) this that(4)] len show ?thesis by (auto simp: list_all2_iff)
    qed
    ultimately show ?thesis using len q(1,3,4) by blast
  qed
  show ?case
  proof (cases "is_Abs pt")
    case pA: True
    then obtain ns Ts ts where pt: "pt = Abs ns Ts ts" by (cases pt) auto
    have pre1: "\<forall>T\<in>typs ts. wft ar T" "abs_bound (tbnd (fst env)) ts" and tvT: "tvars Ts \<subseteq> tbnd iTs"
      using wp ab by (simp_all add: pt e)
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from h have m: "ok (fm alg ((nt, Tt) # bs) ts tt env) env1" by (simp add: e pt ob)
      have "\<forall>T\<in>typs tt. cert_typ alg ar T" using wo by (simp add: ob)
      note ih = IH[OF m pre1(1) this pre1(2)]
      note i = m_postD[OF ih] and ib = m_postD_bstable[OF ih]
      show ?thesis
      proof (rule m_postI)
        show "mextends env env1" by (rule i(1))
        show "mvars env1 pt" using i(2) by (simp add: pt mvars_simps)
        show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" by (rule i(3))
        show "bstable env \<Longrightarrow> bstable env1" by (rule ib)
      next
        fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
          and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
        from tp obtain P1 where T1: "Ty = tsubst (mtinst tye) Ts \<rightarrow>\<^sub>T P1"
          and tb: "e0\<langle>0:tsubst (mtinst tye) Ts\<rangle> \<turnstile> inst (mtinst tye) ts : P1" by (auto simp: pt)
        from to obtain P2 where T2: "Ty = Tt \<rightarrow>\<^sub>T P2" and tt: "e0\<langle>0:Tt\<rangle> \<turnstile> tt : P2"
          and cTt: "cert_typ alg ar Tt" by (auto simp: ob)
        from T1 T2 have eq: "tsubst (mtinst tye) Ts = Tt" "P1 = P2" by simp_all
        have bse': "bs_env TVar (e0\<langle>0:Tt\<rangle>) ((nt, Tt) # bs)" by (rule bs_env_TVar_Cons[OF bse cTt])
        have tb': "e0\<langle>0:Tt\<rangle> \<turnstile> inst (mtinst tye) ts : P2" using tb eq by simp
        show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
        proof (intro conjI impI)
          show "btyped tye (snd env1)" by (rule i(4)[OF ex bse' tb' tt bt])
          assume bf: "btyped tye te"
          have w1: "wt (minst (tye, te) pt)" by (rule wt_closedI[OF typing_minst[OF tp bf]])
          have w2: "wt (Abs nt Tt tt)" using wt_closedI[OF to] by (simp add: ob)
          from conv_Abs[OF w1[unfolded pt minst_simps fst_conv eq] w2 i(5)[OF ex bse' tb' tt bt bf]]
          show "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by (simp add: pt ob eq)
        qed
      qed
    next
      case oA: False
      from h oA obtain Tt where st: "ok (subst_type iTs Ts) Tt"
        and m: "ok (fm alg ((ns, Tt) # bs) ts (incr ob $ Bound 0) env) env1"
        by (auto simp: e pt)
      have Tt: "Tt = tsubst (mtinst iTs) Ts" by (rule ok_subst_type[OF st])
      have "\<forall>T\<in>typs (incr ob $ Bound 0). cert_typ alg ar T" using wo by (simp add: typs_incr)
      note ih = IH[OF m pre1(1) this pre1(2)]
      note i = m_postD[OF ih] and ib = m_postD_bstable[OF ih]
      show ?thesis
      proof (rule m_postI)
        show "mextends env env1" by (rule i(1))
        show "mvars env1 pt" using i(2) by (simp add: pt mvars_simps)
        show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" by (rule i(3))
        show "bstable env \<Longrightarrow> bstable env1" by (rule ib)
      next
        fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
          and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
        have "textends iTs tye" using i(1) ex by (auto simp: e mextends_def intro: textends_trans)
        from mtinst_tbnd[OF this tvT] Tt have eq: "tsubst (mtinst tye) Ts = Tt" by simp
        from tp obtain P1 where T1: "Ty = Tt \<rightarrow>\<^sub>T P1"
          and tb: "e0\<langle>0:Tt\<rangle> \<turnstile> inst (mtinst tye) ts : P1" and cTt: "cert_typ alg ar Tt"
          by (auto simp: pt eq)
        have bse': "bs_env TVar (e0\<langle>0:Tt\<rangle>) ((ns, Tt) # bs)" by (rule bs_env_TVar_Cons[OF bse cTt])
        have il: "incr ob = lift ob 0" by (simp add: incr_def incr_aux_lift)
        have "e0\<langle>0:Tt\<rangle> \<turnstile> lift ob 0 : Tt \<rightarrow>\<^sub>T P1" using lift_type[OF to[unfolded T1], of 0 Tt] by simp
        then have tl: "e0\<langle>0:Tt\<rangle> \<turnstile> lift ob 0 $ Bound 0 : P1" by (rule typing.App) auto
        then have to': "e0\<langle>0:Tt\<rangle> \<turnstile> incr ob $ Bound 0 : P1" by (simp add: il)
        show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
        proof (intro conjI impI)
          show "btyped tye (snd env1)" by (rule i(4)[OF ex bse' tb to' bt])
          assume bf: "btyped tye te"
          have c: "minst (tye, te) ts \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> lift ob 0 $ Bound 0"
            using i(5)[OF ex bse' tb to' bt bf] by (simp add: il)
          have w1: "wt (minst (tye, te) pt)" by (rule wt_closedI[OF typing_minst[OF tp bf]])
          have ta: "e0 \<turnstile> Abs ns Tt (lift ob 0 $ Bound 0) : Ty" using typing.Abs[OF cTt tl] T1 by simp
          have "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> Abs ns Tt (lift ob 0 $ Bound 0)"
            using conv_Abs[OF w1[unfolded pt minst_simps fst_conv eq] wt_closedI[OF ta] c]
            by (simp add: pt eq)
          also have "Abs ns Tt (lift ob 0 $ Bound 0) \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            by (rule beta_eta_conv[OF eta_reds_beta_eta_reds[OF r_into_rtranclp[of eta, OF eta_lift_Bound0]]])
              (rule wt_closedI[OF ta])
          finally show "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" .
        qed
      qed
    qed
  next
    case pA: False
    show ?thesis
    proof (cases "is_Abs ob")
      case True
      then obtain nt Tt tt where ob: "ob = Abs nt Tt tt" by (cases ob) auto
      from h pA have m: "ok (fm alg ((nt, Tt) # bs) (incr pt $ Bound 0) tt env) env1"
        by (simp add: e ob)
      have pre: "\<forall>T\<in>typs (incr pt $ Bound 0). wft ar T" "\<forall>T\<in>typs tt. cert_typ alg ar T"
        "abs_bound (tbnd (fst env)) (incr pt $ Bound 0)"
        using wp wo abs_bound_incr_Bound0[OF pA ab] by (simp_all add: ob typs_incr e)
      note i = m_postD[OF IH[OF m pre]]
      note ib = m_postD_bstable[OF IH[OF m pre]]
      have il: "incr t = lift t 0" for t by (simp add: incr_def incr_aux_lift)
      show ?thesis
      proof (rule m_postI)
        show "mextends env env1" by (rule i(1))
        show "mvars env1 pt" using i(2) by (simp add: mvars_simps)
        show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" by (rule i(3))
        show "bstable env \<Longrightarrow> bstable env1" by (rule ib)
      next
        fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
          and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
        from to obtain P2 where T2: "Ty = Tt \<rightarrow>\<^sub>T P2" and tt: "e0\<langle>0:Tt\<rangle> \<turnstile> tt : P2"
          and cTt: "cert_typ alg ar Tt" by (auto simp: ob)
        have bse': "bs_env TVar (e0\<langle>0:Tt\<rangle>) ((nt, Tt) # bs)" by (rule bs_env_TVar_Cons[OF bse cTt])
        have tp': "e0\<langle>0:Tt\<rangle> \<turnstile> inst (mtinst tye) (incr pt $ Bound 0) : P2"
          using tp T2 by (auto simp: il)
        show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
        proof (intro conjI impI)
          show "btyped tye (snd env1)" by (rule i(4)[OF ex bse' tp' tt bt])
          assume bf: "btyped tye te"
          have mi: "minst (tye, te) (incr pt $ Bound 0) = lift (minst (tye, te) pt) 0 $ Bound 0"
            using bf by (simp add: minst_incr)
          have "e0\<langle>0:Tt\<rangle> \<turnstile> lift (minst (tye, te) pt) 0 $ Bound 0 : P2"
            using typing_minst[OF tp' bf] bf by (simp add: minst_incr)
          moreover have "lift (minst (tye, te) pt) 0 $ Bound 0 \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> tt"
            using i(5)[OF ex bse' tp' tt bt bf] bf by (simp add: minst_incr)
          ultimately show "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            using eta_expand_conv(2)[of e0 Tt "minst (tye, te) pt" P2 tt nt] to by (simp add: ob T2)
        qed
      qed
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
        have ptv: "pt = Var ixn T \<degree>\<degree> map Bound is" by (simp add: ptc ph pargs)
        have vpt: "vars pt = {(ixn, T)}" by (auto simp: ptv vars_apps)
        have mi: "minst env' pt = minst env' (Var ixn T) \<degree>\<degree> map Bound is" for env'
          by (simp add: ptv minst_apps o_def)
        have tyv: "tsubst (mtinst tye) T = map e0 is \<Rrightarrow> Ty \<and> (\<forall>i\<in>set is. 0 \<le> i)"
          if "e0 \<turnstile> inst (mtinst tye) pt : Ty" for tye e0 Ty
        proof -
          from that have "e0 \<turnstile> Var ixn (tsubst (mtinst tye) T) \<degree>\<degree> map Bound is : Ty"
            by (simp add: ptv inst_apps o_def)
          then obtain Ts where a1: "e0 \<turnstile> Var ixn (tsubst (mtinst tye) T) : Ts \<Rrightarrow> Ty"
            and a2: "e0 \<tturnstile> map Bound is : Ts"
            by (rule list_app_typeE)
          from a1 have "tsubst (mtinst tye) T = Ts \<Rrightarrow> Ty" by (rule typing_elims(4)) (erule sym)
          with typings_BoundsD[OF a2] show ?thesis by simp
        qed
        from lookup1_cases[OF lk] show ?thesis
        proof (elim disjE exE conjE)
          assume lr: "lr = None" and none: "vt_lookup itms ixn = None"
          from h2 lr obtain itms' where mb: "ok (match_bind itms bs ixn T is ob) itms'"
            and env1: "env1 = (iTs, itms')"
            by auto
          note b = ok_match_bind[OF mb dis]
          let ?u = "abs_list (map (\<lambda>i. bs ! nat_of_integer i) is) (rename (bidx is) 0 ob)"
          show ?thesis
          proof (rule m_postI)
            show "mextends env env1" using b(1,2) by (auto simp: e env1 mextends_def textends_def)
            show "mvars env1 pt" by (simp add: vpt mvars_def env1 b(2))
            show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" by (simp add: e env1)
            show "bstable env \<Longrightarrow> bstable env1"
              using bstable_update[of iTs itms T] abs_bound_flex[OF ab[unfolded ptv]] by (simp add: e env1 b(2))
          next
            fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
              and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
            note tv = tyv[OF tp]
            note mbd = match_binding[OF bse to b(3) b(4)]
            have tu: "e' \<turnstile> ?u : tsubst (mtinst tye) T" for e'
              using mbd(2)[of e'] tv by simp
            have "btyped tye (snd env1)"
              unfolding env1 b(2) snd_conv by (rule btyped_update[OF bt[unfolded e snd_conv] mbd(1) tu])
            moreover have "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            proof -
              have "vt_lookup te ixn = Some (T, ?u)"
                using ex unfolding env1 b(2) mextends_def by (cases ixn) auto
              then show ?thesis using mbd(3) by (simp add: mi minst_Var)
            qed
            ultimately show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
              by blast
          qed
        next
          fix u assume lr: "lr = Some u" and some: "vt_lookup itms ixn = Some (T, u)"
          from h2 lr obtain u' where rd: "ok (red u is []) u'" and ae: "aeconv ob u'"
            and env1: "env1 = (iTs, itms)"
            by (auto split: if_splits)
          show ?thesis
          proof (rule m_postI)
            show "mextends env env1" by (simp add: e env1)
            show "mvars env1 pt" using some by (simp add: vpt mvars_def env1)
            show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" by (simp add: e env1)
            show "bstable env \<Longrightarrow> bstable env1" by (simp add: e env1)
          next
            fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
              and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
            note tv = tyv[OF tp]
            have "btyped tye (snd env1)" using bt by (simp add: e env1)
            moreover have "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
            proof -
              have lt: "vt_lookup te ixn = Some (T, u)"
                using ex some unfolding env1 mextends_def by (cases ixn) auto
              have "\<forall>e. e \<turnstile> u : tsubst (mtinst tye) T"
                using bt some unfolding e btyped_def by (cases ixn) auto
              then have tu: "e0 \<turnstile> u : map e0 is \<Rrightarrow> Ty" using tv by simp
              have tb: "e0 \<tturnstile> map Bound is : map e0 is" using tv by (intro typings_Bounds) simp
              have ta: "e0 \<turnstile> u \<degree>\<degree> map Bound is : Ty" by (rule list_app_typeI[OF tu tb])
              have bb: "u \<degree>\<degree> map Bound is \<rightarrow>\<^sub>\<beta>\<^sup>* u'"
                using red_beta[OF rd] tv by (simp add: rename_bren_Nil)
              have tu': "e0 \<turnstile> u' : Ty"
                by (rule subject_reduction_reds[OF beta_reds_beta_eta_reds[OF bb] ta])
              have "u \<degree>\<degree> map Bound is \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> u'"
                by (rule beta_eta_conv[OF beta_reds_beta_eta_reds[OF bb] wt_closedI[OF ta]])
              also have "u' \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob"
                using aeconv_conv[OF ae wt_closedI[OF to] wt_closedI[OF tu']] by (rule conv_sym)
              finally show ?thesis using lt by (simp add: mi minst_Var)
            qed
            ultimately show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
              by blast
          qed
        qed
      next
        case False
        obtain oh oargs where so: "strip_comb ob = (oh, oargs)" by force
        have obc: "ob = oh \<degree>\<degree> oargs" by (rule strip_comb_apps[OF so])
        note h = h[simplified False if_False so Let_def prod.case]
        text \<open>A rigid head matched against an object head, followed by the arguments:\<close>
        have rig: "m_post bs env env1 pt ob"
          if m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
              (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
            and te: "textends iTs iTs'" and rh: "rigid ph"
            and hd: "\<And>tye. textends iTs' tye \<Longrightarrow> inst (mtinst tye) ph = oh"
            and ab': "\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p"
            and tc: "tye_cert iTs \<Longrightarrow> tye_cert iTs'"
          for iTs'
        proof -
          have pa: "\<forall>p\<in>set pargs. (\<forall>T\<in>typs p. wft ar T) \<and> abs_bound (tbnd (fst (iTs', itms))) p"
            using wp ab' by (auto simp: ptc typs_apps_m)
          have qa: "\<forall>q\<in>set oargs. \<forall>T\<in>typs q. cert_typ alg ar T" using wo by (auto simp: obc typs_apps_m)
          note a = args[OF m pa qa]
          have vh: "vars ph = {}" using rh by (cases ph) auto
          show ?thesis
          proof (rule m_postI)
            show "mextends env env1" using te a by (auto simp: e mextends_def intro: textends_trans)
            have "mvars env1 ph" using vh by (simp add: mvars_def)
            with a show "mvars env1 pt" by (simp add: ptc mvars_apps)
            show "tye_cert (fst env) \<Longrightarrow> tye_cert (fst env1)" using a tc by (simp add: e)
            show "bstable env \<Longrightarrow> bstable env1" using a bstable_textends[OF _ te, of itms] by (simp add: e)
          next
            fix tye te e0 Ty assume ex: "mextends env1 (tye, te)" and bse: "bs_env TVar e0 bs"
              and tp: "e0 \<turnstile> inst (mtinst tye) pt : Ty" and to: "e0 \<turnstile> ob : Ty" and bt: "btyped tye (snd env)"
            have te': "textends iTs' tye" using a ex by (auto simp: mextends_def intro: textends_trans)
            have ih: "inst (mtinst tye) ph = oh" by (rule hd[OF te'])
            from tp have "e0 \<turnstile> oh \<degree>\<degree> map (inst (mtinst tye)) pargs : Ty" by (simp add: ptc inst_apps ih)
            then obtain As where ha: "e0 \<turnstile> oh : As \<Rrightarrow> Ty"
              and pa': "e0 \<tturnstile> map (inst (mtinst tye)) pargs : As" by (rule list_app_typeE)
            from to[unfolded obc] obtain Bs where hb: "e0 \<turnstile> oh : Bs \<Rrightarrow> Ty"
              and qb: "e0 \<tturnstile> oargs : Bs" by (rule list_app_typeE)
            have "As \<Rrightarrow> Ty = Bs \<Rrightarrow> Ty" using typing_unique[OF ha hb] .
            moreover have "length As = length Bs" using typings_nth[OF pa'] typings_nth[OF qb] a by simp
            ultimately have AB: "As = Bs" using funs_eq by blast
            have l2: "list_all2 (\<lambda>p q. \<exists>Ty. e0 \<turnstile> inst (mtinst tye) p : Ty \<and> e0 \<turnstile> q : Ty) pargs oargs"
              using typings_nth[OF pa'] typings_nth[OF qb] a AB by (auto simp: list_all2_conv_all_nth)
            have bt': "btyped tye (snd (iTs', itms))" using bt by (simp add: e)
            from a ex bse l2 bt' have b: "btyped tye (snd env1)"
              "btyped tye te \<Longrightarrow> list_all2 (\<lambda>p q. minst (tye, te) p \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> q) pargs oargs"
              by blast+
            show "btyped tye (snd env1) \<and> (btyped tye te \<longrightarrow> minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob)"
            proof (intro conjI impI)
              show "btyped tye (snd env1)" by (rule b(1))
              assume bf: "btyped tye te"
              have mh: "minst (tye, te) ph = oh" using minst_rigid[OF rh] ih by simp
              have mp: "minst (tye, te) pt = oh \<degree>\<degree> map (minst (tye, te)) pargs" by (simp add: ptc minst_apps mh)
              have w1: "wt (oh \<degree>\<degree> map (minst (tye, te)) pargs)"
                using wt_closedI[OF typing_minst[OF tp bf]] by (simp add: mp)
              have "oh \<degree>\<degree> map (minst (tye, te)) pargs \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> oh \<degree>\<degree> oargs"
                by (rule conv_apps[OF _ w1 wt_closedI[OF to[unfolded obc]] conv_refl])
                  (use b(2)[OF bf] in \<open>simp add: list_all2_map1\<close>)
              then show "minst (tye, te) pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by (simp add: mp obc)
            qed
          qed
        qed
        text \<open>Constants and free variables: their types are matched first.\<close>
        have typed: "(\<forall>tye. textends iTs' tye \<longrightarrow> tsubst (mtinst tye) Ta = Tb) \<and>
            (\<forall>p\<in>set pargs. abs_bound (tbnd iTs') p) \<and> (tye_cert iTs \<longrightarrow> tye_cert iTs')"
          if tm: "ok (typ_match alg Ta Tb iTs) iTs'" and wa: "wft ar Ta" and cb: "cert_typ alg ar Tb"
            and abh: "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
          for Ta Tb iTs'
        proof (intro conjI allI impI ballI)
          have wb: "wft ar Tb" using cb by (rule cert_wft)
          show "textends iTs' tye \<Longrightarrow> tsubst (mtinst tye) Ta = Tb" for tye
            by (rule typ_match_inst[OF tm wa wb])
          have "tbnd iTs \<union> tvars Ta \<subseteq> tbnd iTs'"
            using tbnd_mono[OF typ_match_ext[OF tm]] typ_match_tbnd[OF tm wa wb] by blast
          then show "abs_bound (tbnd iTs') p" if "p \<in> set pargs" for p
            using abh that abs_bound_mono by blast
          show "tye_cert iTs \<Longrightarrow> tye_cert iTs'" by (rule typ_match_cert[OF tm wa wb cb])
        qed
        show ?thesis
        proof (cases ph)
          case ph: (Const a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Const b Tb)
            from h ph oh obtain iTs' where ab': "a = b" and tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have w: "wft ar Ta" "cert_typ alg ar Tb" using wp wo by (simp_all add: ptc obc ph oh typs_apps_m)
            have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            note ty = typed[OF tm w this]
            show ?thesis
              by (rule rig[OF m typ_match_ext[OF tm]]) (use ty in \<open>simp_all add: ph oh ab'\<close>)
          qed (use h ph in auto)
        next
          case ph: (Free a Ta)
          show ?thesis
          proof (cases oh)
            case oh: (Free b Tb)
            from h ph oh obtain iTs' where ab': "a = b" and tm: "ok (typ_match alg Ta Tb iTs) iTs'"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs', itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have w: "wft ar Ta" "cert_typ alg ar Tb" using wp wo by (simp_all add: ptc obc ph oh typs_apps_m)
            have "\<forall>p\<in>set pargs. abs_bound (tbnd iTs \<union> tvars Ta) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            note ty = typed[OF tm w this]
            show ?thesis
              by (rule rig[OF m typ_match_ext[OF tm]]) (use ty in \<open>simp_all add: ph oh ab'\<close>)
          qed (use h ph in auto)
        next
          case ph: (Bound i)
          show ?thesis
          proof (cases oh)
            case oh: (Bound j)
            from h ph oh have ij: "i = j"
              and m: "ok (handle (zip_eq pargs oargs \<bind> (\<lambda>pqs. foldM (\<lambda>(p, q). fm alg bs p q) pqs (iTs, itms)))
                (\<lambda>e. case e of Unequal_Lengths \<Rightarrow> raise Match | _ \<Rightarrow> raise e)) env1"
              by (auto split: if_splits)
            have abb: "\<forall>p\<in>set pargs. abs_bound (tbnd iTs) p"
              using ab abs_bound_apps[of ph] by (simp add: ptc ph)
            show ?thesis
              by (rule rig[OF m textends_refl _ _ abb]) (simp_all add: ph oh ij)
          qed (use h ph in auto)
        qed (use False h strip_comb_head[OF sp] in auto)
      qed
    qed
  qed
qed


subsection \<open>Soundness\<close>

lemma closed_inst: "closed (inst \<rho> t) \<longleftrightarrow> closed t"
  by (simp add: closed_iff_loose_bvar1)

lemma bs_env_Nil: "bs_env \<rho> e []"
  by (simp add: bs_env_def)

text \<open>
  A successful first-order match of a pattern with well-formed types against a closed, typed
  object extends the environment, binds the variables of the pattern, keeps the bindings typed,
  and instantiates the pattern to a term of the type of the object that is equivalent to it. The
  initial bindings are typed, with types whose type variables are bound.
\<close>

theorem first_order_match_sound:
  assumes "ok (first_order_match alg pt ob env) env'"
    and "closed ob" "e \<turnstile> ob : T" "\<forall>U\<in>typs pt. wft ar U"
    and "btyped (fst env) (snd env)" "bstable env"
  shows "mextends env env'" "mvars env' pt" "btyped (fst env') (snd env')"
    "e \<turnstile> minst env' pt : T" "minst env' pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" "bstable env'"
proof -
  have f: "fo_mtch alg False env pt ob = Some (Ok env')"
    using assms(1) by (simp add: first_order_match_def)
  have cl: "\<not> False \<longrightarrow> closed ob" using assms(2) by simp
  note p = fo_postD[OF fo_mtch_sound[OF f refl refl cl assms(4)]]
  show "bstable env'" by (rule fo_postD_bstable[OF fo_mtch_sound[OF f refl refl cl assms(4)] assms(3,6)])
  obtain tye' te' where env': "env' = (tye', te')" by force
  have ex: "textends (fst env) tye'" using p(1) env' by (simp add: mextends_def)
  have bt: "btyped tye' (snd env)"
    using btyped_textends[OF _ _ ex] assms(5,6) by (cases env) simp
  show "mextends env env'" "mvars env' pt" using p(1,2) assms(2) by simp_all
  have b: "btyped tye' te'" using p(3)[of tye' te' e T] assms(2,3) bt by (simp add: env')
  then show "btyped (fst env') (snd env')" by (simp add: env')
  from p(4)[of tye' te' e T] assms(2,3) bt b
  show "e \<turnstile> minst env' pt : T" "minst env' pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" by (simp_all add: env')
qed

text \<open>
  A successful match of a closed, typed pattern against a closed, typed object, in an
  environment with certified type bindings and typed term bindings, extends the environment,
  binds the variables of the pattern, keeps the bindings typed, and instantiates the pattern to a
  term equivalent to the object.
\<close>

theorem match_sound:
  assumes "ok (match alg pt ob env) env'"
    and "closed pt" "closed ob" "e \<turnstile> pt : pT" "e \<turnstile> ob : oT"
    and "tye_cert (fst env)" "btyped (fst env) (snd env)" "bstable env"
  shows "mextends env env'" "mvars env' pt" "btyped (fst env') (snd env')"
    "minst env' pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" "bstable env'"
proof -
  from assms(1) obtain iTs where tm: "ok (typ_match alg pT oT (fst env)) iTs"
    and h: "ok (handle (mtch alg [] pt ob (iTs, snd env))
      (\<lambda>e. case e of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise e)) env'"
    by (auto simp: match_def Let_def fastype_of_closed[OF assms(4,2)] fastype_of_closed[OF assms(5,3)])
  have cp: "cert_typ alg ar pT" "cert_typ alg ar oT"
    using typing_cert_closed[OF assms(4,2)] typing_cert_closed[OF assms(5,3)] .
  have wp: "\<forall>T\<in>typs pt. wft ar T" using typing_typs_cert[OF assms(4)] by (auto simp: cert_wft)
  have wo: "\<forall>T\<in>typs ob. cert_typ alg ar T" using typing_typs_cert[OF assms(5)] .
  have te: "textends (fst env) iTs" by (rule typ_match_ext[OF tm])
  obtain tye' te' where env': "env' = (tye', te')" by force
  have bt: "btyped tye' (snd env)" if "textends iTs tye'"
    using btyped_textends[OF _ _ textends_trans[OF te that]] assms(7,8) by (cases env) simp
  have pat: "ok (case ex of Pattern \<Rightarrow> first_order_match alg pt ob (iTs, snd env) | _ \<Rightarrow> raise ex) env' \<Longrightarrow>
      ok (first_order_match alg pt ob (iTs, snd env)) env'" for ex
    by (cases ex) simp_all
  have bs: "bstable (iTs, snd env)" using bstable_textends[OF _ te] assms(8) by (cases env) simp
  from h consider (m) "ok (mtch alg [] pt ob (iTs, snd env)) env'"
    | (f) "ok (first_order_match alg pt ob (iTs, snd env)) env'"
    using pat by (auto simp: ok_handle)
  then have "mextends (iTs, snd env) env' \<and> mvars env' pt \<and> btyped (fst env') (snd env') \<and>
    minst env' pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob \<and> bstable env'"
  proof cases
    case m
    have "\<forall>i. 0 \<le> i \<longrightarrow> loose_bvar1 pt i \<longrightarrow> tvars (e i) \<subseteq> tbnd iTs"
      using assms(2) by (simp add: closed_iff_loose_bvar1)
    moreover have "tvars pT \<subseteq> tbnd iTs" by (rule typ_match_tbnd[OF tm]) (simp_all add: cp cert_wft)
    ultimately have ab: "abs_bound (tbnd iTs) pt" using typing_abs_bound[OF assms(4)] by blast
    note pm = mtch_sound[OF m refl refl wp wo, unfolded fst_conv, OF ab]
    note p = m_postD[OF pm]
    have ex: "textends iTs tye'" using p(1) by (simp add: env' mextends_def)
    have cert: "tye_cert tye'" using p(3) typ_match_cert[OF tm _ _ cp(2) assms(6)] cp
      by (simp add: env' cert_wft)
    have T: "tsubst (mtinst tye') pT = oT" by (rule typ_match_inst[OF tm _ _ ex]) (simp_all add: cp cert_wft)
    have "(\<lambda>j. tsubst (mtinst tye') (e j)) \<turnstile> inst (mtinst tye') pt : oT"
      using typing_inst[OF assms(4) cert_inst_inst_ok[OF cert_inst_mtinst[OF cert]]] by (simp add: T)
    then have tp: "e \<turnstile> inst (mtinst tye') pt : oT" using assms(2) by (simp add: typing_closed closed_inst)
    have b: "btyped tye' te'" using p(4)[of tye' te', OF _ bs_env_Nil tp assms(5)] bt[OF ex] by (simp add: env')
    with p(5)[of tye' te', OF _ bs_env_Nil tp assms(5)] bt[OF ex] p(1,2) m_postD_bstable[OF pm bs]
    show ?thesis by (simp add: env')
  next
    case f
    have fo: "fo_mtch alg False (iTs, snd env) pt ob = Some (Ok env')"
      using f by (simp add: first_order_match_def)
    have cl: "\<not> False \<longrightarrow> closed ob" using assms(3) by simp
    note pf = fo_mtch_sound[OF fo refl refl cl wp]
    note p = fo_postD[OF pf]
    have ex: "textends iTs tye'" using p(1) env' by (simp add: mextends_def)
    have b: "btyped tye' te'" using p(3)[of tye' te' e oT] assms(3,5) bt[OF ex] by (simp add: env')
    with p(4)[of tye' te' e oT] assms(3,5) bt[OF ex] p(1,2) fo_postD_bstable[OF pf assms(5) bs]
    show ?thesis by (simp add: env')
  qed
  then show "mextends env env'" "mvars env' pt" "btyped (fst env') (snd env')"
    "minst env' pt \<equiv>\<^sub>\<alpha>\<^sub>\<beta>\<^sub>\<eta> ob" "bstable env'"
    using te by (auto simp: mextends_def intro: textends_trans)
qed

end

end
