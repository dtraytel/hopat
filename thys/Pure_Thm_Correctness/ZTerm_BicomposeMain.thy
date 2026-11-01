section \<open>Correctness of the composition of tight proofs: main theorem\<close>

theory ZTerm_BicomposeMain
  imports ZTerm_BicomposeProof
begin

context prf_wf_csig
begin

subsection \<open>The invariant of tight proofs\<close>

definition zty :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> ztyp \<Rightarrow> bool" where
  "zty A m T \<longleftrightarrow> tyA ar A (typ_of T) \<and> (\<forall>(v, S)\<in>tvars (typ_of T). snd v \<le> m)"

definition zann :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> bool" where
  "zann A W m t \<longleftrightarrow> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> T = ztyp_of (W x)) \<and>
    (\<forall>T\<in>ztys t. zty A m T) \<and> (\<exists>Ts U. has_type W Ts (zdec t) U)"

definition zinv :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> bool" where
  "zinv A W m p \<longleftrightarrow> zconst_free p \<and> zno_class p \<and> zrf p \<and> zprf_all (zann A W m) (zty A m) p"

text \<open>
  The invariant of the tight proof \<open>p\<close> of a theorem with maximal index \<open>m\<close>, flex-flex pairs
  \<open>tps\<close>, proposition \<open>P\<close> and hypotheses \<open>H\<close>: for a typing of the theorem and of the variables of
  the proof, the proof is valid and its annotations are typed.
\<close>

definition zthm_prf_inv :: "integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm set \<Rightarrow> zproof \<Rightarrow> bool" where
  "zthm_prf_inv m tps P H p \<longleftrightarrow> (\<exists>A W. finite A \<and> scons A \<and> tcert alg A \<and>
    (\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m) \<and> (\<forall>x. tyA ar A (W x)) \<and> wt_thm ar A W m tps P \<and>
    prf_valid alg ar W H tps (zprf_tr p) P \<and> zinv A W m p)"


subsection \<open>Conversion of the terms of the environment\<close>

text \<open>
  The conversion of a term to a tight term needs only that its constants have instances of their
  declared types (\<open>Consts.typargs\<close>), not that the term is typed: the terms of the environment of
  a unifier are typed only up to the normalisation of their types.
\<close>

fun cts :: "pterm \<Rightarrow> bool" where
  "cts (Const c T) \<longleftrightarrow> const_typ_ok c T"
| "cts (Abs a T t) \<longleftrightarrow> cts t"
| "cts (s $ t) \<longleftrightarrow> cts s \<and> cts t"
| "cts _ \<longleftrightarrow> True"

lemma zterm_of_zdec_cts:
  assumes "cts t" "\<forall>v\<in>vars t. snd v \<noteq> -1" "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
  shows "\<exists>z. zterm_of ztargs t = returnZ z \<and> zdec z = t \<and> (\<forall>V\<in>ztys z. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys t. tvars U))"
  using assms
proof (induction t)
  case (Const c T)
  from ztargs_const_typ_ok[of c T] Const.prems(1) obtain Us where u: "ztargs c T = return Us"
    "zconst_typ c Us = T" "\<forall>U\<in>set Us. tvars U \<subseteq> tvars T"
    by auto
  have r1: "typ_of (ztyp_of X) = X" if "X \<in> set Us" for X
  proof (rule typ_of_ztyp_of)
    show "\<forall>(v, S)\<in>tvars X. snd v \<noteq> -1" using that u(3) Const.prems(3) by fastforce
  qed
  then have r: "map typ_of (map ztyp_of Us) = Us" by (auto intro!: map_idI)
  show ?case
  proof (cases Us rule: remdups_adj.cases)
    case 1
    then show ?thesis using u by simp
  next
    case (2 U)
    then show ?thesis using u r r1 by simp
  next
    case (3 U V Ws)
    then show ?thesis using u r r1 by auto
  qed
next
  case (Free a T)
  then show ?case by (simp add: typ_of_ztyp_of)
next
  case (Var x T)
  then show ?case by (cases x) (simp add: typ_of_ztyp_of)
next
  case (Bound i)
  then show ?case by simp
next
  case (Abs a T t)
  then obtain z where z: "zterm_of ztargs t = returnZ z" "zdec z = t"
    "\<forall>V\<in>ztys z. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys t. tvars U)" by auto
  have "typ_of (ztyp_of T) = T" using Abs.prems(3) by (intro typ_of_ztyp_of) auto
  with z show ?case by auto
next
  case (App s t)
  have ps: "cts s" "\<forall>v\<in>vars s. snd v \<noteq> -1" "\<forall>U\<in>tys s. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    and pt: "cts t" "\<forall>v\<in>vars t. snd v \<noteq> -1" "\<forall>U\<in>tys t. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
    using App.prems by auto
  from App.IH(1)[OF ps] obtain zs where zs: "zterm_of ztargs s = returnZ zs" "zdec zs = s"
    "\<forall>V\<in>ztys zs. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys s. tvars U)" by blast
  from App.IH(2)[OF pt] obtain zt where zt: "zterm_of ztargs t = returnZ zt" "zdec zt = t"
    "\<forall>V\<in>ztys zt. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys t. tvars U)" by blast
  show ?case
  proof (cases "\<exists>T' c. match_of_class (s $ t) = Some (T', c) \<and> s $ t = mk_of_class T' c")
    case True
    then obtain T' c where m: "match_of_class (s $ t) = Some (T', c)" and e: "s $ t = mk_of_class T' c"
      by blast
    then have t: "t = Const STR ''Pure.type'' (Type STR ''itself'' [T'])" by (simp add: mk_of_class_def)
    have "typ_of (ztyp_of T') = T'" using pt(3) t by (intro typ_of_ztyp_of) auto
    then show ?thesis using m e t by (auto simp: of_class_def mk_of_class_def class_suffix_def propT_def)
  next
    case False
    then show ?thesis using zs zt by (auto split: option.splits)
  qed
qed

lemma tenv_zok_cts:
  assumes "\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<noteq> -1 \<and> cts u \<and> (\<forall>v\<in>vars u. snd v \<noteq> -1) \<and>
    (\<forall>T\<in>tys u. (\<forall>(v, S)\<in>tvars T. snd v \<noteq> -1) \<and> tcons (tyenv env) T)"
  shows "tenv_zok ztargs env"
  unfolding tenv_zok_def
proof (intro allI impI)
  fix x U u assume l: "vt_lookup (tenv env) x = Some (U, u)"
  with assms have a: "snd x \<noteq> -1" "cts u" "\<forall>v\<in>vars u. snd v \<noteq> -1" "\<forall>T\<in>tys u. \<forall>(v, S)\<in>tvars T. snd v \<noteq> -1"
    and tc: "\<forall>T\<in>tys u. tcons (tyenv env) T" by blast+
  from zterm_of_zdec_cts[OF a(2-4)] obtain z where z: "zterm_of ztargs u = returnZ z" "zdec z = u"
    "\<forall>V\<in>ztys z. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys u. tvars U)" by blast
  have "\<forall>V\<in>ztys z. tcons (tyenv env) (typ_of V)"
    using z(3) tc unfolding tcons_def by blast
  with a(1) z(1,2) show "snd x \<noteq> -1 \<and> (\<exists>zu. zterm_of ztargs u = returnZ zu \<and> zdec zu = u \<and>
      (\<forall>V\<in>ztys zu. tcons (tyenv env) (typ_of V)))" by blast
qed

lemma has_type_cts: "has_type V Ts t T \<Longrightarrow> cts t"
  by (induction rule: has_type.induct) auto

lemma cts_ren_term[simp]: "cts (ren_term r t) = cts t"
  by (induction r t rule: ren_term.induct) auto

lemma cts_strip_apply:
  assumes "cts B" "cts A" "\<And>t. cts t \<Longrightarrow> cts (f t)"
  shows "cts (strip_apply f B A)"
  using assms(1,2)
proof (induction A arbitrary: B rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "\<exists>U B0 B1 V A2 B2. B = Const STR ''Pure.imp'' U $ B0 $ B1 \<and> A = Const STR ''Pure.imp'' V $ A2 $ B2")
    case True
    then obtain U B0 B1 V A2 B2 where e: "B = Const STR ''Pure.imp'' U $ B0 $ B1"
      "A = Const STR ''Pure.imp'' V $ A2 $ B2" by blast
    have "cts (strip_apply f B1 B2)" using less e by auto
    then show ?thesis using less.prems e by (subst strip_apply.simps) simp
  next
    case nimp: False
    have ni: "(case (B, dest_imp B, dest_imp A) of (c $ _ $ _, Some (_, B1), Some (A2, B2)) \<Rightarrow> c $ A2 $ strip_apply f B1 B2
        | _ \<Rightarrow> X) = X" for X
      using nimp by (auto simp: dest_imp_Some split: pterm.splits option.splits prod.splits)
    show ?thesis
    proof (cases "\<exists>U a0 T0 t1 V a T t2. B = Const STR ''Pure.all'' U $ Abs a0 T0 t1 \<and>
        A = Const STR ''Pure.all'' V $ Abs a T t2")
      case True
      then obtain U a0 T0 t1 V a T t2 where e: "B = Const STR ''Pure.all'' U $ Abs a0 T0 t1"
        "A = Const STR ''Pure.all'' V $ Abs a T t2" by blast
      have "cts (strip_apply f t1 t2)" using less e by auto
      then show ?thesis using less.prems e by (subst strip_apply.simps) (simp add: ni)
    next
      case False
      then have "(case (B, dest_all B, dest_all A) of (c $ _, Some (_, _, t1), Some (a, T, t2)) \<Rightarrow>
          c $ Abs a T (strip_apply f t1 t2) | _ \<Rightarrow> f A) = f A"
        by (auto simp: dest_all_Some split: pterm.splits option.splits prod.splits)
      then have "strip_apply f B A = f A" by (subst strip_apply.simps, subst ni)
      then show ?thesis using less.prems assms(3) by simp
    qed
  qed
qed

text \<open>
  The terms of an environment convert to tight terms: their constants have instances of their
  declared types and no variable has index \<open>-1\<close>. For the environments of the unifier this holds
  as their terms are built from the terms of the problem (whose constants keep their types) and
  from fresh variables; it is a hypothesis of the main theorem.
\<close>

definition zenv_ok :: "env \<Rightarrow> bool" where
  "zenv_ok env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<noteq> -1 \<and> cts u \<and>
    (\<forall>v\<in>vars u. snd v \<noteq> -1) \<and> (\<forall>T\<in>tys u. \<forall>(v, S)\<in>tvars T. snd v \<noteq> -1))"

lemma tenv_zok_zenv_ok:
  assumes "zenv_ok env" "\<forall>T\<in>etys env. tcons (tyenv env) T"
  shows "tenv_zok ztargs env"
  by (rule tenv_zok_cts) (use assms etysI in \<open>fastforce simp: zenv_ok_def\<close>)

lemma mapZ_rel: "\<forall>x\<in>set xs. \<exists>y. f x = returnZ y \<and> R x y \<Longrightarrow> \<exists>ys. mapZ f xs = returnZ ys \<and> list_all2 R xs ys"
  by (induction xs) auto

text \<open>The normalisation of a term of the new theorem, by conversion and tight normalisation.\<close>

lemma normt_ok:
  assumes n: "ok (norm_term env X) X'" and c: "cts X" "\<forall>v\<in>vars X. snd v \<noteq> -1"
    "\<forall>U\<in>tys X. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" and tc: "\<forall>U\<in>tys X. tcons (tyenv env) U"
    and env: "tacyc (tyenv env)" "tcons_env (tyenv env)" "\<forall>U\<in>etys env. tcons (tyenv env) U"
      "tyenv_zok (tyenv env)" "tenv_zok ztargs env"
  shows "\<exists>N. (zterm_of ztargs X \<bind> znorm_term ztargs env) = returnZ N \<and> zdec N = X'"
proof -
  from zterm_of_zdec_cts[OF c] obtain z where z: "zterm_of ztargs X = returnZ z" "zdec z = X"
    "\<forall>V\<in>ztys z. tvars (typ_of V) \<subseteq> (\<Union>U\<in>tys X. tvars U)" by blast
  have "\<forall>V\<in>ztys z. tcons (tyenv env) (typ_of V)" using z(3) tc unfolding tcons_def by blast
  from znorm_term_sim[OF _ z(2) this tc env] n obtain z' where
    "znorm_term ztargs env z = returnZ z'" "zdec z' = X'" by (auto simp: return_def)
  with z(1) show ?thesis by simp
qed


text \<open>Normalisation keeps the canonical forms of \<open>Pure.imp\<close> and \<open>Pure.all\<close>.\<close>

lemma zcanon_zincr_bv[simp]: "zcanon (zincr_bv inc lev t) = zcanon t"
  by (induction inc lev t rule: zincr_bv.induct) auto

lemma zcanon_zsubst_bound: "zcanon arg \<Longrightarrow> zcanon t \<Longrightarrow> zcanon (zsubst_bound arg lev t)"
  by (induction arg lev t rule: zsubst_bound.induct) (auto simp: zincr_boundvars_def)

lemma zcanon_subst_term_bound: "zcanon arg \<Longrightarrow> zcanon t \<Longrightarrow> zcanon (subst_term_bound arg t)"
  by (simp add: subst_term_bound_def zcanon_zsubst_bound)

lemma zcanon_beta_norm_term:
  assumes "beta_norm_term z = Some z'" "zcanon z"
  shows "zcanon z'"
  using assms
proof (induction z z' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn z z')
  note F = "1.hyps" and IH = "1.IH"
  show ?case
  proof (cases z)
    case (ZAbs a T b)
    with F obtain b' where "bn b = Some b'" "z' = ZAbs a T b'" by (auto split: Option.bind_splits)
    with IH "1.prems" ZAbs show ?thesis by auto
  next
    case (ZApp f u)
    have cf: "zcanon f" "zcanon u" using "1.prems" ZApp by auto
    show ?thesis
    proof (cases "\<exists>a T body. f = ZAbs a T body")
      case True
      then obtain a T body where f: "f = ZAbs a T body" by blast
      with F ZApp have "bn (subst_term_bound u body) = Some z'" by simp
      with IH cf f show ?thesis by (auto intro: zcanon_subst_term_bound)
    next
      case False
      with F ZApp obtain nf where nf: "bn f = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some z'"
        by (cases f) (auto split: Option.bind_splits)
      have cnf: "zcanon nf" using IH[OF nf] cf by blast
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbs a T body")
        case True
        then obtain a T body where n: "nf = ZAbs a T body" by blast
        with rest have "bn (subst_term_bound u body) = Some z'" by simp
        with IH cf cnf n show ?thesis by (auto intro: zcanon_subst_term_bound)
      next
        case nA: False
        with rest obtain nu where nu: "bn u = Some nu" "z' = ZApp nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        with IH[OF nu(1)] cf cnf show ?thesis by simp
      qed
    qed
  next
    case (ZVar x T)
    with F "1.prems" show ?thesis by simp
  qed (use F "1.prems" in simp_all)
qed

lemma zcanon_zlookup:
  "zlookup ztargs env xi T = returnZ (Some u) \<Longrightarrow> zcanon u"
  by (auto simp: zlookup_def bindZ_eq_returnZ liftMZ_eq_returnZ intro: zterm_of_zcanon split: if_splits option.splits)

lemma zcanon_znorm_term_aux:
  assumes "znorm_term_aux x = returnZ z'" "zcanon (snd x)" "fst (fst x) = ztargs"
  shows "zcanon z'"
proof -
  have "\<forall>z'. Some y = returnZ z' \<longrightarrow> zcanon (snd x) \<longrightarrow> fst (fst x) = ztargs \<longrightarrow> zcanon z'"
    if "znorm_term_aux x = Some y" for y
    using that
  proof (induction x y rule: znorm_term_aux.raw_induct[rotated, consumes 1])
    case (1 f x y)
    note F = "1.hyps" and IH = "1.IH"
    obtain ta env t where x: "x = ((ta, env), t)" by (cases x) auto
    show ?case
    proof (intro allI impI)
      fix z' assume y: "Some y = returnZ z'" and ct: "zcanon (snd x)" and ta: "fst (fst x) = ztargs"
      have IH': "zcanon w" if "f ((ta, env), s) = returnZ w" "zcanon s" for s w
        using IH[of "((ta, env), s)"] that x ta by (auto simp: returnZ_def)
      from F y have F': "(case t of
          ZVar xi T \<Rightarrow> zlookup ta env xi T \<bind> (\<lambda>r. case r of Some u \<Rightarrow> f ((ta, env), u)
            | None \<Rightarrow> znorm_type (tyenv env) T \<bind> (\<lambda>T'. returnZ (ZVar xi T')))
        | ZConst1 a T \<Rightarrow> znorm_type (tyenv env) T \<bind> (\<lambda>T'. returnZ (ZConst1 a T'))
        | ZConst a Ts \<Rightarrow> mapZ (znorm_type (tyenv env)) Ts \<bind> (\<lambda>Ts'. returnZ (ZConst a Ts'))
        | ZAbs a T b \<Rightarrow> znorm_type (tyenv env) T \<bind> (\<lambda>T'. f ((ta, env), b) \<bind> (\<lambda>b'. returnZ (ZAbs a T' b')))
        | ZApp g u \<Rightarrow> (case g of
            ZAbs _ _ body \<Rightarrow> f ((ta, env), subst_term_bound u body)
          | _ \<Rightarrow> f ((ta, env), g) \<bind> (\<lambda>nf. case nf of
              ZAbs _ _ body \<Rightarrow> f ((ta, env), subst_term_bound u body)
            | _ \<Rightarrow> f ((ta, env), u) \<bind> (\<lambda>nu. returnZ (ZApp nf nu))))
        | ZOfclass T c \<Rightarrow> znorm_type (tyenv env) T \<bind> (\<lambda>T'. returnZ (ZOfclass T' c))
        | t \<Rightarrow> returnZ t) = returnZ z'"
        using F y unfolding x fst_conv snd_conv by simp
      have ct': "zcanon t" using ct x by simp
      have ta': "ta = ztargs" using ta x by simp
      show "zcanon z'"
      proof (cases t)
        case (ZVar xi T)
        with F' obtain r where r: "zlookup ta env xi T = returnZ r"
          and rest: "(case r of Some u \<Rightarrow> f ((ta, env), u)
            | None \<Rightarrow> znorm_type (tyenv env) T \<bind> (\<lambda>T'. returnZ (ZVar xi T'))) = returnZ z'"
          by (auto simp: bindZ_eq_returnZ)
        show ?thesis
        proof (cases r)
          case None
          with rest show ?thesis by (auto simp: bindZ_eq_returnZ)
        next
          case (Some u)
          with rest r ta' have "f ((ta, env), u) = returnZ z'" "zcanon u" by (auto intro: zcanon_zlookup)
          then show ?thesis by (rule IH')
        qed
      next
        case (ZAbs a T b)
        with F' ct' show ?thesis by (auto simp: bindZ_eq_returnZ intro: IH')
      next
        case (ZApp g u)
        have cg: "zcanon g" "zcanon u" using ct' ZApp by auto
        show ?thesis
        proof (cases "\<exists>a T body. g = ZAbs a T body")
          case True
          then obtain a T body where g: "g = ZAbs a T body" by blast
          with F' ZApp have "f ((ta, env), subst_term_bound u body) = returnZ z'" by simp
          with cg g show ?thesis by (auto intro: IH' zcanon_subst_term_bound)
        next
          case False
          with F' ZApp obtain nf where nf: "f ((ta, env), g) = returnZ nf"
            and rest: "(case nf of ZAbs _ _ body \<Rightarrow> f ((ta, env), subst_term_bound u body)
              | _ \<Rightarrow> f ((ta, env), u) \<bind> (\<lambda>nu. returnZ (ZApp nf nu))) = returnZ z'"
            by (cases g) (auto simp: bindZ_eq_returnZ)
          have cnf: "zcanon nf" by (rule IH'[OF nf cg(1)])
          show ?thesis
          proof (cases "\<exists>a T body. nf = ZAbs a T body")
            case True
            then obtain a T body where n: "nf = ZAbs a T body" by blast
            with rest have "f ((ta, env), subst_term_bound u body) = returnZ z'" by simp
            with cg cnf n show ?thesis by (auto intro: IH' zcanon_subst_term_bound)
          next
            case nA: False
            with rest obtain nu where "f ((ta, env), u) = returnZ nu" "z' = ZApp nf nu"
              by (cases nf) (auto simp: bindZ_eq_returnZ)
            with IH'[of u nu] cg cnf show ?thesis by simp
          qed
        qed
      qed (use F' ct' in \<open>auto simp: bindZ_eq_returnZ\<close>)
    qed
  qed
  with assms show ?thesis by (auto simp: returnZ_def)
qed

lemma zcanon_znorm_term:
  "znorm_term ztargs env z = returnZ z' \<Longrightarrow> zcanon z \<Longrightarrow> zcanon z'"
  by (auto simp: znorm_term_def liftOZ_def returnZ_def intro: zcanon_beta_norm_term zcanon_znorm_term_aux[simplified returnZ_def]
      split: if_splits option.splits)


subsection \<open>Normalisation of rigid applications\<close>

lemma list_comb_Const_snoc[simp]: "list_comb (Const c U) (us @ [u]) = list_comb (Const c U) us $ u"
  by (simp add: list_comb_def)

lemma list_comb_Const_not_Abs[simp]: "list_comb (Const c U) us \<noteq> Abs a T b"
  by (induction us rule: rev_induct) auto

lemma cbc_list_comb_Const[simp]:
  "could_beta_contract (list_comb (Const c U) us) \<longleftrightarrow> (\<exists>u\<in>set us. could_beta_contract u)"
proof (induction us rule: rev_induct)
  case (snoc u us)
  have "could_beta_contract (list_comb (Const c U) us $ u) \<longleftrightarrow>
      could_beta_contract (list_comb (Const c U) us) \<or> could_beta_contract u"
    by (cases us rule: rev_cases) auto
  with snoc show ?case by auto
qed (simp add: list_comb_def)

lemma norm_term1_empty_id: "vt_is_empty te \<Longrightarrow> \<not> could_beta_contract t \<Longrightarrow> norm_term1 te t = return t"
proof (induction t)
  case (Var x T)
  then show ?case by (subst norm_term1.simps) (simp add: lookup1_def vt_is_empty_lookup bindM_def return_def)
next
  case (Abs a T b)
  then show ?case by (subst norm_term1.simps) (simp add: bindM_def return_def)
next
  case (App f u)
  then have nf: "norm_term1 te f = return f" "norm_term1 te u = return u" "\<not> (\<exists>a T b. f = Abs a T b)"
    by (auto elim: could_beta_contract.elims)
  then show ?case by (subst norm_term1.simps) (cases f; simp add: bindM_def return_def)
qed (subst norm_term1.simps; simp)+

lemma norm_term1_app:
  assumes "ok (norm_term1 te (f $ u)) X'" "\<forall>a T b. f \<noteq> Abs a T b" "ok (norm_term1 te f) f'" "\<forall>a T b. f' \<noteq> Abs a T b"
  shows "\<exists>u'. X' = f' $ u' \<and> ok (norm_term1 te u) u'"
proof -
  have "norm_term1 te (f $ u) = bindM (norm_term1 te f) (\<lambda>nf. case nf of Abs _ _ body \<Rightarrow> norm_term1 te (subst_bound u body)
      | _ \<Rightarrow> bindM (norm_term1 te u) (\<lambda>nu. return (nf $ nu)))"
    using assms(2) by (subst norm_term1.simps) (cases f; simp)
  with assms(1,3,4) show ?thesis by (cases f') (auto simp: return_def)
qed

lemma norm_term2_app:
  assumes "ok (norm_term2 env (f $ u)) X'" "\<forall>a T b. f \<noteq> Abs a T b" "ok (norm_term2 env f) f'" "\<forall>a T b. f' \<noteq> Abs a T b"
  shows "\<exists>u'. X' = f' $ u' \<and> ok (norm_term2 env u) u'"
proof -
  have "norm_term2 env (f $ u) = bindM (norm_term2 env f) (\<lambda>nf. case nf of Abs _ _ body \<Rightarrow> norm_term2 env (subst_bound u body)
      | _ \<Rightarrow> bindM (norm_term2 env u) (\<lambda>nu. return (nf $ nu)))"
    using assms(2) by (subst norm_term2.simps) (cases f; simp)
  with assms(1,3,4) show ?thesis by (cases f') (auto simp: return_def)
qed

lemma norm_term1_Abs: "ok (norm_term1 te (Abs a T b)) X' \<Longrightarrow> \<exists>b'. X' = Abs a T b' \<and> ok (norm_term1 te b) b'"
  by (subst (asm) norm_term1.simps) (auto simp: return_def)

lemma norm_term2_Abs:
  "ok (norm_term2 env (Abs a T b)) X' \<Longrightarrow> \<exists>T' b'. X' = Abs a T' b' \<and> ok (norm_term2 env b) b'"
  by (subst (asm) norm_term2.simps) (auto simp: return_def)

lemma norm_term1_Const: "ok (norm_term1 te (Const c U)) X' \<Longrightarrow> X' = Const c U"
  by (subst (asm) norm_term1.simps) (simp add: return_def)

lemma norm_term2_Const: "ok (norm_term2 env (Const c U)) X' \<Longrightarrow> \<exists>U'. X' = Const c U'"
  by (subst (asm) norm_term2.simps) (auto simp: return_def)

text \<open>
  Normalisation of a term with a constant head and arguments \<open>u1, ..., un\<close>: the head keeps its
  name, the arguments are normalised.
\<close>

lemma norm_term_rigid:
  assumes "ok (norm_term env (list_comb (Const c U) us)) X'"
  shows "\<exists>U' us'. X' = list_comb (Const c U') us' \<and> list_all2 (\<lambda>u u'. ok (norm_term env u) u') us us'"
proof -
  have nc: "\<not> could_beta_contract (list_comb (Const c U) us) \<longleftrightarrow> (\<forall>u\<in>set us. \<not> could_beta_contract u)"
    by simp
  consider (e) "env_is_empty env" "\<not> could_beta_contract (list_comb (Const c U) us)"
    | (t1) "\<not> (env_is_empty env \<and> \<not> could_beta_contract (list_comb (Const c U) us))" "vt_is_empty (tyenv env)"
    | (t2) "\<not> (env_is_empty env \<and> \<not> could_beta_contract (list_comb (Const c U) us))" "\<not> vt_is_empty (tyenv env)"
    by blast
  then show ?thesis
  proof cases
    case e
    with assms have "X' = list_comb (Const c U) us" by (simp add: norm_term_def return_def)
    moreover have "list_all2 (\<lambda>u u'. ok (norm_term env u) u') us us"
      using e nc by (intro list.rel_refl_strong) (simp add: norm_term_def return_def)
    ultimately show ?thesis by blast
  next
    case t1
    have te: "vt_is_empty (tenv env)" if "env_is_empty env" using that by (simp add: env_is_empty_def)
    have nt: "ok (norm_term env u) u'" if "ok (norm_term1 (tenv env) u) u'" for u u'
    proof (cases "env_is_empty env \<and> \<not> could_beta_contract u")
      case True
      with that norm_term1_empty_id[OF te] have "u' = u" by (simp add: return_def)
      with True show ?thesis by (simp add: norm_term_def return_def)
    next
      case False
      with that t1(2) show ?thesis by (simp add: norm_term_def)
    qed
    have "ok (norm_term1 (tenv env) (list_comb (Const c U) us)) X'" using assms t1 by (simp add: norm_term_def)
    then have "\<exists>us'. X' = list_comb (Const c U) us' \<and> list_all2 (\<lambda>u u'. ok (norm_term1 (tenv env) u) u') us us'"
    proof (induction us arbitrary: X' rule: rev_induct)
      case Nil
      then show ?case using norm_term1_Const by auto
    next
      case (snoc u us)
      have nA: "\<forall>a T b. list_comb (Const c U) us \<noteq> Abs a T b" by (cases us rule: rev_cases) auto
      have "\<exists>f'. ok (norm_term1 (tenv env) (list_comb (Const c U) us)) f'"
        using snoc.prems by (subst (asm) norm_term1.simps) (cases "list_comb (Const c U) us"; auto simp: nA)
      then obtain f' where f': "ok (norm_term1 (tenv env) (list_comb (Const c U) us)) f'" by blast
      from snoc.IH[OF f'] obtain vs where vs: "f' = list_comb (Const c U) vs"
        "list_all2 (\<lambda>u u'. ok (norm_term1 (tenv env) u) u') us vs" by blast
      have nA': "\<forall>a T b. f' \<noteq> Abs a T b" using vs(1) by (cases vs rule: rev_cases) auto
      from norm_term1_app[OF _ nA f' nA'] snoc.prems obtain v where
        "X' = f' $ v" "ok (norm_term1 (tenv env) u) v" by auto
      with vs show ?case by (intro exI[of _ "vs @ [v]"]) (simp add: list_all2_appendI)
    qed
    then obtain us' where u: "X' = list_comb (Const c U) us'"
      "list_all2 (\<lambda>u u'. ok (norm_term1 (tenv env) u) u') us us'" by blast
    from u(2) have "list_all2 (\<lambda>u u'. ok (norm_term env u) u') us us'" by (rule list_all2_mono) (rule nt)
    with u(1) show ?thesis by blast
  next
    case t2
    have nt: "ok (norm_term env u) u'" if "ok (norm_term2 env u) u'" for u u'
    proof -
      have "\<not> env_is_empty env" using t2(2) by (auto simp: env_is_empty_def)
      with that t2(2) show ?thesis by (simp add: norm_term_def)
    qed
    have "ok (norm_term2 env (list_comb (Const c U) us)) X'" using assms t2 by (simp add: norm_term_def)
    then have "\<exists>U' us'. X' = list_comb (Const c U') us' \<and> list_all2 (\<lambda>u u'. ok (norm_term2 env u) u') us us'"
    proof (induction us arbitrary: X' rule: rev_induct)
      case Nil
      then show ?case using norm_term2_Const by auto
    next
      case (snoc u us)
      have nA: "\<forall>a T b. list_comb (Const c U) us \<noteq> Abs a T b" by (cases us rule: rev_cases) auto
      have "\<exists>f'. ok (norm_term2 env (list_comb (Const c U) us)) f'"
        using snoc.prems by (subst (asm) norm_term2.simps) (cases "list_comb (Const c U) us"; auto simp: nA)
      then obtain f' where f': "ok (norm_term2 env (list_comb (Const c U) us)) f'" by blast
      from snoc.IH[OF f'] obtain U' vs where vs: "f' = list_comb (Const c U') vs"
        "list_all2 (\<lambda>u u'. ok (norm_term2 env u) u') us vs" by blast
      have nA': "\<forall>a T b. f' \<noteq> Abs a T b" using vs(1) by (cases vs rule: rev_cases) auto
      from norm_term2_app[OF _ nA f' nA'] snoc.prems obtain v where
        "X' = f' $ v" "ok (norm_term2 env u) v" by auto
      with vs show ?case by (intro exI[of _ U'] exI[of _ "vs @ [v]"]) (simp add: list_all2_appendI)
    qed
    then obtain U' us' where u: "X' = list_comb (Const c U') us'"
      "list_all2 (\<lambda>u u'. ok (norm_term2 env u) u') us us'" by blast
    from u(2) have "list_all2 (\<lambda>u u'. ok (norm_term env u) u') us us'" by (rule list_all2_mono) (rule nt)
    with u(1) show ?thesis by blast
  qed
qed


subsection \<open>Correctness of the composition\<close>

theorem zbicompose_proof_valid:
  assumes ok: "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
      (smax, stpairs, list_implies (Bs @ [Bi]) C) (stpairs, Bs, Bi, C) lifted eres_flg
      (rmax, rtpairs, rprop) nsubgoal) s"
    and res: "bresult (unify_ops cfg vl) s r"
    and cfg: "cfg_alg cfg = alg" and finA: "finite A"
    and state: "wt_thm ar A W smax stpairs (list_implies (Bs @ [Bi]) C)" "ibelow smax (list_implies (Bs @ [Bi]) C)"
    and rule: "wt_thm ar A W rmax rtpairs rprop" "lifted \<Longrightarrow> lifted_over smax Bi rprop nsubgoal"
    and A: "scons A" "\<forall>p\<in>A. snd (fst p) \<le> max rmax smax" "\<forall>x. tyA ar A (W x)"
    and ns: "0 \<le> nsubgoal" "nsubgoal \<le> count_prems rprop" and er: "eres_flg \<Longrightarrow> 0 < nsubgoal"
    and fl: "eres_flg \<Longrightarrow> flatten \<Longrightarrow> lifted"
    and vl: "\<And>xs. length (vl xs) = length xs"
    and cA: "tcert alg A" and lo: "-1 \<le> smax" and A0: "\<forall>p\<in>A. 0 \<le> snd (fst p)"
    and nn: "\<forall>x\<in>vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop. 0 \<le> snd x"
    and sv: "prf_valid alg ar W H stpairs (zprf_tr sprf) (list_implies (Bs @ [Bi]) C)"
    and rv: "prf_valid alg ar W H rtpairs (zprf_tr rprf) rprop"
    and sz: "zinv A W smax sprf" and rz: "zinv A W rmax rprf"
    and vS: "ok (full_prop_of stpairs (list_implies (Bs @ [Bi]) C)) vS"
    and vR: "ok (full_prop_of rtpairs rprop) vR"
    and ze: "zenv_ok (br_env r)"
    and hid: "\<forall>x\<in>prf_vars (zprf_tr rprf) - vars_thm rtpairs rprop. ren_of (br_newas r) smax x = x \<and>
      x \<notin> ren_of (br_newas r) smax ` vars_thm rtpairs rprop"
  shows "\<exists>p. (case na_ren (br_newas r) of None \<Rightarrow> returnZ rprf | Some rr \<Rightarrow> zren_proof rr smax rprf) \<bind>
      (\<lambda>rp. zbicompose_proof ztargs (br_env r) smax flatten Bs (na_As (br_newas r)) (br_A r)
        (na_oldAs (br_newas r)) (na_n (br_newas r))
        (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf) = returnZ p \<and>
    zthm_prf_inv (maxidx (br_env r)) (br_tpairs r) (br_prop r) H p"
proof -
  let ?S = "list_implies (Bs @ [Bi]) C" and ?m = "max rmax smax"
  define nlift where "nlift = count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0)"
  have A2: "\<forall>p\<in>A. snd (fst p) \<le> ?m" using A(2) by blast
  from strip_prems_ok[OF ns] obtain rAsB where "ok (strip_prems nsubgoal [] rprop) rAsB" by blast
  then obtain rAs B where sp1: "ok (strip_prems nsubgoal [] rprop) (rAs, B)" by (cases rAsB) auto
  have P: "rprop = list_implies (rev rAs) B"
    by (rule list_implies_strip_prems[OF sp1]) (use rule(1) in \<open>simp add: wt_thm_def\<close>)
  have wS: "\<forall>X\<in>set Bs. wt_term ar A W smax X propT" "wt_term ar A W smax Bi propT"
    "wt_term ar A W smax C propT"
    using wt_term_list_implies[of ar A W smax "Bs @ [Bi]" C] state(1) by (auto simp: wt_thm_def)
  have wR: "\<forall>X\<in>set (rev rAs). wt_term ar A W rmax X propT" "wt_term ar A W rmax B propT"
    using wt_term_list_implies[of ar A W rmax "rev rAs" B] rule(1) P by (auto simp: wt_thm_def)
  text \<open>Further terms that keep their types in the unifier: the subgoal, the conclusion of the rule
    and the flex-flex pairs.\<close>
  define tpT where "tpT m t u = (SOME T. wt_term ar A W m t T \<and> wt_term ar A W m u T)" for m t u
  have tpS: "wt_term ar A W smax t (tpT smax t u) \<and> wt_term ar A W smax u (tpT smax t u)"
    if "(t, u) \<in> set stpairs" for t u
    unfolding tpT_def by (rule someI_ex) (use state(1) that in \<open>auto simp: wt_thm_def\<close>)
  have tpR: "wt_term ar A W rmax t (tpT rmax t u) \<and> wt_term ar A W rmax u (tpT rmax t u)"
    if "(t, u) \<in> set rtpairs" for t u
    unfolding tpT_def by (rule someI_ex) (use rule(1) that in \<open>auto simp: wt_thm_def\<close>)
  define xsS where "xsS = (Bi, propT) # concat (map (\<lambda>(t, u). [(t, tpT smax t u), (u, tpT smax t u)]) stpairs)"
  define xsR where "xsR = (B, propT) # map (\<lambda>X. (X, propT)) (rev rAs) @
    concat (map (\<lambda>(t, u). [(t, tpT rmax t u), (u, tpT rmax t u)]) rtpairs)"
  have xsS': "\<forall>(X, T)\<in>set xsS. wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S"
    using wS(2) tpS by (fastforce simp: xsS_def vars_thm_def vars_list_implies)
  have xsR': "\<forall>(X, T)\<in>set xsR. wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop"
    using wR tpR by (fastforce simp: xsR_def vars_thm_def vars_list_implies P)
  have xs: "\<forall>(X, T)\<in>set (xsS @ xsR). (wt_term ar A W smax X T \<and> vars X \<subseteq> vars_thm stpairs ?S) \<or>
      (wt_term ar A W rmax X T \<and> vars X \<subseteq> vars_thm rtpairs rprop)"
    using xsS' xsR' by fastforce
  text \<open>The call of the body.\<close>
  have "\<exists>rAs B env s' W0. ok (strip_prems nsubgoal [] rprop) (rAs, B) \<and> env = empty_env ?m \<and>
      okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s' \<and>
      okT (bicompose_body (unify_ops cfg vl)
        (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B))
        env eres_flg rAs) s' \<and>
      pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B) W0 \<and>
      results_typed (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B)
        (xsS @ xsR)"
    by (rule bicompose_aux_call[where incremented=True, OF cfg finA state rule A(1) A2 A(3) A(3) cA _ ns er fl vl xs])
      blast+
  then obtain rAs' B' env s' W0 where sp1': "ok (strip_prems nsubgoal [] rprop) (rAs', B')"
    and e1: "env = empty_env ?m"
    and ok': "okT (bicompose_aux (unify_ops cfg vl) alg flatten match_flg True
        (smax, stpairs, ?S) (stpairs, Bs, Bi, C) lifted eres_flg (rmax, rtpairs, rprop) nsubgoal) s'"
    and body: "okT (bicompose_body (unify_ops cfg vl)
        (bs_ctx (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B'))
        env eres_flg rAs') s'"
    and pa: "pinv_allW (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B') W0"
    and rty: "results_typed (call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs' B')
        (xsS @ xsR)"
    by blast
  from sp1 sp1' have rAsB: "rAs' = rAs" "B' = B" by simp_all
  note body = body[unfolded rAsB] and pa = pa[unfolded rAsB] and rty = rty[unfolded rAsB]
  define sp where "sp = call_spec cfg A vl env flatten match_flg smax stpairs Bs Bi C lifted eres_flg rtpairs rAs B"
  note pa = pa[folded sp_def] and rty = rty[folded sp_def] and body = body[folded sp_def]
  have sel: "bs_cfg sp = cfg" "bs_vl sp = vl" "bs_A sp = A" "bs_env sp = env" "bs_eres sp = eres_flg"
    "bs_rAs sp = rAs" "bc_smax (bs_ctx sp) = smax" "bc_Bs (bs_ctx sp) = Bs" "bc_C (bs_ctx sp) = C"
    "bc_Bi (bs_ctx sp) = Bi" "bc_lifted (bs_ctx sp) = lifted" "bc_flatten (bs_ctx sp) = flatten"
    "bc_nlift (bs_ctx sp) = nlift" "bc_rtpairs (bs_ctx sp) = rtpairs"
    by (simp_all add: sp_def call_spec_def Let_def nlift_def)
  have ss: "s' = s" using okT_det[OF ok' ok] .
  have te: "vt_is_empty (tenv env)" "vt_is_empty (tyenv env)" by (simp_all add: e1 empty_env_def)
  have mx: "maxidx env = ?m" by (simp add: e1)
  have pal: "pinv_all sp" by (rule pinv_allW_pinv_all[OF pa])
  have bi: "binv sp s"
    by (rule bicompose_body_binv) (use body ss cfg finA pal in \<open>simp_all add: sel\<close>)
  have "rchar sp r"
    by (rule bresult_rchar) (use res bi cfg finA pal in \<open>simp_all add: sel\<close>)
  then obtain A1o na tus env' tps where its: "itsok sp A1o na tus"
    and pu: "punifier env (dps_of tus) env' tps" and pr: "prres alg ar A env' tps"
    and ue: "uelem alg cfg env tus (El_R env' tps)" and ad: "okT (addth (bs_ctx sp) A1o na (env', tps)) r"
    by (auto simp: rchar_def sel)
  from rty[unfolded results_typed_def sel, rule_format, OF its[unfolded sel] ue]
  obtain W' e0 W'' where pi': "pinv alg ar A W' env' []" and tp: "\<forall>ab\<in>set tps. ptpok ar A W' env' e0 ab"
    and BC: "\<forall>X\<in>insert C (set Bs). wtprop A W' env' X"
    and pi'': "pinv alg ar A W'' env' []" and As: "\<forall>X\<in>set (na_As na). wtprop A W'' env' X"
    and W''d: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> lifted \<and> smax < snd v \<and> snd v \<le> maxidx env \<and>
      (\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u)"
    and sk1: "lifted \<longrightarrow> 0 \<le> nlift \<and> (\<forall>X\<in>set (na_As na). nlift \<le> ilength (spine_hyps X))"
    and nA: "\<exists>As0 n dps tps1. okT (newAs vl (bs_ctx sp) As0 n dps tps1) na \<and> set As0 \<subseteq> set (rev rAs) \<and>
      (\<forall>X\<in>set As0. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x) \<and>
      As0 = (if eres_flg then tl (rev rAs) else rev rAs)"
    and sk2: "lifted \<longrightarrow> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H)"
    and rsx: "rs_typed ar A (xsS @ xsR) W' env'"
    by blast
  text \<open>The problem, as in the soundness theorem \<open>rchar_valid\<close>.\<close>
  define BBi where "BBi = (if lifted then strip_assums2 B Bi else (B, Bi))"
  define ctx where "ctx = BCtx flatten match_flg lifted smax Bs Bi C rtpairs nlift BBi (BBi # rtpairs @ stpairs)"
  have sp': "sp = BSpec cfg A vl env ctx rAs eres_flg"
    unfolding sp_def by (simp add: call_spec_def Let_def nlift_def BBi_def ctx_def)
  have ctx_sel: "bc_flatten ctx = flatten" "bc_lifted ctx = lifted" "bc_smax ctx = smax" "bc_Bs ctx = Bs"
    "bc_Bi ctx = Bi" "bc_C ctx = C" "bc_rtpairs ctx = rtpairs" "bc_nlift ctx = nlift" "bc_BBi ctx = BBi"
    "bc_dpairs ctx = BBi # rtpairs @ stpairs" "bc_match ctx = match_flg"
    by (simp_all add: ctx_def)
  have sp_sel: "bs_eres sp = eres_flg" "bs_ctx sp = ctx" "bs_vl sp = vl" "bs_rAs sp = rAs" "bs_env sp = env"
    "bs_A sp = A"
    by (simp_all add: sp')
  obtain Pre As0 n dps tps1 where
    rAs': "rev rAs = Pre @ As0" and na: "okT (newAs vl ctx As0 n dps tps1) na"
    and dps: "BBi \<in> set dps"
    and tus: "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
    and n: "0 \<le> n" "n \<le> count_prems (strip_all_body Bi)"
      "nlift + (if 0 < n \<and> flatten then 1 else 0) \<le> count_prems (strip_all_body Bi)" "0 \<le> nlift"
    and A1o: "A1o = (case Pre of [] \<Rightarrow> None | A1 # _ \<Rightarrow> Some A1)" and Pn: "Pre = [] \<longleftrightarrow> \<not> 0 < n"
    and Pe: "Pre = [] \<longleftrightarrow> \<not> eres_flg"
    and pre: "\<And>A1. A1 \<in> set Pre \<Longrightarrow> \<exists>params asms concl. eres_flg \<and> Pre = [A1] \<and>
      assum_problems (nlift + 1) A1 = (params, asms, concl) \<and> 1 \<le> n \<and> n \<le> integer_of_nat (length asms) \<and>
      (rlist_abs params concl, rlist_abs params (asms ! (nat_of_integer n - 1))) \<in> set dps \<and>
      (rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
  proof -
    from its consider (res) tps1 where "\<not> eres_flg" "A1o = None" "tus = BBi # rtpairs @ stpairs"
        "okT (newAs vl ctx (rev rAs) 0 [BBi] tps1) na"
      | (eres) n asm tps1 where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
        "A1o = Some (er_A1 (eres_of sp))"
        "okT (newAs vl ctx (er_As (eres_of sp)) n
          [BBi, (er_concl' (eres_of sp), rlist_abs (er_params (eres_of sp)) asm)] tps1) na"
      using its unfolding itsok_def sp_sel ctx_sel by blast
    then show thesis
    proof cases
      case res
      have "0 \<le> count_prems (strip_all_body Bi)" by (rule count_prems_nonneg)
      with res show thesis
        by (intro that[of "[]" "rev rAs" 0 "[BBi]" tps1]) (simp_all add: nlift_def)
    next
      case eres
      have n1: "1 \<le> nat_of_integer n" using eres(2) by (simp add: integer_reps)
      obtain A1 As where rA: "rev rAs = A1 # As"
        using eres(3) n1 by (cases "rev rAs") (auto simp: asms_of_def sp')
      obtain params asms concl where ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)"
        by (cases "assum_problems (nlift + 1) A1")
      have er: "eres_of sp = ER env params concl (rlist_abs params concl) A1 As" "asms_of sp = asms"
        using rA ap by (simp_all add: eres_of_def asms_of_def sp' ctx_sel)
      have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using eres(1) by (simp add: nlift_def)
      have "ilength asms \<le> nlift + 1"
        by (rule assum_problems_length[OF ap]) (use cnt count_prems_nonneg in simp)
      moreover have nl: "n \<le> ilength asms" using eres(2,3) er(2)
        by (simp add: ilength_eq integer_reps integer_of_nat.rep_eq)
      ultimately have nle: "n \<le> nlift + 1" by simp
      show thesis
      proof (rule that[of "[A1]" As n "[BBi, (rlist_abs params concl, rlist_abs params asm)]" tps1])
        show "okT (newAs vl ctx As n [BBi, (rlist_abs params concl, rlist_abs params asm)] tps1) na"
          using eres(7) er by simp
        show "set (BBi # rtpairs @ stpairs) \<subseteq> set tus"
          using eres(5) er by (auto simp: eres_prob_def sp' ctx_sel)
        show "A1o = (case [A1] of [] \<Rightarrow> None | A1 # _ \<Rightarrow> Some A1)" using eres(6) er by simp
        show "\<exists>params' asms' concl'. eres_flg \<and> [A1] = [A1'] \<and>
            assum_problems (nlift + 1) A1' = (params', asms', concl') \<and> 1 \<le> n \<and>
            n \<le> integer_of_nat (length asms') \<and>
            (rlist_abs params' concl', rlist_abs params' (asms' ! (nat_of_integer n - 1))) \<in>
              set [BBi, (rlist_abs params concl, rlist_abs params asm)] \<and>
            (rlist_abs params' (asms' ! (nat_of_integer n - 1)), rlist_abs params' concl') \<in> set tus"
          if "A1' \<in> set [A1]" for A1'
          using that eres(1,2,4,5) ap er nl by (auto simp: eres_prob_def ilength_eq)
      qed (use rA eres(1,2) nle cnt in auto)
    qed
  qed
  have nnn: "na_n na = n" by (rule newAs_na_ren(2)[OF na])
  have flat: "list_all2 (\<lambda>A1 A'. if flatten then ok (flatten_params vl n A1) A' else A1 = A') (na_oldAs na) (na_As na)"
    using newAs_cases(1)[OF na] by (simp add: ctx_sel)
  have renc: "(na_ren na = None \<and> na_oldAs na = As0) \<or> (lifted \<and>
      na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0) \<and>
      na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0)"
    using newAs_na_ren(1)[OF na] by (simp add: ctx_sel)
  have As0eq: "As0 = (if eres_flg then tl (rev rAs) else rev rAs)"
    using rAs' Pe pre by (cases Pre) auto
  from nA obtain As0' n' dps' tps1' where "As0' = (if eres_flg then tl (rev rAs) else rev rAs)"
    and "\<forall>X\<in>set As0'. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x"
    by blast
  with As0eq have rnt: "\<forall>X\<in>set As0. \<forall>x\<in>vars X. tctx env' W'' (ren_of na smax x) = tctx env' W' x"
    by simp
  text \<open>The proof is computed without warnings or exceptions.\<close>
  have pe: "penv_inv alg ar W'' env'" by (rule pinvD(1)[OF pi''])
  have swf: "swf_env ar env'" by (rule penv_inv_swf_env[OF pe])
  have tiE: "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi'])
  note acE = tinv_tacyc[OF tiE] and tcE = tinv_tcons_env[OF tiE]
  have etE: "\<forall>U\<in>etys env'. tcons (tyenv env') U" using pinvD(3)[OF pi'] tyw_tcons[OF tiE] by blast
  have tcA: "tcons (tyenv env') U" if "tvars U \<subseteq> A" for U using that tinv_tcons[OF tiE] by blast
  text \<open>The renamed tight proof of the rule.\<close>
  have rzc: "zconst_free rprf" using rz by (simp add: zinv_def)
  obtain rp' where rp': "(case na_ren na of None \<Rightarrow> returnZ rprf | Some rr \<Rightarrow> zren_proof rr smax rprf) = returnZ rp'"
    and rp'z: "zconst_free rp'"
    and rp'i: "\<And>\<rho> \<theta> lev. prf_inst \<rho> \<theta> lev (zprf_tr rp') = prf_inst \<rho> (\<theta> \<circ> ren_of na smax) lev (zprf_tr rprf)"
    and rp'v: "prf_vars (zprf_tr rp') = ren_of na smax ` prf_vars (zprf_tr rprf)"
  proof (cases "na_ren na")
    case None
    have "ren_of na smax = id" using None by (intro ext) (simp add: ren_of_def)
    with None rzc show thesis by (intro that[of rprf]) (simp_all add: comp_def)
  next
    case (Some rr)
    from zren_proof_inst[OF rzc lo, of rr] obtain p' where
      "zren_proof rr smax rprf = returnZ p'" "zconst_free p'"
      "\<forall>\<rho> \<theta> lev. prf_inst \<rho> \<theta> lev (zprf_tr p') = prf_inst \<rho> (\<theta> \<circ> zrnf rr smax) lev (zprf_tr rprf)"
      "prf_vars (zprf_tr p') = zrnf rr smax ` prf_vars (zprf_tr rprf)"
      by blast
    with Some show thesis by (intro that[of p']) (simp_all add: ren_of_zrnf[OF Some])
  qed
  have "br_env r = env' \<and> br_A r = A1o \<and> br_newas r = na" using ad by (cases rule: addth_cases) auto
  then have rbr: "br_env r = env'" "br_A r = A1o" "br_newas r = na" by simp_all
  have lold: "length (na_oldAs na) = length (na_As na)" using list_all2_lengthD[OF flat] .
  have A1oN: "A1o = None \<Longrightarrow> \<not> 0 < na_n na" using A1o Pn nnn by (cases Pre) auto
  text \<open>The tight proof is computed without exceptions; its parts.\<close>
  define la where "la = length (na_As na)"
  define fpk where "fpk k = (if flatten then flatten_params_proof_a 0 0 (na_n na) (na_oldAs na ! k, integer_of_nat (la - 1 - k))
    else PBound (integer_of_nat (la - 1 - k)))" for k
  obtain p Ns asm fs sp'' rp'' where
    bp: "zbicompose_proof ztargs env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) [vS, vR]
      rp' sprf = returnZ p"
    and pe: "p = ZAbsps Ns (ZAppp (ZAppps sp'' (map ZBoundp (downto (integer_of_nat (length Bs) + integer_of_nat la - 1)
      (integer_of_nat la)))) (ZAppps rp'' (asm @ fs)))"
    and Ns: "list_all2 (\<lambda>X N. ok (norm_term env' X) (zdec N)) (Bs @ na_As na) Ns"
    and sp'': "sp'' = sprf \<and> (env_is_empty env' \<or> above env' smax) \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sp'')"
    and rp'': "rp'' = rp' \<and> env_is_empty env' \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr rp') (zprf_tr rp'')"
    and asm: "(A1o = None \<or> \<not> 0 < na_n na) \<and> asm = [] \<or>
      (\<exists>A1 C'. A1o = Some A1 \<and> 0 < na_n na \<and> ok (norm_term env' A1) (zdec C') \<and> zcanon C' \<and>
        asm = [zmk_asm_prf C' (na_n na) (nlift + 1)])"
    and fs: "length fs = la" "\<forall>k<la. zprf_tr (fs ! k) = fpk k \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (fpk k) (zprf_tr (fs ! k))"
    sorry
  text \<open>The new theorem is typed by \<open>tctx env' W''\<close> and its variables have non-negative indices.\<close>
  have pi: "pinv alg ar A W0 env (dps_of tus)"
  proof -
    from its consider (res) "\<not> eres_flg" "tus = bc_dpairs (bs_ctx sp)"
      | (eres) n asm where "eres_flg" "1 \<le> n" "nat_of_integer n \<le> length (asms_of sp)"
        "asm = asms_of sp ! (nat_of_integer n - 1)" "tus = eres_prob sp asm"
      unfolding itsok_def sel by blast
    then show ?thesis
    proof cases
      case res
      with pa show ?thesis by (simp add: pinv_allW_def sel)
    next
      case eres
      then have "asm \<in> set (asms_of sp)" by (simp add: integer_reps)
      with pa eres(1,5) show ?thesis by (simp add: pinv_allW_def sel)
    qed
  qed
  from ue obtain s0 xs0 where u0: "unifiers alg env tus = Some (Ok s0)" "evals cfg s0 xs0"
    "El_R env' tps \<in> set xs0"
    by (auto simp: uelem_def)
  have fresh: "v \<notin> fst ` bvps env' \<and> (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
    if "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u" "snd v \<le> maxidx env" for v
  proof -
    have v: "vt_lookup (tenv env) v = None" "v \<notin> fst ` bvps env"
      using te(1) by (auto simp: bvps_def vt_is_empty_lookup)
    from unifiers_fresh[OF cfg finA pi u0 v that] unifiers_fresh_tps[OF cfg finA pi u0 v that]
    show ?thesis by blast
  qed
  have imp: "tyA ar A imp_type"
    using state(1) by (auto simp: wt_thm_def wt_term_def tys_list_implies)
  have ib: "\<forall>X\<in>insert C (set Bs). ibelow smax X" using state(2) by simp
  have ag: "\<forall>v. W'' v \<noteq> W' v \<longrightarrow> bc_smax (bs_ctx sp) < snd v \<and> v \<notin> fst ` bvps env' \<and>
      (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
  proof (intro allI impI)
    fix v assume "W'' v \<noteq> W' v"
    with W''d have "smax < snd v" "snd v \<le> maxidx env" "\<forall>(t, u)\<in>set tus. v \<notin> vars t \<and> v \<notin> vars u"
      by blast+
    with fresh[of v] show "bc_smax (bs_ctx sp) < snd v \<and> v \<notin> fst ` bvps env' \<and>
        (\<forall>(t, u)\<in>set tps. v \<notin> vars t \<and> v \<notin> vars u)"
      by (simp add: sel)
  qed
  have BC': "\<forall>X\<in>insert (bc_C (bs_ctx sp)) (set (bc_Bs (bs_ctx sp))). wtprop A W' env' X \<and> ibelow (bc_smax (bs_ctx sp)) X"
    using BC ib by (simp add: sel)
  have sk: "bc_lifted (bs_ctx sp) \<Longrightarrow> 0 \<le> bc_nlift (bs_ctx sp) \<and> (\<forall>X\<in>set (na_As na).
      \<forall>H\<in>set (take (nat_of_integer (bc_nlift (bs_ctx sp))) (spine_hyps X)). ibelow (bc_smax (bs_ctx sp)) H)"
    using sk1 sk2 by (simp add: sel)
  have imp': "tyA ar (tvars_env (tyenv env') \<union> A) imp_type" using tyA_mono[OF imp] by blast
  note at = addth_typed[OF ad pi' tp BC' pi'' As sk ag imp']
  have wtr: "wt_thm ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') (br_tpairs r) (br_prop r)"
    by (rule at(1))
  have tyr: "thm_typeds ar 0 (UNIV \<union> env_sorts (tyenv (br_env r)))
      \<lparr>th_maxidx = maxidx (br_env r), th_tpairs = br_tpairs r, th_prop = br_prop r\<rparr>"
    by (rule bicompose_aux_thm_typed(1)[OF ok res cfg finA state rule A(1) _ A(3) ns er fl vl _ lo _ _ cA])
      (use A(2) A0 nn in auto)
  have nnr: "\<forall>x\<in>vars_thm (br_tpairs r) (br_prop r). 0 \<le> snd x" using tyr by (simp add: thm_typeds_def)
  have wtyr: "wty (tctx env' W'') [] X T" if "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') X T"
    "vars X \<subseteq> vars_thm (br_tpairs r) (br_prop r)" for X T
    using that nnr by (auto simp: wty_def wt_term_def)
  text \<open>The hidden variables: variables of the proofs that do not occur in the theorems.\<close>
  define OH where "OH = (prf_vars (zprf_tr sprf) \<union> prf_vars (zprf_tr rprf)) -
    (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
  have OHf: "vt_lookup (tenv env') x = None \<and> x \<notin> fst ` bvps env' \<and> (\<forall>(t, u)\<in>set tps. x \<notin> vars t \<and> x \<notin> vars u) \<and>
      0 \<le> snd x" if "x \<in> OH" for x
    sorry
  define W3 where "W3 x = (if x \<in> OH then W x else W'' x)" for x
  have W3x: "W3 x = W'' x" if "x \<notin> OH" for x using that by (simp add: W3_def)
  have pi3: "pinv alg ar A W3 env' []"
  proof (rule pinv_retype[OF pi''], intro allI impI)
    fix x assume "W3 x \<noteq> W'' x"
    then have x: "x \<in> OH" "W3 x = W x" by (auto simp: W3_def split: if_splits)
    have "tyw ar (tyenv env') A (W x)" using tyA_tyw[OF pinvD(2)[OF pi''] spec[OF A(3), of x]] .
    with OHf[OF x(1)] x(2) show "vt_lookup (tenv env') x = None \<and> x \<notin> fst ` bvps env' \<and> tyw ar (tyenv env') A (W3 x)"
      by simp
  qed
  have pvld: "prf_valid alg ar (tctx env' W3) H (br_tpairs r) (zprf_tr p) (br_prop r)"
    unfolding prf_valid_def
  proof (intro allI impI)
    fix V' \<rho> \<theta>
    assume g: "ginst alg ar \<rho>" and ty: "inst_typed (tctx env' W3) V' [] \<rho> \<theta>"
      and sol: "\<forall>(t, u)\<in>set (br_tpairs r). tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
    text \<open>An instance of all variables, and its extension through the unifier.\<close>
    define \<theta>0 where "\<theta>0 x = (if 0 \<le> snd x then \<theta> x else Free STR ''u'' (tsubst \<rho> (tctx env' W3 x)))" for x
    have ty0x: "wty V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W3 x))" for x
    proof (cases "0 \<le> snd x")
      case True
      then show ?thesis using inst_typedD[OF ty True] by (simp add: \<theta>0_def)
    next
      case False
      then show ?thesis by (simp add: \<theta>0_def wty_def has_type.Free)
    qed
    have ty0: "\<forall>x. wty V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W3 x))" using ty0x by blast
    have cl0x: "proper (\<theta>0 x)" "\<not> loose_bvar (\<theta>0 x) 0" for x
    proof -
      have h: "has_type V' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W3 x))" using ty0x[of x] by (simp add: wty_def)
      show "proper (\<theta>0 x)" by (rule has_type_proper[OF h])
      show "\<not> loose_bvar (\<theta>0 x) 0" using has_type_loose_bvar[OF h] by simp
    qed
    have cl0: "\<forall>x. proper (\<theta>0 x) \<and> \<not> loose_bvar (\<theta>0 x) 0" using cl0x by blast
    obtain \<rho>' \<sigma>' \<theta>' where ie: "iext env' \<rho> (isubst \<theta>0) \<rho>' \<sigma>'" and g': "ginst alg ar \<rho>'"
      and cl': "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0"
      and unb\<theta>: "\<And>x. vt_lookup (tenv env') x = None \<Longrightarrow> \<theta>' x = \<theta>0 x"
      and tyc: "\<And>T. tcons (tyenv env') T \<Longrightarrow> tsubst \<rho> (tnorm (tyenv env') T) = tsubst \<rho>' T"
      and smeq: "\<And>t. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t)"
      and tyb: "\<And>V''. \<forall>x. wty V'' [] (\<theta>0 x) (tsubst \<rho> (tctx env' W3 x)) \<Longrightarrow>
        \<forall>x. wty V'' [] (\<theta>' x) (tsubst \<rho>' (W3 x))"
      by (rule inst_bridge[OF pi3 g cl0]) blast
    have tyall': "\<forall>x. wty V' [] (\<theta>' x) (tsubst \<rho>' (W3 x))" by (rule tyb[OF ty0])
    then have ty': "inst_typed W3 V' [] \<rho>' \<theta>'" by (simp add: inst_typed_def)
    from ie have gs': "gsol alg ar (tyenv env') \<rho>'" and ps: "psat (\<sigma>' \<circ> cren \<rho>') env'"
      and agT: "\<And>v S. vt_lookup (tyenv env') v = None \<Longrightarrow> \<rho>' v S = \<rho> v S"
      unfolding iext_def by blast+
    have cl'x: "proper (\<theta>' x)" "\<not> loose_bvar (\<theta>' x) 0" for x using cl' by blast+
    have eq0: "psubst \<rho> \<theta>0 l t = psubst \<rho> \<theta> l t" if "\<forall>x\<in>vars t. 0 \<le> snd x" for l t
      by (rule psubst_cong) (use that in \<open>simp add: \<theta>0_def\<close>)
    have tr0: "tr (psubst \<rho> \<theta>0 0 t) = sm \<rho> (isubst \<theta>0) t" for t
      by (rule tr_psubst_sm) (use cl0x in blast)
    have tr': "tr (psubst \<rho>' \<theta>' 0 t) = sm \<rho>' (isubst \<theta>') t" for t
      by (rule tr_psubst_sm) (use cl'x in blast)
    text \<open>The flex-flex pairs of the unifier and the problem are solved.\<close>
    have sol0: "\<forall>(t, u)\<in>set (br_tpairs r). sm \<rho> (isubst \<theta>0) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> (isubst \<theta>0) u"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set (br_tpairs r)"
      have v: "\<forall>x\<in>vars t. 0 \<le> snd x" "\<forall>x\<in>vars u. 0 \<le> snd x" using nnr tu by (auto simp: vars_thm_def)
      have "tr (psubst \<rho> \<theta>0 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 u)" using sol tu eq0[OF v(1)] eq0[OF v(2)] by auto
      then show "sm \<rho> (isubst \<theta>0) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho> (isubst \<theta>0) u" by (simp add: tr0)
    qed
    have tps_wf: "\<forall>(t, u)\<in>set tps. swf_tm ar [] t \<and> swf_tm ar [] u" using tp ptpok_swf by fast
    have tsol: "\<forall>(t, u)\<in>set tps. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u"
      by (rule addth_tpairs[OF ad ie rigid_isubst swf tps_wf]) (use sol0 in auto)
    have dsol: "sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" if "(t, u) \<in> set tus" for t u
    proof -
      have "\<forall>(t, u)\<in>set tps. mk_subst (\<sigma>' \<circ> cren \<rho>') (tr t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (\<sigma>' \<circ> cren \<rho>') (tr u)"
        using tsol by (simp add: sm_def mk_subst_inst)
      with pu ps have "dsolved_all (\<sigma>' \<circ> cren \<rho>') (dps_of tus)" by (auto simp: punifier_def)
      with that have "dsolved (\<sigma>' \<circ> cren \<rho>') ([], t, u)" by fastforce
      then show ?thesis by (simp add: dsolved_Nil unifies_def sm_def mk_subst_inst)
    qed
    have dsol': "tr (psubst \<rho>' \<theta>' 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 u)" if "(t, u) \<in> set tus" for t u
    proof -
      have "tr (psubst \<rho>' \<theta>' 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t" by (rule equiv_sym[OF smeq])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' u" by (rule dsol[OF that])
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 u)" by (rule smeq)
      finally show ?thesis .
    qed
    have tcW: "tcons (tyenv env') (W x)" for x
    proof -
      have "tyA ar A (W x)" using A(3) by blast
      then show ?thesis using tcA by (simp add: tyA_def)
    qed
    have rs: "typed env' W' [] X T" if "(X, T) \<in> set (xsS @ xsR)" for X T
      using rsx that by (auto simp: rs_typed_def)
    text \<open>The instance of the proof state.\<close>
    define RS where "RS = vars_thm stpairs (list_implies (Bs @ [Bi]) C)"
    have RSs: "snd x \<le> smax" if "x \<in> RS" for x
      using that state(1,2) by (fastforce simp: RS_def vars_thm_def ibelow_def wt_thm_def wt_term_def below_def)
    have agS: "0 \<le> snd (id x) \<and> tctx env' W3 (id x) = tnorm (tyenv env') (W x)" if "x \<in> RS" "0 \<le> snd x" for x
    proof -
      have "W'' x = W' x" using W''d RSs[OF that(1)] by fastforce
      then have e: "tctx env' W3 x = tctx env' W' x" by (simp add: vtyp_def split: option.splits)
      have "\<exists>X T U. x \<in> vars X \<and> typed env' W' [] X T \<and> has_type W [] X U"
      proof -
        from that(1) consider X where "X \<in> insert C (set Bs)" "x \<in> vars X" | "x \<in> vars Bi"
          | t u where "(t, u) \<in> set stpairs" "x \<in> vars t \<or> x \<in> vars u"
          by (auto simp: RS_def vars_thm_def vars_list_implies)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using BC wS by (fastforce simp: wtprop_def wt_term_def)
        next
          case 2
          then show ?thesis using rs[of Bi propT] wS(2) by (fastforce simp: xsS_def wt_term_def)
        next
          case 3
          then show ?thesis using rs[of t "tpT smax t u"] rs[of u "tpT smax t u"] tpS[OF 3(1)]
            by (fastforce simp: xsS_def wt_term_def)
        qed
      qed
      then obtain X T U where "x \<in> vars X" "typed env' W' [] X T" "has_type W [] X U" by blast
      from typed_tctx_agree[OF this(2,3,1)] e that(2) show ?thesis by simp
    qed
    define \<theta>S where "\<theta>S = (\<lambda>x. if x \<in> RS then \<theta>' (id x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyS: "inst_typed W V' [] \<rho>' \<theta>S"
      unfolding \<theta>S_def by (rule inst_typed_transfer[OF ty' pi3 gs' agS]) (simp_all add: tcW)
    have psS: "psubst \<rho>' \<theta>S l X = psubst \<rho>' \<theta>' l X" if "vars X \<subseteq> RS" for l X
      by (rule psubst_cong) (use that in \<open>auto simp: \<theta>S_def\<close>)
    have solS: "tr (psubst \<rho>' \<theta>S 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>S 0 u)" if "(t, u) \<in> set stpairs" for t u
    proof -
      have "vars t \<subseteq> RS" "vars u \<subseteq> RS" using that by (auto simp: RS_def vars_thm_def)
      moreover have "(t, u) \<in> set tus" using that tus by auto
      ultimately show ?thesis using dsol' by (simp add: psS)
    qed
    have Sok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 sprf)
        (list_implies (map (psubst \<rho>' \<theta>' 0) Bs @ [psubst \<rho>' \<theta>' 0 Bi]) (psubst \<rho>' \<theta>' 0 C))"
    proof -
      have "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>S 0 sprf) (psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C))"
        by (rule prf_validD[OF sv g' tyS solS])
      moreover have "prf_inst \<rho>' \<theta>S 0 sprf = prf_inst \<rho>' \<theta>' 0 sprf" by (rule prf_inst_cong) (simp add: sp0)
      moreover have "psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C) = psubst \<rho>' \<theta>' 0 (list_implies (Bs @ [Bi]) C)"
        by (rule psS) (auto simp: RS_def vars_thm_def)
      ultimately show ?thesis by (simp add: psubst_list_implies')
    qed
    text \<open>The instance of the rule, through the renaming of its new premises.\<close>
    define RR where "RR = vars_thm rtpairs rprop"
    define rn where "rn = ren_of na smax"
    have RRn: "0 \<le> snd x" if "x \<in> RR" for x using that nn by (auto simp: RR_def)
    have rnidx: "snd (rn x) = snd x" for x by (simp add: rn_def ren_of_def ren_ix_def split: option.splits)
    have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
      using lifted_over_lifted_rule[OF rule(2) sp1] by simp
    have rnid: "rn x = x" if "snd x \<le> smax \<or> \<not> lifted \<or> (\<exists>(t, u)\<in>set dps. fst x \<in> fst ` vars t) \<or>
        (\<exists>(t, u)\<in>set rtpairs. fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u)" for x
    proof -
      from renc consider "na_ren na = None"
        | "lifted" "na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0)" by (elim disjE conjE) auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis by (simp add: rn_def ren_of_def)
      next
        case 2
        show ?thesis
        proof (rule ccontr)
          assume "rn x \<noteq> x"
          then have sx: "smax < snd x"
            and rnn: "ren_name (fst (rename_bvs dps (rtpairs @ tps1) Bi As0)) (fst x) \<noteq> fst x"
            using 2(2) by (auto simp: rn_def ren_of_def ren_ix_def prod_eq_iff split: if_splits)
          from rename_bvs_unknowns[OF rnn]
          have a: "\<forall>(t, u)\<in>set dps. fst x \<notin> fst ` vars t"
            and b: "\<forall>(t, u)\<in>set (rtpairs @ tps1). fst x \<notin> fst ` vars t \<and> fst x \<notin> fst ` vars u" .
          from that show False
          proof (elim disjE)
            assume "snd x \<le> smax"
            with sx show False by simp
          next
            assume "\<not> lifted"
            with 2(1) show False by simp
          next
            assume "\<exists>(t, u)\<in>set dps. fst x \<in> fst ` vars t"
            with a show False by blast
          next
            assume "\<exists>(t, u)\<in>set rtpairs. fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u"
            then obtain t u where "(t, u) \<in> set rtpairs" "fst x \<in> fst ` vars t \<or> fst x \<in> fst ` vars u" by blast
            with b show False by fastforce
          qed
        qed
      qed
    qed
    have W'x: "W'' x = W' x" if "snd x \<le> smax \<or> \<not> lifted \<or> (\<exists>(t, u)\<in>set tus. x \<in> vars t \<or> x \<in> vars u)" for x
      using W''d that by fastforce
    text \<open>The variables of the rule outside its new premises are neither renamed nor retyped.\<close>
    have keep: "rn x = x \<and> W'' x = W' x"
      if "x \<in> vars B \<or> (\<exists>X\<in>set Pre. x \<in> vars X) \<or> (\<exists>(t, u)\<in>set rtpairs. x \<in> vars t \<or> x \<in> vars u)" for x
    proof (cases "snd x \<le> smax \<or> \<not> lifted")
      case True
      then show ?thesis using rnid W'x by blast
    next
      case False
      then have sx: "smax < snd x" and lf: lifted by auto
      from lr[OF lf] obtain p Bi0 As1 B0 where ls: "lsplit Bi = (p, Bi0)" and rA: "rev rAs = map (lift_pre p) As1"
        and B: "B = lift_pre p B0" by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
        by auto
      have ibBi: "ibelow smax Bi" using state(2) by simp
      have pv: "snd y \<le> smax" if "y \<in> pvars p" for y
        using that ibBi by (auto simp: Bi ibelow_def vars_lift_pre)
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)" using lf by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      from that consider "x \<in> vars B" | X where "X \<in> set Pre" "x \<in> vars X"
        | t u where "(t, u) \<in> set rtpairs" "x \<in> vars t \<or> x \<in> vars u"
        by blast
      then show ?thesis
      proof cases
        case 1
        have "x \<notin> pvars p" using pv sx by fastforce
        with 1 have "x \<in> vars B0" by (auto simp: B vars_lift_pre)
        then have "x \<in> vars (fst BBi)" by (simp add: BBi vars_abs_pre)
        moreover have "BBi \<in> set tus" using tus by auto
        ultimately show ?thesis using rnid[of x] W'x[of x] dps by (cases BBi) force
      next
        case 2
        from pre[OF 2(1)] obtain params asms concl where er: "eres_flg" "Pre = [X]"
          and ap: "assum_problems (nlift + 1) X = (params, asms, concl)" and n1: "1 \<le> n"
          and cd: "(rlist_abs params concl, rlist_abs params (asms ! (nat_of_integer n - 1))) \<in> set dps"
          and ac: "(rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
          by blast
        have cX: "cok X" using rule(1) 2(1) rAs' by (auto simp: wt_thm_def P)
        from rA rAs' er(2) obtain X1 where X: "X = lift_pre p X1" by (cases As1) auto
        have cnt: "nlift + 1 = count_prems (strip_all_body Bi)" using er(1) by (simp add: nlift_def)
        have "set asms \<subseteq> set (phyps p)"
          using assum_problems_lift_pre[OF ok at _ ap[unfolded X]] Bi cnt n(4) by simp
        then have "\<forall>A\<in>set asms. \<forall>y\<in>vars A. snd y \<le> smax" using pv vars_phyps by blast
        with vars_assum_problems[OF ap cX] 2(2) sx have "x \<in> vars concl" by fastforce
        then show ?thesis using rnid[of x] W'x[of x] cd ac by (fastforce simp: vars_rlist_abs)
      next
        case 3
        then show ?thesis using rnid[of x] W'x[of x] tus by fastforce
      qed
    qed
    have agW': "tctx env' W' x = tnorm (tyenv env') (W x)" if "x \<in> RR" for x
    proof -
      have "\<exists>X T U. x \<in> vars X \<and> typed env' W' [] X T \<and> has_type W [] X U"
      proof -
        from that consider "x \<in> vars B" | X where "X \<in> set (rev rAs)" "x \<in> vars X"
          | t u where "(t, u) \<in> set rtpairs" "x \<in> vars t \<or> x \<in> vars u"
          by (auto simp: RR_def vars_thm_def vars_list_implies P)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using rs[of B propT] wR(2) by (fastforce simp: xsR_def wt_term_def)
        next
          case 2
          then show ?thesis using rs[of X propT] wR(1) by (fastforce simp: xsR_def wt_term_def)
        next
          case 3
          then show ?thesis using rs[of t "tpT rmax t u"] rs[of u "tpT rmax t u"] tpR[OF 3(1)]
            by (fastforce simp: xsR_def wt_term_def)
        qed
      qed
      then obtain X T U where "x \<in> vars X" "typed env' W' [] X T" "has_type W [] X U" by blast
      from typed_tctx_agree[OF this(2,3,1)] show ?thesis .
    qed
    have agR: "0 \<le> snd (rn x) \<and> tctx env' W3 (rn x) = tnorm (tyenv env') (W x)" if "x \<in> RR" "0 \<le> snd x" for x
    proof -
      have "tctx env' W3 (rn x) = tctx env' W' x"
      proof (cases "\<exists>X\<in>set As0. x \<in> vars X")
        case True
        with rnt show ?thesis by (auto simp: rn_def)
      next
        case False
        with that(1) have "x \<in> vars B \<or> (\<exists>X\<in>set Pre. x \<in> vars X) \<or> (\<exists>(t, u)\<in>set rtpairs. x \<in> vars t \<or> x \<in> vars u)"
          using rAs' by (auto simp: RR_def vars_thm_def vars_list_implies P)
        from keep[OF this] show ?thesis by (simp add: vtyp_def split: option.splits)
      qed
      with agW'[OF that(1)] rnidx that(2) show ?thesis by simp
    qed
    define \<theta>R where "\<theta>R = (\<lambda>x. if x \<in> RR then \<theta>' (rn x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyR: "inst_typed W V' [] \<rho>' \<theta>R"
      unfolding \<theta>R_def by (rule inst_typed_transfer[OF ty' pi3 gs' agR]) (simp_all add: tcW)
    have psR: "psubst \<rho>' \<theta>R l X = psubst \<rho>' \<theta>' l X" if "vars X \<subseteq> RR" "\<forall>x\<in>vars X. rn x = x" for l X
      by (rule psubst_cong) (use that in \<open>auto simp: \<theta>R_def\<close>)
    have clR: "\<not> loose_bvar (\<theta>R x) 0" for x using cl'x by (simp add: \<theta>R_def)
    have solR: "tr (psubst \<rho>' \<theta>R 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 u)" if "(t, u) \<in> set rtpairs" for t u
    proof -
      have v: "vars t \<subseteq> RR" "vars u \<subseteq> RR" using that by (auto simp: RR_def vars_thm_def)
      have k: "\<forall>x\<in>vars t. rn x = x" "\<forall>x\<in>vars u. rn x = x" using that keep by blast+
      have "psubst \<rho>' \<theta>R 0 t = psubst \<rho>' \<theta>' 0 t" "psubst \<rho>' \<theta>R 0 u = psubst \<rho>' \<theta>' 0 u"
        using psR[OF v(1) k(1)] psR[OF v(2) k(2)] by simp_all
      moreover have "(t, u) \<in> set tus" using that tus by auto
      ultimately show ?thesis using dsol' by simp
    qed
    have Rok0: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>R 0 rprf) (psubst \<rho>' \<theta>R 0 rprop)"
      by (rule prf_validD[OF rv g' tyR solR])
    have ptR: "prf_inst \<rho>' \<theta>R 0 rprf = prf_inst \<rho>' \<theta>'' 0 rprf" for \<theta>'' by (rule prf_inst_cong) (simp add: rp0)
    have Rok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 rp') (psubst \<rho>' \<theta>R 0 rprop)"
    proof (cases "na_ren na")
      case None
      then show ?thesis using Rok0 ptR[of \<theta>'] by (simp add: rp'_def ren_prf_def)
    next
      case (Some rr)
      have "prf_aeq (prf_inst \<rho>' (\<theta>' \<circ> ren_ix rr) 0 rprf) (prf_inst \<rho>' \<theta>' 0 (map_proof_terms (ren_term rr) id rprf))"
      proof (rule map_proof_terms_ren_inst)
        show "\<forall>x. proper (\<theta>' x)" using cl'x by blast
        show "\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>y\<in>vars (\<theta>' x). 0 \<le> snd y)" using tyall' by (auto simp: wty_def)
        show "anns_proper rprf" by (rule anns_proper_prf_all[OF rw ann0_proper])
      qed (simp_all add: rp0)
      with Rok0 ptR[of "\<theta>' \<circ> ren_ix rr"] Some show ?thesis
        by (auto simp: rp'_def ren_prf_def intro: prf_ok_aeq)
    qed
    text \<open>The conclusion of the rule and the subgoal have equivalent instances.\<close>
    have Bkeep: "psubst \<rho>' \<theta>R 0 B = psubst \<rho>' \<theta>' 0 B"
      using keep by (intro psR) (auto simp: RR_def vars_thm_def vars_list_implies P)
    have BBi_eq: "tr (psubst \<rho>' \<theta>R 0 B) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 Bi)"
    proof (cases lifted)
      case False
      then have "BBi = (B, Bi)" by (simp add: BBi_def)
      with dsol'[of B Bi] tus Bkeep show ?thesis by auto
    next
      case True
      from lr[OF True] obtain p Bi0 B0 where ls: "lsplit Bi = (p, Bi0)" and B: "B = lift_pre p B0"
        by (auto simp: lifted_rule_def)
      from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
        by auto
      have BBi: "BBi = (abs_pre p B0, abs_pre p Bi0)"
        using True by (simp add: BBi_def B Bi strip_assums2_lift_pre[OF ok at])
      from dsol'[of "abs_pre p B0" "abs_pre p Bi0"] tus BBi
      have "sm \<rho>' (isubst \<theta>') (abs_pre p B0) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' (isubst \<theta>') (abs_pre p Bi0)" by (simp add: tr')
      from sm_lift_pre_equiv[OF this] Bkeep show ?thesis by (simp add: tr' B Bi)
    qed
    text \<open>The instance of the new theorem and its relation to the instance through the unifier.\<close>
    have wS': "\<forall>X\<in>set Bs. wfp ar X" "wfp ar C" using BC by (auto simp: wtprop_def)
    have wN: "\<forall>X\<in>set (na_As na). wfp ar X" using As by (auto simp: wtprop_def)
    have iS: "\<forall>X\<in>set Bs. ibelow smax X" "ibelow smax C" using state(2) by simp_all
    note rg = rigid_isubst[of \<theta>0] and clI = closed_isubst[OF cl0]
    obtain Hs C' where bprop: "br_prop r = list_implies Hs C'"
      and relH: "list_all2 (\<lambda>X Y. sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
      and relC: "sm \<rho> (isubst \<theta>0) C' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' C"
    proof -
      note obt = that
      have rel_unb: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Xs Xs" if "\<forall>X\<in>set Xs. wfp ar X \<and> unb env' X" for Xs
        using that by (intro list.rel_refl_strong) (simp add: inst_rel_unb[OF ie rg clI])
      have rel_norm: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Xs Ys"
        if "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y) Xs Ys" "\<forall>X\<in>set Xs. wfp ar X" for Xs Ys
      proof -
        have "list_all2 (\<lambda>X Y. ok (norm_term env' X) Y \<and> X \<in> set Xs) Xs Ys"
          using that(1) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
        then show ?thesis by (rule list_all2_mono) (use that(2) inst_rel_norm[OF ie rg clI swf] in blast)
      qed
      have unbS: "\<forall>X\<in>set Bs. unb env' X" "unb env' C" if "above env' smax"
        using iS above_unb[OF that] by auto
      have fin: "thesis" if h1: "br_prop r = list_implies Hs C'"
        and h2: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
        and h3: "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'"
        for Hs C'
      proof (rule obt[OF h1])
        show "list_all2 (\<lambda>X Y. sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X) (Bs @ na_As na) Hs"
          using h2 by (rule list_all2_mono) simp
        show "sm \<rho> (isubst \<theta>0) C' \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' C" using h3 by simp
      qed
      from ad show thesis
      proof (cases rule: addth_cases)
        case empty
        have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) (Bs @ na_As na)"
          using wS' wN unb_empty[OF empty(1)] by (intro rel_unb) auto
        moreover have "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C"
          by (rule inst_rel_unb[OF ie rg clI wS'(2) unb_empty[OF empty(1)]])
        ultimately show thesis by (rule fin[rotated]) (simp add: empty(2) sel)
      next
        case (norm ntps Hs C')
        from norm(4) consider (lifted) As' where "above env' smax" "lifted" "C' = C" "Hs = Bs @ As'"
            "list_all2 (\<lambda>X X'. okT (norm_term_skip env' nlift X) X') (na_As na) As'"
          | (above) As' where "above env' smax" "C' = C" "Hs = Bs @ As'"
            "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (na_As na) As'"
          | (all) "list_all2 (\<lambda>X X'. ok (norm_term env' X) X') (Bs @ na_As na) Hs" "ok (norm_term env' C) C'"
          unfolding sel by blast
        then have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs \<and> inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'"
        proof cases
          case lifted
          from sk1 sk2 lifted(2) have n0: "0 \<le> nlift"
            and h: "\<forall>X\<in>set (na_As na). \<forall>H\<in>set (take (nat_of_integer nlift) (spine_hyps X)). ibelow smax H"
            by auto
          have sku: "skip_unb env' nlift X" if "X \<in> set (na_As na)" for X
            by (rule skip_unb_take[OF n0]) (use h that above_unb[OF lifted(1)] in blast)
          have "list_all2 (\<lambda>X X'. okT (norm_term_skip env' nlift X) X' \<and> X \<in> set (na_As na)) (na_As na) As'"
            using lifted(5) by (induction rule: list_all2_induct) (auto elim: list_all2_mono)
          then have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (na_As na) As'"
            by (rule list_all2_mono) (use wN sku inst_rel_skip[OF ie rg clI swf] in blast)
          moreover have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Bs Bs"
            using wS' unbS[OF lifted(1)] by (intro rel_unb) auto
          ultimately show ?thesis
            using lifted inst_rel_unb[OF ie rg clI wS'(2) unbS(2)[OF lifted(1)]] by (simp add: list_all2_appendI)
        next
          case above
          have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (na_As na) As'" by (rule rel_norm[OF above(4) wN])
          moreover have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') Bs Bs"
            using wS' unbS[OF above(1)] by (intro rel_unb) auto
          ultimately show ?thesis
            using above inst_rel_unb[OF ie rg clI wS'(2) unbS(2)[OF above(1)]] by (simp add: list_all2_appendI)
        next
          case all
          have "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
            by (rule rel_norm[OF all(1)]) (use wS' wN in auto)
          with inst_rel_norm[OF ie rg clI swf wS'(2) all(2)] show ?thesis by simp
        qed
        then have rr: "list_all2 (inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>') (Bs @ na_As na) Hs"
          "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' C C'" by blast+
        show thesis by (rule fin[OF _ rr]) (simp add: norm(2))
      qed
    qed
    define Ns where "Ns = map (psubst \<rho> \<theta>0 0) Hs"
    have lHs: "length Hs = length Bs + length (na_As na)" using list_all2_lengthD[OF relH] by simp
    have rel_tr: "tr (psubst \<rho> \<theta>0 0 Y) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 X)"
      if "sm \<rho> (isubst \<theta>0) Y \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X" for X Y
    proof -
      have "tr (psubst \<rho> \<theta>0 0 Y) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' X" using that by (simp add: tr0)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 X)" by (rule smeq)
      finally show ?thesis .
    qed
    have relN: "tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 ((Bs @ na_As na) ! j))" if "j < length Hs" for j
      using rel_tr list_all2_nthD2[OF relH that] that by (simp add: Ns_def)
    text \<open>Typing of the instance of the new theorem.\<close>
    have tyr0: "inst_typed (tctx env' W3) V' [] \<rho> \<theta>0" using ty0 by (simp add: inst_typed_def)
    have wtP: "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' W3) (maxidx env') (br_prop r) propT"
      using wtr by (simp add: wt_thm_def)
    have "wty (tctx env' W3) [] (br_prop r) propT" by (rule wtyr[OF wtP]) (simp add: vars_thm_def)
    from wty_psubst[OF this tyr0] have wtyP: "wty V' [] (psubst \<rho> \<theta>0 0 (br_prop r)) propT" by simp
    have wtyN: "\<forall>N\<in>set Ns. wty V' [] N propT" "wty V' [] (psubst \<rho> \<theta>0 0 C') propT"
      using wty_list_implies[OF wtyP[unfolded bprop psubst_list_implies']] by (auto simp: Ns_def)
    have wtyR: "wty V' [] (psubst \<rho>' \<theta>R 0 X) propT" if "X \<in> set (rev rAs)" for X
    proof -
      have "wty W [] X propT"
        using wR(1) that nn by (auto simp: wty_def wt_term_def vars_thm_def vars_list_implies P)
      from wty_psubst[OF this tyR] show ?thesis by simp
    qed
    have cokR: "cok X" if "X \<in> set (rev rAs)" for X using rule(1) that by (auto simp: wt_thm_def P)
    text \<open>The premise of the rule proved by an assumption.\<close>
    have pre_ok: "(map (psubst \<rho>' \<theta>R 0) Pre = [] \<and> \<not> 0 < na_n na) \<or>
      (\<exists>A1 iA1. map (psubst \<rho>' \<theta>R 0) Pre = [iA1] \<and> 0 < na_n na \<and> A1o = Some A1 \<and>
        prf_ok V' H [] (rev Ns) (mk_asm_prf A1 (na_n na) (nlift + 1)) iA1)"
    proof (cases Pre)
      case Nil
      then show ?thesis using Pn nnn by simp
    next
      case (Cons A1 Pre')
      then have A1: "A1 \<in> set Pre" by simp
      from pre[OF A1] obtain params asms concl where er: "eres_flg" "Pre = [A1]"
        and ap: "assum_problems (nlift + 1) A1 = (params, asms, concl)" and n1: "1 \<le> n" "n \<le> integer_of_nat (length asms)"
        and ac: "(rlist_abs params (asms ! (nat_of_integer n - 1)), rlist_abs params concl) \<in> set tus"
        by blast
      have A1r: "A1 \<in> set (rev rAs)" using rAs' er(2) by simp
      have vA1: "vars A1 \<subseteq> RR" using A1r by (auto simp: RR_def vars_thm_def vars_list_implies P)
      have kA1: "\<forall>x\<in>vars A1. rn x = x" using keep A1 by blast
      let ?asm = "asms ! (nat_of_integer n - 1)"
      have va: "vars ?asm \<subseteq> vars A1" "vars concl \<subseteq> vars A1"
      proof -
        have "nat_of_integer n - 1 < length asms" using n1 by (simp add: integer_reps integer_of_nat.rep_eq)
        then show "vars ?asm \<subseteq> vars A1" "vars concl \<subseteq> vars A1"
          using vars_assum_problems[OF ap cokR[OF A1r]] by auto
      qed
      have "tr (psubst \<rho>' \<theta>' 0 (rlist_abs params ?asm)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 (rlist_abs params concl))"
        by (rule dsol'[OF ac])
      then have "tr (psubst \<rho>' \<theta>' 0 ?asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 concl)"
        using cl'x by (simp add: tr_psubst_rlist_abs equiv_Abs_m_inj)
      moreover have "psubst \<rho>' \<theta>R 0 ?asm = psubst \<rho>' \<theta>' 0 ?asm" "psubst \<rho>' \<theta>R 0 concl = psubst \<rho>' \<theta>' 0 concl"
        using va vA1 kA1 by (auto intro!: psR)
      ultimately have e: "tr (psubst \<rho>' \<theta>R 0 ?asm) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 concl)" by simp
      have "prf_ok V' H [] (rev Ns) (mk_asm_prf A1 n (nlift + 1)) (psubst \<rho>' \<theta>R 0 A1)"
        by (rule mk_asm_prf_ok[OF cokR[OF A1r] _ wtyR[OF A1r] ap n1 e]) (simp add: closed_inst_def clR)
      then show ?thesis using er(2) A1o nnn n1 by auto
    qed
    text \<open>The new premises, from the premises of the rule.\<close>
    let ?la = "length (na_As na)" and ?lb = "length Bs"
    have lold0: "length (na_oldAs na) = length As0" using renc by auto
    have revN: "rev Ns ! (?la - 1 - k) = Ns ! (?lb + k)" if "k < ?la" for k
      using that lHs by (simp add: Ns_def rev_nth)
    have olds: "\<forall>k<length (na_oldAs na). prf_ok V' H [] (rev Ns)
      ((if flatten then flatten_params_proof 0 0 (na_n na) else (\<lambda>x. PBound (snd x)))
        (na_oldAs na ! k, integer_of_nat (?la - 1 - k))) (map (psubst \<rho>' \<theta>R 0) As0 ! k)"
    proof (intro allI impI)
      fix k assume k: "k < length (na_oldAs na)"
      have kA: "k < ?la" "k < length As0" using k lold lold0 by auto
      let ?A = "na_oldAs na ! k" and ?A' = "na_As na ! k" and ?Ao = "As0 ! k"
      have A0r: "?Ao \<in> set (rev rAs)" using kA rAs' by auto
      have vA0: "vars ?Ao \<subseteq> RR" using A0r by (auto simp: RR_def vars_thm_def vars_list_implies P)
      have rel: "aconv_term (psubst \<rho>' \<theta>' 0 ?A) (psubst \<rho>' \<theta>R 0 ?Ao) \<and> cok ?A"
      proof -
        from renc consider "na_ren na = None" "na_oldAs na = As0"
          | (ren) "lifted" "na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0)"
            "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0"
          by (elim disjE conjE) auto
        then show ?thesis
        proof cases
          case 1
          then have "rn x = x" for x by (simp add: rn_def ren_of_def)
          with 1 vA0 cokR[OF A0r] show ?thesis by (auto simp: psR)
        next
          case ren
          let ?r = "rename_bvs dps (rtpairs @ tps1) Bi As0"
          from lr[OF ren(1)] obtain p Bi0 As1 where ls: "lsplit Bi = (p, Bi0)" and rA: "rev rAs = map (lift_pre p) As1"
            and big: "\<forall>X\<in>set As1. \<forall>x\<in>vars X. smax < snd x"
            by (auto simp: lifted_rule_def)
          from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
            by auto
          from A0r rA obtain X0 where X0: "?Ao = lift_pre p X0" "X0 \<in> set As1" by auto
          have ibBi: "ibelow smax Bi" using state(2) by simp
          have pv: "snd y \<le> smax" if "y \<in> pvars p" for y
            using that ibBi by (auto simp: Bi ibelow_def vars_lift_pre)
          have A: "?A = lift_pre p (ren_term ?r X0)"
            using ren(3) kA X0 by (simp add: Bi strip_apply_lift_pre[OF ok at])
          have "aconv_term (psubst \<rho>' \<theta>' 0 (lift_pre p (ren_term ?r X0))) (psubst \<rho>' \<theta>R 0 (lift_pre p X0))"
          proof (rule aconv_psubst_lift_pre_ren)
            show "\<forall>x\<in>pvars p. \<theta>R x = \<theta>' x"
              using vA0 X0(1) pv rnid by (auto simp: \<theta>R_def vars_lift_pre)
            show "\<forall>x\<in>vars X0. \<theta>R x = \<theta>' (ren_ix ?r x)"
              using vA0 X0 big ren(2) by (auto simp: \<theta>R_def vars_lift_pre rn_def ren_of_def)
          qed
          moreover have "cok ?A"
          proof -
            have "wfp ar ?Ao" using wR(1) A0r cokR[OF A0r] by (auto simp: wfp_def wt_term_def swf_tm_def)
            then have "wfp ar ?A" using wfp_lift_pre_ren_term[of ar p ?r X0] X0(1) A by simp
            then show ?thesis by (simp add: wfp_def)
          qed
          ultimately show ?thesis using A X0(1) by simp
        qed
      qed
      have trA: "tr (psubst \<rho>' \<theta>' 0 ?A) = tr (psubst \<rho>' \<theta>R 0 ?Ao)" using rel aconv_term_tr by blast
      have wA0: "wty V' [] (psubst \<rho>' \<theta>R 0 ?Ao) propT" by (rule wtyR[OF A0r])
      have wA: "wty V' [] (psubst \<rho>' \<theta>' 0 ?A) propT"
      proof -
        have "has_type V' [] (psubst \<rho>' \<theta>' 0 ?A) propT"
          using wA0 rel has_type_aconv'[OF aconv_term_sym'] by (auto simp: wty_def)
        moreover have "\<forall>v\<in>vars (psubst \<rho>' \<theta>' 0 ?A). 0 \<le> snd v" using tyall' by (auto simp: vars_psubst wty_def)
        ultimately show ?thesis by (simp add: wty_def)
      qed
      have relk: "tr (rev Ns ! (?la - 1 - k)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 ?A')"
        using relN[of "?lb + k"] revN[OF kA(1)] lHs kA by (simp add: nth_append)
      have wNk: "wty V' [] (rev Ns ! (?la - 1 - k)) propT"
        using wtyN(1) revN[OF kA(1)] lHs kA by (simp add: Ns_def)
      have k': "?la - 1 - k < length (rev Ns)" using kA lHs by (simp add: Ns_def)
      show "prf_ok V' H [] (rev Ns) ((if flatten then flatten_params_proof 0 0 (na_n na) else (\<lambda>x. PBound (snd x)))
          (?A, integer_of_nat (?la - 1 - k))) (map (psubst \<rho>' \<theta>R 0) As0 ! k)"
      proof (cases flatten)
        case True
        have fl: "ok (flatten_params vl n ?A) ?A'" using list_all2_nthD[OF flat] k True by simp
        have wA': "wty V' [] (psubst \<rho>' \<theta>' 0 ?A') propT"
        proof -
          have "wtprop A W'' env' ?A'" using As kA by simp
          then have tp': "typed env' W'' [] ?A' propT" and tw: "\<forall>U\<in>tys ?A'. tyw ar (tyenv env') A U"
            by (auto simp: wtprop_def)
          have ti'': "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi3])
          have "wty V' [] (psubst \<rho>' \<theta>' 0 ?A') (tsubst \<rho>' propT)"
          proof (rule typed_psubst_wty[OF tp' pi3 gs'])
            show "\<forall>U\<in>tys ?A'. tcons (tyenv env') U" using tw tyw_tcons[OF ti''] by blast
            show "tcons (tyenv env') propT" by (simp add: tcons_def propT_def)
            show "\<forall>x\<in>vars ?A'. wty V' [] (\<theta>' x) (tsubst \<rho>' (W3 x))" using tyall' by blast
          qed
          then show ?thesis by (simp add: propT_def)
        qed
        have "prf_ok V' H [] (rev Ns) (flatten_params_proof 0 0 n (?A, integer_of_nat (?la - 1 - k))) (psubst \<rho>' \<theta>' 0 ?A)"
        proof (rule flatten_params_proof_ok[OF _ _ fl _ wA wA' k' wNk relk])
          show "cok ?A" using rel by blast
          show "closed_inst \<theta>' ?A" using cl'x by (simp add: closed_inst_def)
          show "length (vl (map fst (strip_params ?A))) = length (strip_params ?A)" using vl by simp
          show "\<forall>h\<in>set (rev Ns). wty V' [] h propT" using wtyN(1) by simp
        qed
        then show ?thesis using True nnn kA trA wA0 by (auto intro: prf_ok.conv)
      next
        case False
        have AA: "?A' = ?A" using list_all2_nthD[OF flat] k False by simp
        have "prf_ok V' H [] (rev Ns) (PBound (integer_of_nat (?la - 1 - k))) (rev Ns ! (?la - 1 - k))"
          using prf_ok.PBound[of "integer_of_nat (?la - 1 - k)" "rev Ns" V' "[]" H] k' wNk
          by (simp add: integer_reps)
        moreover have "tr (rev Ns ! (?la - 1 - k)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>R 0 ?Ao)" using relk AA trA by simp
        ultimately show ?thesis using False kA wA0 by (auto intro: prf_ok.conv)
      qed
    qed
    text \<open>The composed proof of the instances.\<close>
    let ?core = "core_prf flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1)"
    have core_ok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 (?core sprf rp')) (list_implies Ns (psubst \<rho>' \<theta>' 0 C))"
      unfolding prf_inst_core_prf
    proof (rule core_prf_ok[OF Sok _ BBi_eq _ wtyN(1) _ _ lold _ olds pre_ok])
      show "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 rp')
          (list_implies (map (psubst \<rho>' \<theta>R 0) Pre @ map (psubst \<rho>' \<theta>R 0) As0) (psubst \<rho>' \<theta>R 0 B))"
        using Rok by (simp add: P rAs' psubst_list_implies')
      show "length Ns = length Bs + length (na_As na)" using lHs by (simp add: Ns_def)
      show "length (map (psubst \<rho>' \<theta>' 0) Bs) = length Bs" by simp
      show "length (map (psubst \<rho>' \<theta>R 0) As0) = length (na_oldAs na)" using lold0 by simp
      show "\<forall>j<length Bs. tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)"
      proof (intro allI impI)
        fix j assume j: "j < length Bs"
        then show "tr (Ns ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)"
          using relN[of j] lHs by (simp add: nth_append)
      qed
    qed
    text \<open>The proof that was computed is equivalent to the instance of the composed proof.\<close>
    have pinst: "prf_aeq (prf_inst \<rho>' \<theta>' 0 (?core sprf rp')) (prf_inst \<rho> \<theta>0 0 p)"
    proof -
      from pc consider (e) "env_is_empty env'" "p = ?core sprf rp'"
        | (a) rp'' where "\<not> env_is_empty env'" "above env' smax" "p = ?core sprf rp''"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
        | (g) "\<not> env_is_empty env'" "\<not> above env' smax"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
        by blast
      then show ?thesis
      proof cases
        case e
        have "\<rho>' = \<rho>" using agT e(1) by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
        moreover have "\<theta>' = \<theta>0" using unb\<theta> e(1) by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
        ultimately show ?thesis using e(2) by (simp add: prf_aeq.refl)
      next
        case a
        have unbT: "vt_lookup (tyenv env') v = None" if "snd v \<le> smax" for v
          using a(2) that unfolding above_def by (blast intro: vt_above_lookup)
        have tcong: "tsubst \<rho> U = tsubst \<rho>' U" if "\<forall>(v, S)\<in>tvars U. snd v \<le> smax" for U
          by (rule tsubst_cong) (use that unbT agT in fastforce)
        have "prf_inst \<rho>' \<theta>' 0 sprf = prf_inst \<rho> \<theta>0 0 sprf"
          by (rule prf_inst_tcong[OF sp0], rule prf_all_mono[OF sw]) (use tcong in auto)
        moreover have "prf_aeq (prf_inst \<rho>' \<theta>' 0 rp') (prf_inst \<rho> \<theta>0 0 rp'')"
          by (rule norm_proof_inst[OF a(4) rA ie swf smeq cl0 cl' _ tyc]) (use ty0 in \<open>auto simp: wty_def\<close>)
        ultimately show ?thesis using a(3)
          by (simp add: prf_inst_core_prf) (rule prf_aeq_core_prf[OF prf_aeq.refl])
      next
        case g
        have "prf_all (ann_ok_env env') (tcons (tyenv env')) (?core sprf rp')"
          by (rule prf_all_core_prf[OF sA rA ann_ok_env_Bound])
        from norm_proof_inst[OF g(3) this ie swf smeq cl0 cl' _ tyc] ty0 show ?thesis
          by (auto simp: wty_def)
      qed
    qed
    have okp: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 p) (list_implies Ns (psubst \<rho>' \<theta>' 0 C))"
      by (rule prf_ok_aeq[OF core_ok pinst])
    have pv: "prf_vars p = {}"
    proof -
      have c: "prf_vars (?core sprf q) = {}" if "prf_vars q = {}" for q
        using that sp0 by (simp add: prf_vars_core_prf)
      from pc consider (e) "env_is_empty env'" "p = ?core sprf rp'"
        | (a) rp'' where "\<not> env_is_empty env'" "above env' smax" "p = ?core sprf rp''"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
        | (g) "\<not> env_is_empty env'" "\<not> above env' smax"
          "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
        by blast
      then show ?thesis
      proof cases
        case e
        then show ?thesis using c[OF rp'0] by simp
      next
        case a
        then show ?thesis using c[OF prf_vars_prf_rel[OF a(4) rp'0]] by simp
      next
        case g
        then show ?thesis using prf_vars_prf_rel[OF g(3) c[OF rp'0]] by simp
      qed
    qed
    have "prf_inst \<rho> \<theta>0 0 p = prf_inst \<rho> \<theta> 0 p" by (rule prf_inst_cong) (simp add: pv)
    moreover have "psubst \<rho> \<theta> 0 (br_prop r) = psubst \<rho> \<theta>0 0 (br_prop r)"
      using eq0[of "br_prop r" 0] nnr by (simp add: vars_thm_def)
    moreover have "tr (list_implies Ns (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 (br_prop r))"
    proof -
      have "tr (psubst \<rho>' \<theta>' 0 C) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 C')" by (rule equiv_sym[OF rel_tr[OF relC]])
      then have "tr (list_implies Ns (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_implies Ns (psubst \<rho> \<theta>0 0 C'))"
        by (intro tr_list_implies_cong) (simp_all add: list.rel_refl)
      then show ?thesis by (simp add: bprop psubst_list_implies' Ns_def)
    qed
    ultimately show "prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 p) (psubst \<rho> \<theta> 0 (br_prop r))"
      using prf_ok.conv[OF okp _ wtyP] by simp
  qed
  text \<open>The invariant of the new proof.\<close>
  have pv: "prf_vars p = {}"
  proof -
    have c: "prf_vars (?core sprf q) = {}" if "prf_vars q = {}" for q
      using that sp0 by (simp add: prf_vars_core_prf)
    from pc consider (e) "p = ?core sprf rp'"
      | (a) rp'' where "p = ?core sprf rp''" "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
      | (g) "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
      by blast
    then show ?thesis
    proof cases
      case e
      then show ?thesis using c[OF rp'0] by simp
    next
      case a
      then show ?thesis using c[OF prf_vars_prf_rel[OF a(2) rp'0]] by simp
    next
      case g
      then show ?thesis using prf_vars_prf_rel[OF g c[OF rp'0]] by simp
    qed
  qed
  let ?Ar = "tvars_env (tyenv env') \<union> A"
  have ti'': "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi''])
  have wfp: "wft ar propT" using imp by (simp add: tyA_def imp_type_def)
  have aB: "ann0 B (Bound j)" if "0 \<le> j" for B j by (rule ann0_Bound[OF that wfp])
  have tyAr: "tyA ar ?Ar (tnorm (tyenv env') U)" if "tyA ar A U" for U
    using tyw_tnorm[OF ti'' tyA_tyw[OF ti'' that]] by (simp add: tyA_def tyw_def)
  have sw0: "prf_all (ann0 A) (tyA ar A) sprf" by (rule prf_all_mono[OF sw]) auto
  have cA0: "prf_all (ann0 A) (tyA ar A) (?core sprf q)" if "prf_all (ann0 A) (tyA ar A) q" for q
    by (rule prf_all_core_prf[OF sw0 that aB])
  have mono: "prf_all (ann0 ?Ar) (tyA ar ?Ar) q" if "prf_all (ann0 A) (tyA ar A) q" for q
    by (rule prf_all_mono[OF that]) (auto intro: ann0_mono tyA_mono)
  have rel: "prf_all (ann0 ?Ar) (tyA ar ?Ar) q'"
    if "prf_rel (ann_rel env') (tnorm (tyenv env')) q q'" "prf_all (ann0 A) (tyA ar A) q" for q q'
    by (rule prf_all_prf_rel[OF that]) (auto intro: ann0_ann_rel[OF _ _ pi''] tyAr)
  have pa: "prf_all (ann0 ?Ar) (tyA ar ?Ar) p"
  proof -
    from pc consider (e) "p = ?core sprf rp'"
      | (a) rp'' where "p = ?core sprf rp''" "prf_rel (ann_rel env') (tnorm (tyenv env')) rp' rp''"
      | (g) "prf_rel (ann_rel env') (tnorm (tyenv env')) (?core sprf rp') p"
      by blast
    then show ?thesis
    proof cases
      case e
      then show ?thesis using mono[OF cA0[OF rw']] by simp
    next
      case a
      show ?thesis unfolding a(1) by (rule prf_all_core_prf[OF mono[OF sw0] rel[OF a(2) rw'] aB])
    next
      case g
      show ?thesis by (rule rel[OF g cA0[OF rw']])
    qed
  qed
  from wt_thm_restrict[OF wtr wfp] obtain Wr where Wr: "\<forall>x. tyA ar ?Ar (Wr x)"
    "wt_thm ar ?Ar Wr (maxidx env') (br_tpairs r) (br_prop r)"
    "\<forall>x\<in>vars_thm (br_tpairs r) (br_prop r). Wr x = tctx env' W'' x" .
  have tvlo: "\<forall>q\<in>tvars_env (tyenv (br_env r)). 0 \<le> snd (fst q)"
    by (rule bicompose_aux_thm_typed(4)[OF ok res cfg finA state rule A(1) _ A(3) ns er fl vl _ lo _ _ cA])
      (use A(2) A0 nn in auto)
  have "thm_prf_inv (maxidx env') (br_tpairs r) (br_prop r) H p"
    unfolding thm_prf_inv_def
  proof (intro conjI exI[of _ ?Ar] exI[of _ Wr])
    show "prf_vars p = {}" by (rule pv)
    show "finite ?Ar" using finA finite_tvars_env by simp
    show "scons ?Ar" using ti'' by (simp add: tinv_def)
    show "tcert alg ?Ar" using pinvD(7)[OF pi'' cA] cA by simp
    show "\<forall>q\<in>?Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx env'"
      using tvlo A0 ti'' rbr(1) by (auto simp: tinv_def)
    show "\<forall>x. tyA ar ?Ar (Wr x)" by (rule Wr(1))
    show "wt_thm ar ?Ar Wr (maxidx env') (br_tpairs r) (br_prop r)" by (rule Wr(2))
    show "prf_valid alg ar Wr H (br_tpairs r) p (br_prop r)" by (rule prf_valid_cong[OF pvld Wr(3) pv])
    show "prf_all (ann0 ?Ar) (tyA ar ?Ar) p" by (rule pa)
  qed
  then show ?thesis using bp rbr by (auto simp: nlift_def rp'_def)
qed

end

end
