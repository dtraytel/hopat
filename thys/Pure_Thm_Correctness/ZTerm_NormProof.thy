section \<open>Normalisation of tight proofs\<close>

theory ZTerm_NormProof
  imports ZTerm_Norm
begin

text \<open>
  The instances of a tight proof and of its normalisation are equivalent, with the instances of
  the theorems through the unifier (the bridge of theory
  \<^theory>\<open>Pure_Thm_Correctness.Proof_Bridge\<close>). The relation of the annotations is semantic: for
  every bridge, the instances of an annotation and of its normalisation are equivalent.
\<close>

context csig
begin

subsection \<open>\<open>\<beta>\<close>-normalisation of tight terms\<close>

lemma beta_norm_term_beta:
  assumes "beta_norm_term z = Some z'"
  shows "proper (zdec z) \<Longrightarrow> proper (zdec z') \<and> tr (zdec z) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec z')"
  using assms
proof (induction z z' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn z z')
  note F = "1.hyps" and IH = "1.IH" and pr = "1.prems"
  have sb: "proper (zdec (subst_term_bound u body)) \<and>
      tr (zdec (ZApp (ZAbs a T body) u)) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (subst_term_bound u body))"
    if "proper (zdec (ZApp (ZAbs a T body) u))" for a T body u
  proof -
    from that have p: "proper (zdec body)" "proper (zdec u)" by simp_all
    have "tr (zdec (ZApp (ZAbs a T body) u)) \<rightarrow>\<^sub>\<beta> tr (zdec (subst_term_bound u body))"
      using p by (simp add: zdec_subst_term_bound tr_subst_bound beta.beta)
    then show ?thesis using p by (simp add: zdec_subst_term_bound proper_subst_bound)
  qed
  show ?case
  proof (cases z)
    case (ZAbs a T b)
    with F obtain b' where b: "bn b = Some b'" and z': "z' = ZAbs a T b'"
      by (auto split: Option.bind_splits)
    from IH[OF b] pr ZAbs have "proper (zdec b') \<and> tr (zdec b) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec b')" by simp
    with ZAbs z' show ?thesis by auto
  next
    case (ZApp f u)
    show ?thesis
    proof (cases "\<exists>a T body. f = ZAbs a T body")
      case True
      then obtain a T body where f: "f = ZAbs a T body" by blast
      with F ZApp have n: "bn (subst_term_bound u body) = Some z'" by simp
      from sb[of a T body u] pr ZApp f have s: "proper (zdec (subst_term_bound u body))"
        "tr (zdec z) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (subst_term_bound u body))" by auto
      from IH[OF n s(1)] s(2) show ?thesis by (auto intro: rtranclp_trans)
    next
      case False
      with F ZApp obtain nf where nf: "bn f = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some z'"
        by (cases f) (auto split: Option.bind_splits)
      from pr ZApp have pf: "proper (zdec f)" and pu: "proper (zdec u)" by auto
      from IH[OF nf pf] have hf: "proper (zdec nf)" "tr (zdec f) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec nf)" by auto
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbs a T body")
        case True
        then obtain a T body where nfa: "nf = ZAbs a T body" by blast
        with rest have n: "bn (subst_term_bound u body) = Some z'" by simp
        from sb[of a T body u] hf(1) pu nfa have s: "proper (zdec (subst_term_bound u body))"
          "tr (zdec (ZApp nf u)) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (subst_term_bound u body))" by auto
        from IH[OF n s(1)] have "proper (zdec z') \<and> tr (zdec (subst_term_bound u body)) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec z')" .
        moreover have "tr (zdec z) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (ZApp nf u))" using hf(2) ZApp by (simp add: rtrancl_beta_AppL)
        ultimately show ?thesis using s(2) by (auto intro: rtranclp_trans)
      next
        case False
        with rest obtain nu where nu: "bn u = Some nu" and z': "z' = ZApp nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        from IH[OF nu pu] have "proper (zdec nu)" "tr (zdec u) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec nu)" by auto
        with hf ZApp z' show ?thesis by auto
      qed
    qed
  qed (use F pr in auto)
qed

lemma beta_norm_term_normal:
  assumes "beta_norm_term z = Some z'"
  shows "\<not> could_beta_contract (zdec z')"
  using assms
proof (induction z z' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn z z')
  note F = "1.hyps" and IH = "1.IH"
  show ?case
  proof (cases z)
    case (ZAbs a T b)
    with F obtain b' where "bn b = Some b'" "z' = ZAbs a T b'" by (auto split: Option.bind_splits)
    with IH show ?thesis by auto
  next
    case (ZApp f u)
    show ?thesis
    proof (cases "\<exists>a T body. f = ZAbs a T body")
      case True
      then obtain a T body where "f = ZAbs a T body" by blast
      with F ZApp have "bn (subst_term_bound u body) = Some z'" by simp
      with IH show ?thesis by blast
    next
      case False
      with F ZApp obtain nf where nf: "bn f = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some z'"
        by (cases f) (auto split: Option.bind_splits)
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbs a T body")
        case True
        then obtain a T body where "nf = ZAbs a T body" by blast
        with rest have "bn (subst_term_bound u body) = Some z'" by simp
        with IH show ?thesis by blast
      next
        case nA: False
        with rest obtain nu where nu: "bn u = Some nu" "z' = ZApp nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        from IH[OF nf] IH[OF nu(1)] nA nu(2) show ?thesis
          by (cases "zdec nf") (auto simp: zdec_eq_Abs)
      qed
    qed
  qed (use F in \<open>auto simp: of_class_def split: if_splits\<close>)
qed

text \<open>\<open>beta_norm_term\<close> terminates on typed terms (as head normalisation, by strong
  normalisation of typable terms).\<close>

lemma beta_norm_term_term:
  "has_type W Ts (zdec z) T \<Longrightarrow> \<exists>z'. beta_norm_term z = Some z' \<and> has_type W Ts (zdec z') T"
proof (induction z arbitrary: Ts T rule: wf_induct_rule[OF wf_inv_image[OF wf_sn_less, of "\<lambda>z. tr (zdec z)"]])
  case (1 z)
  have red: "\<exists>z'. beta_norm_term u = Some z' \<and> has_type W Us (zdec z') U"
    if "(sup beta subt)\<^sup>+\<^sup>+ (tr (zdec z)) (tr (zdec u))" "has_type W Us (zdec u) U" for u Us U
    using "1.IH"[OF _ that(2)] sn_lessI[OF typableI[OF has_type_tr[OF "1.prems"]] that(1)] by simp
  have bstep: "(sup beta subt)\<^sup>+\<^sup>+ (tr (zdec z)) (tr (zdec (subst_term_bound u body)))"
    if "tr (zdec z) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (ZApp (ZAbs a U body) u))" "proper (zdec body)" "proper (zdec u)"
    for a U body u
  proof -
    have "tr (zdec (ZApp (ZAbs a U body) u)) \<rightarrow>\<^sub>\<beta> tr (zdec (subst_term_bound u body))"
      using that(2,3) by (simp add: zdec_subst_term_bound tr_subst_bound beta.beta)
    then have "(sup beta subt) (tr (zdec (ZApp (ZAbs a U body) u))) (tr (zdec (subst_term_bound u body)))"
      by simp
    with beta_reds_sup[OF that(1)] show ?thesis by (metis rtranclp_into_tranclp1)
  qed
  show ?case
  proof (cases z)
    case (ZAbs a U b)
    from "1.prems" ZAbs obtain V' where tyb: "has_type W (typ_of U # Ts) (zdec b) V'"
      and T: "T = typ_of U \<rightarrow>\<^sub>T V'"
      by (auto elim: has_type_elims)
    have "\<exists>b'. beta_norm_term b = Some b' \<and> has_type W (typ_of U # Ts) (zdec b') V'"
      by (rule red[OF _ tyb]) (auto simp: ZAbs subt_def)
    then show ?thesis using ZAbs T by (subst beta_norm_term.simps) (auto intro: has_type.Abs)
  next
    case (ZApp f u)
    from "1.prems" ZApp obtain U where tyf: "has_type W Ts (zdec f) (U \<rightarrow>\<^sub>T T)" and tyu: "has_type W Ts (zdec u) U"
      by (auto elim: has_type_elims)
    have pu: "proper (zdec u)" by (rule has_type_proper[OF tyu])
    show ?thesis
    proof (cases "\<exists>a U' body. f = ZAbs a U' body")
      case True
      then obtain a U' body where f: "f = ZAbs a U' body" by blast
      from tyf f have tyb: "has_type W (U # Ts) (zdec body) T" by (auto elim: has_type_elims)
      have tys: "has_type W Ts (zdec (subst_term_bound u body)) T"
        by (simp add: zdec_subst_term_bound has_type_subst_bound[OF tyb tyu])
      have st: "(sup beta subt)\<^sup>+\<^sup>+ (tr (zdec z)) (tr (zdec (subst_term_bound u body)))"
        by (rule bstep) (use ZApp f has_type_proper[OF tyb] pu in auto)
      from red[OF st tys] ZApp f show ?thesis by (subst beta_norm_term.simps) simp
    next
      case False
      have "\<exists>nf. beta_norm_term f = Some nf \<and> has_type W Ts (zdec nf) (U \<rightarrow>\<^sub>T T)"
        by (rule red[OF _ tyf]) (auto simp: ZApp subt_def)
      then obtain nf where nf: "beta_norm_term f = Some nf" "has_type W Ts (zdec nf) (U \<rightarrow>\<^sub>T T)" by blast
      have rf: "tr (zdec f) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec nf)"
        using beta_norm_term_beta[OF nf(1) has_type_proper[OF tyf]] by blast
      have unf: "beta_norm_term z = (case nf of ZAbs _ _ body \<Rightarrow> beta_norm_term (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZApp nf nu)))"
        unfolding ZApp using False nf(1) by (subst beta_norm_term.simps) (cases f; simp cong: zterm.case_cong)
      show ?thesis
      proof (cases "\<exists>a U' body. nf = ZAbs a U' body")
        case True
        then obtain a U' body where nfa: "nf = ZAbs a U' body" by blast
        from nf(2) nfa have tyb: "has_type W (U # Ts) (zdec body) T" by (auto elim: has_type_elims)
        have tys: "has_type W Ts (zdec (subst_term_bound u body)) T"
          by (simp add: zdec_subst_term_bound has_type_subst_bound[OF tyb tyu])
        have st: "(sup beta subt)\<^sup>+\<^sup>+ (tr (zdec z)) (tr (zdec (subst_term_bound u body)))"
          by (rule bstep) (use ZApp nfa rf has_type_proper[OF tyb] pu in \<open>auto simp: rtrancl_beta_AppL\<close>)
        from red[OF st tys] unf nfa show ?thesis by simp
      next
        case nA: False
        have "\<exists>nu. beta_norm_term u = Some nu \<and> has_type W Ts (zdec nu) U"
          by (rule red[OF _ tyu]) (auto simp: ZApp subt_def)
        then obtain nu where "beta_norm_term u = Some nu" "has_type W Ts (zdec nu) U" by blast
        with unf nA nf(2) show ?thesis by (cases nf) (auto intro: has_type.App)
      qed
    qed
  qed (subst beta_norm_term.simps; use "1.prems" in simp)+
qed

lemma beta_norm_term_idem: "beta_norm_term z = Some z' \<Longrightarrow> beta_norm_term z' = Some z'"
  by (rule beta_norm_term_no_redex[OF beta_norm_term_normal])

text \<open>Tight proofs without \<open>\<beta>\<close>-redexes of term abstractions where \<open>beta_norm_prooft\<close> looks
  (\<open>zrf\<close>), and in addition with \<open>\<beta>\<close>-normal term arguments there (\<open>zrfn\<close>).\<close>

fun zrf :: "zproof \<Rightarrow> bool" where
  "zrf (ZAbst a T p) \<longleftrightarrow> zrf p"
| "zrf (ZAppt p t) \<longleftrightarrow> zrf p \<and> (\<forall>a T q. p \<noteq> ZAbst a T q)"
| "zrf _ \<longleftrightarrow> True"

fun zrfn :: "zproof \<Rightarrow> bool" where
  "zrfn (ZAbst a T p) \<longleftrightarrow> zrfn p"
| "zrfn (ZAppt p t) \<longleftrightarrow> zrfn p \<and> (\<forall>a T q. p \<noteq> ZAbst a T q) \<and> beta_norm_term t = Some t"
| "zrfn _ \<longleftrightarrow> True"

lemma beta_norm_prooft_zrfn: "zrfn p \<Longrightarrow> beta_norm_prooft p = Some p"
proof (induction p)
  case (ZAbst a T q)
  then show ?case by (subst beta_norm_prooft.simps) simp
next
  case (ZAppt f u)
  then show ?case by (subst beta_norm_prooft.simps) (cases f; simp)
qed (subst beta_norm_prooft.simps; simp)+

subsection \<open>Instantiation of tight terms\<close>

lemma tsubst_zconst_typ: "tsubst \<rho> (zconst_typ c Us) = zconst_typ c (map (tsubst \<rho>) Us)"
proof -
  have d: "tsubst \<rho> dummyT = dummyT" by (simp add: dummyT_def)
  have p: "tsubst \<rho> (case map_of (zip ps Vs) x of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) =
      (case map_of (zip ps (map (tsubst \<rho>) Vs)) x of Some X \<Rightarrow> X | None \<Rightarrow> dummyT)" for ps Vs x
    by (simp add: map_of_zip_map2 d split: option.splits)
  show ?thesis
  proof (cases "c = STR ''Pure.imp'' \<or> c = STR ''Pure.all''")
    case True
    then show ?thesis by (auto simp: zconst_typ_def imp_type_def propT_def d split: list.splits)
  next
    case False
    then show ?thesis by (simp add: zconst_typ_def tsubst_tsubst p d split: option.splits)
  qed
qed

fun zvars :: "zterm \<Rightarrow> (indexname \<times> ztyp) set" where
  "zvars (ZVar x T) = {(x, T)}"
| "zvars (ZAbs a T t) = zvars t"
| "zvars (ZApp t u) = zvars t \<union> zvars u"
| "zvars _ = {}"

end

context prf_wf_csig
begin

lemma zdec_zsubst_term:
  assumes "\<forall>T\<in>ztys t. typ_of (typ T) = tsubst \<rho> (typ_of T)"
    "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> zdec (case var (x, typ T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (typ T)) = \<theta> x"
    "\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> var (x, typ T) = None"
    "\<forall>x. \<not> loose_bvar (\<theta> x) 0"
  shows "zdec (zsubst_term typ var t) = psubst \<rho> \<theta> 0 (zdec t)"
  using assms
proof (induction t)
  case (ZVar x T)
  then show ?case by (cases "snd x = -1") (auto simp: incr_boundvars_def split: option.splits)
next
  case (ZConst0 c)
  then show ?case using tsubst_zconst_typ[of \<rho> c "[]"] by simp
next
  case (ZConst1 c T)
  then show ?case using tsubst_zconst_typ[of \<rho> c "[typ_of T]"] by simp
next
  case (ZConst c Ts)
  then have "zconst_typ c (map (\<lambda>x. typ_of (typ x)) Ts) = zconst_typ c (map (\<lambda>x. tsubst \<rho> (typ_of x)) Ts)"
    by (simp cong: map_cong)
  with ZConst show ?case using tsubst_zconst_typ[of \<rho> c "map typ_of Ts"] by (simp add: comp_def)
next
  case (ZAbs a T t)
  then have "psubst \<rho> \<theta> 1 (zdec t) = psubst \<rho> \<theta> 0 (zdec t)" by (intro psubst_closed_lev) auto
  with ZAbs show ?case by simp
next
  case (ZOfclass T c)
  then show ?case by (simp add: of_class_def propT_def)
qed simp_all

subsection \<open>Bridges and related annotations\<close>

definition zbridge :: "env \<Rightarrow> tinst \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> tinst \<Rightarrow> (nat \<Rightarrow> dB) \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> bool" where
  "zbridge env \<rho> \<theta> \<rho>' \<sigma>' \<theta>' \<longleftrightarrow> iext env \<rho> (isubst \<theta>) \<rho>' \<sigma>' \<and> swf_env ar env \<and>
    (\<forall>t. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t)) \<and>
    (\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0) \<and> (\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0) \<and>
    (\<forall>x. \<forall>y\<in>vars (\<theta> x). 0 \<le> snd y) \<and>
    (\<forall>T. tcons (tyenv env) T \<longrightarrow> tsubst \<rho> (tnorm (tyenv env) T) = tsubst \<rho>' T)"

definition ann_zrel :: "env \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "ann_zrel env t t' \<longleftrightarrow> (\<forall>\<rho> \<theta> \<rho>' \<sigma>' \<theta>' lev. zbridge env \<rho> \<theta> \<rho>' \<sigma>' \<theta>' \<longrightarrow> 0 \<le> lev \<longrightarrow>
    ann_eq (Some (psubst \<rho>' \<theta>' lev t)) (Some (psubst \<rho> \<theta> lev t')))"

lemma ann_rel_zrel: "ann_rel env t t' \<Longrightarrow> ann_zrel env t t'"
  unfolding ann_zrel_def zbridge_def by (blast intro: ann_rel_inst)

text \<open>
  The instance through the unifier of a term, and the instance of its instantiation by the
  normal forms of (some of) its variables, are equivalent.
\<close>

lemma sm_zinst:
  assumes ie: "iext env \<rho> (isubst \<theta>) \<rho>' \<sigma>'" and swf: "swf_env ar env"
    and cl: "\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0"
    and v: "\<forall>x\<in>vars t. (\<exists>U u rb. ok (norm_term env (Var x U)) u \<and> \<theta>v x = u \<and> swf_tm ar rb (Var x U)) \<or>
      (vt_lookup (tenv env) x = None \<and> (\<exists>U. \<theta>v x = Var x U))"
    and ty: "\<forall>U\<in>tys t. tsubst \<rho> (tsubst \<rho>v U) = tsubst \<rho>' U"
  shows "sm (\<lambda>v S. tsubst \<rho> (\<rho>v v S)) (isubst (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
  using v ty
proof (induction t)
  case (Const a T)
  have rig: "rigid_subst \<sigma>'" using ie by (simp add: iext_def)
  from Const.prems(2) have "tsubst \<rho> (tsubst \<rho>v T) = tsubst \<rho>' T" by simp
  then show ?case using rigid_substD[OF rig] by (simp add: sm_def tsubst_tsubst)
next
  case (Free a T)
  have rig: "rigid_subst \<sigma>'" using ie by (simp add: iext_def)
  from Free.prems(2) have "tsubst \<rho> (tsubst \<rho>v T) = tsubst \<rho>' T" by simp
  then show ?case using rigid_substD[OF rig] by (simp add: sm_def tsubst_tsubst)
next
  case (Var x T)
  have clx: "\<forall>y\<in>vars s. \<not> loose_bvar (\<theta> y) 0" for s using cl by blast
  have l: "sm (\<lambda>v S. tsubst \<rho> (\<rho>v v S)) (isubst (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))) (Var x T) = sm \<rho> (isubst \<theta>) (\<theta>v x)"
    by (simp add: sm_def tr_psubst_sm[OF clx])
  have r: "sm \<rho>' \<sigma>' (Var x T) = sm \<rho>' \<sigma>' (Var x U)" for U by (simp add: sm_def)
  from Var.prems(1) consider (n) U u rb where "ok (norm_term env (Var x U)) u" "\<theta>v x = u" "swf_tm ar rb (Var x U)"
    | (u) U where "vt_lookup (tenv env) x = None" "\<theta>v x = Var x U"
    by auto
  then show ?case
  proof cases
    case n
    have "sm \<rho> (isubst \<theta>) (\<theta>v x) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' (Var x U)"
      using iext_norm_term[OF ie rigid_isubst swf n(3,1)] n(2) by simp
    then show ?thesis by (simp only: l r[of U])
  next
    case u
    have e: "\<sigma>' (code (AVar x)) = tr (\<theta> x)" using u(1) ie by (cases x) (auto simp: iext_def)
    have eq: "sm \<rho> (isubst \<theta>) (\<theta>v x) = sm \<rho>' \<sigma>' (Var x T)" using u(2) e by (simp add: sm_def)
    show ?thesis unfolding l eq by (rule equiv_refl)
  qed
next
  case (Abs a T t)
  have "sm (\<lambda>v S. tsubst \<rho> (\<rho>v v S)) (isubst (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
    by (rule Abs.IH) (use Abs.prems in auto)
  then show ?case by (simp only: sm_Abs) (rule equiv_Abs)
next
  case (App s t)
  have "sm (\<lambda>v S. tsubst \<rho> (\<rho>v v S)) (isubst (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))) s \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' s"
    by (rule App.IH(1)) (use App.prems in auto)
  moreover have "sm (\<lambda>v S. tsubst \<rho> (\<rho>v v S)) (isubst (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))) t \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t"
    by (rule App.IH(2)) (use App.prems in auto)
  ultimately show ?case by (simp only: sm_App) (rule equiv_App)
qed (simp add: sm_def)

text \<open>
  Hence the instance of an annotation through the unifier is equivalent to the instance of a
  \<open>\<beta>\<close>-normal form of its instantiation.
\<close>

lemma ann_eq_zinst:
  assumes zb: "zbridge env \<rho> \<theta> \<rho>' \<sigma>' \<theta>'"
    and b: "tr t1 \<rightarrow>\<^sub>\<beta>\<^sup>* tr t2" "proper t2"
    and t1: "t1 = psubst \<rho>v \<theta>v 0 t0"
    and clv: "\<forall>x. proper (\<theta>v x) \<and> \<not> loose_bvar (\<theta>v x) 0"
    and v: "\<forall>x\<in>vars t0. (\<exists>U u rb. ok (norm_term env (Var x U)) u \<and> \<theta>v x = u \<and> swf_tm ar rb (Var x U)) \<or>
      (vt_lookup (tenv env) x = None \<and> (\<exists>U. \<theta>v x = Var x U))"
    and ty: "\<forall>U\<in>tys t0. tsubst \<rho> (tsubst \<rho>v U) = tsubst \<rho>' U"
    and lev: "0 \<le> lev"
  shows "ann_eq (Some (psubst \<rho>' \<theta>' lev t0)) (Some (psubst \<rho> \<theta> lev t2))"
proof -
  from zb have ie: "iext env \<rho> (isubst \<theta>) \<rho>' \<sigma>'" and swf: "swf_env ar env"
    and smeq: "\<And>t. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t)"
    and cl: "\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0" and cl': "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0"
    and nn: "\<forall>x. \<forall>y\<in>vars (\<theta> x). 0 \<le> snd y"
    by (auto simp: zbridge_def)
  have clx: "\<forall>y\<in>vars s. \<not> loose_bvar (\<theta> y) 0" "\<forall>y\<in>vars s. \<not> loose_bvar (\<theta>' y) 0" for s using cl cl' by blast+
  define \<theta>'' where "\<theta>'' = (\<lambda>x. psubst \<rho> \<theta> 0 (\<theta>v x))"
  define \<rho>'' where "\<rho>'' = (\<lambda>v S. tsubst \<rho> (\<rho>v v S))"
  have cl'': "\<forall>y\<in>vars s. \<not> loose_bvar (\<theta>'' y) 0" for s
    using closed_psubst[of "\<theta>v y" \<theta> \<rho> for y] clv cl by (auto simp: \<theta>''_def)
  have lv: "psubst \<rho>' \<theta>' lev t0 = psubst \<rho>' \<theta>' 0 t0" "psubst \<rho> \<theta> lev t2 = psubst \<rho> \<theta> 0 t2"
    using psubst_closed_lev[OF clx(2) lev] psubst_closed_lev[OF clx(1) lev] by simp_all
  have cs: "closed_on UNIV (isubst \<theta> \<circ> cren \<rho>)" by (rule closed_on_cren[OF closed_isubst[OF cl]])
  have "tr (psubst \<rho> \<theta> 0 t2) = mk_subst (isubst \<theta> \<circ> cren \<rho>) (tr t2)"
    by (simp add: tr_psubst_sm[OF clx(1)] sm_def mk_subst_inst)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> mk_subst (isubst \<theta> \<circ> cren \<rho>) (tr t1)"
    by (rule mk_subst_equiv[OF equiv_sym[OF beta_into_equiv[OF b(1)]] cs])
  also have "\<dots> = tr (psubst \<rho> \<theta> 0 t1)" by (simp add: tr_psubst_sm[OF clx(1)] sm_def mk_subst_inst)
  also have "\<dots> = tr (psubst \<rho>'' \<theta>'' 0 t0)" by (simp add: t1 psubst_psubst \<rho>''_def \<theta>''_def)
  also have "\<dots> = sm \<rho>'' (isubst \<theta>'') t0" by (rule tr_psubst_sm[OF cl''])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t0"
    unfolding \<rho>''_def \<theta>''_def by (rule sm_zinst[OF ie swf cl v ty])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t0)" by (rule smeq)
  finally have "tr (remove_types (psubst \<rho>' \<theta>' 0 t0)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (psubst \<rho> \<theta> 0 t2))"
    by (rule remove_types_equiv[OF equiv_sym])
  moreover have "proper (psubst \<rho> \<theta> 0 t2)" using b(2) cl by (intro proper_psubst) auto
  moreover have "\<forall>x\<in>vars (psubst \<rho> \<theta> 0 t2). 0 \<le> snd x" using nn by (auto simp: vars_psubst)
  ultimately show ?thesis by (simp add: ann_eq_def lv)
qed

subsection \<open>Mapping the terms and types of tight proofs\<close>

fun zno_class :: "zproof \<Rightarrow> bool" where
  "zno_class (OFCLASSp T c) \<longleftrightarrow> False"
| "zno_class (ZAbst a T p) \<longleftrightarrow> zno_class p"
| "zno_class (ZAbsp a t p) \<longleftrightarrow> zno_class p"
| "zno_class (ZAppt p t) \<longleftrightarrow> zno_class p"
| "zno_class (ZAppp p q) \<longleftrightarrow> zno_class p \<and> zno_class q"
| "zno_class _ \<longleftrightarrow> True"

lemma map_zproof_ZAbst:
  "map_zproof ty tm p = returnZ p' \<Longrightarrow> (\<exists>a T q. p' = ZAbst a T q) \<longleftrightarrow> (\<exists>a T q. p = ZAbst a T q)"
  by (cases p) (auto simp: bindZ_eq_returnZ map_insts_def)

lemma map_zproof_rel:
  assumes "zconst_free p" "zno_class p" "zprf_all P Q p"
    and tm: "\<And>t. P t \<Longrightarrow> \<exists>t'. tm t = returnZ t' \<and> R (zdec t) (zdec t') \<and> beta_norm_term t' = Some t'"
    and ty: "\<And>T. Q T \<Longrightarrow> typ_of (ty T) = f (typ_of T)"
  shows "\<exists>p'. map_zproof ty tm p = returnZ p' \<and> prf_rel R f (zprf_tr p) (zprf_tr p') \<and>
    (zrf p \<longrightarrow> zrfn p') \<and> zconst_free p' \<and> zno_class p'"
  using assms(1-3)
proof (induction p)
  case (ZAbst a T q)
  then obtain q' where q: "map_zproof ty tm q = returnZ q'" "prf_rel R f (zprf_tr q) (zprf_tr q')"
    "zrf q \<longrightarrow> zrfn q'" "zconst_free q'" "zno_class q'" by auto
  have e: "map_option f (Some (typ_of T)) = Some (typ_of (ty T))" using ty ZAbst.prems(3) by simp
  have "prf_rel R f (Abst a (Some (typ_of T)) (zprf_tr q)) (Abst a (map_option f (Some (typ_of T))) (zprf_tr q'))"
    by (rule prf_rel.Abst[OF q(2)])
  then have "prf_rel R f (zprf_tr (ZAbst a T q)) (zprf_tr (ZAbst a (ty T) q'))" by (simp only: e zprf_tr.simps)
  with q show ?case by auto
next
  case (ZAbsp a t q)
  then obtain q' where q: "map_zproof ty tm q = returnZ q'" "prf_rel R f (zprf_tr q) (zprf_tr q')"
    "zconst_free q'" "zno_class q'" by auto
  from tm ZAbsp.prems(3) obtain t' where t: "tm t = returnZ t'" "R (zdec t) (zdec t')" by auto
  with q show ?case by (auto intro: prf_rel.AbsP)
next
  case (ZAppt q t)
  then obtain q' where q: "map_zproof ty tm q = returnZ q'" "prf_rel R f (zprf_tr q) (zprf_tr q')"
    "zrf q \<longrightarrow> zrfn q'" "zconst_free q'" "zno_class q'" by auto
  from tm ZAppt.prems(3) obtain t' where t: "tm t = returnZ t'" "R (zdec t) (zdec t')"
    "beta_norm_term t' = Some t'" by auto
  have "(\<exists>a T r. q' = ZAbst a T r) \<longleftrightarrow> (\<exists>a T r. q = ZAbst a T r)" by (rule map_zproof_ZAbst[OF q(1)])
  with q t show ?case by (auto intro: prf_rel.PAppt)
next
  case (ZAppp q r)
  then obtain q' r' where "map_zproof ty tm q = returnZ q'" "prf_rel R f (zprf_tr q) (zprf_tr q')"
    "zconst_free q'" "zno_class q'"
    "map_zproof ty tm r = returnZ r'" "prf_rel R f (zprf_tr r) (zprf_tr r')"
    "zconst_free r'" "zno_class r'" by auto
  then show ?case by (auto intro: prf_rel.PAppp)
qed (auto intro: prf_rel.intros)

subsection \<open>The visible instantiation of \<open>znorm_proof\<close>\<close>

lemma znorm_proof_instT:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tyenv_zok \<theta>"
    "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v \<and> tcons \<theta> (TVar v S)"
  shows "\<exists>Us. mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) tvl = returnZ Us \<and>
    map typ_of Us = map (\<lambda>(v, S). tnorm \<theta> (TVar v S)) tvl"
proof -
  have "\<forall>x\<in>set tvl. \<exists>y. (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) x = returnZ y \<and> typ_of y = (\<lambda>(v, S). tnorm \<theta> (TVar v S)) x"
  proof
    fix x assume x: "x \<in> set tvl"
    obtain v S where vS: "x = (v, S)" by (cases x)
    with x assms(4) have "0 \<le> snd v" "tcons \<theta> (TVar v S)" by auto
    then have t: "typ_of (ZTVar v S) = TVar v S" "tcons \<theta> (typ_of (ZTVar v S))" by auto
    from znorm_type_ok[OF assms(1-3) t(2)] t(1) vS
    show "\<exists>y. (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) x = returnZ y \<and> typ_of y = (\<lambda>(v, S). tnorm \<theta> (TVar v S)) x"
      by auto
  qed
  from mapZ_ex[OF this] show ?thesis by blast
qed

lemma typ_of_zsubst_type_vis:
  assumes us: "map typ_of Us = map (\<lambda>(v, S). tnorm \<theta> (TVar v S)) tvl" and d: "distinct tvl"
    and nn: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v"
  shows "typ_of (zsubst_type (map_of (zip tvl Us)) T) =
    tsubst (\<lambda>v S. if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S) (typ_of T)"
proof (induction T)
  case (ZTVar v S)
  have len: "length tvl = length Us" using arg_cong[OF us, of length] by simp
  show ?case
  proof (cases "(v, S) \<in> set tvl")
    case True
    then obtain i where i: "i < length tvl" "tvl ! i = (v, S)" by (auto simp: in_set_conv_nth)
    have "map_of (zip tvl Us) (tvl ! i) = Some (Us ! i)" using map_of_zip_nth[OF len d, of i] i len by simp
    then have "map_of (zip tvl Us) (v, S) = Some (Us ! i)" using i(2) by simp
    moreover have "typ_of (Us ! i) = tnorm \<theta> (TVar v S)"
      using arg_cong[OF us, of "\<lambda>xs. xs ! i"] i len by simp
    moreover have "snd v \<noteq> -1" using True nn by auto
    ultimately show ?thesis using True by simp
  next
    case False
    then have "map_of (zip tvl Us) (v, S) = None" using map_of_zip_is_None[OF len] by simp
    with False show ?thesis by simp
  qed
qed (simp_all add: propT_def)

lemma zlookup_var_map_of: "zlookup_var xs v = map_of xs v"
  by (induction xs v rule: zlookup_var.induct) auto

lemma set_zdedup_vars: "set (zdedup_vars vs) = set vs"
  by (induction vs rule: zdedup_vars.induct) auto

lemma distinct_zdedup_vars: "distinct (zdedup_vars vs)"
  by (induction vs rule: zdedup_vars.induct) (auto simp: set_zdedup_vars)

lemma tsubst_TVar_id: "tsubst (\<lambda>v S. TVar v S) U = U"
  by (induction U) (auto intro: map_idI)

text \<open>Types whose type variables are visible or unbound, and annotations whose variables are.\<close>

definition ztyp_vis :: "(indexname \<times> psort) list \<Rightarrow> tyenv \<Rightarrow> ztyp \<Rightarrow> bool" where
  "ztyp_vis tvl \<theta> T \<longleftrightarrow> tcons \<theta> (typ_of T) \<and> (\<forall>(v, S)\<in>tvars (typ_of T). (v, S) \<in> set tvl \<or> vt_lookup \<theta> v = None)"

definition zann_vis :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> (indexname \<times> psort) list \<Rightarrow> indexname set \<Rightarrow> env \<Rightarrow> zterm \<Rightarrow> bool" where
  "zann_vis V tvl X env t \<longleftrightarrow>
    (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> T = ztyp_of (V x) \<and> typ_of T = V x \<and>
      (x \<in> X \<or> vt_lookup (tenv env) x = None)) \<and>
    (\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> x \<notin> X) \<and> (\<forall>T\<in>ztys t. ztyp_vis tvl (tyenv env) T) \<and>
    (\<exists>Ts U. has_type V Ts (zdec t) U)"

lemma tsubst_vis_tnorm:
  assumes ac: "tacyc \<theta>" and vis: "\<forall>(v, S)\<in>tvars U. (v, S) \<in> set tvl \<or> vt_lookup \<theta> v = None"
  shows "tsubst (\<lambda>v S. if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S) U = tnorm \<theta> U"
  unfolding tnorm_tsubst[of \<theta> U]
proof (rule tsubst_cong)
  fix v S assume "(v, S) \<in> tvars U"
  with vis show "(if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S) = tnorm \<theta> (TVar v S)"
    by (auto simp: tnorm_TVar[OF ac])
qed

lemma vars_zdec: "vars (zdec t) = {x. \<exists>T. (x, T) \<in> zvars t \<and> snd x \<noteq> -1}"
  by (induction t) (auto simp: of_class_def)

lemma tvars_tys_zdec: "U \<in> tys (zdec t) \<Longrightarrow> tvars U \<subseteq> (\<Union>T\<in>ztys t. tvars (typ_of T))"
proof (induction t)
  case (ZConst0 c)
  then show ?case using tvars_zconst_typ[of c "[]"] by simp
next
  case (ZConst1 c T)
  then show ?case using tvars_zconst_typ[of c "[typ_of T]"] by simp
next
  case (ZConst c Ts)
  then show ?case using tvars_zconst_typ[of c "map typ_of Ts"] by auto
qed (auto simp: of_class_def propT_def split: if_splits)

text \<open>
  The normalisation of a tight proof (with an environment and visible propositions): the
  annotations are related to their normalisations for every bridge, and types are normalised.
  The variables of the annotations are typed by \<open>V\<close> and are visible or unbound; the visible
  ones have typed normal forms (in a typing \<open>V'\<close>, which also types the instances of the others).
\<close>

lemma znorm_proof_rel:
  fixes V V' :: "indexname \<Rightarrow> ptyp" and env :: env and visible :: "pterm list" and p :: zproof
  defines "\<theta> \<equiv> tyenv env" and "tvl \<equiv> visible_tvars visible" and "X \<equiv> fst ` set (visible_vars visible)"
  defines "\<rho>v \<equiv> \<lambda>v S. if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S"
  assumes ne: "\<not> env_is_empty env" "visible \<noteq> []"
    and ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and et: "\<forall>U\<in>etys env. tcons \<theta> U"
    and zo: "tyenv_zok \<theta>" and zt: "tenv_zok ztargs env"
    and tv: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v \<and> tcons \<theta> (TVar v S)"
    and vv: "\<forall>(a, T)\<in>set (visible_vars visible). T = V a \<and> 0 \<le> snd a \<and> tvars T \<subseteq> set tvl"
    and vn: "\<forall>a\<in>X. \<exists>t' rb. norm_term env (Var a (tsubst \<rho>v (V a))) = return t' \<and>
      swf_tm ar rb (Var a (tsubst \<rho>v (V a))) \<and> has_type V' [] t' (tsubst \<rho>v (V a))"
    and vh: "\<forall>x. x \<notin> X \<longrightarrow> V' x = tsubst \<rho>v (V x)"
    and pa: "zprf_all (zann_vis V tvl X env) (ztyp_vis tvl \<theta>) p"
    and pc: "zconst_free p" "zno_class p" "zrf p"
  shows "\<exists>p'. znorm_proof ztargs env visible p = returnZ p' \<and>
    prf_rel (ann_zrel env) (tnorm \<theta>) (zprf_tr p) (zprf_tr p')"
proof -
  have dtv: "distinct tvl" by (simp add: tvl_def visible_tvars_def distinct_dedup)
  have tvn: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v" using tv by auto
  text \<open>The instantiation of types.\<close>
  obtain instT where instT: "(if vt_is_empty \<theta> then returnZ None
        else do {Us \<leftarrow> mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) tvl; returnZ (Some (zip tvl Us))}) = returnZ instT"
    and ity: "\<And>T. typ_of ((case instT of None \<Rightarrow> id | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs)) T)
      = tsubst \<rho>v (typ_of T)"
  proof (cases "vt_is_empty \<theta>")
    case True
    have "\<rho>v = (\<lambda>v S. TVar v S)" by (intro ext) (simp add: \<rho>v_def tnorm_empty[OF True])
    then show thesis using True by (intro that[of None]) (simp_all add: tsubst_TVar_id)
  next
    case False
    from znorm_proof_instT[OF ac tc zo tv] obtain Us where
      Us: "mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) tvl = returnZ Us"
        "map typ_of Us = map (\<lambda>(v, S). tnorm \<theta> (TVar v S)) tvl"
      by blast
    have len: "length Us = length tvl" using arg_cong[OF Us(2), of length] by simp
    show thesis
    proof (rule that[of "Some (zip tvl Us)"])
      show "(if vt_is_empty \<theta> then returnZ None
          else do {Us \<leftarrow> mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) tvl; returnZ (Some (zip tvl Us))}) =
          returnZ (Some (zip tvl Us))"
        using False Us(1) by simp
      show "typ_of ((case Some (zip tvl Us) of None \<Rightarrow> id
          | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs)) T) = tsubst \<rho>v (typ_of T)" for T
      proof (cases "tvl = []")
        case True
        then have "\<rho>v = (\<lambda>v S. TVar v S)" by (auto simp: \<rho>v_def)
        with True show ?thesis by (simp add: tsubst_TVar_id)
      next
        case False
        then have "\<not> List.null (zip tvl Us)" using len by (cases tvl; cases Us) auto
        with typ_of_zsubst_type_vis[OF Us(2) dtv tvn] show ?thesis by (simp add: \<rho>v_def)
      qed
    qed
  qed
  define ity where "ity = (case instT of None \<Rightarrow> id | Some xs \<Rightarrow> if List.null xs then id else zsubst_type (map_of xs))"
  have ity': "typ_of (ity T) = tsubst \<rho>v (typ_of T)" for T using ity by (simp add: ity_def)
  have vnorm: "tsubst \<rho>v U = tnorm \<theta> U" if "\<forall>(v, S)\<in>tvars U. (v, S) \<in> set tvl \<or> vt_lookup \<theta> v = None" for U
    using tsubst_vis_tnorm[OF ac that] by (simp add: \<rho>v_def)
  text \<open>The visible variables and their normal forms.\<close>
  have Vv: "typ_of (ztyp_of (V a)) = V a" "tvars (V a) \<subseteq> set tvl" if "a \<in> X" for a
  proof -
    from that obtain T where "(a, T) \<in> set (visible_vars visible)" by (auto simp: X_def)
    with vv have "T = V a" "tvars T \<subseteq> set tvl" by auto
    then show "tvars (V a) \<subseteq> set tvl" by simp
    then show "typ_of (ztyp_of (V a)) = V a" using tvn by (intro typ_of_ztyp_of) fastforce
  qed
  define vs where "vs = zdedup_vars (map (\<lambda>(a, T). (a, ity (ztyp_of T))) (visible_vars visible))"
  have svs: "set vs = (\<lambda>a. (a, ity (ztyp_of (V a)))) ` X"
    using vv by (force simp: vs_def set_zdedup_vars X_def)
  have dvs: "distinct vs" by (simp add: vs_def distinct_zdedup_vars)
  have zn: "\<exists>u. znorm_term ztargs env (ZVar a T) = returnZ u \<and>
      ok (norm_term env (Var a (tsubst \<rho>v (V a)))) (zdec u) \<and> has_type V' [] (zdec u) (tsubst \<rho>v (V a)) \<and>
      (\<exists>rb. swf_tm ar rb (Var a (tsubst \<rho>v (V a))))"
    if "(a, T) \<in> set vs" for a T
  proof -
    from that svs have a: "a \<in> X" and T: "T = ity (ztyp_of (V a))" by auto
    from vn a obtain t' rb where n: "norm_term env (Var a (tsubst \<rho>v (V a))) = return t'"
      and sw: "swf_tm ar rb (Var a (tsubst \<rho>v (V a)))" and ht: "has_type V' [] t' (tsubst \<rho>v (V a))" by blast
    have a0: "0 \<le> snd a" using a vv by (auto simp: X_def)
    have tT: "typ_of T = tsubst \<rho>v (V a)" by (simp add: T ity' Vv[OF a])
    have tcT: "tcons \<theta> (tsubst \<rho>v (V a))"
    proof -
      have "tsubst \<rho>v (V a) = tnorm \<theta> (V a)" using Vv(2)[OF a] by (intro vnorm) auto
      then show ?thesis using tcons_tnorm[OF ac] by simp
    qed
    have "\<exists>z'. znorm_term ztargs env (ZVar a T) = returnZ z' \<and> zdec z' = t'"
      by (rule znorm_term_sim[OF n]) (use a0 tT tcT ac tc et zo zt in \<open>auto simp: \<theta>_def\<close>)
    with n sw ht show ?thesis by (auto simp: return_def)
  qed
  have ex0: "\<exists>ys. mapZ f xs = returnZ ys" if "\<forall>x\<in>set xs. \<exists>y. f x = returnZ y" for f :: "indexname \<times> ztyp \<Rightarrow> zterm Z" and xs
    using that by (induction xs) auto
  have "\<forall>x\<in>set vs. \<exists>u. (\<lambda>(a, T). znorm_term ztargs env (ZVar a T)) x = returnZ u"
    using zn by fastforce
  from ex0[OF this] obtain us where us: "mapZ (\<lambda>(a, T). znorm_term ztargs env (ZVar a T)) vs = returnZ us"
    by blast
  have lus: "length us = length vs" using us
    by (induction vs arbitrary: us) (auto simp: bindZ_eq_returnZ)
  have usi: "znorm_term ztargs env (ZVar (fst (vs ! i)) (snd (vs ! i))) = returnZ (us ! i)" if "i < length vs" for i
    using us that by (induction vs arbitrary: us i) (auto simp: bindZ_eq_returnZ nth_Cons split: nat.splits)
  text \<open>The instantiation of variables.\<close>
  define inst where "inst = zsubst_term ity (zlookup_var (zip vs us))"
  define \<theta>v where "\<theta>v x = (if x \<in> X then zdec (the (map_of (zip vs us) (x, ity (ztyp_of (V x)))))
    else Var x (tsubst \<rho>v (V x)))" for x
  have lk: "map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u \<Longrightarrow> x \<in> X \<Longrightarrow>
      ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u) \<and> has_type V' [] (zdec u) (tsubst \<rho>v (V x)) \<and>
      (\<exists>rb. swf_tm ar rb (Var x (tsubst \<rho>v (V x))))" for x u
  proof -
    assume m: "map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u" and "x \<in> X"
    from m obtain i where i: "i < length vs" "vs ! i = (x, ity (ztyp_of (V x)))" "us ! i = u"
      using lus by (auto simp: in_set_zip dest!: map_of_SomeD)
    from zn[of x "ity (ztyp_of (V x))"] i nth_mem[OF i(1)] usi[OF i(1)] show ?thesis by auto
  qed
  have lkX: "\<exists>u. map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u" if "x \<in> X" for x
  proof -
    have "(x, ity (ztyp_of (V x))) \<in> set vs" using that svs by auto
    then show ?thesis using lus by (auto simp: map_of_zip_is_Some[symmetric])
  qed
  have lkN: "map_of (zip vs us) (x, T) = None" if "x \<notin> X" for x T
    using that svs lus by (auto simp: map_of_zip_is_None)
  have \<theta>v_ok: "proper (\<theta>v x) \<and> \<not> loose_bvar (\<theta>v x) 0" for x
  proof (cases "x \<in> X")
    case True
    from lkX[OF True] obtain u where "map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u" by blast
    with lk[OF this True] True have "has_type V' [] (\<theta>v x) (tsubst \<rho>v (V x))" by (simp add: \<theta>v_def)
    then show ?thesis using has_type_proper has_type_loose_bvar by fastforce
  qed (simp add: \<theta>v_def)
  have \<theta>v_ty: "has_type V' [] (\<theta>v x) (tsubst \<rho>v (V x))" for x
  proof (cases "x \<in> X")
    case True
    from lkX[OF True] obtain u where "map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u" by blast
    with lk[OF this True] True show ?thesis by (simp add: \<theta>v_def)
  next
    case False
    then have "V' x = tsubst \<rho>v (V x)" using vh by blast
    with False show ?thesis by (simp add: \<theta>v_def has_type.Var)
  qed
  text \<open>An annotation and its normalisation.\<close>
  have ann: "\<exists>t'. liftOZ (beta_norm_term (inst t)) = returnZ t' \<and> ann_zrel env (zdec t) (zdec t') \<and>
      beta_norm_term t' = Some t'"
    if za: "zann_vis V tvl X env t" for t
  proof -
    from za have zv: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> T = ztyp_of (V x) \<and> typ_of T = V x \<and>
        (x \<in> X \<or> vt_lookup (tenv env) x = None)"
      and zf: "\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> x \<notin> X" and zt': "\<forall>T\<in>ztys t. ztyp_vis tvl \<theta> T"
      and ht: "\<exists>Ts U. has_type V Ts (zdec t) U"
      by (auto simp: zann_vis_def \<theta>_def)
    have i1: "zdec (inst t) = psubst \<rho>v \<theta>v 0 (zdec t)"
      unfolding inst_def
    proof (rule zdec_zsubst_term)
      show "\<forall>T\<in>ztys t. typ_of (ity T) = tsubst \<rho>v (typ_of T)" by (simp add: ity')
      show "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
          zdec (case zlookup_var (zip vs us) (x, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity T)) = \<theta>v x"
      proof (intro ballI impI, clarify)
        fix x T assume xT: "(x, T) \<in> zvars t" "snd x \<noteq> -1"
        with zv have T: "T = ztyp_of (V x)" by auto
        show "zdec (case zlookup_var (zip vs us) (x, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity T)) = \<theta>v x"
        proof (cases "x \<in> X")
          case True
          with lkX[OF True] T show ?thesis by (auto simp: zlookup_var_map_of \<theta>v_def)
        next
          case False
          have "typ_of T = V x" using zv xT by auto
          with False lkN[OF False] T xT(2) show ?thesis by (simp add: zlookup_var_map_of \<theta>v_def ity')
        qed
      qed
      show "\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> zlookup_var (zip vs us) (x, ity T) = None"
        using zf lkN by (auto simp: zlookup_var_map_of)
      show "\<forall>x. \<not> loose_bvar (\<theta>v x) 0" using \<theta>v_ok by blast
    qed
    from ht obtain Ts U where htU: "has_type V Ts (zdec t) U" by blast
    have "has_type V' (map (tsubst \<rho>v) Ts @ []) (psubst \<rho>v \<theta>v (integer_of_nat (length Ts)) (zdec t)) (tsubst \<rho>v U)"
      by (rule has_type_psubst[OF htU]) (use \<theta>v_ty in auto)
    moreover have "psubst \<rho>v \<theta>v (integer_of_nat (length Ts)) (zdec t) = psubst \<rho>v \<theta>v 0 (zdec t)"
      using \<theta>v_ok by (intro psubst_closed_lev) auto
    ultimately have hi: "has_type V' (map (tsubst \<rho>v) Ts) (zdec (inst t)) (tsubst \<rho>v U)" by (simp add: i1)
    from beta_norm_term_term[OF hi] obtain t' where bt: "beta_norm_term (inst t) = Some t'" by blast
    have pi: "proper (zdec (inst t))" by (rule has_type_proper[OF hi])
    from beta_norm_term_beta[OF bt pi] have b: "proper (zdec t')" "tr (zdec (inst t)) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec t')" by auto
    have rel: "ann_zrel env (zdec t) (zdec t')"
      unfolding ann_zrel_def
    proof (intro allI impI)
      fix \<rho> \<theta>0 \<rho>' \<sigma>' \<theta>' and lev :: integer assume zb: "zbridge env \<rho> \<theta>0 \<rho>' \<sigma>' \<theta>'" and lev: "0 \<le> lev"
      show "ann_eq (Some (psubst \<rho>' \<theta>' lev (zdec t))) (Some (psubst \<rho> \<theta>0 lev (zdec t')))"
      proof (rule ann_eq_zinst[OF zb b(2) b(1) i1 _ _ _ lev])
        show "\<forall>x. proper (\<theta>v x) \<and> \<not> loose_bvar (\<theta>v x) 0" using \<theta>v_ok by blast
        show "\<forall>x\<in>vars (zdec t). (\<exists>U u rb. ok (norm_term env (Var x U)) u \<and> \<theta>v x = u \<and> swf_tm ar rb (Var x U)) \<or>
            (vt_lookup (tenv env) x = None \<and> (\<exists>U. \<theta>v x = Var x U))"
        proof
          fix x assume "x \<in> vars (zdec t)"
          then obtain T where xT: "(x, T) \<in> zvars t" "snd x \<noteq> -1" by (auto simp: vars_zdec)
          show "(\<exists>U u rb. ok (norm_term env (Var x U)) u \<and> \<theta>v x = u \<and> swf_tm ar rb (Var x U)) \<or>
              (vt_lookup (tenv env) x = None \<and> (\<exists>U. \<theta>v x = Var x U))"
          proof (cases "x \<in> X")
            case True
            from lkX[OF True] obtain u where m: "map_of (zip vs us) (x, ity (ztyp_of (V x))) = Some u" by blast
            from lk[OF m True] m True show ?thesis by (auto simp: \<theta>v_def)
          next
            case False
            with zv xT show ?thesis by (auto simp: \<theta>v_def)
          qed
        qed
        show "\<forall>U\<in>tys (zdec t). tsubst \<rho> (tsubst \<rho>v U) = tsubst \<rho>' U"
        proof
          fix U assume U: "U \<in> tys (zdec t)"
          have "\<forall>(v, S)\<in>tvars U. (v, S) \<in> set tvl \<or> vt_lookup \<theta> v = None"
            using tvars_tys_zdec[OF U] zt' by (fastforce simp: ztyp_vis_def)
          then have "tsubst \<rho>v U = tnorm \<theta> U" by (rule vnorm)
          moreover have "tcons \<theta> U" using tcons_tys_zdec[of t \<theta>] zt' U by (auto simp: ztyp_vis_def)
          ultimately show "tsubst \<rho> (tsubst \<rho>v U) = tsubst \<rho>' U" using zb by (auto simp: zbridge_def \<theta>_def)
        qed
      qed
    qed
    have "beta_norm_term t' = Some t'" by (rule beta_norm_term_idem[OF bt])
    with bt rel show ?thesis by auto
  qed
  text \<open>The mapped proof.\<close>
  from map_zproof_rel[OF pc(1,2) pa, of "\<lambda>t. liftOZ (beta_norm_term (inst t))" "ann_zrel env" ity "tnorm \<theta>"]
  obtain p' where p': "map_zproof ity (\<lambda>t. liftOZ (beta_norm_term (inst t))) p = returnZ p'"
    "prf_rel (ann_zrel env) (tnorm \<theta>) (zprf_tr p) (zprf_tr p')" "zrf p \<longrightarrow> zrfn p'"
  proof -
    have "\<exists>p'. map_zproof ity (\<lambda>t. liftOZ (beta_norm_term (inst t))) p = returnZ p' \<and>
        prf_rel (ann_zrel env) (tnorm \<theta>) (zprf_tr p) (zprf_tr p') \<and> (zrf p \<longrightarrow> zrfn p') \<and> zconst_free p' \<and> zno_class p'"
    proof (rule map_zproof_rel[OF pc(1,2) pa])
      show "\<exists>t'. liftOZ (beta_norm_term (inst t)) = returnZ t' \<and> ann_zrel env (zdec t) (zdec t') \<and>
          beta_norm_term t' = Some t'" if "zann_vis V tvl X env t" for t
        by (rule ann[OF that])
      show "typ_of (ity T) = tnorm \<theta> (typ_of T)" if "ztyp_vis tvl \<theta> T" for T
        using that by (simp add: ity' ztyp_vis_def vnorm)
    qed
    then show thesis using that by blast
  qed
  have bp: "beta_norm_prooft p' = Some p'" by (rule beta_norm_prooft_zrfn) (use p'(3) pc(3) in blast)
  have "znorm_proof ztargs env visible p = returnZ p'"
    using ne unfolding znorm_proof_def \<theta>_def[symmetric] tvl_def[symmetric] instT
    by (simp add: Let_def ity_def[symmetric] vs_def[symmetric] inst_def[symmetric] us p'(1) bp)
  with p'(2) show ?thesis by blast
qed

lemma norm_ann_zrel:
  assumes n: "ok (norm_term env t0) t0'" and sw: "swf_tm ar rb t0" and v: "\<forall>x\<in>vars t0. 0 \<le> snd x"
  shows "ann_zrel env t0 t0'"
  unfolding ann_zrel_def
proof (intro allI impI)
  fix \<rho> \<theta> \<rho>' \<sigma>' \<theta>' and lev :: integer assume zb: "zbridge env \<rho> \<theta> \<rho>' \<sigma>' \<theta>'" and lev: "0 \<le> lev"
  from zb have ie: "iext env \<rho> (isubst \<theta>) \<rho>' \<sigma>'" and swf: "swf_env ar env"
    and smeq: "\<And>t. sm \<rho>' \<sigma>' t \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t)"
    and cl: "\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0" and cl': "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0"
    and nn: "\<forall>x. \<forall>y\<in>vars (\<theta> x). 0 \<le> snd y"
    by (auto simp: zbridge_def)
  have clx: "proper (\<theta> x)" "\<not> loose_bvar (\<theta> x) 0" "proper (\<theta>' x)" "\<not> loose_bvar (\<theta>' x) 0" for x
    using cl cl' by blast+
  have sw': "swf_tm ar rb t0'" using norm_term_swf_tm[OF n swf sw] by simp
  have lv: "psubst \<rho>' \<theta>' lev s = psubst \<rho>' \<theta>' 0 s" "psubst \<rho> \<theta> lev s = psubst \<rho> \<theta> 0 s" for s
    using psubst_closed_lev[of s \<theta>' lev \<rho>'] psubst_closed_lev[of s \<theta> lev \<rho>] clx lev by simp_all
  have "tr (psubst \<rho> \<theta> 0 t0') = sm \<rho> (isubst \<theta>) t0'" by (rule tr_psubst_sm) (use clx in blast)
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' t0" by (rule iext_norm_term[OF ie rigid_isubst swf sw n])
  also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 t0)" by (rule smeq)
  finally have e: "tr (remove_types (psubst \<rho>' \<theta>' 0 t0)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (psubst \<rho> \<theta> 0 t0'))"
    by (rule remove_types_equiv[OF equiv_sym])
  have "proper t0'" using sw' by (simp add: swf_tm_def)
  then have p: "proper (psubst \<rho> \<theta> 0 t0')" using clx by (intro proper_psubst) auto
  have "\<forall>x\<in>vars (psubst \<rho> \<theta> 0 t0'). 0 \<le> snd x" using nn by (auto simp: vars_psubst)
  with e p show "ann_eq (Some (psubst \<rho>' \<theta>' lev t0)) (Some (psubst \<rho> \<theta> lev t0'))"
    by (simp add: ann_eq_def lv)
qed

lemma prf_rel_zrel_inst:
  assumes "prf_rel (ann_zrel env) (tnorm (tyenv env)) p p'" "prf_all P (tcons (tyenv env)) p"
    "zbridge env \<rho> \<theta> \<rho>' \<sigma>' \<theta>'" "0 \<le> lev"
  shows "prf_aeq (prf_inst \<rho>' \<theta>' lev p) (prf_inst \<rho> \<theta> lev p')"
proof (rule prf_rel_inst[OF assms(1,2) _ _ assms(4)])
  show "ann_eq (Some (psubst \<rho>' \<theta>' lev t)) (Some (psubst \<rho> \<theta> lev t'))"
    if "ann_zrel env t t'" "0 \<le> lev" for t t' lev
    using that assms(3) by (auto simp: ann_zrel_def)
  show "tsubst \<rho> (tnorm (tyenv env) T) = tsubst \<rho>' T" if "tcons (tyenv env) T" for T
    using that assms(3) by (auto simp: zbridge_def)
qed

subsection \<open>The composed tight proof\<close>

lemma length_mapZ: "mapZ f xs = returnZ ys \<Longrightarrow> length ys = length xs"
  by (induction xs arbitrary: ys) (auto simp: bindZ_eq_returnZ)

lemma zbicompose_core_eq:
  fixes ta env flatten Bs As A oldAs n m visible p q
  defines "normt \<equiv> \<lambda>t. do {t' \<leftarrow> zterm_of ta t; znorm_term ta env t'}"
  defines "la \<equiv> integer_of_nat (length As)" and "lb \<equiv> integer_of_nat (length Bs)"
  assumes Ns: "mapZ normt (Bs @ As) = returnZ Ns"
    and asm: "(if n > 0 then (case A of None \<Rightarrow> raiseZ ZOption
        | Some C \<Rightarrow> do {C' \<leftarrow> normt C; returnZ [zmk_asm_prf C' n m]}) else returnZ []) = returnZ asm"
    and Os: "mapZ (zterm_of ta) oldAs = returnZ Os" and len: "length oldAs = length As"
    and fs: "(if flatten then mapZ (\<lambda>x. znorm_proof ta env visible (zflatten_params_proof 0 0 n x))
        (zip Os (downto (la - 1) 0)) else returnZ (map (\<lambda>x. ZBoundp (snd x)) (zip Os (downto (la - 1) 0)))) =
      returnZ fs"
  shows "zbicompose_core ta env flatten Bs As A oldAs n m visible p q =
    returnZ (ZAbsps Ns (ZAppp (ZAppps q (map ZBoundp (downto (lb + la - 1) la))) (ZAppps p (asm @ fs))))"
proof -
  have lO: "length Os = length As" using length_mapZ[OF Os] len by simp
  have ld: "length (downto (la - 1) 0) = length As"
    by (simp add: la_def downto_map integer_reps integer_of_nat.rep_eq)
  have z: "zip_eq Os (downto (la - 1) 0) = return (zip Os (downto (la - 1) 0))"
    using ok_zip_eq[of Os "downto (la - 1) 0"] lO ld by (simp add: return_def)
  show ?thesis
    using Ns asm Os fs z
    by (simp add: zbicompose_core_def Let_def normt_def[symmetric] la_def[symmetric] lb_def[symmetric]
        cong: if_cong)
qed

end

end
