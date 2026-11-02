section \<open>Hidden variables of tight proofs\<close>

theory ZTerm_Hidden
  imports ZTerm_Thm
begin

text \<open>
  Isabelle identifies the schematic variables of tight terms by their names and types, the
  judgment of this formalisation by their names. A tight proof may contain variables with the
  same name and different types that do not occur in its theorem (hidden variables): the
  composition of tight proofs renames variables of the rule to names of hidden variables of its
  proof, and the normalisation instantiates a hidden variable whose type becomes that of a visible
  variable of the same name. The invariant of tight proofs therefore relates a tight proof to a
  valid tight proof whose hidden variables have their own names: the annotations of the former are
  equivalent to instances of those of the latter, in which every pair of a name and a type has a
  name of its own (\<open>sepz\<close>).
\<close>

subsection \<open>Renaming the variables of tight terms\<close>

instance ztyp :: countable
  by countable_datatype

definition enc_name :: "name \<Rightarrow> ztyp \<Rightarrow> name" where
  "enc_name n T = String.implode (replicate (to_nat (n, T)) CHR ''a'')"

lemma enc_name_inj: "enc_name n T = enc_name n' T' \<longleftrightarrow> n = n' \<and> T = T'"
proof
  assume "enc_name n T = enc_name n' T'"
  then have "length (String.explode (enc_name n T)) = length (String.explode (enc_name n' T'))" by simp
  then have "to_nat (n, T) = to_nat (n', T')" by (simp add: enc_name_def)
  then show "n = n' \<and> T = T'" by simp
qed simp

text \<open>Renaming of the schematic variables (index other than \<open>-1\<close>) by a function of their names
  and types.\<close>

fun zrenv :: "(indexname \<Rightarrow> ztyp \<Rightarrow> indexname) \<Rightarrow> zterm \<Rightarrow> zterm" where
  "zrenv f (ZVar x T) = (if snd x = -1 then ZVar x T else ZVar (f x T) T)"
| "zrenv f (ZAbs a T t) = ZAbs a T (zrenv f t)"
| "zrenv f (ZApp t u) = ZApp (zrenv f t) (zrenv f u)"
| "zrenv f t = t"

definition idx_pres :: "(indexname \<Rightarrow> ztyp \<Rightarrow> indexname) \<Rightarrow> bool" where
  "idx_pres f \<longleftrightarrow> (\<forall>x T. snd (f x T) = snd x)"

definition sepn :: "indexname \<Rightarrow> ztyp \<Rightarrow> indexname" where
  "sepn x T = (enc_name (fst x) T, snd x)"

abbreviation sepz :: "zterm \<Rightarrow> zterm" where
  "sepz \<equiv> zrenv sepn"

lemma idx_pres_snd: "idx_pres f \<Longrightarrow> snd (f x T) = snd x"
  by (cases x) (simp add: idx_pres_def)

lemma idx_pres_sepn[simp]: "idx_pres sepn"
  by (simp add: idx_pres_def sepn_def)

lemma snd_sepn[simp]: "snd (sepn x T) = snd x"
  by (simp add: sepn_def)

lemma sepn_inj: "sepn x T = sepn y U \<longleftrightarrow> x = y \<and> T = U"
  by (cases x; cases y) (auto simp: sepn_def enc_name_inj)

lemma zrenv_comp:
  "idx_pres f \<Longrightarrow> zrenv g (zrenv f t) = zrenv (\<lambda>x T. g (f x T) T) t"
  by (induction t) (auto simp: idx_pres_def)

context prf_wf_csig
begin

lemma zrenv_cong:
  "(\<And>x T. (x, T) \<in> zvars t \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> f x T = g x T) \<Longrightarrow> zrenv f t = zrenv g t"
  by (induction t) auto

lemma zrenv_id: "(\<And>x T. (x, T) \<in> zvars t \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> f x T = x) \<Longrightarrow> zrenv f t = t"
  by (induction t) auto

lemma zvars_zrenv: "zvars (zrenv f t) = (\<lambda>(x, T). (if snd x = -1 then x else f x T, T)) ` zvars t"
  by (induction t) (auto simp: image_Un)

lemma ztys_zrenv[simp]: "ztys (zrenv f t) = ztys t"
  by (induction t) auto

lemma zdec_zrenv_loose[simp]: "loose_bvar (zdec (zrenv f t)) k = loose_bvar (zdec t) k"
  by (induction t arbitrary: k) auto

lemma zincr_bv_zrenv: "zincr_bv inc lev (zrenv f t) = zrenv f (zincr_bv inc lev t)"
  by (induction inc lev t rule: zincr_bv.induct) auto

lemma zincr_boundvars_zrenv: "zincr_boundvars inc (zrenv f t) = zrenv f (zincr_boundvars inc t)"
  by (simp add: zincr_boundvars_def zincr_bv_zrenv)

lemma zsubst_bound_zrenv: "zsubst_bound (zrenv f a) lev (zrenv f t) = zrenv f (zsubst_bound a lev t)"
  by (induction a lev t rule: zsubst_bound.induct) (auto simp: zincr_boundvars_zrenv)

lemma subst_term_bound_zrenv: "subst_term_bound (zrenv f a) (zrenv f t) = zrenv f (subst_term_bound a t)"
  by (simp add: subst_term_bound_def zsubst_bound_zrenv)

lemma zrenv_ZAbs_iff: "zrenv f t = ZAbs a T b \<longleftrightarrow> (\<exists>b'. t = ZAbs a T b' \<and> b = zrenv f b')"
  by (cases t) auto

lemma zrenv_ZApp_iff: "zrenv f t = ZApp u v \<longleftrightarrow> (\<exists>u' v'. t = ZApp u' v' \<and> u = zrenv f u' \<and> v = zrenv f v')"
  by (cases t) auto

lemma zrenv_is_ZAbs: "(\<exists>a T b. zrenv f t = ZAbs a T b) \<longleftrightarrow> (\<exists>a T b. t = ZAbs a T b)"
  by (cases t) auto

lemma beta_norm_term_atom:
  "\<not> (\<exists>a T b. t = ZAbs a T b) \<Longrightarrow> \<not> (\<exists>g u. t = ZApp g u) \<Longrightarrow> beta_norm_term t = Some t"
  by (subst beta_norm_term.simps) (cases t; auto)

lemma beta_norm_prooft_atom:
  "\<not> (\<exists>a T q. p = ZAbst a T q) \<Longrightarrow> \<not> (\<exists>g u. p = ZAppt g u) \<Longrightarrow> beta_norm_prooft p = Some p"
  by (subst beta_norm_prooft.simps) (cases p; auto)

lemma beta_norm_term_zrenv_some:
  "beta_norm_term t = Some t' \<Longrightarrow> beta_norm_term (zrenv f t) = Some (zrenv f t')"
proof (induction t t' rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn t r)
  note IH = "1.IH" and h = "1.hyps"
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with h obtain b' where "bn b = Some b'" "r = ZAbs a T b'" by (auto split: Option.bind_splits)
    with IH ZAbs show ?thesis by (subst beta_norm_term.simps) auto
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>a T body. g = ZAbs a T body")
      case True
      then obtain a T body where g: "g = ZAbs a T body" by blast
      with h ZApp have "bn (subst_term_bound u body) = Some r" by simp
      from IH[OF this] show ?thesis
        by (subst beta_norm_term.simps) (simp add: ZApp g subst_term_bound_zrenv)
    next
      case False
      with h ZApp obtain nf where nf: "bn g = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound u body)
          | _ \<Rightarrow> Option.bind (bn u) (\<lambda>nu. Some (ZApp nf nu))) = Some r"
        by (cases g) (auto split: Option.bind_splits)
      have g': "\<not> (\<exists>a T b. zrenv f g = ZAbs a T b)" using False by (simp add: zrenv_is_ZAbs)
      have ng: "beta_norm_term (zrenv f g) = Some (zrenv f nf)" by (rule IH[OF nf])
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbs a T body")
        case True
        then obtain a T body where n: "nf = ZAbs a T body" by blast
        with rest have "bn (subst_term_bound u body) = Some r" by simp
        from IH[OF this] have "beta_norm_term (subst_term_bound (zrenv f u) (zrenv f body)) = Some (zrenv f r)"
          by (simp add: subst_term_bound_zrenv)
        then show ?thesis using g' ng n
          by (subst beta_norm_term.simps) (cases "zrenv f g"; simp add: ZApp)
      next
        case nA: False
        with rest obtain nu where nu: "bn u = Some nu" "r = ZApp nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        have nf': "\<not> (\<exists>a T b. zrenv f nf = ZAbs a T b)" using nA by (simp add: zrenv_is_ZAbs)
        from IH[OF nu(1)] g' ng nf' nu(2) show ?thesis
          by (subst beta_norm_term.simps) (cases "zrenv f g"; cases "zrenv f nf"; simp add: ZApp)
      qed
    qed
  qed (use h in \<open>auto simp: beta_norm_term_atom\<close>)
qed

lemma beta_norm_term_zrenv_some_rev:
  "beta_norm_term s = Some s' \<Longrightarrow> s = zrenv f t \<Longrightarrow> \<exists>t'. beta_norm_term t = Some t' \<and> s' = zrenv f t'"
proof (induction s s' arbitrary: t rule: beta_norm_term.raw_induct[rotated, consumes 1])
  case (1 bn s r)
  note IH = "1.IH" and h = "1.hyps" and st = "1.prems"
  show ?case
  proof (cases t)
    case (ZAbs a T b)
    with st h obtain b' where "bn (zrenv f b) = Some b'" "r = ZAbs a T b'" by (auto split: Option.bind_splits)
    with IH ZAbs show ?thesis by (subst beta_norm_term.simps) fastforce
  next
    case (ZApp g u)
    show ?thesis
    proof (cases "\<exists>a T body. g = ZAbs a T body")
      case True
      then obtain a T body where g: "g = ZAbs a T body" by blast
      with h st ZApp have "bn (subst_term_bound (zrenv f u) (zrenv f body)) = Some r" by simp
      from IH[OF this subst_term_bound_zrenv] show ?thesis
        by (subst beta_norm_term.simps) (simp add: ZApp g)
    next
      case False
      have g': "\<not> (\<exists>a T b. zrenv f g = ZAbs a T b)" using False by (simp add: zrenv_is_ZAbs)
      with h st ZApp obtain nf where nf: "bn (zrenv f g) = Some nf"
        and rest: "(case nf of ZAbs _ _ body \<Rightarrow> bn (subst_term_bound (zrenv f u) body)
          | _ \<Rightarrow> Option.bind (bn (zrenv f u)) (\<lambda>nu. Some (ZApp nf nu))) = Some r"
        by (cases "zrenv f g") (auto split: Option.bind_splits)
      from IH[OF nf HOL.refl] obtain nf0 where nf0: "beta_norm_term g = Some nf0" "nf = zrenv f nf0" by blast
      show ?thesis
      proof (cases "\<exists>a T body. nf0 = ZAbs a T body")
        case True
        then obtain a T body where n: "nf0 = ZAbs a T body" by blast
        with rest nf0 have "bn (subst_term_bound (zrenv f u) (zrenv f body)) = Some r" by simp
        from IH[OF this subst_term_bound_zrenv] obtain t' where
          "beta_norm_term (subst_term_bound u body) = Some t'" "r = zrenv f t'" by blast
        then show ?thesis using False nf0 n
          by (subst beta_norm_term.simps) (cases g; simp add: ZApp)
      next
        case nA: False
        have nf': "\<not> (\<exists>a T b. nf = ZAbs a T b)" using nA nf0(2) by (simp add: zrenv_is_ZAbs)
        with rest obtain nu where nu: "bn (zrenv f u) = Some nu" "r = ZApp nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        from IH[OF nu(1) HOL.refl] obtain nu0 where "beta_norm_term u = Some nu0" "nu = zrenv f nu0" by blast
        then show ?thesis using False nf0 nA nu(2)
          by (subst beta_norm_term.simps) (cases g; cases nf0; simp add: ZApp)
      qed
    qed
  qed (use h st in \<open>auto simp: beta_norm_term_atom split: if_splits\<close>)
qed

lemma beta_norm_term_zrenv: "beta_norm_term (zrenv f t) = map_option (zrenv f) (beta_norm_term t)"
proof (cases "beta_norm_term t")
  case None
  show ?thesis
  proof (rule ccontr)
    assume "beta_norm_term (zrenv f t) \<noteq> map_option (zrenv f) (beta_norm_term t)"
    with None obtain s' where "beta_norm_term (zrenv f t) = Some s'" by auto
    from beta_norm_term_zrenv_some_rev[OF this HOL.refl] None show False by auto
  qed
qed (simp add: beta_norm_term_zrenv_some)


subsection \<open>Renaming the variables of tight proofs\<close>

fun zrenp :: "(indexname \<Rightarrow> ztyp \<Rightarrow> indexname) \<Rightarrow> zproof \<Rightarrow> zproof" where
  "zrenp f (ZAbst a T p) = ZAbst a T (zrenp f p)"
| "zrenp f (ZAbsp a t p) = ZAbsp a (zrenv f t) (zrenp f p)"
| "zrenp f (ZAppt p t) = ZAppt (zrenp f p) (zrenv f t)"
| "zrenp f (ZAppp p q) = ZAppp (zrenp f p) (zrenp f q)"
| "zrenp f p = p"

lemma zrenp_comp: "idx_pres f \<Longrightarrow> zrenp g (zrenp f p) = zrenp (\<lambda>x T. g (f x T) T) p"
  by (induction p) (simp_all add: zrenv_comp)

lemma zrenp_ZAbst_iff: "zrenp f p = ZAbst a T q \<longleftrightarrow> (\<exists>q'. p = ZAbst a T q' \<and> q = zrenp f q')"
  by (cases p) auto

lemma zrenp_is_ZAbst: "(\<exists>a T q. zrenp f p = ZAbst a T q) \<longleftrightarrow> (\<exists>a T q. p = ZAbst a T q)"
  by (cases p) auto

lemma zsubst_proof_bound_zrenp:
  "zsubst_proof_bound (zrenv f a) lev (zrenp f p) = zrenp f (zsubst_proof_bound a lev p)"
  by (induction a lev p rule: zsubst_proof_bound.induct) (simp_all add: zsubst_bound_zrenv)

lemma subst_proof_bound_zrenp: "subst_proof_bound (zrenv f a) (zrenp f p) = zrenp f (subst_proof_bound a p)"
  by (simp add: subst_proof_bound_def zsubst_proof_bound_zrenp)

lemma zconst_free_zrenp[simp]: "zconst_free (zrenp f p) = zconst_free p"
  by (induction p) auto

lemma zno_class_zrenp[simp]: "zno_class (zrenp f p) = zno_class p"
  by (induction p) auto

lemma zrf_zrenp[simp]: "zrf (zrenp f p) = zrf p"
  by (induction p) (auto simp: zrenp_ZAbst_iff)

lemma zlb_zrenp[simp]: "zlb n (zrenp f p) = zlb n p"
  by (induction n p rule: zlb.induct) auto

lemma zprf_all_zrenp: "zprf_all P Q (zrenp f p) = zprf_all (\<lambda>t. P (zrenv f t)) Q p"
  by (induction p) auto

lemma beta_norm_prooft_zrenp_some:
  "beta_norm_prooft p = Some p' \<Longrightarrow> beta_norm_prooft (zrenp f p) = Some (zrenp f p')"
proof (induction p p' rule: beta_norm_prooft.raw_induct[rotated, consumes 1])
  case (1 bn p r)
  note IH = "1.IH" and h = "1.hyps"
  show ?case
  proof (cases p)
    case (ZAbst a T q)
    with h obtain q' where "bn q = Some q'" "r = ZAbst a T q'" by (auto split: Option.bind_splits)
    with IH ZAbst show ?thesis by (subst beta_norm_prooft.simps) auto
  next
    case (ZAppt g u)
    show ?thesis
    proof (cases "\<exists>a T body. g = ZAbst a T body")
      case True
      then obtain a T body where g: "g = ZAbst a T body" by blast
      with h ZAppt have "bn (subst_proof_bound u body) = Some r" by simp
      from IH[OF this] show ?thesis
        by (subst beta_norm_prooft.simps) (simp add: ZAppt g subst_proof_bound_zrenp)
    next
      case False
      with h ZAppt obtain nf where nf: "bn g = Some nf"
        and rest: "(case nf of ZAbst _ _ body \<Rightarrow> bn (subst_proof_bound u body)
          | _ \<Rightarrow> Option.bind (beta_norm_term u) (\<lambda>nu. Some (ZAppt nf nu))) = Some r"
        by (cases g) (auto split: Option.bind_splits)
      have g': "\<not> (\<exists>a T b. zrenp f g = ZAbst a T b)" using False by (simp add: zrenp_is_ZAbst)
      have ng: "beta_norm_prooft (zrenp f g) = Some (zrenp f nf)" by (rule IH[OF nf])
      show ?thesis
      proof (cases "\<exists>a T body. nf = ZAbst a T body")
        case True
        then obtain a T body where n: "nf = ZAbst a T body" by blast
        with rest have "bn (subst_proof_bound u body) = Some r" by simp
        from IH[OF this] have "beta_norm_prooft (subst_proof_bound (zrenv f u) (zrenp f body)) = Some (zrenp f r)"
          by (simp add: subst_proof_bound_zrenp)
        then show ?thesis using g' ng n
          by (subst beta_norm_prooft.simps) (cases "zrenp f g"; simp add: ZAppt)
      next
        case nA: False
        with rest obtain nu where nu: "beta_norm_term u = Some nu" "r = ZAppt nf nu"
          by (cases nf) (auto split: Option.bind_splits)
        have nf': "\<not> (\<exists>a T b. zrenp f nf = ZAbst a T b)" using nA by (simp add: zrenp_is_ZAbst)
        from beta_norm_term_zrenv[of f u] nu(1) g' ng nf' nu(2) show ?thesis
          by (subst beta_norm_prooft.simps) (cases "zrenp f g"; cases "zrenp f nf"; simp add: ZAppt)
      qed
    qed
  qed (use h in \<open>auto simp: beta_norm_prooft_atom\<close>)
qed

lemma Some_ZOk_returnZ: "Some (ZOk x) = returnZ x"
  by (simp add: returnZ_def)

lemma zvars_zterm_of: "zterm_of ta A = returnZ z \<Longrightarrow> (x, T) \<in> zvars z \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> x \<in> vars A"
proof (induction ta A arbitrary: z rule: zterm_of.induct)
  case (4 ta c T)
  from "4.prems"(1) obtain Ts where
    "z = (case Ts of [] \<Rightarrow> ZConst0 c | [U] \<Rightarrow> ZConst1 c (ztyp_of U) | _ \<Rightarrow> ZConst c (map ztyp_of Ts))"
    by (auto simp: bindZ_eq_returnZ)
  then have "zvars z = {}" by (auto split: list.splits)
  with "4.prems"(2) show ?case by simp
next
  case (5 ta a T b)
  then show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (6 ta t u)
  then show ?case by (auto simp: bindZ_eq_returnZ Some_ZOk_returnZ split: option.splits if_splits) (blast+)
qed auto

lemma zrenv_zterm_of:
  "zterm_of ta A = returnZ z \<Longrightarrow> (\<And>x T. x \<in> vars A \<Longrightarrow> f x T = x) \<Longrightarrow> zrenv f z = z"
  by (rule zrenv_id) (use zvars_zterm_of in blast)

text \<open>Renamings of names only (of schematic variables) commute with lifting.\<close>

definition nren :: "(name \<Rightarrow> name) \<Rightarrow> indexname \<Rightarrow> ztyp \<Rightarrow> indexname" where
  "nren \<mu> x T = (\<mu> (fst x), snd x)"

lemma idx_pres_nren[simp]: "idx_pres (nren \<mu>)"
  by (simp add: idx_pres_def nren_def)

lemma zcombound_zrenv: "zrenv f (zcombound t n k) = zcombound (zrenv f t) n k"
  by (induction t n k rule: zcombound.induct) simp_all

lemma zlift_term_nren:
  "0 \<le> inc \<Longrightarrow> \<forall>(x, T)\<in>zvars t. -1 \<le> snd x \<Longrightarrow>
    zlift_term inc Ts lev (zrenv (nren \<mu>) t) = zrenv (nren \<mu>) (zlift_term inc Ts lev t)"
proof (induction inc Ts lev t rule: zlift_term.induct)
  case (1 inc Ts lev x i T)
  then show ?case by (cases "i \<ge> 0") (auto simp: nren_def zcombound_zrenv)
qed auto

lemma zlift_term'_nren:
  "0 \<le> inc \<Longrightarrow> \<forall>(x, T)\<in>zvars t. -1 \<le> snd x \<Longrightarrow>
    zlift_term' inc Ts lev (zrenv (nren \<mu>) t) = zrenv (nren \<mu>) (zlift_term' inc Ts lev t)"
  by (simp add: zlift_term'_def zlift_term_nren)

lemma zlift_prf_nren:
  assumes "zlift_prf inc Ts lev p = returnZ q" "zconst_free p" "0 \<le> inc"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) p"
  shows "zlift_prf inc Ts lev (zrenp (nren \<mu>) p) = returnZ (zrenp (nren \<mu>) q)"
  using assms
proof (induction inc Ts lev p arbitrary: q rule: zlift_prf.induct)
  case (2 inc Ts lev a t p)
  then show ?case using zlift_term'_nren[of inc t Ts lev \<mu>] by (auto simp: bindZ_eq_returnZ)
next
  case (3 inc Ts lev p t)
  then show ?case using zlift_term'_nren[of inc t Ts lev \<mu>] by (auto simp: bindZ_eq_returnZ)
next
  case (4 inc Ts lev p q)
  then show ?case by (auto simp: bindZ_eq_returnZ Some_ZOk_returnZ)
qed (auto simp: bindZ_eq_returnZ)

lemma zrenp_ZAppps: "zrenp f (ZAppps p qs) = ZAppps (zrenp f p) (map (zrenp f) qs)"
  by (induction qs arbitrary: p) (simp_all add: ZAppps_def)

lemma zrenp_ZAbsps: "zrenp f (ZAbsps ts p) = ZAbsps (map (zrenv f) ts) (zrenp f p)"
  by (induction ts) (simp_all add: ZAbsps_def)

lemma zrenp_foldr_zmk_app:
  "zrenp f (snd (snd x)) = snd (snd x) \<Longrightarrow> zrenp f (snd (snd (foldr zmk_app bs x))) = snd (snd (foldr zmk_app bs x))"
proof (induction bs arbitrary: x)
  case (Cons b bs)
  obtain i' j' r where r: "foldr zmk_app bs x = (i', j', r)" by (cases "foldr zmk_app bs x")
  with Cons have rr: "zrenp f r = r" by (metis snd_conv)
  have e: "foldr zmk_app (b # bs) x = zmk_app b (i', j', r)" using r by simp
  show ?case unfolding e using rr by (simp add: zmk_app_def)
qed simp

lemma zrenp_foldr_zmk_app_ZBoundp[simp]:
  "zrenp f (snd (snd (foldr zmk_app bs (i, j, ZBoundp k)))) = snd (snd (foldr zmk_app bs (i, j, ZBoundp k)))"
  by (rule zrenp_foldr_zmk_app) simp

lemma zlift_prems_nren:
  assumes "zlift_prems ta inc k pf Ts bs i j G = returnZ q" "zconst_free pf" "0 \<le> inc"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) pf" "\<And>x. x \<in> vars G \<Longrightarrow> \<mu> (fst x) = fst x"
  shows "zlift_prems ta inc k (zrenp (nren \<mu>) pf) Ts bs i j G = returnZ (zrenp (nren \<mu>) q)"
  using assms
proof (induction ta inc k pf Ts bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 ta inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with "1.prems"(1) obtain A' p where A': "zterm_of ta A = returnZ A'"
      and p: "zlift_prems ta inc k pf Ts (True # bs) (i + 1) j B = returnZ p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    have "zrenv (nren \<mu>) A' = A'" by (rule zrenv_zterm_of[OF A']) (use "1.prems"(5) in \<open>auto simp: nren_def\<close>)
    moreover have "zlift_prems ta inc k (zrenp (nren \<mu>) pf) Ts (True # bs) (i + 1) j B = returnZ (zrenp (nren \<mu>) p)"
      by (rule "1.IH"(1)[OF True A'[unfolded returnZ_def] p "1.prems"(2,3,4)]) (use "1.prems"(5) in auto)
    ultimately show ?thesis using True A' q by (auto simp: bindZ_eq_returnZ)
  next
    case False
    with "1.prems"(1) obtain p where p: "zlift_prf inc (rev Ts) 0 pf = returnZ p"
      and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
      by (auto simp: bindZ_eq_returnZ)
    from zlift_prf_nren[OF p "1.prems"(2,3,4)] False q show ?thesis
      by (simp add: zrenp_ZAppps comp_def)
  qed
next
  case (2 ta inc k pf Ts bs i j c U a T t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with "2.prems"(1) obtain p where p: "zlift_prems ta inc k pf (ztyp_of T # Ts) (False # bs) i (j + 1) t = returnZ p"
      and q: "q = ZAbst a (ztyp_of T) p"
      by (auto simp: bindZ_eq_returnZ)
    have "zlift_prems ta inc k (zrenp (nren \<mu>) pf) (ztyp_of T # Ts) (False # bs) i (j + 1) t = returnZ (zrenp (nren \<mu>) p)"
      by (rule "2.IH"(1)[OF True p "2.prems"(2,3,4)]) (use "2.prems"(5) in auto)
    with True q show ?thesis by (auto simp: bindZ_eq_returnZ)
  next
    case False
    with "2.prems"(1) obtain p where p: "zlift_prf inc (rev Ts) 0 pf = returnZ p"
      and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
      by (auto simp: bindZ_eq_returnZ)
    from zlift_prf_nren[OF p "2.prems"(2,3,4)] False q show ?thesis
      by (simp add: zrenp_ZAppps comp_def)
  qed
qed (simp_all add: bindZ_eq_returnZ, (elim exE conjE, hypsubst, simp add: zrenp_ZAppps comp_def zlift_prf_nren)+)

lemma zlift_proof_nren:
  assumes "zlift_proof ta G inc prems pf = returnZ q" "zconst_free pf" "0 \<le> inc"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) pf"
    "\<And>x. x \<in> vars G \<union> (\<Union>A\<in>set prems. vars A) \<Longrightarrow> \<mu> (fst x) = fst x"
  shows "zlift_proof ta G inc prems (zrenp (nren \<mu>) pf) = returnZ (zrenp (nren \<mu>) q)"
proof -
  from assms(1) obtain As p where As: "mapZ (zterm_of ta) prems = returnZ As"
    and p: "zlift_prems ta inc (integer_of_nat (length prems)) pf [] [] 0 0 G = returnZ p" and q: "q = ZAbsps As p"
    by (auto simp: zlift_proof_def bindZ_eq_returnZ)
  have p': "zlift_prems ta inc (integer_of_nat (length prems)) (zrenp (nren \<mu>) pf) [] [] 0 0 G = returnZ (zrenp (nren \<mu>) p)"
    by (rule zlift_prems_nren[OF p assms(2,3,4)]) (use assms(5) in blast)
  have "map (zrenv (nren \<mu>)) As = As"
    using As assms(5)
  proof (induction prems arbitrary: As)
    case (Cons A prems)
    from Cons.prems(1) obtain A' As' where "zterm_of ta A = returnZ A'" "mapZ (zterm_of ta) prems = returnZ As'"
      "As = A' # As'" by (auto simp: bindZ_eq_returnZ)
    moreover have "zrenv (nren \<mu>) A' = A'"
      by (rule zrenv_zterm_of[OF calculation(1)]) (use Cons.prems(2) in \<open>auto simp: nren_def\<close>)
    ultimately show ?case using Cons by auto
  qed simp
  with As p' q show ?thesis by (simp add: zlift_proof_def zrenp_ZAbsps)
qed



subsection \<open>The invariant of tight proofs with hidden variables\<close>

text \<open>The typing of the separated variables (\<open>sepz\<close>): each by its own type.\<close>

definition Wenc :: "indexname \<Rightarrow> ptyp" where
  "Wenc y = (if \<exists>x T. y = sepn x T then typ_of (snd (SOME xT. y = sepn (fst xT) (snd xT))) else dummyT)"

lemma Wenc_sepn[simp]: "Wenc (sepn x T) = typ_of T"
proof -
  have "\<exists>xT. sepn x T = sepn (fst xT) (snd xT)" by (intro exI[of _ "(x, T)"]) simp
  then have "sepn x T = sepn (fst (SOME xT. sepn x T = sepn (fst xT) (snd xT))) (snd (SOME xT. sepn x T = sepn (fst xT) (snd xT)))"
    by (rule someI_ex)
  then have "snd (SOME xT. sepn x T = sepn (fst xT) (snd xT)) = T" by (simp add: sepn_inj)
  moreover have "\<exists>x' T'. sepn x T = sepn x' T'" by blast
  ultimately show ?thesis by (simp add: Wenc_def)
qed

lemma incr_boundvars_Var[simp]: "incr_boundvars n (Var x T) = Var x T"
  by (simp add: incr_boundvars_eq)

lemma zdec_zrenv:
  "(\<And>x T. (x, T) \<in> zvars t \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> \<theta> x = Var (f x T) (typ_of T)) \<Longrightarrow> idx_pres f \<Longrightarrow>
    zdec (zrenv f t) = psubst TVar \<theta> lev (zdec t)"
proof (induction t arbitrary: lev)
  case (ZVar x T)
  then show ?case by (cases x) (auto simp: idx_pres_def)
next
  case (ZConst0 c)
  then show ?case by (simp add: tsubst_TVar_id)
next
  case (ZConst1 c T)
  then show ?case by (simp add: tsubst_TVar_id)
next
  case (ZConst c Ts)
  then show ?case by (simp add: tsubst_TVar_id)
next
  case (ZAbs a T t)
  then show ?case by (simp add: tsubst_TVar_id)
next
  case (ZOfclass T c)
  then show ?case by (simp add: of_class_def tsubst_TVar_id)
qed auto

lemma has_type_zrenv:
  assumes "has_type W Ts (zdec t) U" "idx_pres f"
    "\<And>x T. (x, T) \<in> zvars t \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> W' (f x T) = typ_of T"
  shows "has_type W' Ts (zdec (zrenv f t)) U"
  using assms
proof (induction t arbitrary: Ts U)
  case (ZVar x T)
  show ?case
  proof (cases "snd x = -1")
    case True
    with ZVar.prems(1) have "U = typ_of T" by (auto elim: has_type_elims)
    with True show ?thesis by (auto intro: has_type.Free)
  next
    case False
    with ZVar.prems(1) have U: "U = typ_of T" by (auto elim: has_type_elims)
    have "snd (f x T) \<noteq> -1" using False idx_pres_snd[OF ZVar.prems(2)] by simp
    with False U ZVar.prems(3) show ?thesis by (auto intro!: has_type.Var)
  qed
next
  case (ZBound i)
  then show ?case by (auto elim!: has_type_elims intro: has_type.Bound)
next
  case (ZConst0 c)
  then show ?case by (auto elim!: has_type_elims intro: has_type.Const)
next
  case (ZConst1 c T)
  then show ?case by (auto elim!: has_type_elims intro: has_type.Const)
next
  case (ZConst c Ts')
  then show ?case by (auto elim!: has_type_elims intro: has_type.Const)
next
  case (ZAbs a T t)
  from ZAbs.prems(1) obtain U' where U: "U = typ_of T \<rightarrow>\<^sub>T U'" and h: "has_type W (typ_of T # Ts) (zdec t) U'"
    by (auto elim: has_type_elims)
  have "has_type W' (typ_of T # Ts) (zdec (zrenv f t)) U'" by (rule ZAbs.IH[OF h ZAbs.prems(2)]) (use ZAbs.prems(3) in auto)
  with U show ?case by (auto intro: has_type.Abs)
next
  case (ZApp t u)
  from ZApp.prems(1) obtain T where t: "has_type W Ts (zdec t) (T \<rightarrow>\<^sub>T U)" and u: "has_type W Ts (zdec u) T"
    by (auto elim: has_type_elims)
  have "has_type W' Ts (zdec (zrenv f t)) (T \<rightarrow>\<^sub>T U)" by (rule ZApp.IH(1)[OF t ZApp.prems(2)]) (use ZApp.prems(3) in auto)
  moreover have "has_type W' Ts (zdec (zrenv f u)) T" by (rule ZApp.IH(2)[OF u ZApp.prems(2)]) (use ZApp.prems(3) in auto)
  ultimately show ?case by (auto intro: has_type.App)
next
  case (ZOfclass T c)
  have "has_type W' Ts (of_class (typ_of T) c) U"
    using ZOfclass.prems(1) by (simp add: of_class_def) (auto elim!: has_type_elims intro!: has_type.intros)
  then show ?case by simp
qed

definition zann_s :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> bool" where
  "zann_s A m t \<longleftrightarrow> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> tyA ar A (typ_of T)) \<and>
    (\<forall>T\<in>ztys t. zty A m T) \<and> (\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U)"

definition zsyn :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> zproof \<Rightarrow> bool" where
  "zsyn A m p \<longleftrightarrow> zconst_free p \<and> zno_class p \<and> zrf p \<and> zprf_all (zann_s A m) (zty A m) p"

definition zrel :: "(indexname \<Rightarrow> pterm) \<Rightarrow> pterm \<Rightarrow> pterm \<Rightarrow> bool" where
  "zrel \<Theta> t0 t \<longleftrightarrow> ann_eq (Some (psubst TVar \<Theta> 0 t0)) (Some t)"

definition sepv :: "indexname \<Rightarrow> ptyp \<Rightarrow> pterm" where
  "sepv x T = Var (sepn x (ztyp_of T)) T"

definition hid_ok :: "(indexname \<Rightarrow> ptyp) \<Rightarrow> indexname set \<Rightarrow> (indexname \<Rightarrow> pterm) \<Rightarrow> bool" where
  "hid_ok W X \<Theta> \<longleftrightarrow> (\<forall>x. proper (\<Theta> x) \<and> \<not> loose_bvar (\<Theta> x) 0) \<and>
    (\<forall>x. 0 \<le> snd x \<longrightarrow> wty Wenc [] (\<Theta> x) (W x)) \<and> (\<forall>x\<in>X. \<Theta> x = sepv x (W x))"

text \<open>
  The invariant of the tight proof \<open>p\<close> of a theorem: a valid tight proof \<open>p0\<close> of the theorem
  satisfies the invariant @{const zthm_prf_inv}; the annotations of \<open>p\<close>, with variables separated by
  their names and types, are equivalent to instances of those of \<open>p0\<close> (\<open>\<Theta>\<close>, which keeps the
  variables of the theorem); the annotations of \<open>p\<close> are typed by the types of their variables.
\<close>

definition zthm_hinv :: "integer \<Rightarrow> (pterm \<times> pterm) list \<Rightarrow> pterm \<Rightarrow> pterm set \<Rightarrow> zproof \<Rightarrow> bool" where
  "zthm_hinv m tps P H p \<longleftrightarrow> (\<exists>A W p0 \<Theta>. finite A \<and> scons A \<and> tcert alg A \<and>
    (\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m) \<and> (\<forall>x. tyA ar A (W x)) \<and> wt_thm ar A W m tps P \<and>
    prf_valid alg ar W H tps (zprf_tr p0) P \<and> zinv A W m p0 \<and>
    prf_rel (zrel \<Theta>) id (zprf_tr p0) (zprf_tr (zrenp sepn p)) \<and> hid_ok W (vars_thm tps P) \<Theta> \<and> zsyn A m p)"

lemma typ_of_ztyp_of_tyA: "tyA ar A T \<Longrightarrow> \<forall>q\<in>A. 0 \<le> snd (fst q) \<Longrightarrow> typ_of (ztyp_of T) = T"
  by (rule typ_of_ztyp_of) (fastforce simp: tyA_def)

lemma zann_zann_s:
  assumes "zann A W m t" "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
  shows "zann_s A m t"
proof -
  from assms(1) have v: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> T = ztyp_of (W x)"
    and ty: "\<forall>T\<in>ztys t. zty A m T" and h: "\<exists>Ts U. has_type W Ts (zdec t) U"
    by (auto simp: zann_def)
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA assms(2,3) by blast
  from h obtain Ts U where "has_type W Ts (zdec t) U" by blast
  then have "has_type Wenc Ts (zdec (sepz t)) U"
    by (rule has_type_zrenv) (use v tw in auto)
  moreover have "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> tyA ar A (typ_of T)" using v tw assms(2) by fastforce
  ultimately show ?thesis using v ty by (fastforce simp: zann_s_def)
qed

lemma prf_rel_Abst_id: "prf_rel R id p p' \<Longrightarrow> prf_rel R id (Abst a T p) (Abst a T p')"
  using prf_rel.Abst[of R id p p' a T] by (simp add: option.map_id)

lemma prf_rel_PClass_id: "prf_rel R id (PClass T c) (PClass T c)"
  using prf_rel.PClass[of R id T c] by simp

lemma ann_eq_refl_proper: "proper t \<Longrightarrow> \<forall>x\<in>vars t. 0 \<le> snd x \<Longrightarrow> ann_eq (Some t) (Some t)"
  by (simp add: ann_eq_def)

lemma zinv_zthm_hinv_rel:
  assumes "zprf_all (zann A W m) (zty A m) p" "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
  shows "prf_rel (zrel (\<lambda>x. sepv x (W x))) id (zprf_tr p) (zprf_tr (zrenp sepn p))"
proof -
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA assms(2,3) by blast
  have r: "zrel (\<lambda>x. sepv x (W x)) (zdec t) (zdec (sepz t))" if "zann A W m t" for t
  proof -
    from that have v: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> T = ztyp_of (W x)"
      and h: "\<exists>Ts U. has_type W Ts (zdec t) U" by (auto simp: zann_def)
    have e: "zdec (sepz t) = psubst TVar (\<lambda>x. sepv x (W x)) 0 (zdec t)"
      by (rule zdec_zrenv) (use v tw in \<open>auto simp: sepv_def\<close>)
    from h obtain Ts U where "has_type W Ts (zdec t) U" by blast
    then have "proper (zdec (sepz t))" using has_type_zrenv[of W Ts t U sepn Wenc] v tw
      by (auto intro: has_type_proper)
    moreover have "\<forall>x\<in>vars (zdec (sepz t)). 0 \<le> snd x"
      using v by (auto simp: vars_zdec zvars_zrenv sepn_def split: if_splits)
    ultimately show ?thesis by (simp add: zrel_def e[symmetric] ann_eq_refl_proper)
  qed
  from assms(1) show ?thesis
    by (induction p) (auto intro!: prf_rel.intros prf_rel_Abst_id prf_rel_PClass_id simp: r)
qed

lemma hid_ok_sepv:
  assumes "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
  shows "hid_ok W X (\<lambda>x. sepv x (W x))"
proof -
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA assms by blast
  show ?thesis
    by (auto simp: hid_ok_def sepv_def wty_def tw intro!: has_type.Var)
qed

theorem zthm_prf_inv_hinv: "zthm_prf_inv m tps P H p \<Longrightarrow> zthm_hinv m tps P H p"
proof -
  assume "zthm_prf_inv m tps P H p"
  then obtain A W where A: "finite A" "scons A" "tcert alg A" "\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m"
    "\<forall>x. tyA ar A (W x)" and w: "wt_thm ar A W m tps P" "prf_valid alg ar W H tps (zprf_tr p) P"
    and z: "zinv A W m p"
    by (auto simp: zthm_prf_inv_def)
  have A0: "\<forall>q\<in>A. 0 \<le> snd (fst q)" using A(4) by blast
  from z have za: "zprf_all (zann A W m) (zty A m) p" and zs: "zconst_free p" "zno_class p" "zrf p"
    by (auto simp: zinv_def)
  have "zprf_all (zann_s A m) (zty A m) p"
    by (rule zprf_all_mono[OF za]) (use zann_zann_s A(5) A0 in auto)
  with zs have "zsyn A m p" by (simp add: zsyn_def)
  with A w z zinv_zthm_hinv_rel[OF za A(5) A0] hid_ok_sepv[OF A(5) A0] show ?thesis
    unfolding zthm_hinv_def by blast
qed

text \<open>Instantiation keeps equivalent annotations equivalent.\<close>

lemma proper_remove_types[simp]: "proper (remove_types t) = proper t"
  by (induction t rule: remove_types.induct) auto

lemma loose_bvar_remove_types[simp]: "loose_bvar (remove_types t) k = loose_bvar t k"
  by (induction t arbitrary: k rule: remove_types.induct) auto

lemma ann_eq_psubst:
  assumes "ann_eq (Some a) (Some b)" "\<forall>x. proper (\<theta> x) \<and> \<not> loose_bvar (\<theta> x) 0" "\<forall>x. \<forall>y\<in>vars (\<theta> x). 0 \<le> snd y"
  shows "ann_eq (Some (psubst \<rho> \<theta> 0 a)) (Some (psubst \<rho> \<theta> 0 b))"
proof -
  from assms(1) have e: "tr (remove_types a) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types b)" and pb: "proper b"
    by (auto simp: ann_eq_def)
  let ?\<theta> = "\<lambda>x. remove_types (\<theta> x)"
  have cl: "\<forall>x. proper (?\<theta> x) \<and> \<not> loose_bvar (?\<theta> x) 0" using assms(2) by simp
  have clx: "\<forall>y\<in>vars s. \<not> loose_bvar (?\<theta> y) 0" for s using cl by blast
  have tr_eq: "tr (remove_types (psubst \<rho> \<theta> 0 t)) = mk_subst (isubst ?\<theta> \<circ> cren \<rho>) (tr (remove_types t))" for t
    by (simp add: remove_types_psubst[unfolded comp_def] tr_psubst_sm[OF clx] sm_def mk_subst_inst)
  have "tr (remove_types (psubst \<rho> \<theta> 0 a)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (psubst \<rho> \<theta> 0 b))"
    unfolding tr_eq by (rule mk_subst_equiv[OF e closed_on_cren[OF closed_isubst[OF cl]]])
  moreover have "proper (psubst \<rho> \<theta> 0 b)" using pb assms(2) by (intro proper_psubst) auto
  moreover have "\<forall>x\<in>vars (psubst \<rho> \<theta> 0 b). 0 \<le> snd x" using assms(3) by (auto simp: vars_psubst)
  ultimately show ?thesis by (simp add: ann_eq_def)
qed


text \<open>Elimination of the relation of proofs with the same types.\<close>

lemma prf_rel_id_Abst: "prf_rel R id q (Abst a T p') \<Longrightarrow> \<exists>p. q = Abst a T p \<and> prf_rel R id p p'"
  by (erule prf_rel.cases) (simp_all add: option.map_id)

lemma prf_rel_id_AbsP: "prf_rel R id q (AbsP a t p') \<Longrightarrow> \<exists>t0 p. q = AbsP a t0 p \<and> rel_option R t0 t \<and> prf_rel R id p p'"
  by (erule prf_rel.cases) simp_all

lemma prf_rel_id_PAppt: "prf_rel R id q (PAppt p' t) \<Longrightarrow> \<exists>p t0. q = PAppt p t0 \<and> prf_rel R id p p' \<and> rel_option R t0 t"
  by (erule prf_rel.cases) simp_all

lemma prf_rel_id_PAppp:
  "prf_rel R id q (PAppp p1' p2') \<Longrightarrow> \<exists>p1 p2. q = PAppp p1 p2 \<and> prf_rel R id p1 p1' \<and> prf_rel R id p2 p2'"
  by (erule prf_rel.cases) simp_all

lemma prf_rel_id_leaf:
  "prf_rel R id q MinProof \<Longrightarrow> q = MinProof" "prf_rel R id q (PBound i) \<Longrightarrow> q = PBound i"
  "prf_rel R id q (Hyp t) \<Longrightarrow> q = Hyp t" "prf_rel R id q (PClass T c) \<Longrightarrow> q = PClass T c"
  by (erule prf_rel.cases; simp)+

text \<open>The pairs of names and types of the schematic variables of the annotations of a tight proof.\<close>

fun zprf_zvars :: "zproof \<Rightarrow> (indexname \<times> ztyp) set" where
  "zprf_zvars (ZAbst a T p) = zprf_zvars p"
| "zprf_zvars (ZAbsp a t p) = {(x, T). (x, T) \<in> zvars t \<and> snd x \<noteq> -1} \<union> zprf_zvars p"
| "zprf_zvars (ZAppt p t) = zprf_zvars p \<union> {(x, T). (x, T) \<in> zvars t \<and> snd x \<noteq> -1}"
| "zprf_zvars (ZAppp p q) = zprf_zvars p \<union> zprf_zvars q"
| "zprf_zvars p = {}"

lemma zprf_all_zprf_zvars:
  "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> zprf_zvars p) (\<lambda>_. True) p"
proof -
  have "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> S) (\<lambda>_. True) p" if "zprf_zvars p \<subseteq> S" for S
    using that by (induction p arbitrary: S) auto
  then show ?thesis by blast
qed

lemma prf_rel_zrenp_aeq:
  assumes "prf_rel R id q (zprf_tr (zrenp f r))" "zprf_all Pr (\<lambda>_. True) r"
    and "\<And>a t. R a (zdec (zrenv f t)) \<Longrightarrow> Pr t \<Longrightarrow> ann_eq (Some (psubst \<rho> \<theta>1 0 a)) (Some (psubst \<rho> \<theta>2 0 (zdec (zrenv g (zrenv f t)))))"
    and "\<forall>x. \<not> loose_bvar (\<theta>1 x) 0" "\<forall>x. \<not> loose_bvar (\<theta>2 x) 0" "0 \<le> lev"
  shows "prf_aeq (prf_inst \<rho> \<theta>1 lev q) (prf_inst \<rho> \<theta>2 lev (zprf_tr (zrenp g (zrenp f r))))"
  using assms(1,2,6)
proof (induction r arbitrary: q lev)
  case (ZAbst a T r)
  from prf_rel_id_Abst[OF ZAbst.prems(1)[unfolded zrenp.simps zprf_tr.simps]] obtain q' where
    "q = Abst a (Some (typ_of T)) q'" "prf_rel R id q' (zprf_tr (zrenp f r))" by blast
  with ZAbst.IH[of q' "lev + 1"] ZAbst.prems(2,3) show ?case by (auto simp: id_def intro: prf_aeq.Abst)
next
  case (ZAbsp a t r)
  from prf_rel_id_AbsP[OF ZAbsp.prems(1)[unfolded zrenp.simps zprf_tr.simps]] obtain t0 q' where q: "q = AbsP a t0 q'"
    "rel_option R t0 (Some (zdec (zrenv f t)))" "prf_rel R id q' (zprf_tr (zrenp f r))"
    by blast
  from q(2) obtain a0 where a0: "t0 = Some a0" "R a0 (zdec (zrenv f t))" by (cases t0) auto
  have cl1: "\<forall>x\<in>vars s. \<not> loose_bvar (\<theta>1 x) 0" and cl2: "\<forall>x\<in>vars s. \<not> loose_bvar (\<theta>2 x) 0" for s
    using assms(4,5) by blast+
  have "ann_eq (Some (psubst \<rho> \<theta>1 lev a0)) (Some (psubst \<rho> \<theta>2 lev (zdec (zrenv g (zrenv f t)))))"
    using assms(3)[OF a0(2)] ZAbsp.prems(2) psubst_closed_lev[OF cl1 ZAbsp.prems(3)] psubst_closed_lev[OF cl2 ZAbsp.prems(3)]
    by simp
  with ZAbsp.IH[OF q(3)] ZAbsp.prems(2,3) q(1) a0(1) show ?case by (auto intro: prf_aeq.AbsP)
next
  case (ZAppt r t)
  from prf_rel_id_PAppt[OF ZAppt.prems(1)[unfolded zrenp.simps zprf_tr.simps]] obtain q' t0 where q: "q = PAppt q' t0"
    "prf_rel R id q' (zprf_tr (zrenp f r))" "rel_option R t0 (Some (zdec (zrenv f t)))"
    by blast
  from q(3) obtain a0 where a0: "t0 = Some a0" "R a0 (zdec (zrenv f t))" by (cases t0) auto
  have cl1: "\<forall>x\<in>vars s. \<not> loose_bvar (\<theta>1 x) 0" and cl2: "\<forall>x\<in>vars s. \<not> loose_bvar (\<theta>2 x) 0" for s
    using assms(4,5) by blast+
  have "ann_eq (Some (psubst \<rho> \<theta>1 lev a0)) (Some (psubst \<rho> \<theta>2 lev (zdec (zrenv g (zrenv f t)))))"
    using assms(3)[OF a0(2)] ZAppt.prems(2) psubst_closed_lev[OF cl1 ZAppt.prems(3)] psubst_closed_lev[OF cl2 ZAppt.prems(3)]
    by simp
  with ZAppt.IH[OF q(2)] ZAppt.prems(2,3) q(1) a0(1) show ?case by (auto intro: prf_aeq.PAppt)
next
  case (ZAppp r1 r2)
  from prf_rel_id_PAppp[OF ZAppp.prems(1)[unfolded zrenp.simps zprf_tr.simps]] obtain q1 q2 where q: "q = PAppp q1 q2"
    "prf_rel R id q1 (zprf_tr (zrenp f r1))" "prf_rel R id q2 (zprf_tr (zrenp f r2))"
    by blast
  with ZAppp.IH(1)[OF q(2)] ZAppp.IH(2)[OF q(3)] ZAppp.prems(2,3) show ?case by (auto intro: prf_aeq.PAppp)
next
  case ZNop
  have "q = MinProof" by (rule prf_rel_id_leaf(1)) (use ZNop.prems(1) in \<open>simp only: zrenp.simps zprf_tr.simps\<close>)
  then show ?case by (simp add: prf_aeq.refl)
next
  case (ZConstp c)
  have "q = MinProof" by (rule prf_rel_id_leaf(1)) (use ZConstp.prems(1) in \<open>simp only: zrenp.simps zprf_tr.simps\<close>)
  then show ?case by (simp add: prf_aeq.refl)
next
  case (ZBoundp i)
  have "q = PBound i" by (rule prf_rel_id_leaf(2)) (use ZBoundp.prems(1) in \<open>simp only: zrenp.simps zprf_tr.simps\<close>)
  then show ?case by (simp add: prf_aeq.refl)
next
  case (ZHyp t)
  have "q = Hyp (zdec t)" by (rule prf_rel_id_leaf(3)) (use ZHyp.prems(1) in \<open>simp only: zrenp.simps zprf_tr.simps\<close>)
  then show ?case by (simp add: prf_aeq.refl)
next
  case (OFCLASSp T c)
  have "q = PClass (typ_of T) c" by (rule prf_rel_id_leaf(4)) (use OFCLASSp.prems(1) in \<open>simp only: zrenp.simps zprf_tr.simps\<close>)
  then show ?case by (simp add: prf_aeq.refl)
qed

text \<open>
  Separating the hidden variables of a tight proof that satisfies @{const zthm_hinv} gives a tight
  proof that satisfies @{const zthm_prf_inv}: \<open>\<nu>\<close> keeps the variables of the theorem and gives the
  other pairs of the proof distinct names that are not names of variables of the theorem.
\<close>

theorem zthm_hinv_sep:
  assumes inv: "zthm_hinv m tps P H p"
    and ip: "idx_pres \<nu>"
    and nt: "\<And>x T. (x, typ_of T) \<in> vps_thm tps P \<Longrightarrow> \<nu> x T = x"
    and inj: "\<And>x T y U. (x, T) \<in> zprf_zvars p \<Longrightarrow> (y, U) \<in> zprf_zvars p \<Longrightarrow> \<nu> x T = \<nu> y U \<Longrightarrow> x = y \<and> T = U"
    and fr: "\<And>x T. (x, T) \<in> zprf_zvars p \<Longrightarrow> (x, typ_of T) \<notin> vps_thm tps P \<Longrightarrow> \<nu> x T \<notin> vars_thm tps P"
    and nn: "\<forall>x\<in>vars_thm tps P. 0 \<le> snd x"
  shows "zthm_prf_inv m tps P H (zrenp \<nu> p)"
proof -
  from inv obtain A W p0 \<Theta> where A: "finite A" "scons A" "tcert alg A" "\<forall>q\<in>A. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> m"
    "\<forall>x. tyA ar A (W x)" and wt: "wt_thm ar A W m tps P" and pv: "prf_valid alg ar W H tps (zprf_tr p0) P"
    and z0: "zinv A W m p0" and rel: "prf_rel (zrel \<Theta>) id (zprf_tr p0) (zprf_tr (zrenp sepn p))"
    and ho: "hid_ok W (vars_thm tps P) \<Theta>" and zs: "zsyn A m p"
    by (auto simp: zthm_hinv_def)
  have A0: "\<forall>q\<in>A. 0 \<le> snd (fst q)" using A(4) by blast
  let ?PV = "zprf_zvars p"
  let ?TP = "{(x, T). (x, typ_of T) \<in> vps_thm tps P}"
  from zs have zp: "zprf_all (zann_s A m) (zty A m) p" and zc: "zconst_free p" "zno_class p" "zrf p"
    by (auto simp: zsyn_def)
  have zpv: "zprf_all (\<lambda>t. zann_s A m t \<and> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> ?PV)) (\<lambda>T. zty A m T \<and> True) p"
    by (rule zprf_all_conj[OF zp zprf_all_zprf_zvars])
  text \<open>The pairs of the proof: indices, types.\<close>
  have pvi: "snd x \<noteq> -1 \<and> 0 \<le> snd x \<and> tyA ar A (typ_of T) \<and> zcan T" if "(x, T) \<in> ?PV" for x T
  proof -
    have "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> tyA ar A (typ_of T) \<and> zcan T) (\<lambda>_. True) p"
    proof (rule zprf_all_mono[OF zp])
      fix t assume "zann_s A m t"
      then show "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> tyA ar A (typ_of T) \<and> zcan T"
        by (fastforce simp: zann_s_def zty_def dest: zvars_ztys)
    qed simp
    then have "\<forall>(x, T)\<in>?PV. snd x \<noteq> -1 \<and> 0 \<le> snd x \<and> tyA ar A (typ_of T) \<and> zcan T"
      by (induction p) auto
    with that show ?thesis by blast
  qed
  have vpsW: "W x = T" if "(x, T) \<in> vps_thm tps P" for x T
  proof -
    from wt have "\<forall>t\<in>insert P (\<Union>(t, u)\<in>set tps. {t, u}). \<exists>U. has_type W [] t U"
      by (fastforce simp: wt_thm_def wt_term_def)
    with that show ?thesis by (fastforce simp: vps_thm_def dest: vps_has_type_typ)
  qed
  text \<open>The typing of the separated proof.\<close>
  define W' where "W' y = (if \<exists>xT\<in>?PV. \<nu> (fst xT) (snd xT) = y then typ_of (snd (SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = y))
    else W y)" for y
  have W'PV: "W' (\<nu> x T) = typ_of T" if "(x, T) \<in> ?PV" for x T
  proof -
    have "\<exists>xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T" using that by (intro exI[of _ "(x, T)"]) simp
    from someI_ex[OF this] have sm: "(SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T) \<in> ?PV \<and>
        \<nu> (fst (SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T)) (snd (SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T)) = \<nu> x T" .
    obtain y U where yU0: "(SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T) = (y, U)"
      by (cases "SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T")
    with sm have yU: "(SOME xT. xT \<in> ?PV \<and> \<nu> (fst xT) (snd xT) = \<nu> x T) = (y, U)" "(y, U) \<in> ?PV" "\<nu> y U = \<nu> x T"
      by simp_all
    from inj[OF yU(2) that yU(3)] have "U = T" by simp
    with that yU show ?thesis by (auto simp: W'_def)
  qed
  have W'th: "W' x = W x" if "x \<in> vars_thm tps P" for x
  proof (cases "\<exists>xT\<in>?PV. \<nu> (fst xT) (snd xT) = x")
    case True
    then obtain y U where yU: "(y, U) \<in> ?PV" "\<nu> y U = x" by auto
    show ?thesis
    proof (cases "(y, typ_of U) \<in> vps_thm tps P")
      case True
      with nt have "\<nu> y U = y" by blast
      with yU W'PV[OF yU(1)] vpsW[OF True] show ?thesis by simp
    next
      case False
      from fr[OF yU(1) False] yU(2) that show ?thesis by simp
    qed
  qed (simp add: W'_def)
  have W'A: "tyA ar A (W' y)" for y
  proof (cases "\<exists>xT\<in>?PV. \<nu> (fst xT) (snd xT) = y")
    case True
    then obtain x T where "(x, T) \<in> ?PV" "\<nu> x T = y" by auto
    with W'PV pvi show ?thesis by metis
  qed (simp add: W'_def A(5)[rule_format])
  text \<open>Renaming the separated variables to the separated proof.\<close>
  define g where "g y U = (if \<exists>x. y = sepn x U then \<nu> (SOME x. y = sepn x U) U else y)" for y U
  have g: "g (sepn x T) T = \<nu> x T" for x T by (simp add: g_def sepn_inj)
  have ipg: "idx_pres g"
    unfolding idx_pres_def
  proof (intro allI)
    fix y U
    show "snd (g y U) = snd y"
    proof (cases "\<exists>x. y = sepn x U")
      case True
      define x0 where "x0 = (SOME x. y = sepn x U)"
      have y: "y = sepn x0 U" unfolding x0_def using True by (rule someI_ex)
      have "g y U = \<nu> x0 U" using True by (simp add: g_def x0_def)
      then show ?thesis using idx_pres_snd[OF ip, of x0 U] y by simp
    qed (simp add: g_def)
  qed
  have gs: "zrenv g (sepz t) = zrenv \<nu> t" for t by (simp add: zrenv_comp g)
  have gsp: "zrenp g (zrenp sepn p) = zrenp \<nu> p" by (simp add: zrenp_comp g)
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA A(5) A0 by blast
  define \<theta>\<kappa> where "\<theta>\<kappa> y = (if \<exists>x T. y = sepn x T \<and> snd x \<noteq> -1 \<and> ((x, T) \<in> ?PV \<or> (x, typ_of T) \<in> vps_thm tps P)
    then Var (g y (SOME T. \<exists>x. y = sepn x T)) (Wenc y) else Free STR ''u'' (Wenc y))" for y
  have \<theta>\<kappa>: "\<theta>\<kappa> (sepn x T) = Var (\<nu> x T) (typ_of T)"
    if "snd x \<noteq> -1" "(x, T) \<in> ?PV \<or> (x, typ_of T) \<in> vps_thm tps P" for x T
  proof -
    have s: "(SOME T'. \<exists>x'. sepn x T = sepn x' T') = T" by (rule some_equality) (auto simp: sepn_inj)
    have "\<exists>x' T'. sepn x T = sepn x' T' \<and> snd x' \<noteq> -1 \<and> ((x', T') \<in> ?PV \<or> (x', typ_of T') \<in> vps_thm tps P)"
      using that by blast
    with s show ?thesis by (simp add: \<theta>\<kappa>_def g)
  qed
  have \<theta>\<kappa>cl: "proper (\<theta>\<kappa> y) \<and> \<not> loose_bvar (\<theta>\<kappa> y) 0" for y by (simp add: \<theta>\<kappa>_def)
  have \<theta>\<kappa>v: "\<forall>v\<in>vars (\<theta>\<kappa> y). 0 \<le> snd v \<and> W' v = Wenc y" for y
  proof (cases "\<exists>x T. y = sepn x T \<and> snd x \<noteq> -1 \<and> ((x, T) \<in> ?PV \<or> (x, typ_of T) \<in> vps_thm tps P)")
    case True
    then obtain x T where xT: "y = sepn x T" "snd x \<noteq> -1" "(x, T) \<in> ?PV \<or> (x, typ_of T) \<in> vps_thm tps P" by blast
    have "0 \<le> snd (\<nu> x T)"
    proof -
      have "0 \<le> snd x"
      proof (cases "(x, T) \<in> ?PV")
        case True
        with pvi show ?thesis by blast
      next
        case False
        with xT(3) have "x \<in> vars_thm tps P" by (force simp: vps_thm_def vars_thm_def vars_vps)
        with nn show ?thesis by blast
      qed
      with idx_pres_snd[OF ip] show ?thesis by simp
    qed
    moreover have "W' (\<nu> x T) = typ_of T"
    proof (cases "(x, T) \<in> ?PV")
      case True
      with W'PV show ?thesis by blast
    next
      case False
      with xT(3) have v: "(x, typ_of T) \<in> vps_thm tps P" by blast
      then have "x \<in> vars_thm tps P" by (force simp: vps_thm_def vars_thm_def vars_vps)
      with nt[OF v] W'th vpsW[OF v] show ?thesis by simp
    qed
    ultimately show ?thesis using xT \<theta>\<kappa> by simp
  qed (simp add: \<theta>\<kappa>_def)
  have zd: "zdec (zrenv \<nu> t) = psubst TVar \<theta>\<kappa> 0 (zdec (sepz t))" if "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> ?PV" for t
  proof -
    have "zdec (zrenv g (sepz t)) = psubst TVar \<theta>\<kappa> 0 (zdec (sepz t))"
    proof (rule zdec_zrenv[OF _ ipg])
      fix y U assume "(y, U) \<in> zvars (sepz t)" "snd y \<noteq> -1"
      then obtain x where x: "(x, U) \<in> zvars t" "snd x \<noteq> -1" "y = sepn x U"
        by (auto simp: zvars_zrenv split: if_splits)
      have "(x, U) \<in> ?PV" using that x(1,2) by blast
      then show "\<theta>\<kappa> y = Var (g y U) (typ_of U)" using \<theta>\<kappa>[OF x(2)] g[of x U] x(3) by simp
    qed
    then show ?thesis by (simp add: gs)
  qed
  text \<open>The invariant of the separated proof.\<close>
  have zann': "zann A W' m (zrenv \<nu> t)" if "zann_s A m t" "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> ?PV" for t
  proof -
    from that(1) obtain Ts U where h: "has_type Wenc Ts (zdec (sepz t)) U" by (auto simp: zann_s_def)
    from that(1) have ty: "\<forall>T\<in>ztys t. zty A m T" and v: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m"
      by (auto simp: zann_s_def)
    have "has_type W' Ts (zdec (zrenv g (sepz t))) U"
    proof (rule has_type_zrenv[OF h ipg])
      fix y U' assume "(y, U') \<in> zvars (sepz t)" "snd y \<noteq> -1"
      then obtain x where x: "(x, U') \<in> zvars t" "snd x \<noteq> -1" "y = sepn x U'"
        by (auto simp: zvars_zrenv split: if_splits)
      have "(x, U') \<in> ?PV" using that(2) x(1,2) by blast
      then show "W' (g y U') = typ_of U'" using W'PV g[of x U'] x(3) by simp
    qed
    then have h': "has_type W' Ts (zdec (zrenv \<nu> t)) U" by (simp add: gs)
    have "\<forall>(x, T)\<in>zvars (zrenv \<nu> t). snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m"
      using v ip by (auto simp: zvars_zrenv idx_pres_def)
    moreover have "\<forall>T\<in>ztys (zrenv \<nu> t). zty A m T" using ty by simp
    ultimately show ?thesis using h' by (intro zann_intro) auto
  qed
  have zi: "zinv A W' m (zrenp \<nu> p)"
  proof -
    have "zprf_all (zann A W' m) (zty A m) (zrenp \<nu> p)"
      unfolding zprf_all_zrenp by (rule zprf_all_mono[OF zpv]) (use zann' in auto)
    with zc show ?thesis by (simp add: zinv_def)
  qed
  have wt': "wt_thm ar A W' m tps P" by (rule wt_thm_vars_cong[OF wt]) (use W'th in auto)
  text \<open>Validity of the separated proof.\<close>
  have pv': "prf_valid alg ar W' H tps (zprf_tr (zrenp \<nu> p)) P"
    unfolding prf_valid_def
  proof (intro allI impI)
    fix V' \<rho> \<theta> assume g0: "ginst alg ar \<rho>" and ty: "inst_typed W' V' [] \<rho> \<theta>"
      and s: "\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta> 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta> 0 u)"
    define \<theta>' where "\<theta>' x = (if 0 \<le> snd x then \<theta> x else Free STR ''u'' dummyT)" for x
    have \<theta>'w: "0 \<le> snd x \<Longrightarrow> wty V' [] (\<theta>' x) (tsubst \<rho> (W' x))" for x
      using inst_typedD[OF ty] by (simp add: \<theta>'_def)
    have \<theta>'ty: "inst_typed W' V' [] \<rho> \<theta>'" using \<theta>'w by (simp add: inst_typed_def)
    have \<theta>'cl: "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0" "\<forall>x. \<forall>y\<in>vars (\<theta>' x). 0 \<le> snd y"
    proof -
      have "proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0 \<and> (\<forall>y\<in>vars (\<theta>' x). 0 \<le> snd y)" for x
      proof (cases "0 \<le> snd x")
        case True
        from \<theta>'w[OF True] show ?thesis
          by (auto simp: wty_def intro: has_type_proper dest: has_type_loose_bvar[where Ts = "[]", simplified])
      qed (simp add: \<theta>'_def)
      then show "\<forall>x. proper (\<theta>' x) \<and> \<not> loose_bvar (\<theta>' x) 0" "\<forall>x. \<forall>y\<in>vars (\<theta>' x). 0 \<le> snd y" by blast+
    qed
    define \<theta>0 where "\<theta>0 x = psubst \<rho> \<theta>' 0 (psubst TVar \<theta>\<kappa> 0 (\<Theta> x))" for x
    from ho have hcl: "\<forall>x. proper (\<Theta> x) \<and> \<not> loose_bvar (\<Theta> x) 0" and hw: "\<And>x. 0 \<le> snd x \<Longrightarrow> wty Wenc [] (\<Theta> x) (W x)"
      and hth: "\<forall>x\<in>vars_thm tps P. \<Theta> x = sepv x (W x)"
      by (auto simp: hid_ok_def)
    have \<theta>0th: "\<theta>0 x = \<theta>' x" if "x \<in> vars_thm tps P" for x
    proof -
      have v: "(x, typ_of (ztyp_of (W x))) \<in> vps_thm tps P"
      proof -
        from that have "x \<in> fst ` vps_thm tps P"
          by (auto simp: vps_thm_def vars_thm_def vars_vps image_Un image_UN)
        then obtain T where T: "(x, T) \<in> vps_thm tps P" by force
        with vpsW have WT: "W x = T" by blast
        show ?thesis using T tw[of x] WT by simp
      qed
      have sx: "snd x \<noteq> -1" using that nn by fastforce
      have "\<theta>\<kappa> (sepn x (ztyp_of (W x))) = Var x (W x)"
        using \<theta>\<kappa>[OF sx] v nt[OF v] by (simp add: tw)
      then show ?thesis using hth that by (simp add: \<theta>0_def sepv_def incr_boundvars_eq)
    qed
    have \<theta>0ty: "inst_typed W V' [] \<rho> \<theta>0"
      unfolding inst_typed_def
    proof (intro allI impI)
      fix x :: indexname assume x: "0 \<le> snd x"
      from hw[OF x] have h: "has_type Wenc [] (\<Theta> x) (W x)" and hv: "\<forall>v\<in>vars (\<Theta> x). 0 \<le> snd v"
        by (auto simp: wty_def)
      have "has_type W' (map (tsubst TVar) [] @ []) (psubst TVar \<theta>\<kappa> (integer_of_nat (length ([] :: ptyp list))) (\<Theta> x))
          (tsubst TVar (W x))"
      proof (rule has_type_psubst[OF h], intro ballI)
        fix y assume "y \<in> vars (\<Theta> x)"
        have "has_type W' [] (\<theta>\<kappa> y) (Wenc y)"
        proof (cases "\<exists>x T. y = sepn x T \<and> snd x \<noteq> -1 \<and> ((x, T) \<in> ?PV \<or> (x, typ_of T) \<in> vps_thm tps P)")
          case True
          then obtain v where v: "\<theta>\<kappa> y = Var v (Wenc y)" by (simp add: \<theta>\<kappa>_def)
          with \<theta>\<kappa>v[of y] have "W' v = Wenc y" by simp
          with v show ?thesis by (simp add: has_type.Var)
        qed (simp add: \<theta>\<kappa>_def has_type.Free)
        then show "has_type W' [] (\<theta>\<kappa> y) (tsubst TVar (Wenc y))" by (simp add: tsubst_TVar_id)
      qed
      then have h1: "has_type W' [] (psubst TVar \<theta>\<kappa> 0 (\<Theta> x)) (W x)" by (simp add: tsubst_TVar_id)
      have v1: "\<forall>v\<in>vars (psubst TVar \<theta>\<kappa> 0 (\<Theta> x)). 0 \<le> snd v" using \<theta>\<kappa>v by (auto simp: vars_psubst)
      have "wty W' [] (psubst TVar \<theta>\<kappa> 0 (\<Theta> x)) (W x)" using h1 v1 by (simp add: wty_def)
      from wty_psubst[OF this \<theta>'ty] show "wty V' [] (\<theta>0 x) (tsubst \<rho> (W x))" by (simp add: \<theta>0_def)
    qed
    have \<theta>'th: "\<theta>' x = \<theta> x" if "x \<in> vars_thm tps P" for x using nn that by (simp add: \<theta>'_def)
    have Pi: "psubst \<rho> \<theta>0 0 P = psubst \<rho> \<theta> 0 P"
      by (rule psubst_cong) (use \<theta>0th \<theta>'th in \<open>auto simp: vars_thm_def\<close>)
    have tps0: "\<forall>(t, u)\<in>set tps. tr (psubst \<rho> \<theta>0 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 u)"
    proof (intro ballI, clarify)
      fix t u assume tu: "(t, u) \<in> set tps"
      have "psubst \<rho> \<theta>0 0 t = psubst \<rho> \<theta> 0 t" "psubst \<rho> \<theta>0 0 u = psubst \<rho> \<theta> 0 u"
        by (rule psubst_cong, use \<theta>0th \<theta>'th tu in \<open>force simp: vars_thm_def\<close>)+
      with s tu show "tr (psubst \<rho> \<theta>0 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 u)" by auto
    qed
    from prf_validD[OF pv g0 \<theta>0ty] tps0 have ok0: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 (zprf_tr p0)) (psubst \<rho> \<theta> 0 P)"
      by (auto simp: Pi)
    have \<theta>\<kappa>n: "\<forall>x. \<forall>y\<in>vars (\<theta>\<kappa> x). 0 \<le> snd y" using \<theta>\<kappa>v by blast
    have \<theta>0cl: "\<forall>x. \<not> loose_bvar (\<theta>0 x) 0"
    proof
      fix x
      have a: "proper (psubst TVar \<theta>\<kappa> 0 (\<Theta> x)) \<and> \<not> loose_bvar (psubst TVar \<theta>\<kappa> 0 (\<Theta> x)) 0"
        by (rule closed_psubst) (use hcl \<theta>\<kappa>cl in blast)+
      have "proper (\<theta>0 x) \<and> \<not> loose_bvar (\<theta>0 x) 0"
        unfolding \<theta>0_def by (rule closed_psubst) (use a \<theta>'cl(1) in auto)
      then show "\<not> loose_bvar (\<theta>0 x) 0" by blast
    qed
    have e0: "psubst \<rho> \<theta>0 0 a = psubst \<rho> \<theta>' 0 (psubst TVar \<theta>\<kappa> 0 (psubst TVar \<Theta> 0 a))" for a
    proof -
      have "\<theta>0 = (\<lambda>x. psubst \<rho> (\<lambda>y. psubst \<rho> \<theta>' 0 (\<theta>\<kappa> y)) 0 (\<Theta> x))"
        by (rule ext) (simp add: \<theta>0_def psubst_psubst tsubst_TVar_id)
      then show ?thesis by (simp add: psubst_psubst tsubst_TVar_id)
    qed
    have zpv': "zprf_all (\<lambda>t. zann_s A m t \<and> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> ?PV)) (\<lambda>_. True) p"
      by (rule zprf_all_mono[OF zpv]) auto
    have aeq: "prf_aeq (prf_inst \<rho> \<theta>0 0 (zprf_tr p0)) (prf_inst \<rho> \<theta>' 0 (zprf_tr (zrenp g (zrenp sepn p))))"
    proof (rule prf_rel_zrenp_aeq[OF rel zpv' _ \<theta>0cl])
      show "\<forall>x. \<not> loose_bvar (\<theta>' x) 0" using \<theta>'cl by blast
      show "0 \<le> (0 :: integer)" by simp
    next
      fix a t assume r: "zrel \<Theta> a (zdec (zrenv sepn t))" and t: "zann_s A m t \<and> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> ?PV)"
      from r have "ann_eq (Some (psubst TVar \<Theta> 0 a)) (Some (zdec (sepz t)))" by (simp add: zrel_def)
      from ann_eq_psubst[OF this, of \<theta>\<kappa> TVar] \<theta>\<kappa>cl \<theta>\<kappa>n
      have "ann_eq (Some (psubst TVar \<theta>\<kappa> 0 (psubst TVar \<Theta> 0 a))) (Some (psubst TVar \<theta>\<kappa> 0 (zdec (sepz t))))" by blast
      from ann_eq_psubst[OF this, of \<theta>' \<rho>] \<theta>'cl
      have "ann_eq (Some (psubst \<rho> \<theta>' 0 (psubst TVar \<theta>\<kappa> 0 (psubst TVar \<Theta> 0 a))))
          (Some (psubst \<rho> \<theta>' 0 (psubst TVar \<theta>\<kappa> 0 (zdec (sepz t)))))" by blast
      then show "ann_eq (Some (psubst \<rho> \<theta>0 0 a)) (Some (psubst \<rho> \<theta>' 0 (zdec (zrenv g (sepz t)))))"
        using zd t by (simp add: e0 gs)
    qed
    have "prf_inst \<rho> \<theta>' 0 (zprf_tr (zrenp \<nu> p)) = prf_inst \<rho> \<theta> 0 (zprf_tr (zrenp \<nu> p))"
    proof (rule prf_inst_cong)
      fix x assume "x \<in> prf_vars (zprf_tr (zrenp \<nu> p))"
      moreover have "\<forall>x\<in>prf_vars (zprf_tr (zrenp \<nu> p)). 0 \<le> snd x"
        using zinv_prf_vars[OF zi] by blast
      ultimately show "\<theta>' x = \<theta> x" by (simp add: \<theta>'_def)
    qed
    with prf_ok_aeq[OF ok0 aeq] gsp show "prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 (zprf_tr (zrenp \<nu> p))) (psubst \<rho> \<theta> 0 P)"
      by simp
  qed
  from A W'A wt' pv' zi show ?thesis unfolding zthm_prf_inv_def by blast
qed


subsection \<open>The instantiation of the normalisation of tight proofs\<close>

text \<open>
  The normalisation of a tight proof (\<open>znorm_proof\<close>) instantiates the types by \<open>ity\<close> and the
  variables by a table \<open>lk\<close> keyed by visible variables with their instantiated types, independently
  of the proof.
\<close>

lemma znorm_proof_inst:
  fixes V V' :: "indexname \<Rightarrow> ptyp" and env :: env and visible :: "pterm list"
    and PU :: "ptyp \<Rightarrow> bool"
  defines "\<theta> \<equiv> tyenv env" and "tvl \<equiv> visible_tvars visible" and "X \<equiv> {a. (a, V a) \<in> set (visible_vars visible)}"
  defines "\<rho>v \<equiv> \<lambda>v S. if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S"
  assumes ne: "\<not> env_is_empty env" "visible \<noteq> []"
    and ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and et: "\<forall>U\<in>etys env. tcons \<theta> U"
    and zo: "tyenv_zok \<theta>" and zt: "tenv_zok ztargs env"
    and tv: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v \<and> tcons \<theta> (TVar v S)"
    and vv: "\<forall>(a, T)\<in>set (visible_vars visible). (T = V a \<or> vt_lookup (tenv env) a = None) \<and> 0 \<le> snd a \<and>
      tvars T \<subseteq> set tvl"
    and vn: "\<forall>a\<in>X. \<exists>t' rb. norm_term env (Var a (tsubst \<rho>v (V a))) = return t' \<and>
      swf_tm ar rb (Var a (tsubst \<rho>v (V a))) \<and> has_type V' [] t' (tsubst \<rho>v (V a))"
    and pu: "\<And>U. PU U \<Longrightarrow> tcons \<theta> U \<Longrightarrow> PU (tnorm \<theta> U)"
    and pe: "\<forall>T\<in>zetys ztargs env. PU (typ_of T)"
    and pvv: "\<forall>(a, T)\<in>set (visible_vars visible). PU T"
  shows "\<exists>ity lk. (\<forall>q. znorm_proof ztargs env visible q =
      map_zproof ity (\<lambda>t. liftOZ (beta_norm_term (zsubst_term ity lk t))) q \<bind> (\<lambda>p. liftOZ (beta_norm_prooft p))) \<and>
    (\<forall>T. typ_of (ity T) = tsubst \<rho>v (typ_of T)) \<and> (\<forall>T. zcan T \<longrightarrow> zcan (ity T)) \<and>
    (\<forall>x K u. lk (x, K) = Some u \<longrightarrow>
      ((x \<in> X \<and> K = ity (ztyp_of (V x)) \<longrightarrow> ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u) \<and>
         has_type V' [] (zdec u) (tsubst \<rho>v (V x)) \<and> (\<exists>rb. swf_tm ar rb (Var x (tsubst \<rho>v (V x))))) \<and>
       (\<not> (x \<in> X \<and> K = ity (ztyp_of (V x))) \<longrightarrow> vt_lookup (tenv env) x = None \<and> zdec u = Var x (typ_of K))) \<and>
      (\<forall>T\<in>ztys u. zcan T \<and> tcons \<theta> (typ_of T) \<and> PU (typ_of T)) \<and> 0 \<le> snd x \<and>
      x \<in> fst ` set (visible_vars visible)) \<and>
    (\<forall>x. x \<in> X \<longrightarrow> lk (x, ity (ztyp_of (V x))) \<noteq> None)"
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
  have zity: "zcan (ity T)" if "zcan T" for T
  proof (cases "vt_is_empty \<theta>")
    case True
    with instT have "instT = None" by simp
    with that show ?thesis by (simp add: ity_def)
  next
    case False
    with instT obtain Us where Us: "mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) tvl = returnZ Us"
      "instT = Some (zip tvl Us)" by (auto simp: bindZ_eq_returnZ)
    have cU: "\<forall>U\<in>set Us'. zcan U" if "mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) l = returnZ Us'" for l Us'
      using that
    proof (induction l arbitrary: Us')
      case (Cons vS l)
      obtain v S where vS: "vS = (v, S)" by (cases vS)
      from Cons.prems vS obtain U Us'' where "znorm_type \<theta> (ZTVar v S) = returnZ U"
        "mapZ (\<lambda>(v, S). znorm_type \<theta> (ZTVar v S)) l = returnZ Us''" "Us' = U # Us''"
        by (auto simp: bindZ_eq_returnZ)
      with Cons.IH zcan_znorm_type[of \<theta> "ZTVar v S" U] show ?case by simp
    qed simp
    have "zcan (zsubst_type (map_of (zip tvl Us)) T)"
      by (rule zcan_zsubst_type[OF that]) (use cU[OF Us(1)] in \<open>auto dest: map_of_SomeD set_zip_rightD\<close>)
    with that Us(2) show ?thesis by (simp add: ity_def)
  qed
  have Gity: "zcan (ity T) \<and> PU (typ_of (ity T))" if "zcan T \<and> PU (typ_of T)" "ztyp_vis tvl \<theta> T" for T
  proof -
    have "typ_of (ity T) = tnorm \<theta> (typ_of T)" using that(2) by (simp add: ity' ztyp_vis_def vnorm)
    with that pu zity show ?thesis by (simp add: ztyp_vis_def)
  qed
  define G where "G T \<longleftrightarrow> zcan T \<and> tcons \<theta> (typ_of T) \<and> PU (typ_of T)" for T
  have GG: "G T'" if "G T" "znorm_type \<theta> T = returnZ T'" for T T'
  proof -
    from that(1) have t: "tcons \<theta> (typ_of T)" by (simp add: G_def)
    from znorm_type_ok[OF ac tc zo t] that(2) have e: "typ_of T' = tnorm \<theta> (typ_of T)" by auto
    with that pu tcons_tnorm[OF ac] zcan_znorm_type show ?thesis by (auto simp: G_def)
  qed
  text \<open>The visible variables and their normal forms.\<close>
  have Vv: "typ_of (ztyp_of (V a)) = V a" "tvars (V a) \<subseteq> set tvl" if "a \<in> X" for a
  proof -
    from that have "(a, V a) \<in> set (visible_vars visible)" by (simp add: X_def)
    with vv have "tvars (V a) \<subseteq> set tvl" by auto
    then show "tvars (V a) \<subseteq> set tvl" by simp
    then show "typ_of (ztyp_of (V a)) = V a" using tvn by (intro typ_of_ztyp_of) fastforce
  qed
  have Tv: "typ_of (ztyp_of T) = T" "tvars T \<subseteq> set tvl" "0 \<le> snd a"
    if "(a, T) \<in> set (visible_vars visible)" for a T
  proof -
    from that vv show "tvars T \<subseteq> set tvl" "0 \<le> snd a" by auto
    then show "typ_of (ztyp_of T) = T" using tvn by (intro typ_of_ztyp_of) fastforce
  qed
  define vs where "vs = zdedup_vars (map (\<lambda>(a, T). (a, ity (ztyp_of T))) (visible_vars visible))"
  have svs: "set vs = (\<lambda>(a, T). (a, ity (ztyp_of T))) ` set (visible_vars visible)"
    by (force simp: vs_def set_zdedup_vars)
  have svX: "(a, ity (ztyp_of (V a))) \<in> set vs" if "a \<in> X" for a
    using that svs by (force simp: X_def)
  have svE: "\<exists>T. (a, T) \<in> set (visible_vars visible) \<and> K = ity (ztyp_of T)" if "(a, K) \<in> set vs" for a K
    using that svs by auto
  have dvs: "distinct vs" by (simp add: vs_def distinct_zdedup_vars)
  have zn: "\<exists>u. znorm_term ztargs env (ZVar a T) = returnZ u \<and>
      ok (norm_term env (Var a (tsubst \<rho>v (V a)))) (zdec u) \<and> has_type V' [] (zdec u) (tsubst \<rho>v (V a)) \<and>
      (\<exists>rb. swf_tm ar rb (Var a (tsubst \<rho>v (V a))))"
    if a: "a \<in> X" and T: "T = ity (ztyp_of (V a))" for a T
  proof -
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
  have zn0: "\<exists>u. znorm_term ztargs env (ZVar a K) = returnZ u \<and>
      (a \<in> X \<and> K = ity (ztyp_of (V a)) \<or> vt_lookup (tenv env) a = None \<and> zdec u = Var a (typ_of K))"
    if aK: "(a, K) \<in> set vs" for a K
  proof -
    from svE[OF aK] obtain T where aT: "(a, T) \<in> set (visible_vars visible)" and K: "K = ity (ztyp_of T)"
      by blast
    show ?thesis
    proof (cases "T = V a")
      case True
      then have a: "a \<in> X" using aT by (simp add: X_def)
      from zn[OF a HOL.refl] obtain u where "znorm_term ztargs env (ZVar a (ity (ztyp_of (V a)))) = returnZ u"
        by blast
      with a K True show ?thesis by blast
    next
      case False
      with vv aT have ub: "vt_lookup (tenv env) a = None" by auto
      note tv' = Tv[OF aT]
      have tK: "typ_of K = tsubst \<rho>v T" by (simp add: K ity' tv'(1))
      have tn: "tsubst \<rho>v T = tnorm \<theta> T" using tv'(2) by (intro vnorm) auto
      have tcT: "tcons \<theta> (tsubst \<rho>v T)" using tn tcons_tnorm[OF ac] by simp
      have n: "norm_term env (Var a (tsubst \<rho>v T)) = return (Var a (tsubst \<rho>v T))"
        using norm_term_unbound[OF ub ac[unfolded \<theta>_def] tc[unfolded \<theta>_def] tcT[unfolded \<theta>_def]] tn
          tnorm_idem[OF ac]
        by (simp add: \<theta>_def)
      have "\<exists>z'. znorm_term ztargs env (ZVar a K) = returnZ z' \<and> zdec z' = Var a (tsubst \<rho>v T)"
        by (rule znorm_term_sim[OF n]) (use tv'(3) tK tcT ac tc et zo zt in \<open>auto simp: \<theta>_def\<close>)
      with ub tK show ?thesis by auto
    qed
  qed
  have ex0: "\<exists>ys. mapZ f xs = returnZ ys" if "\<forall>x\<in>set xs. \<exists>y. f x = returnZ y" for f :: "indexname \<times> ztyp \<Rightarrow> zterm Z" and xs
    using that by (induction xs) auto
  have "\<forall>x\<in>set vs. \<exists>u. (\<lambda>(a, T). znorm_term ztargs env (ZVar a T)) x = returnZ u"
    using zn0 by fastforce
  from ex0[OF this] obtain us where us: "mapZ (\<lambda>(a, T). znorm_term ztargs env (ZVar a T)) vs = returnZ us"
    by blast
  have lus: "length us = length vs" using us
    by (induction vs arbitrary: us) (auto simp: bindZ_eq_returnZ)
  have usi: "znorm_term ztargs env (ZVar (fst (vs ! i)) (snd (vs ! i))) = returnZ (us ! i)" if "i < length vs" for i
    using us that by (induction vs arbitrary: us i) (auto simp: bindZ_eq_returnZ nth_Cons split: nat.splits)
  have Gus: "\<forall>T\<in>ztys u. G T" if "u \<in> set us" for u
  proof -
    from that obtain i where i: "i < length vs" "us ! i = u" using lus by (auto simp: in_set_conv_nth)
    obtain a T where aT: "vs ! i = (a, T)" by (cases "vs ! i")
    have "(a, T) \<in> set vs" using i(1) aT nth_mem by metis
    from svE[OF this] obtain T0 where aT0: "(a, T0) \<in> set (visible_vars visible)" and T: "T = ity (ztyp_of T0)"
      by blast
    have zu: "znorm_term ztargs env (ZVar a T) = returnZ u" using usi[OF i(1)] aT i(2) by simp
    have tVa: "tvars T0 \<subseteq> set tvl" "typ_of (ztyp_of T0) = T0" using Tv[OF aT0] by auto
    have tnv: "tsubst \<rho>v T0 = tnorm \<theta> T0" using tVa(1) by (intro vnorm) auto
    have tcV: "tcons \<theta> T0" using tVa(1) tv unfolding tcons_def by fastforce
    have PV: "PU T0" using aT0 pvv by auto
    have GT: "G T"
      using zity[of "ztyp_of T0"] tnv tcV PV pu tcons_tnorm[OF ac] by (simp add: G_def T ity' tVa(2))
    have GE: "G T" if "T \<in> zetys ztargs env" for T
    proof -
      from that obtain x U v zv where l: "vt_lookup (tenv env) x = Some (U, v)" "zterm_of ztargs v = returnZ zv"
        "T \<in> ztys zv" by (auto simp: zetys_def)
      have "\<exists>zu. zterm_of ztargs v = returnZ zu \<and> zdec zu = v \<and> (\<forall>V\<in>ztys zu. tcons (tyenv env) (typ_of V))"
        using zt l(1) unfolding tenv_zok_def by blast
      then obtain zv' where "zterm_of ztargs v = returnZ zv'" "\<forall>V\<in>ztys zv'. tcons \<theta> (typ_of V)"
        by (auto simp: \<theta>_def)
      with l have "tcons \<theta> (typ_of T)" by simp
      moreover have "zcan T" using ztys_zterm_of_zcan[OF l(2)] l(3) by blast
      moreover have "PU (typ_of T)" using pe that by blast
      ultimately show ?thesis by (simp add: G_def)
    qed
    show ?thesis
      by (rule ztys_znorm_term[OF zu]) (use GT GE GG in \<open>auto simp: \<theta>_def\<close>)
  qed
  define lk where "lk = zlookup_var (zip vs us)"
  have lkm: "lk k = map_of (zip vs us) k" for k by (simp add: lk_def zlookup_var_map_of)
  have eq: "znorm_proof ztargs env visible q =
      map_zproof ity (\<lambda>t. liftOZ (beta_norm_term (zsubst_term ity lk t))) q \<bind> (\<lambda>p. liftOZ (beta_norm_prooft p))" for q
    using ne instT[unfolded \<theta>_def tvl_def] us
    by (simp add: znorm_proof_def ity_def[symmetric] vs_def[symmetric] lk_def Let_def tvl_def[symmetric])
  have lku: "((x \<in> X \<and> K = ity (ztyp_of (V x)) \<longrightarrow> ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u) \<and>
         has_type V' [] (zdec u) (tsubst \<rho>v (V x)) \<and> (\<exists>rb. swf_tm ar rb (Var x (tsubst \<rho>v (V x))))) \<and>
       (\<not> (x \<in> X \<and> K = ity (ztyp_of (V x))) \<longrightarrow> vt_lookup (tenv env) x = None \<and> zdec u = Var x (typ_of K))) \<and>
      (\<forall>T\<in>ztys u. zcan T \<and> tcons \<theta> (typ_of T) \<and> PU (typ_of T)) \<and> 0 \<le> snd x \<and>
      x \<in> fst ` set (visible_vars visible)"
    if l: "lk (x, K) = Some u" for x K u
  proof -
    from l obtain i where i: "i < length vs" "vs ! i = (x, K)" "us ! i = u"
      using lus by (auto simp: lkm in_set_zip dest!: map_of_SomeD)
    have xK: "(x, K) \<in> set vs" using i nth_mem by metis
    have zu: "znorm_term ztargs env (ZVar x K) = returnZ u" using usi[OF i(1)] i by simp
    from zn0[OF xK] obtain u' where u': "znorm_term ztargs env (ZVar x K) = returnZ u'"
      "x \<in> X \<and> K = ity (ztyp_of (V x)) \<or> vt_lookup (tenv env) x = None \<and> zdec u' = Var x (typ_of K)"
      by blast
    from u'(1) zu have uu: "u' = u" by (simp add: returnZ_def)
    have c1: "(x \<in> X \<and> K = ity (ztyp_of (V x)) \<longrightarrow> ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u) \<and>
         has_type V' [] (zdec u) (tsubst \<rho>v (V x)) \<and> (\<exists>rb. swf_tm ar rb (Var x (tsubst \<rho>v (V x))))) \<and>
       (\<not> (x \<in> X \<and> K = ity (ztyp_of (V x))) \<longrightarrow> vt_lookup (tenv env) x = None \<and> zdec u = Var x (typ_of K))"
    proof (cases "x \<in> X \<and> K = ity (ztyp_of (V x))")
      case True
      from zn[OF conjunct1[OF True] conjunct2[OF True]] zu True show ?thesis by (auto simp: returnZ_def)
    next
      case False
      with u'(2) uu have "vt_lookup (tenv env) x = None \<and> zdec u = Var x (typ_of K)" by simp
      with False show ?thesis by blast
    qed
    have "u \<in> set us" using i lus by (metis nth_mem)
    from Gus[OF this] have "\<forall>T\<in>ztys u. zcan T \<and> tcons \<theta> (typ_of T) \<and> PU (typ_of T)" by (simp add: G_def)
    moreover have "0 \<le> snd x" using svE[OF xK] Tv(3) by blast
    moreover have "x \<in> fst ` set (visible_vars visible)" using svE[OF xK] by force
    ultimately show ?thesis using c1 by blast
  qed
  have lkX: "lk (x, ity (ztyp_of (V x))) \<noteq> None" if "x \<in> X" for x
  proof -
    have "(x, ity (ztyp_of (V x))) \<in> set vs" using svX[OF that] .
    then show ?thesis using lus by (auto simp: lkm map_of_zip_is_Some[symmetric])
  qed
  show ?thesis
    by (rule exI[of _ ity], rule exI[of _ lk]) (use eq ity' zity lku lkX in blast)
qed


subsection \<open>Normalisation of a tight proof with renamed variables\<close>

text \<open>The instantiation of the separated variables is an instantiation by their names.\<close>

lemma zdec_sepz_zsubst:
  assumes "\<forall>T\<in>ztys t. typ_of (ity T) = tsubst \<rho> (typ_of T)"
    "\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> vk (x, ity T) = None"
    "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
      \<Theta>s (sepn x T) = zdec (sepz (case vk (x, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity T)))"
    "\<forall>y. \<not> loose_bvar (\<Theta>s y) 0"
  shows "zdec (sepz (zsubst_term ity vk t)) = psubst \<rho> \<Theta>s 0 (zdec (sepz t))"
  using assms
proof (induction t)
  case (ZVar x T)
  then show ?case by (cases "snd x = -1") (auto simp: incr_boundvars_eq split: option.splits)
next
  case (ZConst0 c)
  then show ?case using tsubst_zconst_typ[of \<rho> c "[]"] by simp
next
  case (ZConst1 c T)
  then show ?case using tsubst_zconst_typ[of \<rho> c "[typ_of T]"] by simp
next
  case (ZConst c Ts)
  then have "zconst_typ c (map (\<lambda>x. typ_of (ity x)) Ts) = zconst_typ c (map (\<lambda>x. tsubst \<rho> (typ_of x)) Ts)"
    by (simp cong: map_cong)
  with ZConst show ?case using tsubst_zconst_typ[of \<rho> c "map typ_of Ts"] by (simp add: comp_def)
next
  case (ZAbs a T t)
  then have "psubst \<rho> \<Theta>s 1 (zdec (sepz t)) = psubst \<rho> \<Theta>s 0 (zdec (sepz t))" by (intro psubst_closed_lev) auto
  with ZAbs show ?case by simp
next
  case (ZOfclass T c)
  then show ?case by (simp add: of_class_def propT_def)
qed simp_all

lemma zdec_Var_inv: "zdec u = Var x T \<Longrightarrow> \<exists>K. u = ZVar x K \<and> typ_of K = T \<and> snd x \<noteq> -1"
  by (cases u) (auto simp: of_class_def split: if_splits)

lemma zvars_zsubst_term:
  "(y, U) \<in> zvars (zsubst_term ity vk t) \<Longrightarrow>
    (\<exists>x T. (x, T) \<in> zvars t \<and> vk (x, ity T) = None \<and> y = x \<and> U = ity T) \<or>
    (\<exists>x T u. (x, T) \<in> zvars t \<and> vk (x, ity T) = Some u \<and> (y, U) \<in> zvars u)"
  by (induction t) (force split: option.splits)+

text \<open>Mapping a tight proof and its renaming.\<close>

lemma prf_vars_zprf_tr: "prf_vars (zprf_tr q) = fst ` zprf_zvars q"
  by (induction q) (auto simp: vars_zdec image_iff; force)+

lemma zprf_zvars_snd: "(x, T) \<in> zprf_zvars q \<Longrightarrow> snd x \<noteq> -1"
  by (induction q) auto

lemma zprf_all_zprf_zvars_ex: "zprf_all P Q p \<Longrightarrow> (x, T) \<in> zprf_zvars p \<Longrightarrow> \<exists>t. P t \<and> (x, T) \<in> zvars t"
  by (induction p) auto

lemma prf_rel_Abst_ident: "prf_rel R (\<lambda>T. T) p p' \<Longrightarrow> prf_rel R (\<lambda>T. T) (Abst a T p) (Abst a T p')"
  using prf_rel.Abst[of R "\<lambda>T. T" p p' a T] by (simp add: option.map_ident)

lemma map_zproof_ren2:
  assumes "zconst_free p" "zno_class p" "zprf_all P Q p"
    and tm: "\<And>t. P t \<Longrightarrow> \<exists>c a. tm t = returnZ c \<and> tm (zrenv f t) = returnZ a \<and> R (zdec c) (zdec (sepz a)) \<and>
      beta_norm_term c = Some c \<and> beta_norm_term a = Some a \<and> S a"
    and ty: "\<And>T. Q T \<Longrightarrow> Q' (ty T)"
  shows "\<exists>q q'. map_zproof ty tm p = returnZ q \<and> map_zproof ty tm (zrenp f p) = returnZ q' \<and>
    prf_rel R (\<lambda>T. T) (zprf_tr q) (zprf_tr (zrenp sepn q')) \<and> (zrf p \<longrightarrow> zrfn q \<and> zrfn q') \<and>
    zconst_free q' \<and> zno_class q' \<and> zprf_all S Q' q'"
  using assms(1-3)
proof (induction p)
  case (ZAbst a T r)
  from ZAbst.prems have r: "zconst_free r" "zno_class r" "zprf_all P Q r" and QT: "Q T" by simp_all
  from ZAbst.IH[OF r] obtain q q' where q: "map_zproof ty tm r = returnZ q" "map_zproof ty tm (zrenp f r) = returnZ q'"
    "prf_rel R (\<lambda>T. T) (zprf_tr q) (zprf_tr (zrenp sepn q'))" "zrf r \<longrightarrow> zrfn q \<and> zrfn q'" "zconst_free q'" "zno_class q'"
    "zprf_all S Q' q'" by blast
  have "prf_rel R (\<lambda>T. T) (zprf_tr (ZAbst a (ty T) q)) (zprf_tr (zrenp sepn (ZAbst a (ty T) q')))"
    using prf_rel_Abst_ident[OF q(3)] by simp
  with q QT ty show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (ZAbsp a t r)
  from ZAbsp.prems have r: "zconst_free r" "zno_class r" "zprf_all P Q r" and Pt: "P t" by simp_all
  from ZAbsp.IH[OF r] obtain q q' where q: "map_zproof ty tm r = returnZ q" "map_zproof ty tm (zrenp f r) = returnZ q'"
    "prf_rel R (\<lambda>T. T) (zprf_tr q) (zprf_tr (zrenp sepn q'))" "zconst_free q'" "zno_class q'" "zprf_all S Q' q'" by blast
  from tm[OF Pt] obtain c u where t: "tm t = returnZ c" "tm (zrenv f t) = returnZ u" "R (zdec c) (zdec (sepz u))" "S u"
    by blast
  have "prf_rel R (\<lambda>T. T) (zprf_tr (ZAbsp a c q)) (zprf_tr (zrenp sepn (ZAbsp a u q')))"
    using prf_rel.AbsP[of R "Some (zdec c)" "Some (zdec (sepz u))" "\<lambda>T. T", OF _ q(3)] t(3) by simp
  with q t show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (ZAppt r t)
  from ZAppt.prems have r: "zconst_free r" "zno_class r" "zprf_all P Q r" and Pt: "P t" by simp_all
  from ZAppt.IH[OF r] obtain q q' where q: "map_zproof ty tm r = returnZ q" "map_zproof ty tm (zrenp f r) = returnZ q'"
    "prf_rel R (\<lambda>T. T) (zprf_tr q) (zprf_tr (zrenp sepn q'))" "zrf r \<longrightarrow> zrfn q \<and> zrfn q'" "zconst_free q'" "zno_class q'"
    "zprf_all S Q' q'" by blast
  from tm[OF Pt] obtain c u where t: "tm t = returnZ c" "tm (zrenv f t) = returnZ u" "R (zdec c) (zdec (sepz u))"
    "beta_norm_term c = Some c" "beta_norm_term u = Some u" "S u"
    by blast
  have a1: "(\<exists>a T r'. q = ZAbst a T r') \<longleftrightarrow> (\<exists>a T r'. r = ZAbst a T r')" by (rule map_zproof_ZAbst[OF q(1)])
  have a2: "(\<exists>a T r'. q' = ZAbst a T r') \<longleftrightarrow> (\<exists>a T r'. zrenp f r = ZAbst a T r')" by (rule map_zproof_ZAbst[OF q(2)])
  have a3: "(\<exists>a T r'. zrenp f r = ZAbst a T r') \<longleftrightarrow> (\<exists>a T r'. r = ZAbst a T r')" by (rule zrenp_is_ZAbst)
  have "prf_rel R (\<lambda>T. T) (zprf_tr (ZAppt q c)) (zprf_tr (zrenp sepn (ZAppt q' u)))"
    using prf_rel.PAppt[OF q(3), of "Some (zdec c)" "Some (zdec (sepz u))"] t(3) by simp
  with q t a1 a2 a3 show ?case by (auto simp: bindZ_eq_returnZ)
next
  case (ZAppp r1 r2)
  from ZAppp.prems have r: "zconst_free r1" "zno_class r1" "zprf_all P Q r1" "zconst_free r2" "zno_class r2" "zprf_all P Q r2"
    by simp_all
  from ZAppp.IH(1)[OF r(1-3)] ZAppp.IH(2)[OF r(4-6)] obtain q1 q1' q2 q2' where
    "map_zproof ty tm r1 = returnZ q1" "map_zproof ty tm (zrenp f r1) = returnZ q1'"
    "prf_rel R (\<lambda>T. T) (zprf_tr q1) (zprf_tr (zrenp sepn q1'))" "zconst_free q1'" "zno_class q1'" "zprf_all S Q' q1'"
    "map_zproof ty tm r2 = returnZ q2" "map_zproof ty tm (zrenp f r2) = returnZ q2'"
    "prf_rel R (\<lambda>T. T) (zprf_tr q2) (zprf_tr (zrenp sepn q2'))" "zconst_free q2'" "zno_class q2'" "zprf_all S Q' q2'"
    by blast
  then show ?case by (auto simp: bindZ_eq_returnZ intro: prf_rel.PAppp)
qed (auto intro: prf_rel.intros)


text \<open>
  The normalisation of a tight proof whose hidden variables are renamed (\<open>\<mu>\<close>, not to names of
  visible variables or of variables of the environment): its annotations, with separated
  variables, are instances of those of the normalisation of the tight proof. A renamed hidden
  variable is instantiated like the variable of its new name, if that is visible with the
  instantiated type.
\<close>

lemma znorm_proof_ren:
  fixes V V' :: "indexname \<Rightarrow> ptyp" and env :: env and visible :: "pterm list"
    and PU :: "ptyp \<Rightarrow> bool" and PI :: "integer \<Rightarrow> bool" and \<mu> :: "name \<Rightarrow> name"
  defines "\<theta> \<equiv> tyenv env" and "tvl \<equiv> visible_tvars visible" and "X \<equiv> {a. (a, V a) \<in> set (visible_vars visible)}"
  defines "\<rho>v \<equiv> \<lambda>v S. if (v, S) \<in> set tvl then tnorm \<theta> (TVar v S) else TVar v S"
  assumes ne: "\<not> env_is_empty env" "visible \<noteq> []"
    and ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and et: "\<forall>U\<in>etys env. tcons \<theta> U"
    and zo: "tyenv_zok \<theta>" and zt: "tenv_zok ztargs env"
    and tv: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v \<and> tcons \<theta> (TVar v S)"
    and vv: "\<forall>(a, T)\<in>set (visible_vars visible). (T = V a \<or> vt_lookup (tenv env) a = None) \<and> 0 \<le> snd a \<and>
      tvars T \<subseteq> set tvl"
    and vn: "\<forall>a\<in>X. \<exists>t' rb. norm_term env (Var a (tsubst \<rho>v (V a))) = return t' \<and>
      swf_tm ar rb (Var a (tsubst \<rho>v (V a))) \<and> has_type V' [] t' (tsubst \<rho>v (V a))"
    and vh: "\<forall>x. x \<notin> X \<longrightarrow> V' x = tsubst \<rho>v (V x)"
    and pu: "\<And>U. PU U \<Longrightarrow> tcons \<theta> U \<Longrightarrow> PU (tnorm \<theta> U)"
    and pe: "\<forall>T\<in>zetys ztargs env. PU (typ_of T)"
    and pvv: "\<forall>(a, T)\<in>set (visible_vars visible). PU T"
    and pa: "zprf_all (zann_vis V tvl X env) (ztyp_vis tvl \<theta>) p"
    and pc: "zconst_free p" "zno_class p" "zrf p"
    and pz: "zprf_all (\<lambda>t. \<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) (\<lambda>T. zcan T \<and> PU (typ_of T)) p"
    and pi: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x)) (\<lambda>_. True) p"
    and pie: "\<forall>x\<in>fst ` bvps env. 0 \<le> snd x \<and> PI (snd x)" and pin: "\<And>k. PI k \<Longrightarrow> 0 \<le> k"
    and mu: "\<forall>x T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow>
      x \<notin> fst ` set (visible_vars visible) \<and> x \<notin> fst ` bvps env"
    and zp: "znorm_proof ztargs env visible p = returnZ p'"
  shows "\<exists>p'' \<Theta>'. znorm_proof ztargs env visible (zrenp (nren \<mu>) p) = returnZ p'' \<and>
    prf_rel (zrel \<Theta>') (\<lambda>T. T) (zprf_tr p') (zprf_tr (zrenp sepn p'')) \<and>
    (\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow>
      \<Theta>' x = Var (sepn x (ztyp_of (V' x))) (typ_of (ztyp_of (V' x)))) \<and>
    (\<forall>x. proper (\<Theta>' x) \<and> \<not> loose_bvar (\<Theta>' x) 0) \<and>
    (\<forall>x T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> has_type Wenc [] (\<Theta>' x) (V' x) \<and>
      (\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> PI (snd y))) \<and>
    zconst_free p'' \<and> zno_class p'' \<and> zrfn p'' \<and>
    zprf_all (\<lambda>t. (\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) \<and>
      (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x) \<and> (\<exists>w. typ_of T = V' w))) (\<lambda>T. zcan T \<and> PU (typ_of T)) p'' \<and>
    (\<forall>n. zlb n p \<longrightarrow> zlb n p'') \<and>
    (\<forall>x\<in>prf_vars (zprf_tr p'). (\<exists>T. (x, T) \<in> zprf_zvars p) \<or> x \<in> fst ` bvps env)"
proof -
  from znorm_proof_inst[of env visible V V' PU, folded \<theta>_def tvl_def X_def, folded \<rho>v_def, OF ne ac tc et zo zt tv vv vn pu pe pvv]
  obtain ity vk where eq: "\<And>q. znorm_proof ztargs env visible q =
      map_zproof ity (\<lambda>t. liftOZ (beta_norm_term (zsubst_term ity vk t))) q \<bind> (\<lambda>p. liftOZ (beta_norm_prooft p))"
    and ity': "\<And>T. typ_of (ity T) = tsubst \<rho>v (typ_of T)" and zity: "\<And>T. zcan T \<Longrightarrow> zcan (ity T)"
    and lku: "\<And>x K u. vk (x, K) = Some u \<Longrightarrow>
      ((x \<in> X \<and> K = ity (ztyp_of (V x)) \<longrightarrow> ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u) \<and>
         has_type V' [] (zdec u) (tsubst \<rho>v (V x)) \<and> (\<exists>rb. swf_tm ar rb (Var x (tsubst \<rho>v (V x))))) \<and>
       (\<not> (x \<in> X \<and> K = ity (ztyp_of (V x))) \<longrightarrow> vt_lookup (tenv env) x = None \<and> zdec u = Var x (typ_of K))) \<and>
      (\<forall>T\<in>ztys u. zcan T \<and> tcons \<theta> (typ_of T) \<and> PU (typ_of T)) \<and> 0 \<le> snd x \<and>
      x \<in> fst ` set (visible_vars visible)"
    and lkX: "\<And>x. x \<in> X \<Longrightarrow> vk (x, ity (ztyp_of (V x))) \<noteq> None"
    by blast
  define tm where "tm t = liftOZ (beta_norm_term (zsubst_term ity vk t))" for t
  have vnorm: "tsubst \<rho>v U = tnorm \<theta> U" if "\<forall>(v, S)\<in>tvars U. (v, S) \<in> set tvl \<or> vt_lookup \<theta> v = None" for U
    using tsubst_vis_tnorm[OF ac that] by (simp add: \<rho>v_def)
  text \<open>The values of the table, with separated variables.\<close>
  define lv where "lv x K = (case vk (x, ity K) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity K))" for x K
  have lvm: "snd x = -1 \<Longrightarrow> vk (x, K) = None" for x K using lku[of x K] by (cases "vk (x, K)") auto
  have lvs: "has_type Wenc [] (zdec (sepz (lv x K))) (typ_of (ity K)) \<and> proper (zdec (sepz (lv x K))) \<and>
      \<not> loose_bvar (zdec (sepz (lv x K))) 0 \<and>
      (\<forall>(z, Tz)\<in>zvars (lv x K). snd z \<noteq> -1 \<longrightarrow> 0 \<le> snd z \<and> (z = x \<or> z \<in> fst ` bvps env)) \<and>
      (K = ztyp_of (V x) \<and> typ_of K = V x \<longrightarrow> (\<forall>(z, Tz)\<in>zvars (lv x K). snd z \<noteq> -1 \<longrightarrow> typ_of Tz = V' z)) \<and>
      (\<forall>(z, Tz)\<in>zvars (lv x K). snd z \<noteq> -1 \<longrightarrow> typ_of Tz = V' z \<or> typ_of Tz = typ_of (ity K)) \<and>
      (\<forall>T\<in>ztys (lv x K). zcan T \<and> PU (typ_of T) \<or> T = ity K)"
    if x: "snd x \<noteq> -1" and xp: "0 \<le> snd x" for x K
  proof (cases "vk (x, ity K)")
    case None
    have "typ_of (ity K) = V' x" if "K = ztyp_of (V x)" "typ_of K = V x"
    proof -
      have "x \<notin> X" using lkX None that(1) by blast
      with vh have "V' x = tsubst \<rho>v (V x)" by blast
      with that ity' show ?thesis by simp
    qed
    then show ?thesis using None x xp by (auto simp: lv_def intro: has_type.Var)
  next
    case (Some u)
    note l = lku[OF Some]
    have tz: "\<forall>T\<in>ztys u. zcan T \<and> PU (typ_of T)" using l by blast
    show ?thesis
    proof (cases "x \<in> X \<and> ity K = ity (ztyp_of (V x))")
      case True
      with l have n: "ok (norm_term env (Var x (tsubst \<rho>v (V x)))) (zdec u)"
        and h: "has_type V' [] (zdec u) (tsubst \<rho>v (V x))" by blast+
      have tK: "tsubst \<rho>v (V x) = typ_of (ity K)"
      proof -
        from True have "(x, V x) \<in> set (visible_vars visible)" by (simp add: X_def)
        with vv have "tvars (V x) \<subseteq> set tvl" by auto
        then have "typ_of (ztyp_of (V x)) = V x" using tv by (intro typ_of_ztyp_of) fastforce
        with True ity' show ?thesis by metis
      qed
      have hs: "has_type Wenc [] (zdec (sepz u)) (typ_of (ity K))"
        using has_type_zrenv[OF h idx_pres_sepn] tK by simp
      have vu: "vars (zdec u) \<subseteq> {x} \<union> fst ` bvps env" using norm_term_vars[OF n] by auto
      have zv: "\<forall>(z, Tz)\<in>zvars u. snd z \<noteq> -1 \<longrightarrow> 0 \<le> snd z \<and> (z = x \<or> z \<in> fst ` bvps env) \<and> typ_of Tz = V' z"
      proof (intro ballI impI, clarify)
        fix z Tz assume "(z, Tz) \<in> zvars u" "snd z \<noteq> -1"
        moreover from this have "z \<in> vars (zdec u)" by (auto simp: vars_zdec)
        ultimately show "0 \<le> snd z \<and> (z = x \<or> z \<in> fst ` bvps env) \<and> typ_of Tz = V' z"
          using vu xp pie has_type_zvars[OF h] by fastforce
      qed
      have pr: "proper (zdec (sepz u))" using has_type_proper[OF hs] .
      have cl: "\<not> loose_bvar (zdec (sepz u)) 0" using has_type_loose_bvar[OF hs] by simp
      have lvK: "lv x K = u" by (simp add: lv_def Some)
      have z1: "\<forall>(z, Tz)\<in>zvars u. snd z \<noteq> -1 \<longrightarrow> 0 \<le> snd z \<and> (z = x \<or> z \<in> fst ` bvps env)"
        and z2: "\<forall>(z, Tz)\<in>zvars u. snd z \<noteq> -1 \<longrightarrow> typ_of Tz = V' z"
        using zv by blast+
      have z3: "\<forall>(z, Tz)\<in>zvars u. snd z \<noteq> -1 \<longrightarrow> typ_of Tz = V' z \<or> typ_of Tz = typ_of (ity K)"
        using z2 by blast
      show ?thesis unfolding lvK using hs pr cl z1 z2 z3 tz by blast
    next
      case False
      with l have "zdec u = Var x (typ_of (ity K))" by blast
      from zdec_Var_inv[OF this] obtain K' where u: "u = ZVar x K'" "typ_of K' = typ_of (ity K)" by blast
      have "typ_of (ity K) = V' x" if "K = ztyp_of (V x)" "typ_of K = V x"
      proof -
        have "x \<notin> X" using False that(1) by blast
        with vh have "V' x = tsubst \<rho>v (V x)" by blast
        with that ity' show ?thesis by simp
      qed
      then show ?thesis using Some u x xp tz by (auto simp: lv_def intro: has_type.Var)
    qed
  qed
  text \<open>The instantiation by names of the separated variables.\<close>
  define inv where "inv y = (SOME xT. y = sepn (fst xT) (snd xT))" for y
  have inv: "inv (sepn x T) = (x, T)" for x T
    unfolding inv_def by (rule some_equality) (auto simp: sepn_inj)
  define \<Theta>s where "\<Theta>s y = (if \<exists>x T. y = sepn x T \<and> 0 \<le> snd x then zdec (sepz (lv (fst (inv y)) (snd (inv y))))
    else Var y (Wenc y))" for y
  have \<Theta>s: "\<Theta>s (sepn x T) = zdec (sepz (lv x T))" if "0 \<le> snd x" for x T
  proof -
    have "\<exists>x' T'. sepn x T = sepn x' T' \<and> 0 \<le> snd x'" using that by blast
    then show ?thesis by (simp add: \<Theta>s_def inv)
  qed
  have \<Theta>scl: "proper (\<Theta>s y) \<and> \<not> loose_bvar (\<Theta>s y) 0" for y
  proof (cases "\<exists>x T. y = sepn x T \<and> 0 \<le> snd x")
    case True
    then obtain x T where "y = sepn x T" "0 \<le> snd x" by blast
    with lvs[of x T] show ?thesis by (auto simp: \<Theta>s)
  qed (simp add: \<Theta>s_def)
  have \<Theta>sv: "\<forall>v\<in>vars (\<Theta>s (sepn x T)). 0 \<le> snd v \<and> (\<exists>z Tz. v = sepn z Tz \<and> (z, Tz) \<in> zvars (lv x T) \<and> snd z \<noteq> -1)"
    if x0: "0 \<le> snd x" for x T
  proof
    fix v assume "v \<in> vars (\<Theta>s (sepn x T))"
    then obtain Tv where "(v, Tv) \<in> zvars (sepz (lv x T))" "snd v \<noteq> -1" by (auto simp: \<Theta>s[OF x0] vars_zdec)
    then obtain z where z: "(z, Tv) \<in> zvars (lv x T)" "snd z \<noteq> -1" "v = sepn z Tv"
      by (auto simp: zvars_zrenv split: if_splits)
    have "snd x \<noteq> -1" using x0 by auto
    from lvs[OF this x0] z(1,2) have "0 \<le> snd z" by blast
    with z show "0 \<le> snd v \<and> (\<exists>z Tz. v = sepn z Tz \<and> (z, Tz) \<in> zvars (lv x T) \<and> snd z \<noteq> -1)"
      by (cases z) force
  qed
  text \<open>The renamed hidden variables and their instances.\<close>
  define RH where "RH = {x. (\<exists>T. (x, T) \<in> zprf_zvars p) \<and> \<mu> (fst x) \<noteq> fst x}"
  define \<Psi> where "\<Psi> y = (if \<exists>x\<in>RH. y = sepn x (ity (ztyp_of (V x)))
    then \<Theta>s (sepn (nren \<mu> (fst (inv y)) (ztyp_of (V (fst (inv y))))) (ztyp_of (V (fst (inv y)))))
    else if 0 \<le> snd y then Var y (Wenc y) else Free STR ''u'' (Wenc y))" for y
  have \<Psi>RH: "\<Psi> (sepn x (ity (ztyp_of (V x)))) = \<Theta>s (sepn (nren \<mu> x (ztyp_of (V x))) (ztyp_of (V x)))" if "x \<in> RH" for x
    using that by (auto simp: \<Psi>_def inv)
  have \<Psi>id: "\<Psi> (sepn z Tz) = Var (sepn z Tz) (typ_of Tz)" if "z \<notin> RH" "0 \<le> snd z" for z Tz
    using that by (auto simp: \<Psi>_def sepn_inj)
  define \<Theta>' where "\<Theta>' x = \<Psi> (sepn x (ztyp_of (V' x)))" for x
  have \<Psi>cl: "proper (\<Psi> y) \<and> \<not> loose_bvar (\<Psi> y) 0" for y using \<Theta>scl by (simp add: \<Psi>_def)
  have pvi: "0 \<le> snd x \<and> PI (snd x)" if "(x, T) \<in> zprf_zvars p" for x T
  proof -
    have "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> PI (snd x)) (\<lambda>_. True) p"
      by (rule zprf_all_mono[OF pi]) (use pin in auto)
    then have "\<forall>(x, T)\<in>zprf_zvars p. 0 \<le> snd x \<and> PI (snd x)" by (induction p) auto
    with that show ?thesis by blast
  qed
  have RHv: "x \<notin> X \<and> x \<notin> fst ` set (visible_vars visible) \<and> x \<notin> fst ` bvps env" if "x \<in> RH" for x
  proof -
    from that obtain T where "(x, T) \<in> zprf_zvars p" "\<mu> (fst x) \<noteq> fst x" by (auto simp: RH_def)
    with mu have a: "x \<notin> fst ` set (visible_vars visible)" "x \<notin> fst ` bvps env" by blast+
    moreover from a(1) have "x \<notin> X" by (force simp: X_def)
    ultimately show ?thesis by blast
  qed
  have \<Psi>v: "\<forall>v\<in>vars (\<Psi> y). 0 \<le> snd v" for y
  proof (cases "\<exists>x\<in>RH. y = sepn x (ity (ztyp_of (V x)))")
    case True
    then obtain x where x: "x \<in> RH" "y = sepn x (ity (ztyp_of (V x)))" by blast
    then obtain T where "(x, T) \<in> zprf_zvars p" by (auto simp: RH_def)
    with pvi have "0 \<le> snd (nren \<mu> x (ztyp_of (V x)))" by (simp add: nren_def)
    with \<Theta>sv x show ?thesis by (simp add: \<Psi>RH)
  next
    case False
    then show ?thesis by (simp add: \<Psi>_def)
  qed
  have ityPU: "zcan (ity T) \<and> PU (typ_of (ity T))" if "zcan T" "PU (typ_of T)" "ztyp_vis tvl \<theta> T" for T
  proof -
    have "typ_of (ity T) = tnorm \<theta> (typ_of T)" using that(3) by (simp add: ity' ztyp_vis_def vnorm)
    with that pu zity show ?thesis by (simp add: ztyp_vis_def)
  qed
  define SA where "SA a \<longleftrightarrow> (\<exists>Ts U. has_type Wenc Ts (zdec (sepz a)) U) \<and> (\<forall>T\<in>ztys a. zcan T \<and> PU (typ_of T)) \<and>
    (\<forall>(x, T)\<in>zvars a. snd x \<noteq> -1 \<longrightarrow> PI (snd x) \<and> (\<exists>w. typ_of T = V' w))" for a
  define P where "P t \<longleftrightarrow> ((zann_vis V tvl X env t \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T))) \<and>
    (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x))) \<and> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> zprf_zvars p)" for t
  text \<open>The annotations.\<close>
  have ann: "\<exists>c a. tm t = returnZ c \<and> tm (zrenv (nren \<mu>) t) = returnZ a \<and> zrel \<Theta>' (zdec c) (zdec (sepz a)) \<and>
      beta_norm_term c = Some c \<and> beta_norm_term a = Some a \<and> SA a \<and>
      (\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar (zdec t) k \<longrightarrow> \<not> loose_bvar (zdec a) k) \<and>
      (\<forall>(z, Tz)\<in>zvars c. snd z \<noteq> -1 \<longrightarrow> (\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env)"
    if Pt: "P t" for t
  proof -
    from Pt have zv: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> T = ztyp_of (V x) \<and> typ_of T = V x \<and>
        (x \<in> X \<or> vt_lookup (tenv env) x = None)"
      and zt': "\<forall>T\<in>ztys t. ztyp_vis tvl \<theta> T" and ht: "\<exists>Ts U. has_type V Ts (zdec t) U"
      and tz: "\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)" and ti: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x)"
      and tp: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (x, T) \<in> zprf_zvars p"
      by (auto simp: P_def zann_vis_def \<theta>_def)
    have tn: "0 \<le> snd x" if "(x, T) \<in> zvars t" "snd x \<noteq> -1" for x T using ti pin that by blast
    define ta where "ta = zrenv (nren \<mu>) t"
    have zta: "\<exists>x. (x, T) \<in> zvars t \<and> snd x \<noteq> -1 \<and> y = nren \<mu> x T" if "(y, T) \<in> zvars ta" "snd y \<noteq> -1" for y T
      using that by (auto simp: ta_def zvars_zrenv nren_def split: if_splits)
    have ztam: "snd y = -1 \<Longrightarrow> (y, T) \<in> zvars ta \<Longrightarrow> (y, T) \<in> zvars t" for y T
      by (auto simp: ta_def zvars_zrenv nren_def split: if_splits)
    obtain Ts U where htU: "has_type V Ts (zdec t) U" using ht by blast
    have hs: "has_type Wenc Ts (zdec (sepz t)) U" by (rule has_type_zrenv[OF htU idx_pres_sepn]) simp
    have sta: "sepz ta = zrenv (\<lambda>x T. sepn (nren \<mu> x T) T) t" by (simp add: ta_def zrenv_comp)
    have hsa: "has_type Wenc Ts (zdec (sepz ta)) U"
      unfolding sta by (rule has_type_zrenv[OF htU]) (simp_all add: idx_pres_def nren_def)
    have e1: "zdec (sepz (zsubst_term ity vk t)) = psubst \<rho>v \<Theta>s 0 (zdec (sepz t))"
    proof (rule zdec_sepz_zsubst)
      show "\<forall>T\<in>ztys t. typ_of (ity T) = tsubst \<rho>v (typ_of T)" using ity' by blast
      show "\<forall>(x, T)\<in>zvars t. snd x = -1 \<longrightarrow> vk (x, ity T) = None" using lvm by blast
      show "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow>
          \<Theta>s (sepn x T) = zdec (sepz (case vk (x, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity T)))"
        using \<Theta>s tn by (auto simp: lv_def)
      show "\<forall>y. \<not> loose_bvar (\<Theta>s y) 0" using \<Theta>scl by blast
    qed
    have e2: "zdec (sepz (zsubst_term ity vk ta)) = psubst \<rho>v \<Theta>s 0 (zdec (sepz ta))"
    proof (rule zdec_sepz_zsubst)
      show "\<forall>T\<in>ztys ta. typ_of (ity T) = tsubst \<rho>v (typ_of T)" using ity' by blast
      show "\<forall>(x, T)\<in>zvars ta. snd x = -1 \<longrightarrow> vk (x, ity T) = None" using lvm by blast
      show "\<forall>(x, T)\<in>zvars ta. snd x \<noteq> -1 \<longrightarrow>
          \<Theta>s (sepn x T) = zdec (sepz (case vk (x, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar x (ity T)))"
      proof (intro ballI impI, clarify)
        fix y T assume "(y, T) \<in> zvars ta" "snd y \<noteq> -1"
        from zta[OF this] obtain x where "(x, T) \<in> zvars t" "snd x \<noteq> -1" "y = nren \<mu> x T" by blast
        with tn have "0 \<le> snd y" by (simp add: nren_def)
        then show "\<Theta>s (sepn y T) = zdec (sepz (case vk (y, ity T) of Some u \<Rightarrow> u | None \<Rightarrow> ZVar y (ity T)))"
          by (simp add: \<Theta>s lv_def)
      qed
      show "\<forall>y. \<not> loose_bvar (\<Theta>s y) 0" using \<Theta>scl by blast
    qed
    have \<Theta>sty: "has_type Wenc [] (\<Theta>s y) (tsubst \<rho>v (Wenc y))" if "y = sepn x T" "0 \<le> snd x" for y x T
      using lvs[of x T] that ity' by (auto simp: \<Theta>s)
    have hvs: "\<forall>y\<in>vars (zdec (sepz w)). \<exists>x T. y = sepn x T \<and> (x, T) \<in> zvars w \<and> snd x \<noteq> -1" for w
      by (auto simp: vars_zdec zvars_zrenv split: if_splits; blast)
    have hi1: "has_type Wenc (map (tsubst \<rho>v) Ts) (zdec (sepz (zsubst_term ity vk t))) (tsubst \<rho>v U)"
    proof -
      have "has_type Wenc (map (tsubst \<rho>v) Ts @ []) (psubst \<rho>v \<Theta>s (integer_of_nat (length Ts)) (zdec (sepz t))) (tsubst \<rho>v U)"
      proof (rule has_type_psubst[OF hs], intro ballI)
        fix y assume "y \<in> vars (zdec (sepz t))"
        with hvs obtain x T where "y = sepn x T" "(x, T) \<in> zvars t" "snd x \<noteq> -1" by blast
        with tn \<Theta>sty show "has_type Wenc [] (\<Theta>s y) (tsubst \<rho>v (Wenc y))" by blast
      qed
      moreover have "psubst \<rho>v \<Theta>s (integer_of_nat (length Ts)) (zdec (sepz t)) = psubst \<rho>v \<Theta>s 0 (zdec (sepz t))"
        using \<Theta>scl by (intro psubst_closed_lev) auto
      ultimately show ?thesis by (simp add: e1)
    qed
    have hi2: "has_type Wenc (map (tsubst \<rho>v) Ts) (zdec (sepz (zsubst_term ity vk ta))) (tsubst \<rho>v U)"
    proof -
      have "has_type Wenc (map (tsubst \<rho>v) Ts @ []) (psubst \<rho>v \<Theta>s (integer_of_nat (length Ts)) (zdec (sepz ta))) (tsubst \<rho>v U)"
      proof (rule has_type_psubst[OF hsa], intro ballI)
        fix y assume "y \<in> vars (zdec (sepz ta))"
        with hvs obtain x T where y: "y = sepn x T" "(x, T) \<in> zvars ta" "snd x \<noteq> -1" by blast
        from zta[OF y(2,3)] obtain x0 where "(x0, T) \<in> zvars t" "snd x0 \<noteq> -1" "x = nren \<mu> x0 T" by blast
        with tn have "0 \<le> snd x" by (simp add: nren_def)
        with y \<Theta>sty show "has_type Wenc [] (\<Theta>s y) (tsubst \<rho>v (Wenc y))" by blast
      qed
      moreover have "psubst \<rho>v \<Theta>s (integer_of_nat (length Ts)) (zdec (sepz ta)) = psubst \<rho>v \<Theta>s 0 (zdec (sepz ta))"
        using \<Theta>scl by (intro psubst_closed_lev) auto
      ultimately show ?thesis by (simp add: e2)
    qed
    from beta_norm_term_term[OF hi1] obtain cs where cs: "beta_norm_term (sepz (zsubst_term ity vk t)) = Some cs"
      "has_type Wenc (map (tsubst \<rho>v) Ts) (zdec cs) (tsubst \<rho>v U)" by blast
    from cs(1) obtain c where c: "beta_norm_term (zsubst_term ity vk t) = Some c" "cs = sepz c"
      by (auto simp: beta_norm_term_zrenv)
    from beta_norm_term_term[OF hi2] obtain as where as: "beta_norm_term (sepz (zsubst_term ity vk ta)) = Some as"
      "has_type Wenc (map (tsubst \<rho>v) Ts) (zdec as) (tsubst \<rho>v U)" by blast
    from as(1) obtain a where a: "beta_norm_term (zsubst_term ity vk ta) = Some a" "as = sepz a"
      by (auto simp: beta_norm_term_zrenv)
    text \<open>The instance of the renamed variables.\<close>
    define g where "g y U = (if \<exists>x. y = sepn x U then sepn (nren \<mu> (fst (inv y)) U) U else y)" for y U
    have g: "g (sepn x T) T = sepn (nren \<mu> x T) T" for x T
    proof -
      have "\<exists>x'. sepn x T = sepn x' T" by blast
      then show ?thesis by (simp add: g_def inv)
    qed
    have gs: "zrenv g (sepz t) = sepz ta" by (simp add: zrenv_comp g ta_def)
    have ipg: "idx_pres g"
      unfolding idx_pres_def
    proof (intro allI)
      fix y U
      show "snd (g y U) = snd y"
      proof (cases "\<exists>x. y = sepn x U")
        case True
        then obtain x where "y = sepn x U" by blast
        then show ?thesis by (simp add: g nren_def)
      qed (simp add: g_def)
    qed
    define Ren where "Ren y = Var (g y (snd (inv y))) (Wenc y)" for y
    have zsta: "zdec (sepz ta) = psubst TVar Ren 0 (zdec (sepz t))"
    proof -
      have "zdec (zrenv g (sepz t)) = psubst TVar Ren 0 (zdec (sepz t))"
      proof (rule zdec_zrenv[OF _ ipg])
        fix y U assume "(y, U) \<in> zvars (sepz t)" "snd y \<noteq> -1"
        then obtain x where "y = sepn x U" by (auto simp: zvars_zrenv split: if_splits)
        then show "Ren y = Var (g y U) (typ_of U)" by (simp add: Ren_def inv)
      qed
      then show ?thesis by (simp add: gs)
    qed
    have ex: "zdec (sepz (zsubst_term ity vk ta)) = psubst TVar \<Psi> 0 (zdec (sepz (zsubst_term ity vk t)))"
    proof -
      have l: "zdec (sepz (zsubst_term ity vk ta)) = psubst \<rho>v (\<lambda>y. psubst \<rho>v \<Theta>s 0 (Ren y)) 0 (zdec (sepz t))"
        by (simp add: e2 zsta psubst_psubst tsubst_TVar_id)
      have r: "psubst TVar \<Psi> 0 (zdec (sepz (zsubst_term ity vk t))) = psubst \<rho>v (\<lambda>y. psubst TVar \<Psi> 0 (\<Theta>s y)) 0 (zdec (sepz t))"
        by (simp add: e1 psubst_psubst tsubst_TVar_id)
      have "psubst \<rho>v (\<lambda>y. psubst \<rho>v \<Theta>s 0 (Ren y)) 0 (zdec (sepz t)) = psubst \<rho>v (\<lambda>y. psubst TVar \<Psi> 0 (\<Theta>s y)) 0 (zdec (sepz t))"
      proof (rule psubst_cong)
        fix y assume "y \<in> vars (zdec (sepz t))"
        with hvs obtain x T where y: "y = sepn x T" "(x, T) \<in> zvars t" "snd x \<noteq> -1" by blast
        have x0: "0 \<le> snd x" by (rule tn[OF y(2,3)])
        have l1: "psubst \<rho>v \<Theta>s 0 (Ren y) = zdec (sepz (lv (nren \<mu> x T) T))"
          using x0 by (simp add: y Ren_def inv g \<Theta>s nren_def incr_boundvars_eq)
        show "psubst \<rho>v \<Theta>s 0 (Ren y) = psubst TVar \<Psi> 0 (\<Theta>s y)"
        proof (cases "\<mu> (fst x) = fst x")
          case True
          then have nx: "nren \<mu> x T = x" by (simp add: nren_def)
          have "x \<notin> RH" using True by (simp add: RH_def)
          have "psubst TVar \<Psi> 0 (zdec (sepz (lv x T))) = zdec (zrenv (\<lambda>y U. y) (sepz (lv x T)))"
          proof (rule zdec_zrenv[symmetric])
            fix y' U assume "(y', U) \<in> zvars (sepz (lv x T))" "snd y' \<noteq> -1"
            then obtain z where z: "(z, U) \<in> zvars (lv x T)" "snd z \<noteq> -1" "y' = sepn z U"
              by (auto simp: zvars_zrenv split: if_splits)
            from lvs[OF y(3) x0] z(1,2) have zb: "0 \<le> snd z" "z = x \<or> z \<in> fst ` bvps env" by blast+
            then have "z \<notin> RH" using \<open>x \<notin> RH\<close> RHv by blast
            with zb z(3) show "\<Psi> y' = Var y' (typ_of U)" by (simp add: \<Psi>id)
          qed (simp add: idx_pres_def)
          also have "\<dots> = zdec (sepz (lv x T))" by (simp add: zrenv_id)
          finally show ?thesis using l1 nx x0 by (simp add: y \<Theta>s)
        next
          case False
          then have xR: "x \<in> RH" using tp y(2,3) by (auto simp: RH_def)
          have T: "T = ztyp_of (V x)" using zv y(2,3) by blast
          have "vk (x, ity T) = None"
          proof (rule ccontr)
            assume "vk (x, ity T) \<noteq> None"
            then obtain u where "vk (x, ity T) = Some u" by blast
            from lku[OF this] RHv[OF xR] show False by blast
          qed
          then have "\<Theta>s y = Var (sepn x (ity T)) (typ_of (ity T))" using y(3) x0 by (simp add: y \<Theta>s lv_def)
          then have "psubst TVar \<Psi> 0 (\<Theta>s y) = \<Psi> (sepn x (ity (ztyp_of (V x))))" by (simp add: T incr_boundvars_eq)
          also have "\<dots> = \<Theta>s (sepn (nren \<mu> x T) T)" using \<Psi>RH[OF xR] by (simp add: T)
          also have "\<dots> = psubst \<rho>v \<Theta>s 0 (Ren y)" using x0 by (simp add: y Ren_def inv g incr_boundvars_eq nren_def)
          finally show ?thesis by simp
        qed
      qed
      with l r show ?thesis by simp
    qed
    text \<open>The variables of the instances.\<close>
    have vinst: "\<exists>x T. (x, T) \<in> zvars w \<and> snd x \<noteq> -1 \<and> (z, Tz) \<in> zvars (lv x T)"
      if "(z, Tz) \<in> zvars (zsubst_term ity vk w)" "snd z \<noteq> -1" for z Tz w
    proof -
      from zvars_zsubst_term[OF that(1)] show ?thesis
      proof (elim disjE exE conjE)
        fix x T assume a: "(x, T) \<in> zvars w" "vk (x, ity T) = None" "z = x" "Tz = ity T"
        with that(2) show ?thesis by (intro exI[of _ x] exI[of _ T]) (simp add: lv_def)
      next
        fix x T u assume a: "(x, T) \<in> zvars w" "vk (x, ity T) = Some u" "(z, Tz) \<in> zvars u"
        have "snd x \<noteq> -1"
        proof
          assume "snd x = -1"
          with lvm a(2) show False by simp
        qed
        with a show ?thesis by (intro exI[of _ x] exI[of _ T]) (simp add: lv_def)
      qed
    qed
    have cv: "zdec (sepz c) = psubst TVar (\<lambda>z. Var (sepn z (ztyp_of (V' z))) (typ_of (ztyp_of (V' z)))) 0 (zdec c)"
    proof (rule zdec_zrenv[OF _ idx_pres_sepn])
      fix z Tz assume zc: "(z, Tz) \<in> zvars c" "snd z \<noteq> -1"
      then have "(z, Tz) \<in> zvars (zsubst_term ity vk t)" using zvars_beta_norm_term[OF c(1)] by blast
      from vinst[OF this zc(2)] obtain x T where x: "(x, T) \<in> zvars t" "snd x \<noteq> -1" "(z, Tz) \<in> zvars (lv x T)"
        by blast
      have x0: "0 \<le> snd x" by (rule tn[OF x(1,2)])
      have T0: "T = ztyp_of (V x) \<and> typ_of T = V x" using zv x(1,2) by fast
      note T = T0[THEN conjunct1] T0[THEN conjunct2]
      from lvs[OF x(2) x0, of T] x(3) zc(2) T have ty: "typ_of Tz = V' z" by blast
      have "Tz \<in> ztys (lv x T)" using x(3) by (rule zvars_ztys)
      with lvs[OF x(2) x0, of T] have "zcan Tz \<or> Tz = ity T" by blast
      then have "zcan Tz" using zity tz zvars_ztys[OF x(1)] by blast
      then have "Tz = ztyp_of (V' z)" using ty ztyp_of_typ_of_zcan by metis
      then show "Var (sepn z (ztyp_of (V' z))) (typ_of (ztyp_of (V' z))) = Var (sepn z Tz) (typ_of Tz)" by simp
    qed
    have \<Theta>'e: "psubst TVar \<Theta>' 0 (zdec c) = psubst TVar \<Psi> 0 (zdec (sepz c))"
    proof -
      have "\<Theta>' = (\<lambda>x. \<Psi> (sepn x (ztyp_of (V' x))))" by (rule ext) (simp add: \<Theta>'_def)
      then show ?thesis by (simp add: cv psubst_psubst tsubst_TVar_id incr_boundvars_eq)
    qed
    text \<open>Normalisation.\<close>
    have pi1: "proper (zdec (sepz (zsubst_term ity vk t)))" using has_type_proper[OF hi1] .
    have pi2: "proper (zdec (sepz (zsubst_term ity vk ta)))" using has_type_proper[OF hi2] .
    from beta_norm_term_beta[OF cs(1) pi1] c(2)
    have b1: "proper (zdec (sepz c))" "tr (zdec (sepz (zsubst_term ity vk t))) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (sepz c))" by simp_all
    from beta_norm_term_beta[OF as(1) pi2] a(2)
    have b2: "proper (zdec (sepz a))" "tr (zdec (sepz (zsubst_term ity vk ta))) \<rightarrow>\<^sub>\<beta>\<^sup>* tr (zdec (sepz a))" by simp_all
    have vc0: "\<forall>v\<in>vars (zdec (sepz c)). 0 \<le> snd v"
    proof
      fix v assume "v \<in> vars (zdec (sepz c))"
      then obtain z Tz where z: "(z, Tz) \<in> zvars c" "snd z \<noteq> -1" "v = sepn z Tz"
        by (auto simp: vars_zdec zvars_zrenv split: if_splits)
      then have "(z, Tz) \<in> zvars (zsubst_term ity vk t)" using zvars_beta_norm_term[OF c(1)] by blast
      from vinst[OF this z(2)] obtain x T where x: "(x, T) \<in> zvars t" "snd x \<noteq> -1" "(z, Tz) \<in> zvars (lv x T)"
        by blast
      from lvs[OF x(2) tn[OF x(1,2)], of T] x(3) z(2) have "0 \<le> snd z" by blast
      with z(3) show "0 \<le> snd v" by simp
    qed
    have va0: "0 \<le> snd v \<and> PI (snd v)" if "(v, Tv) \<in> zvars a" "snd v \<noteq> -1" for v Tv
    proof -
      have "(v, Tv) \<in> zvars (zsubst_term ity vk ta)" using zvars_beta_norm_term[OF a(1)] that(1) by blast
      from vinst[OF this that(2)] obtain y T where y: "(y, T) \<in> zvars ta" "snd y \<noteq> -1" "(v, Tv) \<in> zvars (lv y T)"
        by blast
      from zta[OF y(1,2)] obtain x where x: "(x, T) \<in> zvars t" "snd x \<noteq> -1" "y = nren \<mu> x T" by blast
      have pix: "PI (snd x)" using ti x(1,2) by blast
      have y0: "0 \<le> snd y" using tn[OF x(1,2)] x(3) by (simp add: nren_def)
      from lvs[OF y(2) y0, of T] y(3) that(2) have "v = y \<or> v \<in> fst ` bvps env" "0 \<le> snd v" by blast+
      then show ?thesis using pie pix x(3) by (auto simp: nren_def)
    qed
    have va1: "\<forall>v\<in>vars (zdec (sepz a)). 0 \<le> snd v"
    proof
      fix v assume "v \<in> vars (zdec (sepz a))"
      then obtain z Tz where "(z, Tz) \<in> zvars a" "snd z \<noteq> -1" "v = sepn z Tz"
        by (auto simp: vars_zdec zvars_zrenv split: if_splits)
      with va0 show "0 \<le> snd v" by simp
    qed
    have ae1: "ann_eq (Some (zdec (sepz (zsubst_term ity vk t)))) (Some (zdec (sepz c)))"
      using b1 vc0 by (simp add: ann_eq_def remove_types_equiv beta_into_equiv)
    from ann_eq_psubst[OF ae1, of \<Psi> TVar] \<Psi>cl \<Psi>v
    have ae2: "ann_eq (Some (psubst TVar \<Psi> 0 (zdec (sepz (zsubst_term ity vk t))))) (Some (psubst TVar \<Psi> 0 (zdec (sepz c))))"
      by blast
    have rel: "zrel \<Theta>' (zdec c) (zdec (sepz a))"
    proof -
      have "tr (remove_types (psubst TVar \<Theta>' 0 (zdec c))) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (zdec (sepz (zsubst_term ity vk ta))))"
        using ae2 by (simp add: ann_eq_def \<Theta>'e ex equiv_sym)
      also have "\<dots> \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (remove_types (zdec (sepz a)))" using b2 by (simp add: remove_types_equiv beta_into_equiv)
      finally show ?thesis using b2(1) va1 by (simp add: zrel_def ann_eq_def)
    qed
    have vty: "\<exists>w. typ_of Tz = V' w" if "(z, Tz) \<in> zvars a" "snd z \<noteq> -1" for z Tz
    proof -
      have "(z, Tz) \<in> zvars (zsubst_term ity vk ta)" using zvars_beta_norm_term[OF a(1)] that(1) by blast
      from vinst[OF this that(2)] obtain y T where y: "(y, T) \<in> zvars ta" "snd y \<noteq> -1" "(z, Tz) \<in> zvars (lv y T)"
        by blast
      from zta[OF y(1,2)] obtain x where x: "(x, T) \<in> zvars t" "snd x \<noteq> -1" "y = nren \<mu> x T" by blast
      have y0: "0 \<le> snd y" using tn[OF x(1,2)] x(3) by (simp add: nren_def)
      have T0: "T = ztyp_of (V x) \<and> typ_of T = V x" using zv x(1,2) by fast
      note l = lvs[OF y(2) y0, of T]
      show ?thesis
      proof (cases "x \<in> X")
        case True
        have "(x, T) \<in> zprf_zvars p" using tp x(1,2) by blast
        moreover have "x \<in> fst ` set (visible_vars visible)" using True by (force simp: X_def)
        ultimately have "\<mu> (fst x) = fst x" using mu by blast
        then have "y = x" using x(3) by (simp add: nren_def)
        with l T0 y(3) that(2) have "typ_of Tz = V' z" by blast
        then show ?thesis by blast
      next
        case False
        from l y(3) that(2) have "typ_of Tz = V' z \<or> typ_of Tz = typ_of (ity T)" by blast
        moreover have "typ_of (ity T) = V' x"
        proof -
          have "V' x = tsubst \<rho>v (V x)" using vh False by blast
          then show ?thesis by (simp add: ity' T0[THEN conjunct2])
        qed
        ultimately show ?thesis by metis
      qed
    qed
    have sa: "SA a"
    proof -
      have "\<exists>Ts U. has_type Wenc Ts (zdec (sepz a)) U" using as(2) a(2) by blast
      moreover have "zcan T \<and> PU (typ_of T)" if T: "T \<in> ztys a" for T
      proof -
        from T ztys_beta_norm_term[OF a(1)] have "T \<in> ztys (zsubst_term ity vk ta)" by blast
        from ztys_zsubst_term[OF this] show ?thesis
        proof (elim disjE bexE exE conjE)
          fix T0 assume "T0 \<in> ztys ta" "T = ity T0"
          then have "T0 \<in> ztys t" by (simp add: ta_def)
          with tz zt' ityPU \<open>T = ity T0\<close> show ?thesis by blast
        next
          fix xK u assume "vk xK = Some u" "T \<in> ztys u"
          then show ?thesis using lku by (cases xK) blast
        qed
      qed
      moreover have "\<forall>(x, T)\<in>zvars a. snd x \<noteq> -1 \<longrightarrow> PI (snd x) \<and> (\<exists>w. typ_of T = V' w)" using va0 vty by blast
      ultimately show ?thesis by (simp add: SA_def)
    qed
    have cvars: "(\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env" if "(z, Tz) \<in> zvars c" "snd z \<noteq> -1" for z Tz
    proof -
      have "(z, Tz) \<in> zvars (zsubst_term ity vk t)" using zvars_beta_norm_term[OF c(1)] that(1) by blast
      from vinst[OF this that(2)] obtain x T where x: "(x, T) \<in> zvars t" "snd x \<noteq> -1" "(z, Tz) \<in> zvars (lv x T)"
        by blast
      from lvs[OF x(2) tn[OF x(1,2)], of T] x(3) that(2) have "z = x \<or> z \<in> fst ` bvps env" by blast
      with tp x(1,2) show ?thesis by blast
    qed
    have lb: "\<not> loose_bvar (zdec a) k" if k: "0 \<le> k" "\<not> loose_bvar (zdec t) k" for k
    proof -
      have "\<not> loose_bvar (zdec (sepz t)) k" using k(2) by simp
      then have "\<not> loose_bvar (zdec (sepz ta)) k"
        unfolding zsta
      proof (rule contrapos_nn)
        assume "loose_bvar (psubst TVar Ren 0 (zdec (sepz t))) k"
        show "loose_bvar (zdec (sepz t)) k" by (rule loose_bvar_psubst[OF _ k(1) \<open>loose_bvar _ k\<close>]) (simp add: Ren_def)
      qed
      then have "\<not> loose_bvar (zdec (sepz (zsubst_term ity vk ta))) k"
        unfolding e2
      proof (rule contrapos_nn)
        assume "loose_bvar (psubst \<rho>v \<Theta>s 0 (zdec (sepz ta))) k"
        show "loose_bvar (zdec (sepz ta)) k" by (rule loose_bvar_psubst[OF _ k(1) \<open>loose_bvar _ k\<close>]) (simp add: \<Theta>scl)
      qed
      then have "no_loose_bound (tr (zdec (sepz (zsubst_term ity vk ta)))) (nat_of_integer k)"
        using loose_bvar_tr[OF pi2 k(1)] by simp
      from no_loose_bound_beta[OF b2(2) this] have "no_loose_bound (tr (zdec (sepz a))) (nat_of_integer k)" .
      then have "\<not> loose_bvar (zdec (sepz a)) k" using loose_bvar_tr[OF b2(1) k(1)] by simp
      then show ?thesis by simp
    qed
    show ?thesis
    proof (intro exI conjI allI impI)
      show "tm t = returnZ c" using c(1) by (simp add: tm_def)
      show "tm (zrenv (nren \<mu>) t) = returnZ a" using a(1) by (simp add: tm_def ta_def)
      show "zrel \<Theta>' (zdec c) (zdec (sepz a))" by (rule rel)
      show "beta_norm_term c = Some c" by (rule beta_norm_term_idem[OF c(1)])
      show "beta_norm_term a = Some a" by (rule beta_norm_term_idem[OF a(1)])
      show "SA a" by (rule sa)
      show "\<forall>(z, Tz)\<in>zvars c. snd z \<noteq> -1 \<longrightarrow> (\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env"
        using cvars by blast
    qed (rule lb)
  qed
  text \<open>Assembly.\<close>
  have PP: "zprf_all P (\<lambda>T. (ztyp_vis tvl \<theta> T \<and> zcan T \<and> PU (typ_of T)) \<and> True) p"
    using zprf_all_conj[OF zprf_all_conj[OF zprf_all_conj[OF pa pz] pi] zprf_all_zprf_zvars[of p]]
    by (rule zprf_all_mono) (simp_all add: P_def)
  have zvP: "T = ztyp_of (V x) \<and> typ_of T = V x \<and> zcan T \<and> PU (typ_of T) \<and> ztyp_vis tvl \<theta> T"
    if xT: "(x, T) \<in> zprf_zvars p" for x T
  proof -
    from zprf_all_zprf_zvars_ex[OF PP xT] obtain t where t: "P t" "(x, T) \<in> zvars t" by blast
    have "snd x \<noteq> -1" using pvi[OF xT] by auto
    with t show ?thesis using zvars_ztys[OF t(2)] by (auto simp: P_def zann_vis_def \<theta>_def)
  qed
  have tyQ: "zcan (ity T) \<and> PU (typ_of (ity T))" if "(ztyp_vis tvl \<theta> T \<and> zcan T \<and> PU (typ_of T)) \<and> True" for T
    using that ityPU by blast
  have annR: "\<exists>c a. tm t = returnZ c \<and> tm (zrenv (nren \<mu>) t) = returnZ a \<and> zrel \<Theta>' (zdec c) (zdec (sepz a)) \<and>
      beta_norm_term c = Some c \<and> beta_norm_term a = Some a \<and> SA a" if "P t" for t
  proof -
    from ann[OF that] obtain c a where "tm t = returnZ c" "tm (zrenv (nren \<mu>) t) = returnZ a"
      "zrel \<Theta>' (zdec c) (zdec (sepz a))" "beta_norm_term c = Some c" "beta_norm_term a = Some a" "SA a"
      by blast
    then show ?thesis by blast
  qed
  from map_zproof_ren2[of p P "\<lambda>T. (ztyp_vis tvl \<theta> T \<and> zcan T \<and> PU (typ_of T)) \<and> True" tm "nren \<mu>" "zrel \<Theta>'" SA
      "\<lambda>T. zcan T \<and> PU (typ_of T)" ity, OF pc(1,2) PP annR tyQ]
  obtain q q' where q: "map_zproof ity tm p = returnZ q" "map_zproof ity tm (zrenp (nren \<mu>) p) = returnZ q'"
    "prf_rel (zrel \<Theta>') (\<lambda>T. T) (zprf_tr q) (zprf_tr (zrenp sepn q'))" "zrf p \<longrightarrow> zrfn q \<and> zrfn q'"
    "zconst_free q'" "zno_class q'" "zprf_all SA (\<lambda>T. zcan T \<and> PU (typ_of T)) q'"
    by blast
  have rq: "zrfn q" "zrfn q'" using q(4) pc(3) by blast+
  have qv: "zprf_all (\<lambda>c. \<forall>(z, Tz)\<in>zvars c. snd z \<noteq> -1 \<longrightarrow> (\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env)
      (\<lambda>_. True) q"
  proof (rule map_zproof_all[OF q(1) pc(1,2) PP])
    fix t c assume t: "P t" "tm t = returnZ c"
    from ann[OF t(1)] obtain c' where "tm t = returnZ c'"
      "\<forall>(z, Tz)\<in>zvars c'. snd z \<noteq> -1 \<longrightarrow> (\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env" by blast
    with t(2) show "\<forall>(z, Tz)\<in>zvars c. snd z \<noteq> -1 \<longrightarrow> (\<exists>T'. (z, T') \<in> zprf_zvars p) \<or> z \<in> fst ` bvps env"
      by simp
  qed simp
  have qv': "\<forall>x\<in>prf_vars (zprf_tr q). (\<exists>T. (x, T) \<in> zprf_zvars p) \<or> x \<in> fst ` bvps env"
  proof
    fix x assume "x \<in> prf_vars (zprf_tr q)"
    then obtain T where xT: "(x, T) \<in> zprf_zvars q" by (auto simp: prf_vars_zprf_tr)
    from zprf_all_zprf_zvars_ex[OF qv xT] show "(\<exists>T. (x, T) \<in> zprf_zvars p) \<or> x \<in> fst ` bvps env"
      using zprf_zvars_snd[OF xT] by blast
  qed
  have tmeq: "(\<lambda>t. liftOZ (beta_norm_term (zsubst_term ity vk t))) = tm" by (rule ext) (simp add: tm_def)
  have p'q: "p' = q" using zp q(1) by (simp add: eq tmeq beta_norm_prooft_zrfn[OF rq(1)])
  have zn: "znorm_proof ztargs env visible (zrenp (nren \<mu>) p) = returnZ q'"
    using q(2) by (simp add: eq tmeq beta_norm_prooft_zrfn[OF rq(2)])
  have zl: "zlb n q'" if "zlb n p" for n
  proof (rule map_zproof_zlb[OF q(2)])
    show "zconst_free (zrenp (nren \<mu>) p)" using pc(1) by simp
    show "zlb n (zrenp (nren \<mu>) p)" using that by simp
    show "zprf_all (\<lambda>t. \<exists>t0. P t0 \<and> t = zrenv (nren \<mu>) t0) (\<lambda>_. True) (zrenp (nren \<mu>) p)"
      unfolding zprf_all_zrenp by (rule zprf_all_mono[OF PP]) auto
  next
    fix t t' k assume a: "\<exists>t0. P t0 \<and> t = zrenv (nren \<mu>) t0" "tm t = returnZ t'" "0 \<le> k" "\<not> loose_bvar (zdec t) k"
    then obtain t0 where t0: "P t0" "t = zrenv (nren \<mu>) t0" by blast
    from ann[OF t0(1)] obtain a where "tm (zrenv (nren \<mu>) t0) = returnZ a"
      "\<forall>k. 0 \<le> k \<longrightarrow> \<not> loose_bvar (zdec t0) k \<longrightarrow> \<not> loose_bvar (zdec a) k" by blast
    with a t0 show "\<not> loose_bvar (zdec t') k" by simp
  qed
  have th1: "\<Theta>' x = Var (sepn x (ztyp_of (V' x))) (typ_of (ztyp_of (V' x)))"
    if "0 \<le> snd x" "\<forall>T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) = fst x" for x
  proof -
    have "x \<notin> RH" using that(2) by (auto simp: RH_def)
    with that(1) show ?thesis by (simp add: \<Theta>'_def \<Psi>id)
  qed
  have th3: "has_type Wenc [] (\<Theta>' x) (V' x) \<and> (\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> PI (snd y))"
    if xT: "(x, T) \<in> zprf_zvars p" "\<mu> (fst x) \<noteq> fst x" for x T
  proof -
    have xR: "x \<in> RH" using xT by (auto simp: RH_def)
    from zvP[OF xT(1)] have T: "T = ztyp_of (V x)" "typ_of T = V x" "zcan T" by blast+
    have x0: "0 \<le> snd x" "PI (snd x)" using pvi[OF xT(1)] by blast+
    have "V' x = tsubst \<rho>v (V x)" using vh RHv[OF xR] by blast
    then have tyi: "typ_of (ity T) = V' x" using ity' T(2) by simp
    then have "ztyp_of (V' x) = ity T" using ztyp_of_typ_of_zcan zity[OF T(3)] by metis
    then have th: "\<Theta>' x = \<Theta>s (sepn (nren \<mu> x T) T)" using \<Psi>RH[OF xR] by (simp add: \<Theta>'_def T(1))
    define x' where "x' = nren \<mu> x T"
    have x'0: "0 \<le> snd x'" "snd x' \<noteq> -1" "snd x' = snd x" using x0 by (auto simp: x'_def nren_def)
    note l = lvs[OF x'0(2,1), of T]
    have "has_type Wenc [] (\<Theta>' x) (V' x)" using l tyi x'0(1) by (simp add: th x'_def[symmetric] \<Theta>s)
    moreover have "0 \<le> snd y \<and> PI (snd y)" if y: "y \<in> vars (\<Theta>' x)" for y
    proof -
      from y \<Theta>sv[OF x'0(1), of T] obtain z Tz where z: "0 \<le> snd y" "y = sepn z Tz" "(z, Tz) \<in> zvars (lv x' T)" "snd z \<noteq> -1"
        by (auto simp: th x'_def[symmetric])
      from l z(3,4) have "z = x' \<or> z \<in> fst ` bvps env" by blast
      with pie x0 x'0 have "PI (snd z)" by auto
      with z show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
  show ?thesis
  proof (intro exI conjI allI impI)
    show "znorm_proof ztargs env visible (zrenp (nren \<mu>) p) = returnZ q'" by (rule zn)
    show "prf_rel (zrel \<Theta>') (\<lambda>T. T) (zprf_tr p') (zprf_tr (zrenp sepn q'))" using q(3) by (simp add: p'q)
    show "zconst_free q'" "zno_class q'" "zrfn q'" by (fact q(5) q(6) rq(2))+
    show "zprf_all (\<lambda>t. (\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) \<and>
      (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x) \<and> (\<exists>w. typ_of T = V' w))) (\<lambda>T. zcan T \<and> PU (typ_of T)) q'"
      using q(7) by (simp add: SA_def[abs_def])
  next
    fix x assume "0 \<le> snd x" "\<forall>T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) = fst x"
    then show "\<Theta>' x = Var (sepn x (ztyp_of (V' x))) (typ_of (ztyp_of (V' x)))" by (rule th1)
  next
    fix x show "proper (\<Theta>' x)" "\<not> loose_bvar (\<Theta>' x) 0" using \<Psi>cl by (simp_all add: \<Theta>'_def)
  next
    fix x T assume "(x, T) \<in> zprf_zvars p" "\<mu> (fst x) \<noteq> fst x"
    from th3[OF this] show "has_type Wenc [] (\<Theta>' x) (V' x)" "\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> PI (snd y)" by blast+
  next
    fix n assume "zlb n p" then show "zlb n q'" by (rule zl)
  next
    show "\<forall>x\<in>prf_vars (zprf_tr p'). (\<exists>T. (x, T) \<in> zprf_zvars p) \<or> x \<in> fst ` bvps env"
      using qv' by (simp add: p'q)
  qed
qed

subsection \<open>Renaming of the new premises and composition\<close>

definition ren_cond :: "ren \<Rightarrow> integer \<Rightarrow> (name \<Rightarrow> name) \<Rightarrow> (name \<Rightarrow> name) \<Rightarrow> indexname \<Rightarrow> bool" where
  "ren_cond r m \<mu> \<mu>' x \<longleftrightarrow> (if m < snd x then ren_name (fst r) (\<mu> (fst x)) else \<mu> (fst x)) =
    \<mu>' (if m < snd x then ren_name (fst r) (fst x) else fst x)"

lemma zren_term_zrenv:
  "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> ren_cond r m \<mu> \<mu>' x \<Longrightarrow>
    zren_term r m (zrenv (nren \<mu>) t) = zrenv (nren \<mu>') (zren_term r m t)"
  by (induction r m t rule: zren_term.induct) (auto simp: nren_def ren_cond_def)

lemma map_zproof_zren_nren:
  assumes "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) p = returnZ p'" "zconst_free p"
    "\<forall>(x, T)\<in>zprf_zvars p. ren_cond r m \<mu> \<mu>' x"
  shows "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) p) = returnZ (zrenp (nren \<mu>') p')"
  using assms
proof (induction p arbitrary: p')
  case (ZAbsp a t q)
  have e: "zren_term r m (zrenv (nren \<mu>) t) = zrenv (nren \<mu>') (zren_term r m t)"
    by (rule zren_term_zrenv) (use ZAbsp.prems(3) in auto)
  from ZAbsp.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAbsp a (zren_term r m t) q'" by (auto simp: bindZ_eq_returnZ)
  have "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) q) = returnZ (zrenp (nren \<mu>') q')"
    by (rule ZAbsp.IH[OF q(1)]) (use ZAbsp.prems(2,3) in auto)
  with q e show ?case by (simp add: bindZ_eq_returnZ)
next
  case (ZAppt q t)
  have e: "zren_term r m (zrenv (nren \<mu>) t) = zrenv (nren \<mu>') (zren_term r m t)"
    by (rule zren_term_zrenv) (use ZAppt.prems(3) in auto)
  from ZAppt.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAppt q' (zren_term r m t)" by (auto simp: bindZ_eq_returnZ)
  have "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) q) = returnZ (zrenp (nren \<mu>') q')"
    by (rule ZAppt.IH[OF q(1)]) (use ZAppt.prems(2,3) in auto)
  with q e show ?case by (simp add: bindZ_eq_returnZ)
next
  case (ZAbst a T q)
  from ZAbst.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAbst a (ty T) q'" by (auto simp: bindZ_eq_returnZ)
  have "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) q) = returnZ (zrenp (nren \<mu>') q')"
    by (rule ZAbst.IH[OF q(1)]) (use ZAbst.prems(2,3) in auto)
  with q show ?case by (simp add: bindZ_eq_returnZ)
next
  case (ZAppp q1 q2)
  from ZAppp.prems(1) obtain q1' q2' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q1 = returnZ q1'"
    "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q2 = returnZ q2'" "p' = ZAppp q1' q2'"
    by (auto simp: bindZ_eq_returnZ)
  have "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) q1) = returnZ (zrenp (nren \<mu>') q1')"
    by (rule ZAppp.IH(1)[OF q(1)]) (use ZAppp.prems(2,3) in auto)
  moreover have "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) (zrenp (nren \<mu>) q2) = returnZ (zrenp (nren \<mu>') q2')"
    by (rule ZAppp.IH(2)[OF q(2)]) (use ZAppp.prems(2,3) in auto)
  ultimately show ?case using q by (simp add: bindZ_eq_returnZ)
qed auto

lemma zren_proof_nren:
  "zren_proof r m p = returnZ p' \<Longrightarrow> zconst_free p \<Longrightarrow> \<forall>(x, T)\<in>zprf_zvars p. ren_cond r m \<mu> \<mu>' x \<Longrightarrow>
    zren_proof r m (zrenp (nren \<mu>) p) = returnZ (zrenp (nren \<mu>') p')"
  unfolding zren_proof_def by (rule map_zproof_zren_nren)

lemma zbicompose_core_swap:
  assumes "zbicompose_core ta env flatten Bs As A oldAs n m visible p q = returnZ r"
  shows "\<exists>Ns asm fs. r = ZAbsps Ns (ZAppp (ZAppps q (map ZBoundp (downto (integer_of_nat (length Bs) +
      integer_of_nat (length As) - 1) (integer_of_nat (length As))))) (ZAppps p (asm @ fs))) \<and>
    (\<forall>p' q'. zbicompose_core ta env flatten Bs As A oldAs n m visible p' q' =
      returnZ (ZAbsps Ns (ZAppp (ZAppps q' (map ZBoundp (downto (integer_of_nat (length Bs) +
        integer_of_nat (length As) - 1) (integer_of_nat (length As))))) (ZAppps p' (asm @ fs)))))"
  using assms unfolding zbicompose_core_def Let_def bindZ_eq_returnZ by fastforce


subsection \<open>Variables of lifted proofs\<close>

lemma zvars_zcombound[simp]: "zvars (zcombound t n k) = zvars t"
  by (induction t n k rule: zcombound.induct) auto

lemma zvars_zlift_term:
  "(x, T) \<in> zvars (zlift_term inc Ts lev t) \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> \<forall>(y, U)\<in>zvars t. snd y \<noteq> -1 \<longrightarrow> 0 \<le> snd y \<Longrightarrow>
    \<exists>y U. (y, U) \<in> zvars t \<and> snd y \<noteq> -1 \<and> fst x = fst y \<and> snd x = snd y + inc"
proof (induction inc Ts lev t rule: zlift_term.induct)
  case (1 inc Ts lev x0 i T0)
  show ?case
  proof (cases "0 \<le> i")
    case True
    with "1.prems" show ?thesis by (intro exI[of _ "(x0, i)"] exI[of _ T0]) auto
  next
    case False
    with "1.prems" show ?thesis by auto
  qed
qed auto

lemma zvars_zlift_term':
  assumes "(x, T) \<in> zvars (zlift_term' inc Ts lev t)" "snd x \<noteq> -1" "\<forall>(y, U)\<in>zvars t. snd y \<noteq> -1 \<longrightarrow> 0 \<le> snd y"
  shows "\<exists>y U. (y, U) \<in> zvars t \<and> snd y \<noteq> -1 \<and> fst x = fst y \<and> snd x = snd y + inc"
proof (cases "Ts = [] \<and> inc = 0")
  case True
  with assms show ?thesis by (intro exI[of _ x] exI[of _ T]) (simp add: zlift_term'_def)
next
  case False
  with assms zvars_zlift_term[of x T inc Ts lev t] show ?thesis by (simp add: zlift_term'_def)
qed

lemma zprf_zvars_zlift_prf:
  assumes "zlift_prf inc Ts lev p = returnZ q" "zconst_free p"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) p" "(x, T) \<in> zprf_zvars q"
  shows "\<exists>y U. (y, U) \<in> zprf_zvars p \<and> fst x = fst y \<and> snd x = snd y + inc"
  using assms
proof (induction p arbitrary: q lev)
  case (ZAbst a T0 p)
  from ZAbst.prems(1) obtain p' where p': "zlift_prf inc Ts (lev + 1) p = returnZ p'" "q = ZAbst a (zincr_tvar inc T0) p'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbst.prems(4) p'(2) have "(x, T) \<in> zprf_zvars p'" by simp
  from ZAbst.IH[OF p'(1) _ _ this] ZAbst.prems(2,3) show ?case by simp
next
  case (ZAbsp a t p)
  from ZAbsp.prems(1) obtain p' where p': "zlift_prf inc Ts lev p = returnZ p'" "q = ZAbsp a (zlift_term' inc Ts lev t) p'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAbsp.prems(4) p'(2) consider "(x, T) \<in> zvars (zlift_term' inc Ts lev t)" "snd x \<noteq> -1" | "(x, T) \<in> zprf_zvars p'"
    by auto
  then show ?case
  proof cases
    case 1
    from zvars_zlift_term'[OF 1] ZAbsp.prems(3) obtain y U where "(y, U) \<in> zvars t" "snd y \<noteq> -1" "fst x = fst y"
      "snd x = snd y + inc" by auto
    then show ?thesis by (intro exI[of _ y] exI[of _ U]) simp
  next
    case 2
    from ZAbsp.IH[OF p'(1) _ _ 2] ZAbsp.prems(2,3) show ?thesis by auto
  qed
next
  case (ZAppt p t)
  from ZAppt.prems(1) obtain p' where p': "zlift_prf inc Ts lev p = returnZ p'" "q = ZAppt p' (zlift_term' inc Ts lev t)"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppt.prems(4) p'(2) consider "(x, T) \<in> zvars (zlift_term' inc Ts lev t)" "snd x \<noteq> -1" | "(x, T) \<in> zprf_zvars p'"
    by auto
  then show ?case
  proof cases
    case 1
    from zvars_zlift_term'[OF 1] ZAppt.prems(3) obtain y U where "(y, U) \<in> zvars t" "snd y \<noteq> -1" "fst x = fst y"
      "snd x = snd y + inc" by auto
    then show ?thesis by (intro exI[of _ y] exI[of _ U]) simp
  next
    case 2
    from ZAppt.IH[OF p'(1) _ _ 2] ZAppt.prems(2,3) show ?thesis by auto
  qed
next
  case (ZAppp p1 p2)
  from ZAppp.prems(1) obtain q1 q2 where q: "zlift_prf inc Ts lev p1 = returnZ q1" "zlift_prf inc Ts lev p2 = returnZ q2"
    "q = ZAppp q1 q2" by (auto simp: bindZ_eq_returnZ)
  from ZAppp.prems(4) q(3) consider "(x, T) \<in> zprf_zvars q1" | "(x, T) \<in> zprf_zvars q2" by auto
  then show ?case
  proof cases
    case 1
    from ZAppp.IH(1)[OF q(1) _ _ 1] ZAppp.prems(2,3) show ?thesis by auto
  next
    case 2
    from ZAppp.IH(2)[OF q(2) _ _ 2] ZAppp.prems(2,3) show ?thesis by auto
  qed
qed (auto simp: bindZ_eq_returnZ)

lemma zprf_zvars_foldr_zmk_app:
  "zprf_zvars (snd (snd x)) = {} \<Longrightarrow> zprf_zvars (snd (snd (foldr zmk_app bs x))) = {}"
proof (induction bs arbitrary: x)
  case (Cons b bs)
  obtain i' j' r where r: "foldr zmk_app bs x = (i', j', r)" by (cases "foldr zmk_app bs x")
  with Cons have rr: "zprf_zvars r = {}" by (metis snd_conv)
  have e: "foldr zmk_app (b # bs) x = zmk_app b (i', j', r)" using r by simp
  show ?case unfolding e using rr by (simp add: zmk_app_def)
qed simp

lemma zprf_zvars_foldr_zmk_app_ZBoundp[simp]:
  "zprf_zvars (snd (snd (foldr zmk_app bs (i, j, ZBoundp k)))) = {}"
  by (rule zprf_zvars_foldr_zmk_app) simp

lemma zprf_zvars_ZAppps: "zprf_zvars (ZAppps p qs) = zprf_zvars p \<union> (\<Union>q\<in>set qs. zprf_zvars q)"
  by (induction qs arbitrary: p) (auto simp: ZAppps_def)

lemma zprf_zvars_ZAbsps:
  "zprf_zvars (ZAbsps ts p) = (\<Union>t\<in>set ts. {(x, T). (x, T) \<in> zvars t \<and> snd x \<noteq> -1}) \<union> zprf_zvars p"
  by (induction ts) (auto simp: ZAbsps_def)

lemma zlift_leaf_vars:
  assumes "zlift_prf inc Ts lev pf = returnZ p" "zconst_free pf"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) pf"
    "(x, T) \<in> zprf_zvars (ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i, j, ZBoundp k)))) ks))"
  shows "\<exists>b. (\<exists>U. ((fst x, b), U) \<in> zprf_zvars pf) \<and> snd x = b + inc"
proof -
  from assms(4) have "(x, T) \<in> zprf_zvars p" by (auto simp: zprf_zvars_ZAppps)
  from zprf_zvars_zlift_prf[OF assms(1-3) this] obtain y U where "(y, U) \<in> zprf_zvars pf" "fst x = fst y"
    "snd x = snd y + inc" by blast
  then show ?thesis by (intro exI[of _ "snd y"]) (cases y, auto)
qed

lemma zprf_zvars_zlift_prems:
  assumes "zlift_prems ta inc k pf Ts bs i j G = returnZ q" "zconst_free pf"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) pf" "(x, T) \<in> zprf_zvars q"
  shows "(\<exists>y U. (y, U) \<in> zprf_zvars pf \<and> fst x = fst y \<and> snd x = snd y + inc) \<or> x \<in> vars G"
  using assms
proof (induction ta inc k pf Ts bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 ta inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with "1.prems"(1) obtain A' p where A': "zterm_of ta A = returnZ A'"
      and p: "zlift_prems ta inc k pf Ts (True # bs) (i + 1) j B = returnZ p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    from "1.prems"(4) q consider "(x, T) \<in> zvars A'" "snd x \<noteq> -1" | "(x, T) \<in> zprf_zvars p" by auto
    then show ?thesis
    proof cases
      case 1
      from zvars_zterm_of[OF A' 1] show ?thesis by simp
    next
      case 2
      from "1.IH"(1)[OF True A'[unfolded returnZ_def] p "1.prems"(2,3) 2] show ?thesis by auto
    qed
  next
    case False
    with "1.prems"(1) obtain p where p: "zlift_prf inc (rev Ts) 0 pf = returnZ p"
      and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
      by (auto simp: bindZ_eq_returnZ)
    from "1.prems"(4) q have "(x, T) \<in> zprf_zvars p" by (auto simp: zprf_zvars_ZAppps)
    from zprf_zvars_zlift_prf[OF p "1.prems"(2,3) this] show ?thesis by blast
  qed
next
  case (2 ta inc k pf Ts bs i j c U a T0 t)
  show ?case
  proof (cases "c = STR ''Pure.all''")
    case True
    with "2.prems"(1) obtain p where p: "zlift_prems ta inc k pf (ztyp_of T0 # Ts) (False # bs) i (j + 1) t = returnZ p"
      and q: "q = ZAbst a (ztyp_of T0) p"
      by (auto simp: bindZ_eq_returnZ)
    from "2.prems"(4) q have "(x, T) \<in> zprf_zvars p" by simp
    from "2.IH"(1)[OF True p "2.prems"(2,3) this] show ?thesis by auto
  next
    case False
    with "2.prems"(1) obtain p where p: "zlift_prf inc (rev Ts) 0 pf = returnZ p"
      and q: "q = ZAppps p (map (\<lambda>k. snd (snd (foldr zmk_app bs (i - 1, j - 1, ZBoundp k)))) (downto (i + k - 1) i))"
      by (auto simp: bindZ_eq_returnZ)
    from "2.prems"(4) q have "(x, T) \<in> zprf_zvars p" by (auto simp: zprf_zvars_ZAppps)
    from zprf_zvars_zlift_prf[OF p "2.prems"(2,3) this] show ?thesis by blast
  qed
qed (simp_all add: bindZ_eq_returnZ, ((elim exE conjE)?, (hypsubst)?, (rule disjI1)?, rule zlift_leaf_vars, assumption+)+)

lemma zprf_zvars_zlift_proof:
  assumes "zlift_proof ta G inc prems pf = returnZ q" "zconst_free pf"
    "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) pf" "(x, T) \<in> zprf_zvars q"
  shows "(\<exists>y U. (y, U) \<in> zprf_zvars pf \<and> fst x = fst y \<and> snd x = snd y + inc) \<or>
    x \<in> vars G \<union> (\<Union>A\<in>set prems. vars A)"
proof -
  from assms(1) obtain As p where As: "mapZ (zterm_of ta) prems = returnZ As"
    and p: "zlift_prems ta inc (integer_of_nat (length prems)) pf [] [] 0 0 G = returnZ p" and q: "q = ZAbsps As p"
    by (auto simp: zlift_proof_def bindZ_eq_returnZ)
  from assms(4) q consider a where "a \<in> set As" "(x, T) \<in> zvars a" "snd x \<noteq> -1" | "(x, T) \<in> zprf_zvars p"
    by (auto simp: zprf_zvars_ZAbsps)
  then show ?thesis
  proof cases
    case 1
    from 1(1) obtain k where k: "k < length As" "a = As ! k" by (auto simp: in_set_conv_nth)
    have kl: "k < length prems" using k(1) length_mapZ[OF As] by simp
    have "zterm_of ta (prems ! k) = returnZ a" using mapZ_nth[OF As kl] k(2) by simp
    from zvars_zterm_of[OF this 1(2,3)] nth_mem[OF kl] show ?thesis by blast
  next
    case 2
    from zprf_zvars_zlift_prems[OF p assms(2,3) 2] show ?thesis by blast
  qed
qed

subsection \<open>The relation of annotations under renamings\<close>

lemma prf_rel_zrel_cong:
  "prf_rel (zrel \<Theta>1) f p q \<Longrightarrow> (\<And>x. x \<in> prf_vars p \<Longrightarrow> \<Theta>1 x = \<Theta>2 x) \<Longrightarrow> prf_rel (zrel \<Theta>2) f p q"
proof (induction rule: prf_rel.induct)
  case (AbsP t t' p p' a)
  have "rel_option (zrel \<Theta>2) t t'"
    using AbsP.hyps(1) AbsP.prems psubst_cong[of _ \<Theta>1 \<Theta>2 TVar 0]
    by (cases t; cases t') (auto simp: zrel_def)
  with AbsP show ?case by (auto intro: prf_rel.AbsP)
next
  case (PAppt p p' t t')
  have "rel_option (zrel \<Theta>2) t t'"
    using PAppt.hyps(2) PAppt.prems psubst_cong[of _ \<Theta>1 \<Theta>2 TVar 0]
    by (cases t; cases t') (auto simp: zrel_def)
  with PAppt show ?case by (auto intro: prf_rel.PAppt)
qed (auto intro: prf_rel.intros)

text \<open>An annotation and its renaming, with variables separated.\<close>

definition renv :: "(name \<Rightarrow> name) \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> indexname \<Rightarrow> pterm" where
  "renv \<mu> W x = Var (sepn (nren \<mu> x (ztyp_of (W x))) (ztyp_of (W x))) (W x)"

lemma renv_id: "\<mu> (fst x) = fst x \<Longrightarrow> renv \<mu> W x = sepv x (W x)"
  by (simp add: renv_def sepv_def nren_def)

lemma zann_zrel_ren:
  assumes "zann A W m t" "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
    and \<Theta>: "\<And>x. x \<in> vars (zdec t) \<Longrightarrow> \<Theta> x = renv \<mu> W x"
  shows "zrel \<Theta> (zdec t) (zdec (sepz (zrenv (nren \<mu>) t)))"
proof -
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA assms(2,3) by blast
  from assms(1) have v: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> T = ztyp_of (W x)"
    and h: "\<exists>Ts U. has_type W Ts (zdec t) U" by (auto simp: zann_def)
  have st: "sepz (zrenv (nren \<mu>) t) = zrenv (\<lambda>x T. sepn (nren \<mu> x T) T) t" by (simp add: zrenv_comp)
  have ip: "idx_pres (\<lambda>x T. sepn (nren \<mu> x T) T)" by (simp add: idx_pres_def nren_def)
  have e: "zdec (sepz (zrenv (nren \<mu>) t)) = psubst TVar (renv \<mu> W) 0 (zdec t)"
    unfolding st by (rule zdec_zrenv[OF _ ip]) (use v tw in \<open>auto simp: renv_def\<close>)
  have e2: "psubst TVar (renv \<mu> W) 0 (zdec t) = psubst TVar \<Theta> 0 (zdec t)"
    by (rule psubst_cong) (simp add: \<Theta>)
  from h obtain Ts U where "has_type W Ts (zdec t) U" by blast
  then have "has_type Wenc Ts (zdec (sepz (zrenv (nren \<mu>) t))) U"
    unfolding st by (rule has_type_zrenv[OF _ ip]) (use v tw in auto)
  then have "proper (zdec (sepz (zrenv (nren \<mu>) t)))" by (rule has_type_proper)
  moreover have "\<forall>x\<in>vars (zdec (sepz (zrenv (nren \<mu>) t))). 0 \<le> snd x"
    using v by (auto simp: st vars_zdec zvars_zrenv sepn_def nren_def split: if_splits)
  ultimately show ?thesis by (simp add: zrel_def e[symmetric] e2[symmetric] ann_eq_refl_proper)
qed

lemma zprf_all_zrel_ren:
  assumes "zprf_all (zann A W m) (zty A m) p" "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
    and \<Theta>: "\<And>x. x \<in> prf_vars (zprf_tr p) \<Longrightarrow> \<Theta> x = renv \<mu> W x"
  shows "prf_rel (zrel \<Theta>) id (zprf_tr p) (zprf_tr (zrenp sepn (zrenp (nren \<mu>) p)))"
  using assms(1) \<Theta>
proof (induction p)
  case (ZAbsp a t p)
  have "zrel \<Theta> (zdec t) (zdec (sepz (zrenv (nren \<mu>) t)))"
    by (rule zann_zrel_ren[OF _ assms(2,3)]) (use ZAbsp.prems in auto)
  with ZAbsp show ?case by (auto intro!: prf_rel.AbsP)
next
  case (ZAppt p t)
  have "zrel \<Theta> (zdec t) (zdec (sepz (zrenv (nren \<mu>) t)))"
    by (rule zann_zrel_ren[OF _ assms(2,3)]) (use ZAppt.prems in auto)
  with ZAppt show ?case by (auto intro!: prf_rel.PAppt)
qed (auto intro!: prf_rel.intros prf_rel_Abst_id prf_rel_PClass_id)

lemma zann_s_ren:
  assumes "zann A W m t" "\<forall>x. tyA ar A (W x)" "\<forall>q\<in>A. 0 \<le> snd (fst q)"
  shows "zann_s A m (zrenv (nren \<mu>) t)"
proof -
  have tw: "typ_of (ztyp_of (W x)) = W x" for x using typ_of_ztyp_of_tyA assms(2,3) by blast
  from assms(1) have v: "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> T = ztyp_of (W x)"
    and ty: "\<forall>T\<in>ztys t. zty A m T" and h: "\<exists>Ts U. has_type W Ts (zdec t) U"
    by (auto simp: zann_def)
  have st: "sepz (zrenv (nren \<mu>) t) = zrenv (\<lambda>x T. sepn (nren \<mu> x T) T) t" by (simp add: zrenv_comp)
  have ip: "idx_pres (\<lambda>x T. sepn (nren \<mu> x T) T)" by (simp add: idx_pres_def nren_def)
  from h obtain Ts U where "has_type W Ts (zdec t) U" by blast
  then have "has_type Wenc Ts (zdec (sepz (zrenv (nren \<mu>) t))) U"
    unfolding st by (rule has_type_zrenv[OF _ ip]) (use v tw in auto)
  moreover have "\<forall>(x, T)\<in>zvars (zrenv (nren \<mu>) t). snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> tyA ar A (typ_of T)"
    using v tw assms(2) by (fastforce simp: zvars_zrenv nren_def split: if_splits)
  ultimately show ?thesis using ty by (auto simp: zann_s_def)
qed

lemma znorm_proof_ren':
  assumes h: "znorm_hyps env visible V V' PU PI" and ne: "\<not> env_is_empty env"
    and pk: "znorm_pok env visible V PU PI p"
    and mu: "\<forall>x T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow>
      x \<notin> fst ` set (visible_vars visible) \<and> x \<notin> fst ` bvps env"
    and zp: "znorm_proof ztargs env visible p = returnZ p'"
  shows "\<exists>p'' \<Theta>'. znorm_proof ztargs env visible (zrenp (nren \<mu>) p) = returnZ p'' \<and>
    prf_rel (zrel \<Theta>') (\<lambda>T. T) (zprf_tr p') (zprf_tr (zrenp sepn p'')) \<and>
    (\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow>
      \<Theta>' x = Var (sepn x (ztyp_of (V' x))) (typ_of (ztyp_of (V' x)))) \<and>
    (\<forall>x. proper (\<Theta>' x) \<and> \<not> loose_bvar (\<Theta>' x) 0) \<and>
    (\<forall>x T. (x, T) \<in> zprf_zvars p \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> has_type Wenc [] (\<Theta>' x) (V' x) \<and>
      (\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> PI (snd y))) \<and>
    zconst_free p'' \<and> zno_class p'' \<and> zrfn p'' \<and>
    zprf_all (\<lambda>t. (\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) \<and>
      (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> PI (snd x) \<and> (\<exists>w. typ_of T = V' w))) (\<lambda>T. zcan T \<and> PU (typ_of T)) p'' \<and>
    (\<forall>n. zlb n p \<longrightarrow> zlb n p'') \<and>
    (\<forall>x\<in>prf_vars (zprf_tr p'). (\<exists>T. (x, T) \<in> zprf_zvars p) \<or> x \<in> fst ` bvps env)"
  apply (rule znorm_proof_ren[where V = V and V' = V' and PU = PU and PI = PI])
  using h ne pk mu zp by (simp_all add: znorm_hyps_def znorm_pok_def Let_def)

lemma zrenv_nren_ident[simp]: "zrenv (nren (\<lambda>a. a)) t = t"
  by (rule zrenv_id) (simp add: nren_def)

lemma zrenp_nren_ident[simp]: "zrenp (nren (\<lambda>a. a)) p = p"
  by (induction p) simp_all

lemma prf_rel_ZAppps:
  assumes "prf_rel R f (zprf_tr p) (zprf_tr p')" "list_all2 (\<lambda>q q'. prf_rel R f (zprf_tr q) (zprf_tr q')) qs qs'"
  shows "prf_rel R f (zprf_tr (ZAppps p qs)) (zprf_tr (ZAppps p' qs'))"
  using assms(2,1)
proof (induction qs qs' arbitrary: p p' rule: list_all2_induct)
  case (Cons q qs q' qs')
  have "prf_rel R f (zprf_tr (ZAppp p q)) (zprf_tr (ZAppp p' q'))" using Cons by (auto intro: prf_rel.PAppp)
  with Cons.IH show ?case by (simp add: ZAppps_def)
qed (simp add: ZAppps_def)

lemma prf_rel_ZAbsps:
  "list_all2 (\<lambda>N N'. R (zdec N) (zdec N')) Ns Ns' \<Longrightarrow> prf_rel R f (zprf_tr p) (zprf_tr p') \<Longrightarrow>
    prf_rel R f (zprf_tr (ZAbsps Ns p)) (zprf_tr (ZAbsps Ns' p'))"
  by (induction Ns Ns' rule: list_all2_induct) (auto simp: ZAbsps_def intro: prf_rel.AbsP)

definition zcore_vars :: "ztypargs \<Rightarrow> env \<Rightarrow> bool \<Rightarrow> pterm list \<Rightarrow> pterm list \<Rightarrow> pterm option \<Rightarrow>
    pterm list \<Rightarrow> integer \<Rightarrow> integer \<Rightarrow> pterm list \<Rightarrow> indexname set" where
  "zcore_vars ta env flatten Bs As A oldAs n m visible =
    (case zbicompose_core ta env flatten Bs As A oldAs n m visible ZNop ZNop of
      Some (ZOk r) \<Rightarrow> prf_vars (zprf_tr r) | _ \<Rightarrow> {})"

lemma zcore_vars_returnZ: "zbicompose_core ta env flatten Bs As A oldAs n m visible ZNop ZNop = returnZ r \<Longrightarrow>
    zcore_vars ta env flatten Bs As A oldAs n m visible = prf_vars (zprf_tr r)"
  by (simp add: zcore_vars_def returnZ_def)

lemma zside_hidden:
  assumes q2: "(if nrm then znorm_proof ztargs env vis q else returnZ q) = returnZ q''"
    and za: "zprf_all (zann Ar Wf m0) (zty Ar m0) q''" and zc: "zconst_free q''" "zno_class q''"
    and tyw: "\<forall>x. tyA ar Ar (Wf x)" and A0: "\<forall>a\<in>Ar. 0 \<le> snd (fst a)"
    and pk: "nrm \<Longrightarrow> \<not> env_is_empty env \<and> (\<exists>V PU. znorm_hyps env vis V Wf PU (\<lambda>k. 0 \<le> k \<and> k \<le> m0) \<and>
      (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> m0)) \<and>
      znorm_pok env vis V PU (\<lambda>k. 0 \<le> k \<and> k \<le> m0) q)"
    and mu: "\<forall>x T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow>
      x \<notin> fst ` set (visible_vars vis) \<and> x \<notin> fst ` bvps env"
  shows "\<exists>qa \<Theta>q. (if nrm then znorm_proof ztargs env vis (zrenp (nren \<mu>) q) else returnZ (zrenp (nren \<mu>) q)) =
      returnZ qa \<and>
    prf_rel (zrel \<Theta>q) id (zprf_tr q'') (zprf_tr (zrenp sepn qa)) \<and>
    (\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow> \<Theta>q x = sepv x (Wf x)) \<and>
    (\<forall>x. proper (\<Theta>q x) \<and> \<not> loose_bvar (\<Theta>q x) 0) \<and>
    (\<forall>x T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> wty Wenc [] (\<Theta>q x) (Wf x)) \<and>
    (\<forall>x\<in>prf_vars (zprf_tr q''). (\<exists>T. (x, T) \<in> zprf_zvars q) \<or> x \<in> fst ` bvps env) \<and>
    zconst_free qa \<and> zno_class qa \<and> zprf_all (zann_s Ar m0) (zty Ar m0) qa \<and> (zlb 0 q \<longrightarrow> zlb 0 qa)"
proof -
  have tw: "typ_of (ztyp_of (Wf x)) = Wf x" for x using typ_of_ztyp_of_tyA tyw A0 by blast
  show ?thesis
  proof (cases nrm)
    case False
    then have e: "q'' = q" using q2 by simp
    define \<Theta>q where "\<Theta>q x = (if \<exists>T. (x, T) \<in> zprf_zvars q then renv \<mu> Wf x else sepv x (Wf x))" for x
    have za': "zprf_all (zann Ar Wf m0) (zty Ar m0) q" using za e by simp
    have x0: "0 \<le> snd x" if "(x, T) \<in> zprf_zvars q" for x T
    proof -
      from zprf_all_zprf_zvars_ex[OF za' that] obtain t where "zann Ar Wf m0 t" "(x, T) \<in> zvars t" by blast
      with zprf_zvars_snd[OF that] show ?thesis by (auto simp: zann_def)
    qed
    show ?thesis
    proof (intro exI[of _ "zrenp (nren \<mu>) q"] exI[of _ \<Theta>q] conjI allI impI)
      show "(if nrm then znorm_proof ztargs env vis (zrenp (nren \<mu>) q) else returnZ (zrenp (nren \<mu>) q)) =
          returnZ (zrenp (nren \<mu>) q)" using False by simp
      show "prf_rel (zrel \<Theta>q) id (zprf_tr q'') (zprf_tr (zrenp sepn (zrenp (nren \<mu>) q)))"
        unfolding e by (rule zprf_all_zrel_ren[OF za' tyw A0]) (auto simp: \<Theta>q_def prf_vars_zprf_tr)
    next
      fix x assume "0 \<le> snd x" "\<forall>T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) = fst x"
      then show "\<Theta>q x = sepv x (Wf x)" by (auto simp: \<Theta>q_def renv_id)
    next
      fix x show "proper (\<Theta>q x)" "\<not> loose_bvar (\<Theta>q x) 0" by (simp_all add: \<Theta>q_def renv_def sepv_def)
    next
      fix x T assume xT: "(x, T) \<in> zprf_zvars q" "\<mu> (fst x) \<noteq> fst x"
      have "has_type Wenc [] (renv \<mu> Wf x) (Wf x)" by (simp add: renv_def tw has_type.Var)
      moreover have "\<forall>v\<in>vars (renv \<mu> Wf x). 0 \<le> snd v" using x0[OF xT(1)] by (simp add: renv_def nren_def)
      ultimately show "wty Wenc [] (\<Theta>q x) (Wf x)" using xT(1) by (auto simp: \<Theta>q_def wty_def)
    next
      show "\<forall>x\<in>prf_vars (zprf_tr q''). (\<exists>T. (x, T) \<in> zprf_zvars q) \<or> x \<in> fst ` bvps env"
        by (auto simp: e prf_vars_zprf_tr)
      show "zconst_free (zrenp (nren \<mu>) q)" "zno_class (zrenp (nren \<mu>) q)" using zc e by simp_all
      show "zprf_all (zann_s Ar m0) (zty Ar m0) (zrenp (nren \<mu>) q)"
        unfolding zprf_all_zrenp by (rule zprf_all_mono[OF za']) (use zann_s_ren tyw A0 in auto)
    next
      assume "zlb 0 q" then show "zlb 0 (zrenp (nren \<mu>) q)" by simp
    qed
  next
    case True
    from pk[OF True] obtain V PU where ne: "\<not> env_is_empty env"
      and h: "znorm_hyps env vis V Wf PU (\<lambda>k. 0 \<le> k \<and> k \<le> m0)"
      and pu: "\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> m0)"
      and pok: "znorm_pok env vis V PU (\<lambda>k. 0 \<le> k \<and> k \<le> m0) q" by blast
    from q2 True have n: "znorm_proof ztargs env vis q = returnZ q''" by simp
    from znorm_proof_ren'[OF h ne pok mu n] obtain qa \<Theta>' where
      qa: "znorm_proof ztargs env vis (zrenp (nren \<mu>) q) = returnZ qa"
      and rel: "prf_rel (zrel \<Theta>') (\<lambda>T. T) (zprf_tr q'') (zprf_tr (zrenp sepn qa))"
      and sv: "\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow>
        \<Theta>' x = Var (sepn x (ztyp_of (Wf x))) (typ_of (ztyp_of (Wf x)))"
      and cl: "\<forall>x. proper (\<Theta>' x) \<and> \<not> loose_bvar (\<Theta>' x) 0"
      and ty: "\<forall>x T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> has_type Wenc [] (\<Theta>' x) (Wf x) \<and>
        (\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> 0 \<le> snd y \<and> snd y \<le> m0)"
      and c: "zconst_free qa" "zno_class qa"
      and sa: "zprf_all (\<lambda>t. (\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) \<and>
        (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (0 \<le> snd x \<and> snd x \<le> m0) \<and> (\<exists>w. typ_of T = Wf w)))
        (\<lambda>T. zcan T \<and> PU (typ_of T)) qa"
      and lb: "\<forall>n. zlb n q \<longrightarrow> zlb n qa"
      and pvq: "\<forall>x\<in>prf_vars (zprf_tr q''). (\<exists>T. (x, T) \<in> zprf_zvars q) \<or> x \<in> fst ` bvps env"
      by blast
    have zt: "zty Ar m0 T" if "zcan T \<and> PU (typ_of T)" for T using that pu by (auto simp: zty_def)
    show ?thesis
    proof (intro exI[of _ qa] exI[of _ \<Theta>'] conjI allI impI)
      show "(if nrm then znorm_proof ztargs env vis (zrenp (nren \<mu>) q) else returnZ (zrenp (nren \<mu>) q)) = returnZ qa"
        using True qa by simp
      show "prf_rel (zrel \<Theta>') id (zprf_tr q'') (zprf_tr (zrenp sepn qa))" unfolding id_def by (rule rel)
    next
      fix x assume a: "0 \<le> snd x" "\<forall>T. (x, T) \<in> zprf_zvars q \<longrightarrow> \<mu> (fst x) = fst x"
      from sv a have "\<Theta>' x = Var (sepn x (ztyp_of (Wf x))) (typ_of (ztyp_of (Wf x)))" by blast
      then show "\<Theta>' x = sepv x (Wf x)" by (simp add: sepv_def tw)
    next
      fix x show "proper (\<Theta>' x)" "\<not> loose_bvar (\<Theta>' x) 0" using cl by blast+
    next
      fix x T assume a: "(x, T) \<in> zprf_zvars q" "\<mu> (fst x) \<noteq> fst x"
      from ty a have "has_type Wenc [] (\<Theta>' x) (Wf x)" "\<forall>y\<in>vars (\<Theta>' x). 0 \<le> snd y \<and> 0 \<le> snd y \<and> snd y \<le> m0"
        by blast+
      then show "wty Wenc [] (\<Theta>' x) (Wf x)" by (simp add: wty_def)
    next
      show "\<forall>x\<in>prf_vars (zprf_tr q''). (\<exists>T. (x, T) \<in> zprf_zvars q) \<or> x \<in> fst ` bvps env" by (rule pvq)
      show "zconst_free qa" "zno_class qa" by (fact c)+
      show "zprf_all (zann_s Ar m0) (zty Ar m0) qa"
      proof (rule zprf_all_mono[OF sa])
        fix t assume t: "(\<exists>Ts U. has_type Wenc Ts (zdec (sepz t)) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) \<and>
          (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> (0 \<le> snd x \<and> snd x \<le> m0) \<and> (\<exists>w. typ_of T = Wf w))"
        have "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m0 \<and> tyA ar Ar (typ_of T)"
          using t tyw by fastforce
        with t zt show "zann_s Ar m0 t" by (auto simp: zann_s_def)
      qed (rule zt)
    next
      assume "zlb 0 q" with lb show "zlb 0 qa" by blast
    qed
  qed
qed

text \<open>
  The composition of renamings of the tight proofs of the lifted rule and the proof state: the
  result is the corresponding renaming and instantiation of the composition of the proofs.
\<close>

lemma zbicompose_hidden:
  assumes bp: "zbicompose_proof ztargs env smax flatten Bs As A oldAs n m vis rp sp = returnZ p"
    and fA: "finite Ar" "scons Ar" "tcert alg Ar" and A1: "\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx env"
    and tyw: "\<forall>x. tyA ar Ar (Wf x)" and wt: "wt_thm ar Ar Wf (maxidx env) tps P"
    and pv: "prf_valid alg ar Wf H tps (zprf_tr p) P" and zp: "zinv Ar Wf (maxidx env) p"
    and zn: "\<not> env_is_empty env \<longrightarrow> (\<exists>V PU. znorm_hyps env vis V Wf PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx env) \<and>
      (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx env)) \<and>
      znorm_pok env vis V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx env) rp \<and>
      (\<not> above env smax \<longrightarrow> znorm_pok env vis V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx env) sp))"
    and zl: "zlb 0 rp" "zlb 0 sp" "zlb 0 p"
    and c1r: "\<forall>x T. (x, T) \<in> zprf_zvars rp \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow>
      x \<notin> fst ` set (visible_vars vis) \<and> x \<notin> fst ` bvps env"
    and c1s: "\<forall>x T. (x, T) \<in> zprf_zvars sp \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow>
      x \<notin> fst ` set (visible_vars vis) \<and> x \<notin> fst ` bvps env"
    and c2: "\<forall>x\<in>zcore_vars ztargs env flatten Bs As A oldAs n m vis. \<mu> (fst x) = fst x"
    and c3: "\<forall>x\<in>vars_thm tps P. \<mu> (fst x) = fst x"
    and c4: "\<forall>(x, T)\<in>zprf_zvars rp. \<forall>(y, U)\<in>zprf_zvars sp. fst x = fst y \<longrightarrow> \<mu> (fst x) = fst x"
  shows "\<exists>pa. zbicompose_proof ztargs env smax flatten Bs As A oldAs n m vis (zrenp (nren \<mu>) rp) (zrenp (nren \<mu>) sp) =
    returnZ pa \<and> zthm_hinv (maxidx env) tps P H pa \<and> zlb 0 pa"
proof -
  define m0 where "m0 = maxidx env"
  have A0: "\<forall>a\<in>Ar. 0 \<le> snd (fst a)" using A1 by blast
  have tw: "typ_of (ztyp_of (Wf x)) = Wf x" for x using typ_of_ztyp_of_tyA tyw A0 by blast
  define nr where "nr \<longleftrightarrow> \<not> env_is_empty env"
  define ns where "ns \<longleftrightarrow> \<not> env_is_empty env \<and> \<not> above env smax"
  define BS where "BS = map ZBoundp (downto (integer_of_nat (length Bs) + integer_of_nat (length As) - 1)
    (integer_of_nat (length As)))"
  obtain rp'' sp'' where r2: "(if nr then znorm_proof ztargs env vis rp else returnZ rp) = returnZ rp''"
    and s2: "(if ns then znorm_proof ztargs env vis sp else returnZ sp) = returnZ sp''"
    and core: "zbicompose_core ztargs env flatten Bs As A oldAs n m vis rp'' sp'' = returnZ p"
  proof (cases "env_is_empty env")
    case True
    then show ?thesis using bp by (intro that[of rp sp]) (simp_all add: zbicompose_proof_def nr_def ns_def)
  next
    case False
    with bp obtain r' s' where "znorm_proof ztargs env vis rp = returnZ r'"
      "(if above env smax then returnZ sp else znorm_proof ztargs env vis sp) = returnZ s'"
      "zbicompose_core ztargs env flatten Bs As A oldAs n m vis r' s' = returnZ p"
      by (auto simp: zbicompose_proof_def bindZ_eq_returnZ)
    then show ?thesis using False by (intro that[of r' s']) (simp_all add: nr_def ns_def split: if_splits)
  qed
  from zbicompose_core_swap[OF core, folded BS_def] obtain Ns asm fs where
    pe: "p = ZAbsps Ns (ZAppp (ZAppps sp'' BS) (ZAppps rp'' (asm @ fs)))"
    and sw: "\<And>p' q'. zbicompose_core ztargs env flatten Bs As A oldAs n m vis p' q' =
      returnZ (ZAbsps Ns (ZAppp (ZAppps q' BS) (ZAppps p' (asm @ fs))))" by blast
  text \<open>The parts of the composition.\<close>
  from zp have za: "zprf_all (zann Ar Wf m0) (zty Ar m0) p" and zcp: "zconst_free p" "zno_class p"
    by (simp_all add: zinv_def m0_def)
  from za pe have zaN: "\<forall>N\<in>set Ns. zann Ar Wf m0 N" and zas: "zprf_all (zann Ar Wf m0) (zty Ar m0) sp''"
    and zar: "zprf_all (zann Ar Wf m0) (zty Ar m0) rp''"
    and zaq: "\<forall>q\<in>set (asm @ fs). zprf_all (zann Ar Wf m0) (zty Ar m0) q"
    by (simp_all add: zprf_all_ZAbsps zprf_all_ZAppps)
  from zcp pe have zcs: "zconst_free sp''" "zno_class sp''" and zcr: "zconst_free rp''" "zno_class rp''"
    and zcq: "\<forall>q\<in>set (asm @ fs). zconst_free q \<and> zno_class q"
    by (simp_all add: zconst_free_ZAbsps zno_class_ZAbsps zconst_free_ZAppps zno_class_ZAppps)
  from zl(3) pe have zlN: "\<forall>N\<in>set Ns. \<not> loose_bvar (zdec N) (integer_of_nat 0)"
    and zlq: "\<forall>q\<in>set (asm @ fs). zlb 0 q"
    by (simp_all add: zlb_ZAbsps zlb_ZAppps)
  text \<open>The renamed normalisations of the two proofs.\<close>
  from zside_hidden[OF r2 zar zcr tyw A0, of \<mu>] zn c1r
  obtain rpa \<Theta>r where ra: "(if nr then znorm_proof ztargs env vis (zrenp (nren \<mu>) rp) else returnZ (zrenp (nren \<mu>) rp)) =
      returnZ rpa"
    and rrel: "prf_rel (zrel \<Theta>r) id (zprf_tr rp'') (zprf_tr (zrenp sepn rpa))"
    and rsv: "\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars rp \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow> \<Theta>r x = sepv x (Wf x)"
    and rcl: "\<forall>x. proper (\<Theta>r x) \<and> \<not> loose_bvar (\<Theta>r x) 0"
    and rty: "\<forall>x T. (x, T) \<in> zprf_zvars rp \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> wty Wenc [] (\<Theta>r x) (Wf x)"
    and rpv: "\<forall>x\<in>prf_vars (zprf_tr rp''). (\<exists>T. (x, T) \<in> zprf_zvars rp) \<or> x \<in> fst ` bvps env"
    and rsyn: "zconst_free rpa" "zno_class rpa" "zprf_all (zann_s Ar m0) (zty Ar m0) rpa"
    and rlb: "zlb 0 rp \<longrightarrow> zlb 0 rpa"
    unfolding m0_def nr_def by blast
  from zside_hidden[OF s2 zas zcs tyw A0, of \<mu>] zn c1s
  obtain spa \<Theta>s where sa: "(if ns then znorm_proof ztargs env vis (zrenp (nren \<mu>) sp) else returnZ (zrenp (nren \<mu>) sp)) =
      returnZ spa"
    and srel: "prf_rel (zrel \<Theta>s) id (zprf_tr sp'') (zprf_tr (zrenp sepn spa))"
    and ssv: "\<forall>x. 0 \<le> snd x \<longrightarrow> (\<forall>T. (x, T) \<in> zprf_zvars sp \<longrightarrow> \<mu> (fst x) = fst x) \<longrightarrow> \<Theta>s x = sepv x (Wf x)"
    and scl: "\<forall>x. proper (\<Theta>s x) \<and> \<not> loose_bvar (\<Theta>s x) 0"
    and sty: "\<forall>x T. (x, T) \<in> zprf_zvars sp \<longrightarrow> \<mu> (fst x) \<noteq> fst x \<longrightarrow> wty Wenc [] (\<Theta>s x) (Wf x)"
    and spv: "\<forall>x\<in>prf_vars (zprf_tr sp''). (\<exists>T. (x, T) \<in> zprf_zvars sp) \<or> x \<in> fst ` bvps env"
    and ssyn: "zconst_free spa" "zno_class spa" "zprf_all (zann_s Ar m0) (zty Ar m0) spa"
    and slb: "zlb 0 sp \<longrightarrow> zlb 0 spa"
    unfolding m0_def ns_def by blast
  define pa where "pa = ZAbsps Ns (ZAppp (ZAppps spa BS) (ZAppps rpa (asm @ fs)))"
  have bpa: "zbicompose_proof ztargs env smax flatten Bs As A oldAs n m vis (zrenp (nren \<mu>) rp) (zrenp (nren \<mu>) sp) =
      returnZ pa"
    using ra sa by (cases "env_is_empty env"; cases "above env smax")
      (simp_all add: zbicompose_proof_def nr_def ns_def sw pa_def)
  text \<open>The instantiation of the separated variables.\<close>
  define RHr where "RHr = {x. (\<exists>T. (x, T) \<in> zprf_zvars rp) \<and> \<mu> (fst x) \<noteq> fst x}"
  define RHs where "RHs = {x. (\<exists>T. (x, T) \<in> zprf_zvars sp) \<and> \<mu> (fst x) \<noteq> fst x}"
  define \<Theta> where "\<Theta> x = (if x \<in> RHr then \<Theta>r x else if x \<in> RHs then \<Theta>s x else sepv x (Wf x))" for x
  have pvn: "0 \<le> snd x" if "x \<in> prf_vars (zprf_tr q)" "zprf_all (zann Ar Wf m0) (zty Ar m0) q" for x q
  proof -
    from that(1) obtain T where xT: "(x, T) \<in> zprf_zvars q" by (auto simp: prf_vars_zprf_tr)
    from zprf_all_zprf_zvars_ex[OF that(2) xT] obtain t where "zann Ar Wf m0 t" "(x, T) \<in> zvars t" by blast
    with zprf_zvars_snd[OF xT] show ?thesis by (auto simp: zann_def)
  qed
  have \<Theta>sep: "\<Theta> x = sepv x (Wf x)" if "\<mu> (fst x) = fst x" for x
    using that by (simp add: \<Theta>_def RHr_def RHs_def)
  text \<open>The variables of the parts that do not depend on the proofs keep their names.\<close>
  have cv: "zcore_vars ztargs env flatten Bs As A oldAs n m vis =
      prf_vars (zprf_tr (ZAbsps Ns (ZAppp (ZAppps ZNop BS) (ZAppps ZNop (asm @ fs)))))"
    by (rule zcore_vars_returnZ[OF sw])
  have BSv: "\<forall>q\<in>set BS. zprf_zvars q = {} \<and> zrenp sepn q = q \<and> prf_rel (zrel \<Theta>) id (zprf_tr q) (zprf_tr q) \<and>
      zconst_free q \<and> zno_class q \<and> zprf_all (zann_s Ar m0) (zty Ar m0) q \<and> zlb 0 q"
    by (auto simp: BS_def intro: prf_rel.PBound)
  have fixN: "\<mu> (fst x) = fst x" if "x \<in> vars (zdec N)" "N \<in> set Ns" for x N
  proof -
    from that(1) obtain T where "(x, T) \<in> zvars N" "snd x \<noteq> -1" by (auto simp: vars_zdec)
    with that(2) have "x \<in> zcore_vars ztargs env flatten Bs As A oldAs n m vis"
      by (force simp: cv prf_vars_zprf_tr zprf_zvars_ZAbsps zprf_zvars_ZAppps)
    with c2 show ?thesis by blast
  qed
  have fixq: "\<mu> (fst x) = fst x" if "x \<in> prf_vars (zprf_tr q)" "q \<in> set (asm @ fs)" for x q
  proof -
    from that(1) obtain T where "(x, T) \<in> zprf_zvars q" by (auto simp: prf_vars_zprf_tr)
    with that(2) have "x \<in> zcore_vars ztargs env flatten Bs As A oldAs n m vis"
      by (force simp: cv prf_vars_zprf_tr zprf_zvars_ZAbsps zprf_zvars_ZAppps)
    with c2 show ?thesis by blast
  qed
  have relN: "zrel \<Theta> (zdec N) (zdec (sepz N))" if "N \<in> set Ns" for N
  proof -
    have "zrel \<Theta> (zdec N) (zdec (sepz (zrenv (nren (\<lambda>a. a)) N)))"
      by (rule zann_zrel_ren[OF _ tyw A0]) (use zaN that fixN \<Theta>sep in \<open>auto simp: renv_id\<close>)
    then show ?thesis by simp
  qed
  have relq: "prf_rel (zrel \<Theta>) id (zprf_tr q) (zprf_tr (zrenp sepn q))" if "q \<in> set (asm @ fs)" for q
  proof -
    have "prf_rel (zrel \<Theta>) id (zprf_tr q) (zprf_tr (zrenp sepn (zrenp (nren (\<lambda>a. a)) q)))"
      by (rule zprf_all_zrel_ren[OF _ tyw A0]) (use zaq that fixq \<Theta>sep in \<open>auto simp: renv_id\<close>)
    then show ?thesis by simp
  qed
  have relr: "prf_rel (zrel \<Theta>) id (zprf_tr rp'') (zprf_tr (zrenp sepn rpa))"
  proof (rule prf_rel_zrel_cong[OF rrel])
    fix x assume x: "x \<in> prf_vars (zprf_tr rp'')"
    show "\<Theta>r x = \<Theta> x"
    proof (cases "x \<in> RHr")
      case True
      then show ?thesis by (simp add: \<Theta>_def)
    next
      case False
      have x0: "0 \<le> snd x" by (rule pvn[OF x zar])
      have nRs: "x \<notin> RHs"
      proof
        assume "x \<in> RHs"
        then obtain U where U: "(x, U) \<in> zprf_zvars sp" "\<mu> (fst x) \<noteq> fst x" by (auto simp: RHs_def)
        from rpv x have "(\<exists>T. (x, T) \<in> zprf_zvars rp) \<or> x \<in> fst ` bvps env" by blast
        then show False
        proof (elim disjE exE)
          fix T assume "(x, T) \<in> zprf_zvars rp"
          with c4 U show False by blast
        next
          assume "x \<in> fst ` bvps env"
          with c1s U show False by blast
        qed
      qed
      have "\<Theta>r x = sepv x (Wf x)" by (rule rsv[rule_format, OF x0]) (use False in \<open>auto simp: RHr_def\<close>)
      with False nRs show ?thesis by (simp add: \<Theta>_def)
    qed
  qed
  have rels: "prf_rel (zrel \<Theta>) id (zprf_tr sp'') (zprf_tr (zrenp sepn spa))"
  proof (rule prf_rel_zrel_cong[OF srel])
    fix x assume x: "x \<in> prf_vars (zprf_tr sp'')"
    have x0: "0 \<le> snd x" by (rule pvn[OF x zas])
    have nRr: "x \<notin> RHr"
    proof
      assume "x \<in> RHr"
      then obtain T where T: "(x, T) \<in> zprf_zvars rp" "\<mu> (fst x) \<noteq> fst x" by (auto simp: RHr_def)
      from spv x have "(\<exists>U. (x, U) \<in> zprf_zvars sp) \<or> x \<in> fst ` bvps env" by blast
      then show False
      proof (elim disjE exE)
        fix U assume "(x, U) \<in> zprf_zvars sp"
        with c4 T show False by blast
      next
        assume "x \<in> fst ` bvps env"
        with c1r T show False by blast
      qed
    qed
    show "\<Theta>s x = \<Theta> x"
    proof (cases "x \<in> RHs")
      case True
      with nRr show ?thesis by (simp add: \<Theta>_def)
    next
      case False
      have "\<Theta>s x = sepv x (Wf x)" by (rule ssv[rule_format, OF x0]) (use False in \<open>auto simp: RHs_def\<close>)
      with False nRr show ?thesis by (simp add: \<Theta>_def)
    qed
  qed
  have rel: "prf_rel (zrel \<Theta>) id (zprf_tr p) (zprf_tr (zrenp sepn pa))"
  proof -
    have "zrenp sepn pa = ZAbsps (map sepz Ns) (ZAppp (ZAppps (zrenp sepn spa) BS)
        (ZAppps (zrenp sepn rpa) (map (zrenp sepn) (asm @ fs))))"
      using BSv by (simp add: pa_def zrenp_ZAbsps zrenp_ZAppps map_idI)
    moreover have "prf_rel (zrel \<Theta>) id (zprf_tr (ZAbsps Ns (ZAppp (ZAppps sp'' BS) (ZAppps rp'' (asm @ fs)))))
        (zprf_tr (ZAbsps (map sepz Ns) (ZAppp (ZAppps (zrenp sepn spa) BS)
          (ZAppps (zrenp sepn rpa) (map (zrenp sepn) (asm @ fs))))))"
    proof (rule prf_rel_ZAbsps)
      show "list_all2 (\<lambda>N N'. zrel \<Theta> (zdec N) (zdec N')) Ns (map sepz Ns)"
        using relN by (auto simp: list_all2_map2 intro: list.rel_refl_strong)
      have "prf_rel (zrel \<Theta>) id (zprf_tr (ZAppps sp'' BS)) (zprf_tr (ZAppps (zrenp sepn spa) BS))"
        by (rule prf_rel_ZAppps[OF rels]) (use BSv in \<open>auto intro: list.rel_refl_strong\<close>)
      moreover have "prf_rel (zrel \<Theta>) id (zprf_tr (ZAppps rp'' (asm @ fs)))
          (zprf_tr (ZAppps (zrenp sepn rpa) (map (zrenp sepn) (asm @ fs))))"
      proof (rule prf_rel_ZAppps[OF relr])
        show "list_all2 (\<lambda>q q'. prf_rel (zrel \<Theta>) id (zprf_tr q) (zprf_tr q')) (asm @ fs) (map (zrenp sepn) (asm @ fs))"
          unfolding list_all2_map2 by (rule list.rel_refl_strong) (rule relq)
      qed
      ultimately show "prf_rel (zrel \<Theta>) id (zprf_tr (ZAppp (ZAppps sp'' BS) (ZAppps rp'' (asm @ fs))))
          (zprf_tr (ZAppp (ZAppps (zrenp sepn spa) BS) (ZAppps (zrenp sepn rpa) (map (zrenp sepn) (asm @ fs)))))"
        by (auto intro: prf_rel.PAppp)
    qed
    ultimately show ?thesis by (simp add: pe)
  qed
  have ho: "hid_ok Wf (vars_thm tps P) \<Theta>"
    unfolding hid_ok_def
  proof (intro conjI allI impI ballI)
    fix x
    from rcl scl have a: "proper (\<Theta>r x) \<and> \<not> loose_bvar (\<Theta>r x) 0" "proper (\<Theta>s x) \<and> \<not> loose_bvar (\<Theta>s x) 0"
      by blast+
    show "proper (\<Theta> x)" "\<not> loose_bvar (\<Theta> x) 0" using a by (simp_all add: \<Theta>_def sepv_def)
  next
    fix x :: indexname assume x0: "0 \<le> snd x"
    show "wty Wenc [] (\<Theta> x) (Wf x)"
    proof (cases "x \<in> RHr")
      case True
      then obtain T where "(x, T) \<in> zprf_zvars rp" "\<mu> (fst x) \<noteq> fst x" by (auto simp: RHr_def)
      with rty have "wty Wenc [] (\<Theta>r x) (Wf x)" by blast
      with True show ?thesis by (simp add: \<Theta>_def)
    next
      case nr: False
      show ?thesis
      proof (cases "x \<in> RHs")
        case True
        then obtain T where "(x, T) \<in> zprf_zvars sp" "\<mu> (fst x) \<noteq> fst x" by (auto simp: RHs_def)
        with sty have "wty Wenc [] (\<Theta>s x) (Wf x)" by blast
        with True nr show ?thesis by (simp add: \<Theta>_def)
      next
        case False
        with nr x0 show ?thesis by (simp add: \<Theta>_def sepv_def wty_def tw has_type.Var)
      qed
    qed
  next
    fix x assume "x \<in> vars_thm tps P"
    with c3 show "\<Theta> x = sepv x (Wf x)" by (simp add: \<Theta>sep)
  qed
  have zs: "zsyn Ar m0 pa"
  proof -
    have "zprf_all (zann_s Ar m0) (zty Ar m0) q" if "q \<in> set (asm @ fs)" for q
      by (rule zprf_all_mono[OF bspec[OF zaq that]]) (use zann_zann_s tyw A0 in auto)
    then show ?thesis
      using rsyn ssyn zaN zcq BSv zann_zann_s[OF _ tyw A0]
      by (auto simp: zsyn_def pa_def zconst_free_ZAbsps zno_class_ZAbsps zconst_free_ZAppps zno_class_ZAppps
          zprf_all_ZAbsps zprf_all_ZAppps zrf_ZAbsps_ZAppp)
  qed
  have zla: "zlb 0 pa"
    using zlN zlq BSv rlb slb zl(1,2) by (auto simp: pa_def zlb_ZAbsps zlb_ZAppps)
  show ?thesis
  proof (intro exI[of _ pa] conjI bpa zla)
    show "zthm_hinv (maxidx env) tps P H pa"
      unfolding zthm_hinv_def using fA A1 tyw wt pv zp rel ho zs unfolding m0_def by blast
  qed
qed

subsection \<open>Separating the hidden variables of a proof\<close>

text \<open>Names not in a finite set of names, for the hidden variables of the proof state and the rule.\<close>

definition fresh_name :: "nat \<Rightarrow> bool \<Rightarrow> name \<Rightarrow> ztyp \<Rightarrow> name" where
  "fresh_name k b a T = String.implode (replicate (k + 2 * to_nat (a, T) + (if b then 1 else 0)) CHR ''b'')"

lemma length_fresh_name:
  "length (String.explode (fresh_name k b a T)) = k + 2 * to_nat (a, T) + (if b then 1 else 0)"
  by (simp add: fresh_name_def)

lemma fresh_name_inj: "fresh_name k b a T = fresh_name k b' a' T' \<longleftrightarrow> b = b' \<and> a = a' \<and> T = T'"
proof
  assume "fresh_name k b a T = fresh_name k b' a' T'"
  then have "length (String.explode (fresh_name k b a T)) = length (String.explode (fresh_name k b' a' T'))" by simp
  then have e: "2 * to_nat (a, T) + (if b then 1 else 0) = 2 * to_nat (a', T') + (if b' then (1::nat) else 0)"
    by (simp add: length_fresh_name)
  then have b: "b = b'" by (cases b; cases b') presburger+
  with e have "to_nat (a, T) = to_nat (a', T')" by simp
  then have "(a, T) = (a', T')" by (rule injD[OF inj_to_nat])
  with b show "b = b' \<and> a = a' \<and> T = T'" by simp
qed simp

definition name_bound :: "name set \<Rightarrow> nat" where
  "name_bound N = Suc (Max (insert 0 ((\<lambda>n. length (String.explode n)) ` N)))"

lemma fresh_name_notin: "finite N \<Longrightarrow> fresh_name (name_bound N) b a T \<notin> N"
proof
  assume f: "finite N" and n: "fresh_name (name_bound N) b a T \<in> N"
  then have "length (String.explode (fresh_name (name_bound N) b a T)) \<le>
      Max (insert 0 ((\<lambda>n. length (String.explode n)) ` N))"
    by (intro Max_ge) auto
  then show False by (simp add: length_fresh_name name_bound_def)
qed

definition hsep :: "nat \<Rightarrow> bool \<Rightarrow> (indexname \<times> ptyp) set \<Rightarrow> indexname \<Rightarrow> ztyp \<Rightarrow> indexname" where
  "hsep k b V x T = (if (x, typ_of T) \<in> V then x else (fresh_name k b (fst x) T, snd x))"

definition hunsep :: "nat \<Rightarrow> name \<Rightarrow> name" where
  "hunsep k n = (if \<exists>b a T. n = fresh_name k b a T
    then fst (snd (SOME bat. n = fresh_name k (fst bat) (fst (snd bat)) (snd (snd bat)))) else n)"

lemma hunsep_fresh[simp]: "hunsep k (fresh_name k b a T) = a"
proof -
  have "\<exists>bat. fresh_name k b a T = fresh_name k (fst bat) (fst (snd bat)) (snd (snd bat))"
    by (intro exI[of _ "(b, a, T)"]) simp
  then have "fst (snd (SOME bat. fresh_name k b a T = fresh_name k (fst bat) (fst (snd bat)) (snd (snd bat)))) = a"
    by (rule someI2_ex) (simp add: fresh_name_inj)
  then show ?thesis by (auto simp: hunsep_def)
qed

lemma hunsep_other: "(\<And>b a T. n \<noteq> fresh_name k b a T) \<Longrightarrow> hunsep k n = n"
  by (auto simp: hunsep_def)

lemma idx_pres_hsep[simp]: "idx_pres (hsep k b V)"
  by (simp add: idx_pres_def hsep_def)

lemma zvars_zrenvD:
  "idx_pres f \<Longrightarrow> (y, U) \<in> zvars (zrenv f t) \<Longrightarrow> snd y \<noteq> -1 \<Longrightarrow> \<exists>x. (x, U) \<in> zvars t \<and> snd x \<noteq> -1 \<and> y = f x U"
proof (induction t)
  case (ZVar x0 T0)
  then show ?case by (cases "snd x0 = -1") (auto simp: idx_pres_def)
next
  case (ZApp t u)
  from ZApp.prems(2) have "(y, U) \<in> zvars (zrenv f t) \<or> (y, U) \<in> zvars (zrenv f u)" by simp
  then show ?case
  proof
    assume "(y, U) \<in> zvars (zrenv f t)"
    from ZApp.IH(1)[OF ZApp.prems(1) this ZApp.prems(3)] obtain x where "(x, U) \<in> zvars t" "snd x \<noteq> -1" "y = f x U"
      by blast
    then show ?thesis by (intro exI[of _ x]) simp
  next
    assume "(y, U) \<in> zvars (zrenv f u)"
    from ZApp.IH(2)[OF ZApp.prems(1) this ZApp.prems(3)] obtain x where "(x, U) \<in> zvars u" "snd x \<noteq> -1" "y = f x U"
      by blast
    then show ?thesis by (intro exI[of _ x]) simp
  qed
qed auto

lemma zprf_zvars_zrenpD:
  assumes "idx_pres f" "(y, U) \<in> zprf_zvars (zrenp f p)"
  shows "\<exists>x. (x, U) \<in> zprf_zvars p \<and> y = f x U"
  using assms(2)
proof (induction p)
  case (ZAbst a T0 q)
  then show ?case by simp
next
  case (ZAbsp a t q)
  from ZAbsp.prems consider "(y, U) \<in> zvars (zrenv f t)" "snd y \<noteq> -1" | "(y, U) \<in> zprf_zvars (zrenp f q)" by auto
  then show ?case
  proof cases
    case 1
    from zvars_zrenvD[OF assms(1) 1] obtain x where "(x, U) \<in> zvars t" "snd x \<noteq> -1" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  next
    case 2
    from ZAbsp.IH[OF 2] obtain x where "(x, U) \<in> zprf_zvars q" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  qed
next
  case (ZAppt q t)
  from ZAppt.prems consider "(y, U) \<in> zvars (zrenv f t)" "snd y \<noteq> -1" | "(y, U) \<in> zprf_zvars (zrenp f q)" by auto
  then show ?case
  proof cases
    case 1
    from zvars_zrenvD[OF assms(1) 1] obtain x where "(x, U) \<in> zvars t" "snd x \<noteq> -1" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  next
    case 2
    from ZAppt.IH[OF 2] obtain x where "(x, U) \<in> zprf_zvars q" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  qed
next
  case (ZAppp q1 q2)
  from ZAppp.prems have "(y, U) \<in> zprf_zvars (zrenp f q1) \<or> (y, U) \<in> zprf_zvars (zrenp f q2)" by simp
  then show ?case
  proof
    assume "(y, U) \<in> zprf_zvars (zrenp f q1)"
    from ZAppp.IH(1)[OF this] obtain x where "(x, U) \<in> zprf_zvars q1" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  next
    assume "(y, U) \<in> zprf_zvars (zrenp f q2)"
    from ZAppp.IH(2)[OF this] obtain x where "(x, U) \<in> zprf_zvars q2" "y = f x U" by blast
    then show ?thesis by (intro exI[of _ x]) simp
  qed
qed simp_all

lemma zrenp_ident: "(\<And>x T. (x, T) \<in> zprf_zvars p \<Longrightarrow> f x T = x) \<Longrightarrow> zrenp f p = p"
proof (induction p)
  case (ZAbsp a t q)
  then show ?case by (auto intro!: zrenv_id)
next
  case (ZAppt q t)
  then show ?case by (auto intro!: zrenv_id)
qed simp_all

lemma finite_zvars: "finite (zvars t)"
  by (induction t) auto

lemma finite_zprf_zvars: "finite (zprf_zvars p)"
  by (induction p) (auto intro: finite_subset[OF _ finite_zvars])

lemma vps_thm_vars: "(x, T) \<in> vps_thm tps P \<Longrightarrow> x \<in> vars_thm tps P"
  by (force simp: vps_thm_def vars_thm_def vars_vps)

lemma finite_vars_thm: "finite (vars_thm tps P)"
  by (auto simp: vars_thm_def finite_vars)

lemma wt_thm_vps: "wt_thm ar A W m tps P \<Longrightarrow> (x, T) \<in> vps_thm tps P \<Longrightarrow> T = W x"
proof -
  assume wt: "wt_thm ar A W m tps P" and xT: "(x, T) \<in> vps_thm tps P"
  from xT obtain t where t: "t \<in> insert P (\<Union>(t, u)\<in>set tps. {t, u})" "(x, T) \<in> vps t"
    by (auto simp: vps_thm_def)
  from wt t(1) obtain U where "has_type W [] t U" by (fastforce simp: wt_thm_def wt_term_def)
  from vps_has_type_typ[OF this t(2)] show ?thesis by simp
qed

lemma sep_clean:
  assumes inv: "zthm_hinv m tps P H p" and nn: "\<forall>x\<in>vars_thm tps P. 0 \<le> snd x"
    and fN: "finite N" and vN: "fst ` vars_thm tps P \<subseteq> N" and pN: "\<forall>(x, T)\<in>zprf_zvars p. fst x \<in> N"
  defines "k \<equiv> name_bound N"
  shows "zthm_prf_inv m tps P H (zrenp (hsep k b (vps_thm tps P)) p)"
    and "zrenp (nren (hunsep k)) (zrenp (hsep k b (vps_thm tps P)) p) = p"
    and "\<forall>(y, U)\<in>zprf_zvars (zrenp (hsep k b (vps_thm tps P)) p).
      (y \<in> vars_thm tps P \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k b a T)"
proof -
  let ?V = "vps_thm tps P" and ?\<nu> = "hsep k b (vps_thm tps P)"
  from inv obtain A W where wt: "wt_thm ar A W m tps P" and zs: "zsyn A m p"
    by (auto simp: zthm_hinv_def)
  have fr: "fresh_name k b' a T \<notin> N" for b' a T by (simp add: k_def fresh_name_notin fN)
  have can: "zcan T" if "(x, T) \<in> zprf_zvars p" for x T
  proof -
    from zs have "zprf_all (zann_s A m) (zty A m) p" by (simp add: zsyn_def)
    from zprf_all_zprf_zvars_ex[OF this that] obtain t where "zann_s A m t" "(x, T) \<in> zvars t" by blast
    then show ?thesis using zvars_ztys by (fastforce simp: zann_s_def zty_def)
  qed
  have vty: "typ_of T = typ_of U" if "(x, typ_of T) \<in> ?V" "(x, typ_of U) \<in> ?V" for x T U
    using wt_thm_vps[OF wt that(1)] wt_thm_vps[OF wt that(2)] by simp
  show "zthm_prf_inv m tps P H (zrenp ?\<nu> p)"
  proof (rule zthm_hinv_sep[OF inv idx_pres_hsep _ _ _ nn])
    fix x T assume "(x, typ_of T) \<in> ?V"
    then show "?\<nu> x T = x" by (simp add: hsep_def)
  next
    fix x T y U assume xT: "(x, T) \<in> zprf_zvars p" and yU: "(y, U) \<in> zprf_zvars p" and e: "?\<nu> x T = ?\<nu> y U"
    have xN: "fst x \<in> N" and yN: "fst y \<in> N" using pN xT yU by blast+
    show "x = y \<and> T = U"
    proof (cases "(x, typ_of T) \<in> ?V"; cases "(y, typ_of U) \<in> ?V")
      assume a: "(x, typ_of T) \<in> ?V" "(y, typ_of U) \<in> ?V"
      with e have xy: "x = y" by (simp add: hsep_def)
      with a vty have "typ_of T = typ_of U" by blast
      with can[OF xT] can[OF yU] have "T = U" by (metis ztyp_of_typ_of_zcan)
      with xy show ?thesis by simp
    next
      assume a: "(x, typ_of T) \<in> ?V" "(y, typ_of U) \<notin> ?V"
      with e have "x = (fresh_name k b (fst y) U, snd y)" by (simp add: hsep_def)
      with xN fr show ?thesis by simp
    next
      assume a: "(x, typ_of T) \<notin> ?V" "(y, typ_of U) \<in> ?V"
      with e have "y = (fresh_name k b (fst x) T, snd x)" by (simp add: hsep_def)
      with yN fr show ?thesis by simp
    next
      assume a: "(x, typ_of T) \<notin> ?V" "(y, typ_of U) \<notin> ?V"
      with e have "fresh_name k b (fst x) T = fresh_name k b (fst y) U" "snd x = snd y" by (simp_all add: hsep_def)
      then show ?thesis by (simp add: fresh_name_inj prod_eq_iff)
    qed
  next
    fix x T assume "(x, T) \<in> zprf_zvars p" "(x, typ_of T) \<notin> ?V"
    then have e: "?\<nu> x T = (fresh_name k b (fst x) T, snd x)" by (simp add: hsep_def)
    show "?\<nu> x T \<notin> vars_thm tps P"
    proof
      assume m: "?\<nu> x T \<in> vars_thm tps P"
      from m vN have "fst (?\<nu> x T) \<in> N" by blast
      with e fr show False by simp
    qed
  qed
  show "zrenp (nren (hunsep k)) (zrenp ?\<nu> p) = p"
  proof -
    have "zrenp (\<lambda>x T. nren (hunsep k) (?\<nu> x T) T) p = p"
    proof (rule zrenp_ident)
      fix x T assume xT: "(x, T) \<in> zprf_zvars p"
      have xN: "fst x \<in> N" using pN xT by auto
      have "hunsep k (fst x) = fst x" by (rule hunsep_other) (use xN fr in force)
      then show "nren (hunsep k) (?\<nu> x T) T = x" by (simp add: hsep_def nren_def)
    qed
    then show ?thesis by (simp add: zrenp_comp)
  qed
  show "\<forall>(y, U)\<in>zprf_zvars (zrenp ?\<nu> p). (y \<in> vars_thm tps P \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k b a T)"
  proof
    fix yU assume yU: "yU \<in> zprf_zvars (zrenp ?\<nu> p)"
    obtain y U where e: "yU = (y, U)" by (cases yU)
    from zprf_zvars_zrenpD[OF idx_pres_hsep yU[unfolded e]] obtain x where x: "(x, U) \<in> zprf_zvars p" "y = ?\<nu> x U"
      by blast
    have "(y \<in> vars_thm tps P \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k b a T)"
    proof (cases "(x, typ_of U) \<in> ?V")
      case True
      then have "x \<in> vars_thm tps P" by (rule vps_thm_vars)
      with True x pN show ?thesis by (auto simp: hsep_def)
    next
      case False
      with x show ?thesis by (auto simp: hsep_def)
    qed
    then show "case yU of (y, U) \<Rightarrow> (y \<in> vars_thm tps P \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k b a T)"
      by (simp add: e)
  qed
qed

lemma zvars_zren_term:
  "(y, U) \<in> zvars (zren_term r m t) \<Longrightarrow>
    \<exists>y0. (y0, U) \<in> zvars t \<and> snd y = snd y0 \<and> fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)"
proof (induction r m t rule: zren_term.induct)
  case (1 r m x i T)
  then show ?case by (intro exI[of _ "(x, i)"]) auto
next
  case (3 r m t u)
  from "3.prems" have "(y, U) \<in> zvars (zren_term r m t) \<or> (y, U) \<in> zvars (zren_term r m u)" by simp
  then show ?case
  proof
    assume "(y, U) \<in> zvars (zren_term r m t)"
    from "3.IH"(1)[OF this] obtain y0 where "(y0, U) \<in> zvars t" "snd y = snd y0"
      "fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)" by blast
    then show ?thesis by (intro exI[of _ y0]) simp
  next
    assume "(y, U) \<in> zvars (zren_term r m u)"
    from "3.IH"(2)[OF this] obtain y0 where "(y0, U) \<in> zvars u" "snd y = snd y0"
      "fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)" by blast
    then show ?thesis by (intro exI[of _ y0]) simp
  qed
qed auto

lemma zprf_zvars_map_zren:
  "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) p = returnZ p' \<Longrightarrow> (y, U) \<in> zprf_zvars p' \<Longrightarrow>
    \<exists>y0. (y0, U) \<in> zprf_zvars p \<and> snd y = snd y0 \<and> fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)"
proof (induction p arbitrary: p')
  case (ZAbst a T0 q)
  from ZAbst.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAbst a (ty T0) q'" by (auto simp: bindZ_eq_returnZ)
  from ZAbst.IH[OF q(1)] ZAbst.prems(2) q(2) show ?case by simp
next
  case (ZAbsp a t q)
  from ZAbsp.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAbsp a (zren_term r m t) q'" by (auto simp: bindZ_eq_returnZ)
  from ZAbsp.prems(2) q(2) consider "(y, U) \<in> zvars (zren_term r m t)" "snd y \<noteq> -1" | "(y, U) \<in> zprf_zvars q'" by auto
  then show ?case
  proof cases
    case 1
    from zvars_zren_term[OF 1(1)] obtain y0 where "(y0, U) \<in> zvars t" "snd y = snd y0"
      "fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)" by blast
    with 1(2) show ?thesis by (intro exI[of _ y0]) auto
  next
    case 2
    from ZAbsp.IH[OF q(1) 2] show ?thesis by auto
  qed
next
  case (ZAppt q t)
  from ZAppt.prems(1) obtain q' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q = returnZ q'"
    "p' = ZAppt q' (zren_term r m t)" by (auto simp: bindZ_eq_returnZ)
  from ZAppt.prems(2) q(2) consider "(y, U) \<in> zvars (zren_term r m t)" "snd y \<noteq> -1" | "(y, U) \<in> zprf_zvars q'" by auto
  then show ?case
  proof cases
    case 1
    from zvars_zren_term[OF 1(1)] obtain y0 where "(y0, U) \<in> zvars t" "snd y = snd y0"
      "fst y = (if m < snd y0 then ren_name (fst r) (fst y0) else fst y0)" by blast
    with 1(2) show ?thesis by (intro exI[of _ y0]) auto
  next
    case 2
    from ZAppt.IH[OF q(1) 2] show ?thesis by auto
  qed
next
  case (ZAppp q1 q2)
  from ZAppp.prems(1) obtain q1' q2' where q: "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q1 = returnZ q1'"
    "map_zproof ty (\<lambda>t. returnZ (zren_term r m t)) q2 = returnZ q2'" "p' = ZAppp q1' q2'"
    by (auto simp: bindZ_eq_returnZ)
  from ZAppp.prems(2) q(3) consider "(y, U) \<in> zprf_zvars q1'" | "(y, U) \<in> zprf_zvars q2'" by auto
  then show ?case
  proof cases
    case 1
    from ZAppp.IH(1)[OF q(1) 1] show ?thesis by auto
  next
    case 2
    from ZAppp.IH(2)[OF q(2) 2] show ?thesis by auto
  qed
qed (auto simp: bindZ_eq_returnZ)

lemma zrenp_cong: "(\<And>x T. (x, T) \<in> zprf_zvars p \<Longrightarrow> f x T = g x T) \<Longrightarrow> zrenp f p = zrenp g p"
proof (induction p)
  case (ZAbsp a t q)
  then show ?case by (auto intro!: zrenv_cong)
next
  case (ZAppt q t)
  then show ?case by (auto intro!: zrenv_cong)
qed simp_all

lemma ren_name_cases: "ren_name tab a = a \<or> ren_name tab a \<in> snd ` set tab"
  by (auto simp: ren_name_def split: option.splits dest: map_of_SomeD intro: rev_image_eqI)

lemma ren_name_notin: "a \<notin> fst ` set tab \<Longrightarrow> ren_name tab a = a"
  by (simp add: ren_name_def map_of_eq_None_iff[THEN iffD2])

lemma zconst_free_zlift_prf: "zlift_prf inc Ts lev p = returnZ q \<Longrightarrow> zconst_free p \<Longrightarrow> zconst_free q"
  by (induction p arbitrary: q lev) (auto simp: bindZ_eq_returnZ)

lemma zconst_free_foldr_zmk_app:
  "zconst_free (snd (snd x)) \<Longrightarrow> zconst_free (snd (snd (foldr zmk_app bs x)))"
proof (induction bs arbitrary: x)
  case (Cons b bs)
  obtain i' j' r where r: "foldr zmk_app bs x = (i', j', r)" by (cases "foldr zmk_app bs x")
  with Cons have rr: "zconst_free r" by (metis snd_conv)
  have e: "foldr zmk_app (b # bs) x = zmk_app b (i', j', r)" using r by simp
  show ?case unfolding e using rr by (simp add: zmk_app_def)
qed simp

lemma zconst_free_zlift_prems:
  "zlift_prems ta inc k pf Ts bs i j G = returnZ q \<Longrightarrow> zconst_free pf \<Longrightarrow> zconst_free q"
proof (induction ta inc k pf Ts bs i j G arbitrary: q rule: zlift_prems.induct)
  case (1 ta inc k pf Ts bs i j c U A B)
  show ?case
  proof (cases "c = STR ''Pure.imp''")
    case True
    with "1.prems"(1) obtain A' p where A': "zterm_of ta A = returnZ A'"
      and p: "zlift_prems ta inc k pf Ts (True # bs) (i + 1) j B = returnZ p" and q: "q = ZAbsp (STR ''H'') A' p"
      by (auto simp: bindZ_eq_returnZ)
    from "1.IH"(1)[OF True A'[unfolded returnZ_def] p "1.prems"(2)] q show ?thesis by simp
  next
    case False
    with "1.prems" show ?thesis
      by (auto simp: bindZ_eq_returnZ zconst_free_ZAppps zconst_free_foldr_zmk_app dest: zconst_free_zlift_prf)
  qed
next
  case (2 ta inc k pf Ts bs i j c U a T t)
  then show ?case
    by (cases "c = STR ''Pure.all''")
      (auto simp: bindZ_eq_returnZ zconst_free_ZAppps zconst_free_foldr_zmk_app dest: zconst_free_zlift_prf)
qed (auto simp: bindZ_eq_returnZ zconst_free_ZAppps zconst_free_foldr_zmk_app dest: zconst_free_zlift_prf)

lemma zconst_free_zlift_proof: "zlift_proof ta G inc prems pf = returnZ q \<Longrightarrow> zconst_free pf \<Longrightarrow> zconst_free q"
  by (auto simp: zlift_proof_def bindZ_eq_returnZ zconst_free_ZAbsps dest: zconst_free_zlift_prems)

lemma finite_zcore_vars: "finite (zcore_vars ta env flatten Bs As A oldAs n m visible)"
  by (auto simp: zcore_vars_def finite_prf_vars split: option.splits zres.splits)

text \<open>
  Biresolution with tight proofs that satisfy the invariant modulo the hidden variables: the
  hidden variables of both proofs are separated by fresh names; the separated proofs satisfy the
  invariant, and the theorem for them (@{thm zbiresolution_prf_inv}) applies without conditions on the
  renaming; the composition of the given proofs is a renaming and instantiation of the composition
  of the separated proofs.
\<close>

theorem zbiresolution_hinv:
  assumes br: "okT (biresolution trace match_flg rep brules i state) s0"
    and res: "brresult (unify_ops cfg vl) alg rep s0 (x, (eres_flg, rule))"
    and cfg: "cfg_alg cfg = alg" and vl: "\<And>xs. length (vl xs) = length xs"
    and d: "okT (dest_state state i) (stpairs, Bs, Bi, C)"
    and st: "thm_typeds ar 0 \<Sigma>s state" and ru: "thm_typeds ar 0 \<Sigma>r (rep rule)"
    and si: "zthm_hinv (th_maxidx state) (th_tpairs state) (th_prop state) Hs sprf" "zlb 0 sprf"
    and ri: "zthm_hinv (th_maxidx (rep rule)) (th_tpairs (rep rule)) (th_prop (rep rule)) Hr rprf" "zlb 0 rprf"
    and hs: "\<forall>h\<in>Hr. hyp_ok ar h"
  defines "inc \<equiv> th_maxidx state + 1" and "lr \<equiv> lift_rule Bi (th_maxidx state) (rep rule)"
  shows "\<exists>q. zlift_proof ztargs Bi inc (map (lift_all inc Bi) (strip_imp_prems (th_prop (rep rule)))) rprf = returnZ q \<and>
    (\<exists>vS. ok (full_prop_of (th_tpairs state) (th_prop state)) vS) \<and>
    (\<exists>vR. ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR) \<and>
    (\<forall>vS vR. ok (full_prop_of (th_tpairs state) (th_prop state)) vS \<longrightarrow> ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR \<longrightarrow>
      (\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr (th_maxidx state) q) \<bind>
        (\<lambda>rp. zbicompose_proof ztargs (br_env x) (th_maxidx state) True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf) = returnZ p \<and>
      zthm_hinv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p \<and> zlb 0 p))"
proof -
  let ?smax = "th_maxidx state" and ?R = "rep rule"
  let ?As = "strip_imp_prems (th_prop ?R)" and ?B = "strip_imp_concl (th_prop ?R)"
  let ?VS = "vps_thm (th_tpairs state) (th_prop state)" and ?VR = "vps_thm (th_tpairs ?R) (th_prop ?R)"
  let ?TS = "vars_thm (th_tpairs state) (th_prop state)" and ?TR = "vars_thm (th_tpairs ?R) (th_prop ?R)"
  let ?TL = "vars_thm (th_tpairs lr) (th_prop lr)"
  let ?prems = "map (lift_all inc Bi) ?As"
  from st have sm: "-1 \<le> ?smax" and Slo: "\<forall>x\<in>?TS. 0 \<le> snd x" by (auto simp: thm_typeds_def)
  from ru have nn: "\<forall>x\<in>?TR. 0 \<le> snd x" by (auto simp: thm_typeds_def)
  have inc0: "0 \<le> inc" using sm by (simp add: inc_def)
  from si(1) obtain As Ws where wS: "wt_thm ar As Ws ?smax (th_tpairs state) (th_prop state)"
    by (auto simp: zthm_hinv_def)
  from ri(1) obtain Ar0 Wr where wR: "wt_thm ar Ar0 Wr (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R)"
    by (auto simp: zthm_hinv_def)
  from br res obtain stpairs' Bs' Bi' C' goal where d': "okT (dest_state state i) (stpairs', Bs', Bi', C')"
    and g: "okT (cprem_of state i) goal" and r: "(eres_flg, rule) \<in> set brules"
    and xq: "\<exists>xq0. okT (bicompose_aux (unify_ops cfg vl) alg True match_flg True (pthm_of state)
      (stpairs', Bs', Bi', C') True eres_flg (pthm_of (lift_rule goal (th_maxidx state) (rep rule)))
      (nprems_of (rep rule))) xq0 \<and> bresult (unify_ops cfg vl) xq0 x"
    by (rule biresolution_result)
  have cS: "cok (th_prop state)" using wS by (simp add: wt_thm_def)
  from dest_state_cprem_of[OF d g cS] have sp: "th_prop state = list_implies (Bs @ [Bi]) C" by simp
  have BiS: "vars Bi \<subseteq> ?TS" using sp by (auto simp: vars_thm_def vars_list_implies)
  have Bism: "snd v \<le> ?smax" if "v \<in> vars Bi" for v using wt_thm_below[OF wS] BiS that by blast
  have cR: "cok (th_prop ?R)" using wR by (simp add: wt_thm_def)
  have PR: "th_prop ?R = list_implies ?As ?B" by (rule list_implies_strip_imp[OF cR])
  have plr: "th_prop lr = list_implies ?prems (lift_all inc Bi ?B)"
    by (simp add: lr_def lift_rule_def Let_def inc_def)
  have premsL: "\<Union>(vars ` set ?prems) \<subseteq> ?TL" by (auto simp: plr vars_thm_def vars_list_implies)
  text \<open>The lifted variables of the rule are variables of the lifted rule.\<close>
  have liftv: "(fst y, snd y + inc) \<in> ?TL" if "y \<in> ?TR" for y
  proof -
    obtain pb G0 where ls: "lsplit Bi = (pb, G0)" by (cases "lsplit Bi")
    have la: "vars (lift_all inc Bi t) = pvars pb \<union> (\<lambda>(x, i). (x, i + inc)) ` vars t" for t
      by (simp add: lift_all_lsplit[OF ls] vars_lift_pre vars_incr_indexes)
    have lb: "vars (lift_abs inc Bi t) = (\<lambda>(x, i). (x, i + inc)) ` vars t" for t
      by (simp add: lift_abs_lsplit[OF ls] vars_abs_pre vars_incr_indexes)
    have yf: "(fst y, snd y + inc) = (\<lambda>(x, i). (x, i + inc)) y" by (cases y) simp
    from that consider "y \<in> vars (th_prop ?R)" | t u where "(t, u) \<in> set (th_tpairs ?R)" "y \<in> vars t \<union> vars u"
      by (auto simp: vars_thm_def)
    then show ?thesis
    proof cases
      case 1
      then have "y \<in> vars (list_implies ?As ?B)" by (metis PR)
      then have "y \<in> vars ?B \<or> (\<exists>X\<in>set ?As. y \<in> vars X)" by (auto simp: vars_list_implies)
      then show ?thesis using la yf by (auto simp: plr vars_thm_def vars_list_implies)
    next
      case (2 t u)
      have "(lift_abs inc Bi t, lift_abs inc Bi u) \<in> set (th_tpairs lr)"
        using 2(1) by (force simp: lr_def lift_rule_def Let_def inc_def)
      moreover have "(fst y, snd y + inc) \<in> vars (lift_abs inc Bi t) \<union> vars (lift_abs inc Bi u)"
        using 2(2) lb yf by auto
      ultimately show ?thesis by (force simp: vars_thm_def)
    qed
  qed
  text \<open>Separating the hidden variables by names fresh for a finite set of names.\<close>
  define N0 where "N0 = fst ` (?TS \<union> ?TR \<union> ?TL) \<union> fst ` fst ` (zprf_zvars sprf \<union> zprf_zvars rprf)"
  have fN0: "finite N0" by (simp add: N0_def finite_vars_thm finite_zprf_zvars)
  have constr: "zthm_prf_inv ?smax (th_tpairs state) (th_prop state) Hs (zrenp (hsep (name_bound N) False ?VS) sprf) \<and>
      zrenp (nren (hunsep (name_bound N))) (zrenp (hsep (name_bound N) False ?VS) sprf) = sprf \<and>
      (\<forall>(y, U)\<in>zprf_zvars (zrenp (hsep (name_bound N) False ?VS) sprf).
        (y \<in> ?TS \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name (name_bound N) False a T)) \<and>
      zthm_prf_inv (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R) Hr (zrenp (hsep (name_bound N) True ?VR) rprf) \<and>
      zrenp (nren (hunsep (name_bound N))) (zrenp (hsep (name_bound N) True ?VR) rprf) = rprf \<and>
      (\<forall>(y, U)\<in>zprf_zvars (zrenp (hsep (name_bound N) True ?VR) rprf).
        (y \<in> ?TR \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name (name_bound N) True a T))"
    if fN: "finite N" and N0N: "N0 \<subseteq> N" for N
  proof -
    have v1: "fst ` ?TS \<subseteq> N" "fst ` ?TR \<subseteq> N" using N0N by (auto simp: N0_def)
    have v2: "\<forall>(x, T)\<in>zprf_zvars sprf. fst x \<in> N" "\<forall>(x, T)\<in>zprf_zvars rprf. fst x \<in> N"
      using N0N by (force simp: N0_def)+
    from sep_clean[OF si(1) Slo fN v1(1) v2(1), of False] sep_clean[OF ri(1) nn fN v1(2) v2(2), of True]
    show ?thesis by blast
  qed
  have rcfacts: "zconst_free rc \<and> zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) rc \<and>
      (\<forall>(y, U)\<in>zprf_zvars rc. 0 \<le> snd y) \<and>
      zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) rc"
    if "zthm_prf_inv (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R) Hr rc" for rc
  proof -
    from that obtain Ar1 Wr1 where z: "zinv Ar1 Wr1 (th_maxidx ?R) rc" by (auto simp: zthm_prf_inv_def)
    then have a: "zprf_all (zann Ar1 Wr1 (th_maxidx ?R)) (zty Ar1 (th_maxidx ?R)) rc" by (simp add: zinv_def)
    have "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) rc"
    proof (rule zprf_all_mono[OF a])
      fix t assume t: "zann Ar1 Wr1 (th_maxidx ?R) t"
      show "\<forall>(x, T)\<in>zvars t. -1 \<le> snd x"
      proof (clarify)
        fix x T assume "(x, T) \<in> zvars t"
        with t show "-1 \<le> snd x" by (cases "snd x = -1") (auto simp: zann_def)
      qed
    qed simp
    moreover have "\<forall>(y, U)\<in>zprf_zvars rc. 0 \<le> snd y"
    proof (clarify)
      fix y U assume yU: "(y, U) \<in> zprf_zvars rc"
      from zprf_all_zprf_zvars_ex[OF a yU] obtain t where "zann Ar1 Wr1 (th_maxidx ?R) t" "(y, U) \<in> zvars t" by blast
      with zprf_zvars_snd[OF yU] show "0 \<le> snd y" by (auto simp: zann_def)
    qed
    moreover have "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) rc"
      by (rule zprf_all_mono[OF a]) (auto simp: zann_def)
    ultimately show ?thesis using z by (simp add: zinv_def)
  qed
  have liftact: "zlift_proof ztargs Bi inc ?prems rprf = returnZ (zrenp (nren (hunsep (name_bound N))) qc)"
    if fN: "finite N" and N0N: "N0 \<subseteq> N"
      and l: "zlift_proof ztargs Bi inc ?prems (zrenp (hsep (name_bound N) True ?VR) rprf) = returnZ qc" for N qc
  proof -
    let ?k = "name_bound N" let ?rc = "zrenp (hsep ?k True ?VR) rprf"
    from constr[OF fN N0N] have ri': "zthm_prf_inv (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R) Hr ?rc"
      and bk: "zrenp (nren (hunsep ?k)) ?rc = rprf" by blast+
    from rcfacts[OF ri'] have c: "zconst_free ?rc" and a: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) ?rc"
      by blast+
    have fx: "hunsep ?k (fst v) = fst v" if "v \<in> vars Bi \<union> (\<Union>A\<in>set ?prems. vars A)" for v
    proof (rule hunsep_other)
      have "fst v \<in> N0" using that BiS premsL by (force simp: N0_def)
      with N0N have "fst v \<in> N" by blast
      then show "fst v \<noteq> fresh_name ?k b a T" for b a T using fresh_name_notin[OF fN] by auto
    qed
    from zlift_proof_nren[OF l c inc0 a fx] bk show ?thesis by simp
  qed
  text \<open>The lifted proof.\<close>
  define k0 where "k0 = name_bound N0"
  from constr[OF fN0 subset_refl, folded k0_def] have sinv0: "zthm_prf_inv ?smax (th_tpairs state) (th_prop state) Hs
      (zrenp (hsep k0 False ?VS) sprf)"
    and rinv0: "zthm_prf_inv (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R) Hr (zrenp (hsep k0 True ?VR) rprf)"
    by blast+
  have sl0: "zlb 0 (zrenp (hsep k0 False ?VS) sprf)" and rl0: "zlb 0 (zrenp (hsep k0 True ?VR) rprf)"
    using si(2) ri(2) by simp_all
  from zbiresolution_prf_inv[OF br res cfg vl d st ru sinv0 sl0 rinv0 rl0 hs, folded inc_def lr_def]
  obtain qc0 where lift0: "zlift_proof ztargs Bi inc ?prems (zrenp (hsep k0 True ?VR) rprf) = returnZ qc0"
    and eS: "\<exists>vS. ok (full_prop_of (th_tpairs state) (th_prop state)) vS"
    and eR: "\<exists>vR. ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR"
    by blast
  define q where "q = zrenp (nren (hunsep k0)) qc0"
  have liftq: "zlift_proof ztargs Bi inc ?prems rprf = returnZ q"
    using liftact[OF fN0 subset_refl lift0[unfolded k0_def]] by (simp add: q_def k0_def)
  show ?thesis
  proof (rule exI[of _ q], intro conjI liftq eS eR allI impI)
    fix vS vR
    assume vS: "ok (full_prop_of (th_tpairs state) (th_prop state)) vS"
      and vR: "ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR"
    let ?nsub = "count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1"
    define RN where "RN = (case na_ren (br_newas x) of None \<Rightarrow> {} | Some rr \<Rightarrow> fst ` set (fst rr) \<union> snd ` set (fst rr))"
    define N where "N = N0 \<union> fst ` (vars_thm (br_tpairs x) (br_prop x) \<union> fst ` bvps (br_env x) \<union>
      zcore_vars ztargs (br_env x) True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x)) (na_n (br_newas x))
        ?nsub [vS, vR] \<union> fst ` set (visible_vars [vS, vR])) \<union> RN"
    have fRN: "finite RN" by (simp add: RN_def split: option.splits)
    have fN: "finite N" using fN0 fRN by (simp add: N_def finite_vars_thm finite_bvps finite_zcore_vars)
    have N0N: "N0 \<subseteq> N" by (auto simp: N_def)
    define k where "k = name_bound N"
    let ?sc = "zrenp (hsep k False ?VS) sprf" and ?rc = "zrenp (hsep k True ?VR) rprf"
    from constr[OF fN N0N, folded k_def] have sinv: "zthm_prf_inv ?smax (th_tpairs state) (th_prop state) Hs ?sc"
      and sback: "zrenp (nren (hunsep k)) ?sc = sprf"
      and snames: "\<forall>(y, U)\<in>zprf_zvars ?sc. (y \<in> ?TS \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k False a T)"
      and rinv: "zthm_prf_inv (th_maxidx ?R) (th_tpairs ?R) (th_prop ?R) Hr ?rc"
      and rnames: "\<forall>(y, U)\<in>zprf_zvars ?rc. (y \<in> ?TR \<and> fst y \<in> N) \<or> (\<exists>a T. fst y = fresh_name k True a T)"
      by blast+
    have frN: "fresh_name k b a T \<notin> N" for b a T using fresh_name_notin[OF fN] by (simp add: k_def)
    have sl: "zlb 0 ?sc" and rl: "zlb 0 ?rc" using si(2) ri(2) by simp_all
    from zbiresolution_prf_inv[OF br res cfg vl d st ru sinv sl rinv rl hs, folded inc_def lr_def]
    obtain qc where liftc: "zlift_proof ztargs Bi inc ?prems ?rc = returnZ qc"
      and zlbrp: "\<forall>rp. (case na_ren (br_newas x) of None \<Rightarrow> returnZ qc | Some rr \<Rightarrow> zren_proof rr ?smax qc) =
        returnZ rp \<longrightarrow> zlb 0 rp"
      and E: "\<forall>vS vR. ok (full_prop_of (th_tpairs state) (th_prop state)) vS \<longrightarrow>
        ok (full_prop_of (th_tpairs lr) (th_prop lr)) vR \<longrightarrow>
        zren_ok (br_newas x) ?smax (th_tpairs state) (th_prop state) (th_tpairs lr) (th_prop lr) ?sc qc \<longrightarrow>
        (\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ qc | Some rr \<Rightarrow> zren_proof rr ?smax qc) \<bind>
          (\<lambda>rp. zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
            (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] rp ?sc) = returnZ p \<and>
          zthm_prf_inv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p \<and> zlb 0 p) \<and>
        (\<forall>rp p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ qc | Some rr \<Rightarrow> zren_proof rr ?smax qc) = returnZ rp \<longrightarrow>
          zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
            (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] rp ?sc = returnZ p \<longrightarrow>
          (\<exists>Ar Wf. finite Ar \<and> scons Ar \<and> tcert alg Ar \<and> (\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx (br_env x)) \<and>
            (\<forall>x. tyA ar Ar (Wf x)) \<and> wt_thm ar Ar Wf (maxidx (br_env x)) (br_tpairs x) (br_prop x) \<and>
            prf_valid alg ar Wf (Hs \<union> Hr) (br_tpairs x) (zprf_tr p) (br_prop x) \<and> zinv Ar Wf (maxidx (br_env x)) p \<and>
            (\<not> env_is_empty (br_env x) \<longrightarrow> (\<exists>V PU. znorm_hyps (br_env x) [vS, vR] V Wf PU
              (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) \<and>
              (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx (br_env x))) \<and>
              znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) rp \<and>
              (\<not> above (br_env x) ?smax \<longrightarrow>
                znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) ?sc)))))"
      by (elim exE conjE) (rule that)
    have qq: "q = zrenp (nren (hunsep k)) qc"
      using liftact[OF fN N0N liftc[unfolded k_def]] liftq by (simp add: k_def)
    from rcfacts[OF rinv] have rcc: "zconst_free ?rc" and rca: "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. -1 \<le> snd x) (\<lambda>_. True) ?rc"
      and rc0: "\<forall>(y, U)\<in>zprf_zvars ?rc. 0 \<le> snd y"
      and rca': "zprf_all (\<lambda>t. \<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x) (\<lambda>_. True) ?rc" by blast+
    have qcc: "zconst_free qc" by (rule zconst_free_zlift_proof[OF liftc rcc])
    text \<open>The variables of the lifted separated proof of the rule.\<close>
    have qcv: "y \<in> vars Bi \<or> y \<in> ?TL \<or> ((\<exists>a T. fst y = fresh_name k True a T) \<and> ?smax < snd y)"
      if "(y, U) \<in> zprf_zvars qc" for y U
    proof -
      from zprf_zvars_zlift_proof[OF liftc rcc rca' that] consider y' U' where "(y', U') \<in> zprf_zvars ?rc"
        "fst y = fst y'" "snd y = snd y' + inc" | "y \<in> vars Bi \<union> (\<Union>A\<in>set ?prems. vars A)" by blast
      then show ?thesis
      proof cases
        case 1
        have "0 \<le> snd y'" using rc0 1(1) by blast
        then have sm': "?smax < snd y" using 1(3) by (simp add: inc_def)
        from rnames 1(1) consider "y' \<in> ?TR" | a T where "fst y' = fresh_name k True a T" by blast
        then show ?thesis
        proof cases
          case 1
          from liftv[OF this] \<open>fst y = fst y'\<close> \<open>snd y = snd y' + inc\<close> have "y \<in> ?TL" by (metis prod.collapse)
          then show ?thesis by blast
        next
          case (2 a T)
          then have "fst y = fresh_name k True a T" using \<open>fst y = fst y'\<close> by simp
          with sm' show ?thesis by blast
        qed
      next
        case 2
        then show ?thesis using premsL by blast
      qed
    qed
    have qcN: "fst y \<in> N \<or> (\<exists>a T. fst y = fresh_name k True a T)" if "(y, U) \<in> zprf_zvars qc" for y U
      using qcv[OF that] BiS N0N by (force simp: N0_def)
    have RNN: "RN \<subseteq> N" by (simp add: N_def)
    have renN: "ren_name (fst rr) a \<in> N" if "na_ren (br_newas x) = Some rr" "a \<in> N" for rr a
      using ren_name_cases[of "fst rr" a] that RNN by (auto simp: RN_def)
    have renF: "ren_name (fst rr) (fresh_name k b a T) = fresh_name k b a T" if "na_ren (br_newas x) = Some rr" for rr b a T
      using that RNN frN by (intro ren_name_notin) (force simp: RN_def)
    text \<open>The condition of the main theorem on the renaming holds for the separated proofs.\<close>
    have ro: "zren_ok (br_newas x) ?smax (th_tpairs state) (th_prop state) (th_tpairs lr) (th_prop lr) ?sc qc"
      unfolding zren_ok_def
    proof
      fix y assume y: "y \<in> prf_vars (zprf_tr qc) - ?TL"
      then obtain U where yU: "(y, U) \<in> zprf_zvars qc" by (auto simp: prf_vars_zprf_tr)
      have nTL: "y \<notin> ?TL" using y by blast
      from qcv[OF yU] nTL consider "y \<in> vars Bi" | a T where "fst y = fresh_name k True a T" "?smax < snd y" by blast
      then show "ren_of (br_newas x) ?smax y = y \<and> y \<notin> ren_of (br_newas x) ?smax ` ?TL"
      proof cases
        case 1
        have ys: "snd y \<le> ?smax" by (rule Bism[OF 1])
        then have "ren_of (br_newas x) ?smax y = y" by (simp add: ren_of_def split: option.splits)
        moreover have "y \<notin> ren_of (br_newas x) ?smax ` ?TL"
        proof
          assume "y \<in> ren_of (br_newas x) ?smax ` ?TL"
          then obtain z where z: "z \<in> ?TL" "y = ren_of (br_newas x) ?smax z" by blast
          show False
          proof (cases "?smax < snd z \<and> na_ren (br_newas x) \<noteq> None")
            case True
            then have "snd y = snd z" using z(2) by (auto simp: ren_of_def ren_ix_def)
            with True ys show False by simp
          next
            case False
            then have "y = z" using z(2) by (auto simp: ren_of_def split: option.splits)
            with z(1) nTL show False by simp
          qed
        qed
        ultimately show ?thesis by blast
      next
        case (2 a T)
        have "ren_of (br_newas x) ?smax y = y"
          using 2 renF by (cases y) (auto simp: ren_of_def ren_ix_def split: option.splits)
        moreover have "y \<notin> ren_of (br_newas x) ?smax ` ?TL"
        proof
          assume "y \<in> ren_of (br_newas x) ?smax ` ?TL"
          then obtain z where z: "z \<in> ?TL" "y = ren_of (br_newas x) ?smax z" by blast
          have "fst z \<in> N" using z(1) N0N by (force simp: N0_def)
          then have "fst y \<in> N" using z(2) renN by (auto simp: ren_of_def ren_ix_def split: option.splits)
          with 2(1) frN show False by simp
        qed
        ultimately show ?thesis by blast
      qed
    qed
    note EE = E[rule_format, OF vS vR ro]
    from conjunct1[OF EE] obtain pc0 where
      E1: "(case na_ren (br_newas x) of None \<Rightarrow> returnZ qc | Some rr \<Rightarrow> zren_proof rr ?smax qc) \<bind>
          (\<lambda>rp. zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
            (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] rp ?sc) = returnZ pc0"
      and zlpc: "zlb 0 pc0" by (elim exE conjE) (rule that)
    from E1 obtain rpc where rpc: "(case na_ren (br_newas x) of None \<Rightarrow> returnZ qc | Some rr \<Rightarrow> zren_proof rr ?smax qc) =
        returnZ rpc"
      and bpc: "zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
            (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] rpc ?sc = returnZ pc0"
      by (auto simp: bindZ_eq_returnZ)
    from conjunct2[OF EE, rule_format, OF rpc bpc] obtain Ar Wf where fA: "finite Ar" "scons Ar" "tcert alg Ar"
      and A1: "\<forall>q\<in>Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx (br_env x)"
      and tyw: "\<forall>x. tyA ar Ar (Wf x)" and wt: "wt_thm ar Ar Wf (maxidx (br_env x)) (br_tpairs x) (br_prop x)"
      and pv: "prf_valid alg ar Wf (Hs \<union> Hr) (br_tpairs x) (zprf_tr pc0) (br_prop x)"
      and zp: "zinv Ar Wf (maxidx (br_env x)) pc0"
      and zn: "\<not> env_is_empty (br_env x) \<longrightarrow> (\<exists>V PU. znorm_hyps (br_env x) [vS, vR] V Wf PU
              (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) \<and>
              (\<forall>U. PU U \<longrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx (br_env x))) \<and>
              znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) rpc \<and>
              (\<not> above (br_env x) ?smax \<longrightarrow>
                znorm_pok (br_env x) [vS, vR] V PU (\<lambda>k. 0 \<le> k \<and> k \<le> maxidx (br_env x)) ?sc))"
      by (elim exE conjE) (rule that)
    have zlrpc: "zlb 0 rpc" using zlbrp rpc by blast
    text \<open>The renaming back to the given proofs.\<close>
    define mu where "mu = (case na_ren (br_newas x) of None \<Rightarrow> hunsep k
      | Some rr \<Rightarrow> (\<lambda>n. if \<exists>a T. n = fresh_name k True a T then ren_name (fst rr) (hunsep k n) else hunsep k n))"
    have huN: "hunsep k n = n" if "n \<in> N" for n using that frN by (intro hunsep_other) metis
    have muN: "mu n = n" if "n \<in> N" for n
      using that huN frN by (auto simp: mu_def split: option.splits)
    have muF: "mu (fresh_name k False a T) = a" for a T
      by (auto simp: mu_def fresh_name_inj split: option.splits)
    have rpcN: "fst y \<in> N \<or> (\<exists>a T. fst y = fresh_name k True a T)" if "(y, U) \<in> zprf_zvars rpc" for y U
    proof (cases "na_ren (br_newas x)")
      case None
      with rpc that have "(y, U) \<in> zprf_zvars qc" by simp
      then show ?thesis by (rule qcN)
    next
      case (Some rr)
      with rpc have "map_zproof id (\<lambda>t. returnZ (zren_term rr ?smax t)) qc = returnZ rpc"
        by (simp add: zren_proof_def)
      from zprf_zvars_map_zren[OF this that] obtain y0 where y0: "(y0, U) \<in> zprf_zvars qc"
        "fst y = (if ?smax < snd y0 then ren_name (fst rr) (fst y0) else fst y0)" by blast
      from qcN[OF y0(1)] show ?thesis
      proof
        assume "fst y0 \<in> N"
        with y0(2) renN[OF Some] show ?thesis by auto
      next
        assume "\<exists>a T. fst y0 = fresh_name k True a T"
        then obtain a T' where a: "fst y0 = fresh_name k True a T'" by blast
        then have "fst y = fresh_name k True a T'" using y0(2) renF[OF Some] by simp
        then show ?thesis by blast
      qed
    qed
    have rpa: "(case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr ?smax q) =
        returnZ (zrenp (nren mu) rpc)"
    proof (cases "na_ren (br_newas x)")
      case None
      with rpc qq show ?thesis by (simp add: mu_def)
    next
      case (Some rr)
      with rpc have zr: "zren_proof rr ?smax qc = returnZ rpc" by simp
      have rc: "\<forall>(y, U)\<in>zprf_zvars qc. ren_cond rr ?smax (hunsep k) mu y"
      proof (clarify)
        fix y U assume yU: "(y, U) \<in> zprf_zvars qc"
        from qcv[OF yU] consider "fst y \<in> N" | a T where "fst y = fresh_name k True a T" "?smax < snd y"
          using BiS N0N by (force simp: N0_def)
        then show "ren_cond rr ?smax (hunsep k) mu y"
        proof cases
          case 1
          have "(if ?smax < snd y then ren_name (fst rr) (fst y) else fst y) \<in> N" using 1 renN[OF Some] by auto
          with 1 show ?thesis by (simp add: ren_cond_def huN muN)
        next
          case (2 a T)
          then show ?thesis using renF[OF Some] by (simp add: ren_cond_def mu_def Some) blast
        qed
      qed
      from zren_proof_nren[OF zr qcc rc] Some qq show ?thesis by (simp add: mu_def)
    qed
    have spa: "zrenp (nren mu) ?sc = sprf"
    proof -
      have "zrenp (nren mu) ?sc = zrenp (nren (hunsep k)) ?sc"
      proof (rule zrenp_cong)
        fix y U assume "(y, U) \<in> zprf_zvars ?sc"
        with snames consider "fst y \<in> N" | a T where "fst y = fresh_name k False a T" by blast
        then show "nren mu y U = nren (hunsep k) y U"
          by cases (simp_all add: nren_def muN huN muF)
      qed
      with sback show ?thesis by simp
    qed
    have mvN: "fst z \<notin> N" if "mu (fst z) \<noteq> fst z" for z using that muN by blast
    have hb: "\<exists>pa. zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
        (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] (zrenp (nren mu) rpc) (zrenp (nren mu) ?sc) =
        returnZ pa \<and> zthm_hinv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) pa \<and> zlb 0 pa"
    proof (rule zbicompose_hidden[OF bpc fA A1 tyw wt pv zp zn zlrpc sl zlpc])
      show "\<forall>z T. (z, T) \<in> zprf_zvars rpc \<longrightarrow> mu (fst z) \<noteq> fst z \<longrightarrow>
          z \<notin> fst ` set (visible_vars [vS, vR]) \<and> z \<notin> fst ` bvps (br_env x)"
        using mvN by (force simp: N_def)
      show "\<forall>z T. (z, T) \<in> zprf_zvars ?sc \<longrightarrow> mu (fst z) \<noteq> fst z \<longrightarrow>
          z \<notin> fst ` set (visible_vars [vS, vR]) \<and> z \<notin> fst ` bvps (br_env x)"
        using mvN by (force simp: N_def)
      show "\<forall>z\<in>zcore_vars ztargs (br_env x) True Bs (na_As (br_newas x)) (br_A x) (na_oldAs (br_newas x))
          (na_n (br_newas x)) ?nsub [vS, vR]. mu (fst z) = fst z"
        using muN by (force simp: N_def)
      show "\<forall>z\<in>vars_thm (br_tpairs x) (br_prop x). mu (fst z) = fst z"
        using muN by (force simp: N_def)
      show "\<forall>(z, T)\<in>zprf_zvars rpc. \<forall>(y, U)\<in>zprf_zvars ?sc. fst z = fst y \<longrightarrow> mu (fst z) = fst z"
      proof (clarify)
        fix z T y U assume zT: "(z, T) \<in> zprf_zvars rpc" and yU: "(y, U) \<in> zprf_zvars ?sc" and e: "fst z = fst y"
        show "mu (fst z) = fst z"
        proof (cases "fst z \<in> N")
          case True
          then show ?thesis by (rule muN)
        next
          case False
          with rpcN[OF zT] obtain a T' where a: "fst z = fresh_name k True a T'" by blast
          from snames yU False e obtain a' T'' where "fst y = fresh_name k False a' T''" by fastforce
          with a e show ?thesis by (simp add: fresh_name_inj)
        qed
      qed
    qed
    then obtain pa where pa: "zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
        (na_oldAs (br_newas x)) (na_n (br_newas x)) ?nsub [vS, vR] (zrenp (nren mu) rpc) sprf = returnZ pa"
      and hinv: "zthm_hinv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) pa" and zla: "zlb 0 pa"
      unfolding spa by blast
    show "\<exists>p. (case na_ren (br_newas x) of None \<Rightarrow> returnZ q | Some rr \<Rightarrow> zren_proof rr ?smax q) \<bind>
        (\<lambda>rp. zbicompose_proof ztargs (br_env x) ?smax True Bs (na_As (br_newas x)) (br_A x)
          (na_oldAs (br_newas x)) (na_n (br_newas x))
          (count_prems (strip_all_body Bi) + (if eres_flg then -1 else 0) + 1) [vS, vR] rp sprf) = returnZ p \<and>
      zthm_hinv (maxidx (br_env x)) (br_tpairs x) (br_prop x) (Hs \<union> Hr) p \<and> zlb 0 p"
      using pa hinv zla by (intro exI[of _ pa]) (simp add: rpa)
  qed
qed

end

end
