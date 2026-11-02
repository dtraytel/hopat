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

end

end
