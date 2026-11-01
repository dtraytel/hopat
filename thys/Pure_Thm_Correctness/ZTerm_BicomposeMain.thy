section \<open>Correctness of the composition of tight proofs: main theorem\<close>

theory ZTerm_BicomposeMain
  imports ZTerm_BicomposeProof
begin

context prf_wf_csig
begin

subsection \<open>The invariant of tight proofs\<close>

definition zty :: "(indexname \<times> psort) set \<Rightarrow> integer \<Rightarrow> ztyp \<Rightarrow> bool" where
  "zty A m T \<longleftrightarrow> zcan T \<and> tvars (typ_of T) \<subseteq> A \<and> (\<forall>(v, S)\<in>tvars (typ_of T). snd v \<le> m)"

definition zann :: "(indexname \<times> psort) set \<Rightarrow> (indexname \<Rightarrow> ptyp) \<Rightarrow> integer \<Rightarrow> zterm \<Rightarrow> bool" where
  "zann A W m t \<longleftrightarrow> (\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m \<and> T = ztyp_of (W x)) \<and>
    (\<forall>T\<in>ztys t. zty A m T) \<and> (\<exists>Ts U. has_type W Ts (zdec t) U)"

lemma has_type_zvars:
  "has_type W Ts (zdec t) U \<Longrightarrow> (x, T) \<in> zvars t \<Longrightarrow> snd x \<noteq> -1 \<Longrightarrow> typ_of T = W x"
proof (induction t arbitrary: Ts U)
  case (ZApp t u)
  then show ?case by (auto elim: has_type.cases)
next
  case (ZAbs a T' t)
  then show ?case by (auto elim: has_type.cases)
qed (auto elim: has_type.cases split: if_splits)

lemma zann_intro:
  assumes "\<forall>(x, T)\<in>zvars t. snd x \<noteq> -1 \<longrightarrow> 0 \<le> snd x \<and> snd x \<le> m"
    "\<forall>T\<in>ztys t. zty A m T" "has_type W Ts (zdec t) U"
  shows "zann A W m t"
proof -
  have "T = ztyp_of (W x)" if "(x, T) \<in> zvars t" "snd x \<noteq> -1" for x T
  proof -
    have "T \<in> ztys t" using that(1) by (induction t) auto
    with assms(2) have "zcan T" by (simp add: zty_def)
    with has_type_zvars[OF assms(3) that] show ?thesis using ztyp_of_typ_of_zcan by metis
  qed
  with assms show ?thesis unfolding zann_def by blast
qed

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

lemma tys_strip_apply:
  assumes "\<forall>U\<in>tys B. P U" "\<forall>U\<in>tys A. P U" "\<And>t. \<forall>U\<in>tys t. P U \<Longrightarrow> \<forall>U\<in>tys (f t). P U"
  shows "\<forall>U\<in>tys (strip_apply f B A). P U"
  using assms(1,2)
proof (induction A arbitrary: B rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "\<exists>U B0 B1 V A2 B2. B = Const STR ''Pure.imp'' U $ B0 $ B1 \<and> A = Const STR ''Pure.imp'' V $ A2 $ B2")
    case True
    then obtain U B0 B1 V A2 B2 where e: "B = Const STR ''Pure.imp'' U $ B0 $ B1"
      "A = Const STR ''Pure.imp'' V $ A2 $ B2" by blast
    have IH: "\<forall>U\<in>tys (strip_apply f B1 B2). P U" by (rule less.IH) (use less.prems e in auto)
    have "strip_apply f B A = Const STR ''Pure.imp'' U $ A2 $ strip_apply f B1 B2"
      using e by (subst strip_apply.simps) simp
    with IH less.prems e show ?thesis by auto
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
      have IH: "\<forall>U\<in>tys (strip_apply f t1 t2). P U" by (rule less.IH) (use less.prems e in auto)
      have "strip_apply f B A = Const STR ''Pure.all'' U $ Abs a T (strip_apply f t1 t2)"
        using e by (subst strip_apply.simps) (simp add: ni)
      with IH less.prems e show ?thesis by auto
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


lemma cts_incr_bv[simp]: "cts (incr_bv inc lev t) = cts t"
  by (induction inc lev t rule: incr_bv.induct) auto

lemma cts_incr_boundvars[simp]: "cts (incr_boundvars j t) = cts t"
  by (simp add: incr_boundvars_def)

lemma cts_list_forall: "cts t \<Longrightarrow> cts (list_forall vs t)"
  by (induction vs t rule: list_forall.induct) (auto simp: all_const_def const_typ_ok_def propT_def)

lemma cts_remove_params: "ok (remove_params j n A) A' \<Longrightarrow> cts A \<Longrightarrow> cts A'"
proof (induction A arbitrary: j n A' rule: measure_induct_rule[of size])
  case (less A)
  show ?case
  proof (cases "j = 0 \<and> n \<le> 0")
    case True
    with less.prems show ?thesis by (subst (asm) remove_params.simps) (simp add: return_def)
  next
    case False
    show ?thesis
    proof (cases "dest_imp A")
      case (Some HB)
      obtain H B where HB: "HB = (H, B)" by (cases HB)
      with Some obtain U where A: "A = Const STR ''Pure.imp'' U $ H $ B" by (auto simp: dest_imp_Some)
      have cB: "cts B" "cts H" using less.prems(2) A by auto
      have sB: "size B < size A" using A by simp
      show ?thesis
      proof (cases "n = 1")
        case True
        with less.prems(1) False Some HB have "ok (remove_params j (n - 1) B) A'"
          by (subst (asm) remove_params.simps) simp
        from less.IH[OF sB this cB(1)] show ?thesis .
      next
        case n1: False
        with less.prems(1) False Some HB obtain B' where B': "ok (remove_params j (n - 1) B) B'"
          "A' = implies $ incr_boundvars j H $ B'"
          by (subst (asm) remove_params.simps) (auto simp: return_def)
        from less.IH[OF sB B'(1) cB(1)] B'(2) cB(2) show ?thesis
          by (simp add: implies_def const_typ_ok_def propT_def)
      qed
    next
      case None
      show ?thesis
      proof (cases "dest_all A")
        case (Some aTt)
        obtain a T t where aTt: "aTt = (a, T, t)" by (cases aTt)
        with Some obtain U where A: "A = Const STR ''Pure.all'' U $ Abs a T t" by (auto simp: dest_all_Some)
        have st: "size t < size A" using A by simp
        from less.prems(1) False None Some aTt have "ok (remove_params (j - 1) n t) A'"
          by (subst (asm) remove_params.simps) simp
        from less.IH[OF st this] less.prems(2) A show ?thesis by simp
      next
        case None': None
        with less.prems False None show ?thesis
          by (subst (asm) remove_params.simps) (auto simp: return_def raise_def split: if_splits)
      qed
    qed
  qed
qed

lemma cts_flatten_params: "ok (flatten_params vl n A) A' \<Longrightarrow> cts A \<Longrightarrow> cts A'"
  by (auto simp: flatten_params_def Let_def return_def intro!: cts_list_forall dest: cts_remove_params
      split: option.splits res.splits simp: bindM_def)

text \<open>
  The terms of an environment convert to tight terms: their constants have instances of their
  declared types and no variable has a negative index. For the environments of the unifier this holds
  as their terms are built from the terms of the problem (whose constants keep their types) and
  from fresh variables; it is a hypothesis of the main theorem.
\<close>

definition zenv_ok :: "env \<Rightarrow> bool" where
  "zenv_ok env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> 0 \<le> snd x \<and> cts u \<and>
    (\<forall>v\<in>vars u. 0 \<le> snd v) \<and> (\<forall>T\<in>tys u. \<forall>(v, S)\<in>tvars T. 0 \<le> snd v))"

lemma tenv_zok_zenv_ok:
  assumes "zenv_ok env" "\<forall>T\<in>etys env. tcons (tyenv env) T"
  shows "tenv_zok ztargs env"
  by (rule tenv_zok_cts) (use assms etysI in \<open>fastforce simp: zenv_ok_def integer_nonneg_ne_m1\<close>)

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


subsection \<open>Variables of tight proofs\<close>

lemma prf_vars_zprf_tr: "x \<in> prf_vars (zprf_tr p) \<Longrightarrow> zprf_all P Q p \<Longrightarrow> \<exists>t. P t \<and> x \<in> vars (zdec t)"
  by (induction p) auto

lemma zprf_all_tr:
  "zprf_all P Q p \<Longrightarrow> (\<And>t. P t \<Longrightarrow> P' (zdec t)) \<Longrightarrow> (\<And>T. Q T \<Longrightarrow> Q' (typ_of T)) \<Longrightarrow>
    prf_all P' Q' (zprf_tr p)"
  by (induction p) auto


lemma ztys_zren_term[simp]: "ztys (zren_term r m t) = ztys t"
  by (induction r m t rule: zren_term.induct) auto

lemma zprf_all_zren:
  "map_zproof id (\<lambda>t. returnZ (zren_term r m t)) p = returnZ p' \<Longrightarrow> zconst_free p \<Longrightarrow> zprf_all P Q p \<Longrightarrow>
    (\<And>t. P t \<Longrightarrow> P' (zren_term r m t)) \<Longrightarrow> zprf_all P' Q p'"
  by (induction p arbitrary: p') (auto simp: bindZ_eq_returnZ)

lemma zinv_prf_vars: "zinv A W m p \<Longrightarrow> x \<in> prf_vars (zprf_tr p) \<Longrightarrow> 0 \<le> snd x \<and> snd x \<le> m"
  using prf_vars_zprf_tr[of x p "zann A W m" "zty A m"] by (fastforce simp: zinv_def zann_def vars_zdec)


subsection \<open>Visible variables\<close>

lemma set_term_vars[simp]: "set (term_vars t) = vps t"
  by (induction t) auto

lemma set_term_types[simp]: "set (term_types t) = tys t"
  by (induction t) auto

lemma set_visible_vars: "set (visible_vars ts) = (\<Union>t\<in>set ts. vps t)"
  by (simp add: visible_vars_def)

lemma set_visible_tvars: "set (visible_tvars ts) = (\<Union>t\<in>set ts. \<Union>U\<in>tys t. tvars U)"
  by (simp add: visible_tvars_def set_typ_tvars)

lemma vps_has_type_typ: "has_type V Ts u U \<Longrightarrow> (y, T) \<in> vps u \<Longrightarrow> V y = T"
  by (induction arbitrary: y T rule: has_type.induct) auto

lemma tvars_has_type: "has_type V Ts t T \<Longrightarrow> tvars T \<subseteq> (\<Union>U\<in>tys t \<union> set Ts. tvars U)"
proof (induction rule: has_type.induct)
  case (Bound i Ts T V)
  then have "T \<in> set Ts" by (simp add: integer_reps)
  then show ?case by blast
qed auto

lemma tys_full_prop_of:
  assumes "ok (full_prop_of tps P) p" "\<forall>(t, u)\<in>set tps. \<exists>T. has_type V [] t T"
  shows "(\<Union>U\<in>tys p. tvars U) \<subseteq> (\<Union>U\<in>tys P \<union> (\<Union>(t, u)\<in>set tps. tys t \<union> tys u). tvars U)"
proof -
  from assms(1) obtain eqs where l: "list_all2 (\<lambda>tu eq. ok (mk_equals tu) eq) tps eqs" and p: "p = list_implies eqs P"
    by (auto simp: full_prop_of_def ok_mapM)
  from l assms(2) have "(\<Union>A\<in>set eqs. \<Union>U\<in>tys A. tvars U) \<subseteq> (\<Union>(t, u)\<in>set tps. \<Union>U\<in>tys t \<union> tys u. tvars U)"
  proof (induction rule: list_all2_induct)
    case (Cons tu tps eq eqs)
    obtain t u where tu: "tu = (t, u)" by (cases tu)
    from Cons.prems tu obtain T where ht: "has_type V [] t T" by auto
    have IH: "(\<Union>A\<in>set eqs. \<Union>U\<in>tys A. tvars U) \<subseteq> (\<Union>(t, u)\<in>set tps. \<Union>U\<in>tys t \<union> tys u. tvars U)"
      using Cons.IH Cons.prems by simp
    from Cons.hyps(1) tu fastype_of_closed[OF ht] have "eq = Const STR ''Pure.eq'' (T \<rightarrow>\<^sub>T T \<rightarrow>\<^sub>T propT) $ t $ u"
      by (auto simp: mk_equals_def return_def)
    then have h: "(\<Union>U\<in>tys eq. tvars U) \<subseteq> (\<Union>U\<in>tys t \<union> tys u. tvars U)"
      using tvars_has_type[OF ht] by (auto simp: propT_def)
    show ?case unfolding tu using IH h by auto
  qed simp
  then show ?thesis by (auto simp: p tys_list_implies imp_type_def propT_def)
qed


subsection \<open>Correctness of the composition\<close>

text \<open>
  The judgment identifies schematic variables by their names, Isabelle by their names and types.
  The main theorem therefore assumes that the renaming of the new premises of a lifted rule
  (\<open>rename_bvars\<close>) is injective on the variables of the rule, keeps the hidden variables of its
  tight proof, and gives the renamed variables names (with their indices) that no variable of the
  theorems and their tight proofs has. For the variables of the theorems this is the purpose of
  the renaming; for the variables of the proofs, it excludes a renamed variable taking the name of a
  hidden variable with another type, which Isabelle keeps apart.
\<close>

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
    and rfr: "\<forall>x\<in>vars_thm rtpairs rprop. ren_of (br_newas r) smax x \<noteq> x \<longrightarrow>
      ren_of (br_newas r) smax x \<notin> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop \<union>
        prf_vars (zprf_tr sprf) \<union> prf_vars (zprf_tr rprf)"
    and rinj: "inj_on (ren_of (br_newas r) smax) (vars_thm rtpairs rprop)"
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
  have tusV: "\<forall>(t, u)\<in>set tus. vars t \<union> vars u \<subseteq>
      vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop"
  proof (rule itsok_vars[OF sp_def its])
    show "vars Bi \<subseteq> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop"
      by (auto simp: vars_thm_def vars_list_implies)
    show "vars B \<subseteq> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop"
      by (auto simp: vars_thm_def vars_list_implies P)
    show "\<forall>X\<in>set rAs. vars X \<subseteq> vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop \<and> cok X"
      using rule(1) by (auto simp: vars_thm_def vars_list_implies P wt_thm_def)
    show "\<forall>(t, u)\<in>set (rtpairs @ stpairs). vars t \<union> vars u \<subseteq>
        vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop"
      by (auto simp: vars_thm_def)
    show "\<exists>p Bi0 B0. lsplit Bi = (p, Bi0) \<and> B = lift_pre p B0" if lifted
      using lifted_over_lifted_rule[OF rule(2)[OF that] sp1] by (auto simp: lifted_rule_def)
  qed
  text \<open>The hidden variables: variables of the proofs that do not occur in the theorems.\<close>
  define OH where "OH = (prf_vars (zprf_tr sprf) \<union> prf_vars (zprf_tr rprf)) -
    (vars_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vars_thm rtpairs rprop)"
  have OHf: "vt_lookup (tenv env') x = None \<and> x \<notin> fst ` bvps env' \<and> (\<forall>(t, u)\<in>set tps. x \<notin> vars t \<and> x \<notin> vars u) \<and>
      0 \<le> snd x" if "x \<in> OH" for x
  proof -
    have xO: "x \<in> prf_vars (zprf_tr sprf) \<or> x \<in> prf_vars (zprf_tr rprf)"
      "x \<notin> vars_thm stpairs (list_implies (Bs @ [Bi]) C)" "x \<notin> vars_thm rtpairs rprop"
      using that by (auto simp: OH_def)
    have ix: "0 \<le> snd x" "snd x \<le> maxidx env"
      using xO(1) zinv_prf_vars[OF sz, of x] zinv_prf_vars[OF rz, of x] mx by auto
    have nt: "\<forall>(t, u)\<in>set tus. x \<notin> vars t \<and> x \<notin> vars u" using tusV xO(2,3) by blast
    have v: "vt_lookup (tenv env) x = None" "x \<notin> fst ` bvps env"
      using te(1) by (auto simp: bvps_def vt_is_empty_lookup)
    from unifiers_fresh[OF cfg finA pi u0(1) u0(2) u0(3) v nt ix(2)] fresh[OF nt ix(2)] ix(1)
    show ?thesis by blast
  qed
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
    define RS where "RS = vars_thm stpairs (list_implies (Bs @ [Bi]) C)"
    have RSs: "snd x \<le> smax" if "x \<in> RS" for x
      using that state(1,2) by (fastforce simp: RS_def vars_thm_def ibelow_def wt_thm_def wt_term_def below_def)
    define RR where "RR = vars_thm rtpairs rprop"
    define rn where "rn = ren_of na smax"
    have RRn: "0 \<le> snd x" if "x \<in> RR" for x using that nn by (auto simp: RR_def)
    have rnidx: "snd (rn x) = snd x" for x by (simp add: rn_def ren_of_def ren_ix_def split: option.splits)
    have lr: "lifted \<Longrightarrow> lifted_rule smax Bi (rev rAs) B"
      using lifted_over_lifted_rule[OF rule(2) sp1] by simp
    have agH: "0 \<le> snd x \<and> tctx env' W3 x = tnorm (tyenv env') (W x)" if "x \<in> OH" for x
      using OHf[OF that] that by (simp add: W3_def vtyp_def)
    have rnOH: "rn x \<notin> OH" if "x \<in> RR" for x
    proof
      assume o: "rn x \<in> OH"
      show False
      proof (cases "rn x = x")
        case True
        with o that show False by (simp add: OH_def RR_def)
      next
        case False
        then have sx: "smax < snd x" by (auto simp: rn_def ren_of_def split: option.splits if_splits)
        from o have "rn x \<in> prf_vars (zprf_tr sprf) \<or> rn x \<in> prf_vars (zprf_tr rprf) - vars_thm rtpairs rprop"
          by (auto simp: OH_def)
        then show False
        proof
          assume "rn x \<in> prf_vars (zprf_tr sprf)"
          with zinv_prf_vars[OF sz] rnidx[of x] sx show False by fastforce
        next
          assume "rn x \<in> prf_vars (zprf_tr rprf) - vars_thm rtpairs rprop"
          with hid that rbr show False by (auto simp: rn_def RR_def)
        qed
      qed
    qed
    text \<open>No hidden variable occurs in the new theorem.\<close>
    have oldvars: "vars X \<subseteq> RS \<union> rn ` RR" if "X \<in> set (na_oldAs na)" for X
    proof -
      from renc consider "na_ren na = None" "na_oldAs na = As0"
        | (ren) "lifted" "na_ren na = Some (rename_bvs dps (rtpairs @ tps1) Bi As0)"
          "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0"
        by (elim disjE conjE) auto
      then show ?thesis
      proof cases
        case 1
        then have "rn x = x" for x by (simp add: rn_def ren_of_def)
        moreover have "vars X \<subseteq> RR" using that 1 rAs' by (auto simp: RR_def vars_thm_def vars_list_implies P)
        ultimately show ?thesis by auto
      next
        case ren
        let ?r = "rename_bvs dps (rtpairs @ tps1) Bi As0"
        from that ren obtain Ao where Ao: "Ao \<in> set As0" "X = strip_apply (ren_term ?r) Bi Ao" by auto
        from lr[OF ren(1)] obtain p Bi0 As1 where ls: "lsplit Bi = (p, Bi0)" and rA: "rev rAs = map (lift_pre p) As1"
          and big: "\<forall>X\<in>set As1. \<forall>x\<in>vars X. smax < snd x"
          by (auto simp: lifted_rule_def)
        from lsplit_ok[OF ls] have Bi: "Bi = lift_pre p Bi0" and ok: "\<forall>i\<in>set p. litem_ok i" and at: "atomic Bi0"
          by auto
        have Aor: "Ao \<in> set (rev rAs)" using Ao(1) rAs' by auto
        with rA obtain X0 where X0: "Ao = lift_pre p X0" "X0 \<in> set As1" by auto
        have X: "X = lift_pre p (ren_term ?r X0)" using Ao(2) X0(1) by (simp add: Bi strip_apply_lift_pre[OF ok at])
        have vAo: "vars Ao \<subseteq> RR" using Aor by (auto simp: RR_def vars_thm_def vars_list_implies P)
        have "pvars p \<subseteq> RS" by (auto simp: RS_def vars_thm_def vars_list_implies Bi vars_lift_pre)
        moreover have "vars (ren_term ?r X0) \<subseteq> rn ` RR"
        proof
          fix y assume "y \<in> vars (ren_term ?r X0)"
          then obtain x where x: "x \<in> vars X0" "y = (ren_name (fst ?r) (fst x), snd x)"
            by (auto simp: vars_ren_term)
          have "rn x = y" using x big X0(2) ren(2) by (auto simp: rn_def ren_of_def ren_ix_def)
          moreover have "x \<in> RR" using x(1) vAo X0(1) by (auto simp: vars_lift_pre)
          ultimately show "y \<in> rn ` RR" by blast
        qed
        ultimately show ?thesis by (auto simp: X vars_lift_pre)
      qed
    qed
    have nAvars: "vars X \<subseteq> RS \<union> rn ` RR" if "X \<in> set (na_As na)" for X
    proof -
      from that obtain k where k: "k < length (na_As na)" "X = na_As na ! k" by (auto simp: in_set_conv_nth)
      have k': "k < length (na_oldAs na)" using k lold by simp
      have "vars X \<subseteq> vars (na_oldAs na ! k)"
        using list_all2_nthD[OF flat k'] k(2) by (auto split: if_splits dest: vars_flatten_params)
      with oldvars[OF nth_mem[OF k']] show ?thesis by blast
    qed
    have rOH: "x \<notin> OH" if "x \<in> vars_thm (br_tpairs r) (br_prop r)" for x
    proof -
      from that at(2) have "x \<in> vars_thm tps (list_implies (Bs @ na_As na) C) \<or> x \<in> fst ` bvps env'"
        by (auto simp: sel)
      then show ?thesis
      proof
        assume "x \<in> vars_thm tps (list_implies (Bs @ na_As na) C)"
        then consider "\<exists>(t, u)\<in>set tps. x \<in> vars t \<or> x \<in> vars u" | "x \<in> RS" | X where "X \<in> set (na_As na)" "x \<in> vars X"
          by (auto simp: vars_thm_def vars_list_implies RS_def)
        then show ?thesis
        proof cases
          case 1
          then show ?thesis using OHf by fastforce
        next
          case 2
          then show ?thesis by (auto simp: OH_def RS_def)
        next
          case 3
          with nAvars have "x \<in> RS \<union> rn ` RR" by blast
          then show ?thesis using rnOH by (auto simp: OH_def RS_def)
        qed
      qed (use OHf in blast)
    qed
    have tctx3: "tctx env' W3 x = tctx env' W'' x" if "x \<notin> OH" for x
      using W3x[OF that] by (simp add: vtyp_def split: option.split)
  obtain p Nz asm fs sp'' rp'' where
    bp: "zbicompose_proof ztargs env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) [vS, vR]
      rp' sprf = returnZ p"
    and pe: "p = ZAbsps Nz (ZAppp (ZAppps sp'' (map ZBoundp (downto (integer_of_nat (length Bs) + integer_of_nat la - 1)
      (integer_of_nat la)))) (ZAppps rp'' (asm @ fs)))"
    and Nz: "list_all2 (\<lambda>X N. ok (norm_term env' X) (zdec N)) (Bs @ na_As na) Nz"
    and sp'': "sp'' = sprf \<and> (env_is_empty env' \<or> above env' smax) \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sp'')"
    and rp'': "rp'' = rp' \<and> env_is_empty env' \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr rp') (zprf_tr rp'')"
    and asm: "(A1o = None \<or> \<not> 0 < na_n na) \<and> asm = [] \<or>
      (\<exists>A1 C'. A1o = Some A1 \<and> 0 < na_n na \<and> ok (norm_term env' A1) (zdec C') \<and> zcanon C' \<and>
        asm = [zmk_asm_prf C' (na_n na) (nlift + 1)])"
    and fs: "length fs = la" "\<forall>k<la. zprf_tr (fs ! k) = fpk k \<or>
      \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (fpk k) (zprf_tr (fs ! k))"
  proof -
    define normt where "normt t = zterm_of ztargs t \<bind> znorm_term ztargs env'" for t
    define la' where "la' = integer_of_nat la"
    have tvlo: "\<forall>q\<in>tvars_env (tyenv env'). 0 \<le> snd (fst q)"
      using bicompose_aux_thm_typed(4)[OF ok res cfg finA state rule A(1) _ A(3) ns er fl vl _ lo _ _ cA] A(2) A0 nn rbr(1)
      by auto
    have zo: "tyenv_zok (tyenv env')"
      unfolding tyenv_zok_def
    proof (intro allI impI)
      fix v S U assume l: "vt_lookup (tyenv env') v = Some (S, U)"
      have "snd v \<noteq> -1" using tvlo tvars_envI[OF l] by force
      moreover have "\<forall>(w, S')\<in>tvars U. snd w \<noteq> -1" using tvlo tvars_envI2[OF l] by force
      ultimately show "snd v \<noteq> -1 \<and> (\<forall>(w, S')\<in>tvars U. snd w \<noteq> -1)" by blast
    qed
    have zt: "tenv_zok ztargs env'" by (rule tenv_zok_zenv_ok[OF ze[unfolded rbr(1)] etE])
    have tyAn: "\<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" if "tyw ar (tyenv env') A U" for U
      using that tvlo A0 by (fastforce simp: tyw_def)
    text \<open>The visible normalisation of the proofs (\<open>ZTerm.norm_proof\<close>).\<close>
    define vis where "vis = [vS, vR]"
    define tvl where "tvl = visible_tvars vis"
    define X where "X = fst ` set (visible_vars vis)"
    define \<rho>v where "\<rho>v = (\<lambda>v S. if (v, S) \<in> set tvl then tnorm (tyenv env') (TVar v S) else TVar v S)"
    define Ar where "Ar = tvars_env (tyenv env') \<union> A"
    define PU where "PU U \<longleftrightarrow> tvars U \<subseteq> Ar \<and> (\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx env')" for U
    define V' where "V' = tctx env' W3"
    define V where "V y = (if y \<in> X \<union> OH then W y else if y \<in> rn ` RR then W (the_inv_into RR rn y) else V' y)" for y
    have visv: "set (visible_vars vis) = vps_thm stpairs (list_implies (Bs @ [Bi]) C) \<union> vps_thm rtpairs rprop"
      using vps_full_prop_of[OF vS] vps_full_prop_of[OF vR] by (simp add: vis_def set_visible_vars)
    have XRR: "X = RS \<union> RR"
      using visv by (auto simp: X_def RS_def RR_def vars_thm_def vps_thm_def vars_vps image_Un image_UN)
    have thmty: "\<exists>U. has_type W [] t U" if "t \<in> insert (list_implies (Bs @ [Bi]) C) (\<Union>(t, u)\<in>set stpairs. {t, u}) \<union>
        insert rprop (\<Union>(t, u)\<in>set rtpairs. {t, u})" for t
      using that state(1) rule(1) by (fastforce simp: wt_thm_def wt_term_def)
    have visT: "T = W a" if "(a, T) \<in> set (visible_vars vis)" for a T
    proof -
      from that visv obtain t where t: "t \<in> insert (list_implies (Bs @ [Bi]) C) (\<Union>(t, u)\<in>set stpairs. {t, u}) \<union>
          insert rprop (\<Union>(t, u)\<in>set rtpairs. {t, u})" "(a, T) \<in> vps t"
        by (auto simp: vps_thm_def)
      from thmty[OF t(1)] obtain U where "has_type W [] t U" by blast
      from vps_has_type_typ[OF this t(2)] show ?thesis by simp
    qed
    have thmtys: "tyA ar A U" if "U \<in> tys t" "t \<in> insert (list_implies (Bs @ [Bi]) C) (\<Union>(t, u)\<in>set stpairs. {t, u}) \<union>
        insert rprop (\<Union>(t, u)\<in>set rtpairs. {t, u})" for t U
      using that state(1) rule(1) by (fastforce simp: wt_thm_def wt_term_def)
    have tvlA: "set tvl \<subseteq> A"
    proof
      fix q assume "q \<in> set tvl"
      then obtain t U where tU: "t \<in> set vis" "U \<in> tys t" "q \<in> tvars U" by (auto simp: tvl_def set_visible_tvars)
      have tyS: "\<forall>(t, u)\<in>set stpairs. \<exists>T. has_type W [] t T" and tyR: "\<forall>(t, u)\<in>set rtpairs. \<exists>T. has_type W [] t T"
        using state(1) rule(1) by (fastforce simp: wt_thm_def wt_term_def)+
      from tU(1) consider "t = vS" | "t = vR" by (auto simp: vis_def)
      then show "q \<in> A"
      proof cases
        case 1
        with tU have "q \<in> (\<Union>U\<in>tys vS. tvars U)" by blast
        with tys_full_prop_of[OF vS tyS] obtain U' where
          U': "U' \<in> tys (list_implies (Bs @ [Bi]) C) \<union> (\<Union>(t, u)\<in>set stpairs. tys t \<union> tys u)" "q \<in> tvars U'"
          by blast
        have "tyA ar A U'"
        proof -
          from U'(1) consider "U' \<in> tys (list_implies (Bs @ [Bi]) C)" | t u where "(t, u) \<in> set stpairs" "U' \<in> tys t \<or> U' \<in> tys u"
            by blast
          then show ?thesis
          proof cases
            case 1
            with state(1) show ?thesis by (simp add: wt_thm_def wt_term_def)
          next
            case 2
            with state(1) obtain T where "wt_term ar A W smax t T" "wt_term ar A W smax u T"
              unfolding wt_thm_def by blast
            with 2(2) show ?thesis by (auto simp: wt_term_def)
          qed
        qed
        with U'(2) show ?thesis by (auto simp: tyA_def)
      next
        case 2
        with tU have "q \<in> (\<Union>U\<in>tys vR. tvars U)" by blast
        with tys_full_prop_of[OF vR tyR] obtain U' where
          U': "U' \<in> tys rprop \<union> (\<Union>(t, u)\<in>set rtpairs. tys t \<union> tys u)" "q \<in> tvars U'"
          by blast
        have "tyA ar A U'"
        proof -
          from U'(1) consider "U' \<in> tys rprop" | t u where "(t, u) \<in> set rtpairs" "U' \<in> tys t \<or> U' \<in> tys u"
            by blast
          then show ?thesis
          proof cases
            case 1
            with rule(1) show ?thesis by (simp add: wt_thm_def wt_term_def)
          next
            case 2
            with rule(1) obtain T where "wt_term ar A W rmax t T" "wt_term ar A W rmax u T"
              unfolding wt_thm_def by blast
            with 2(2) show ?thesis by (auto simp: wt_term_def)
          qed
        qed
        with U'(2) show ?thesis by (auto simp: tyA_def)
      qed
    qed
    have tv: "\<forall>(v, S)\<in>set tvl. 0 \<le> snd v \<and> tcons (tyenv env') (TVar v S)"
      using tvlA A0 tcA by fastforce
    have vv: "\<forall>(a, T)\<in>set (visible_vars vis). T = V a \<and> 0 \<le> snd a \<and> tvars T \<subseteq> set tvl"
    proof (intro ballI, clarify)
      fix a T assume aT: "(a, T) \<in> set (visible_vars vis)"
      have a: "a \<in> X" using aT by (force simp: X_def)
      have "0 \<le> snd a"
      proof (cases "a \<in> RR")
        case True
        then show ?thesis by (rule RRn)
      next
        case False
        with a XRR have "a \<in> RS" by simp
        then show ?thesis using nn by (auto simp: RS_def)
      qed
      moreover have "tvars T \<subseteq> set tvl"
      proof -
        from aT obtain t where "t \<in> set vis" "(a, T) \<in> vps t" by (auto simp: set_visible_vars)
        then show ?thesis using vps_tys by (fastforce simp: tvl_def set_visible_tvars)
      qed
      ultimately show "T = V a \<and> 0 \<le> snd a \<and> tvars T \<subseteq> set tvl" using visT[OF aT] a by (simp add: V_def)
    qed
    have vn: "\<forall>a\<in>X. \<exists>t' rb. norm_term env' (Var a (tsubst \<rho>v (V a))) = return t' \<and>
        swf_tm ar rb (Var a (tsubst \<rho>v (V a))) \<and> has_type V' [] t' (tsubst \<rho>v (V a))"
      sorry
    have vh: "\<forall>x. x \<notin> X \<longrightarrow> V' x = tsubst \<rho>v (V x)"
      sorry
    have tiA: "\<forall>q\<in>tvars_env (tyenv env') \<union> A. snd (fst q) \<le> maxidx env'" using tiE by (simp add: tinv_def)
    have pu: "PU (tnorm (tyenv env') U)" if "PU U" "tcons (tyenv env') U" for U
    proof -
      have "tvars (tnorm (tyenv env') U) \<subseteq> Ar" using that(1) tvars_tnorm[OF acE, of U] by (auto simp: PU_def Ar_def)
      moreover have "\<forall>(v, S)\<in>tvars (tnorm (tyenv env') U). snd v \<le> maxidx env'"
      proof (intro ballI, clarify)
        fix v S assume "(v, S) \<in> tvars (tnorm (tyenv env') U)"
        with calculation have "(v, S) \<in> tvars_env (tyenv env') \<union> A" by (auto simp: Ar_def)
        from bspec[OF tiA this] show "snd v \<le> maxidx env'" by simp
      qed
      ultimately show ?thesis by (simp add: PU_def)
    qed
    have PUi: "PU U" if "tvars U \<subseteq> Ar" for U
    proof -
      have "\<forall>(v, S)\<in>tvars U. snd v \<le> maxidx env'"
      proof (intro ballI, clarify)
        fix v S assume "(v, S) \<in> tvars U"
        with that have "(v, S) \<in> tvars_env (tyenv env') \<union> A" by (auto simp: Ar_def)
        from bspec[OF tiA this] show "snd v \<le> maxidx env'" by simp
      qed
      with that show ?thesis by (simp add: PU_def)
    qed
    have pe: "\<forall>T\<in>zetys ztargs env'. PU (typ_of T)"
    proof
      fix T assume "T \<in> zetys ztargs env'"
      then obtain x U u zu where l: "vt_lookup (tenv env') x = Some (U, u)" "zterm_of ztargs u = returnZ zu" "T \<in> ztys zu"
        by (auto simp: zetys_def)
      from ze rbr(1) l(1) have z: "cts u" "\<forall>v\<in>vars u. 0 \<le> snd v" "\<forall>T\<in>tys u. \<forall>(v, S)\<in>tvars T. 0 \<le> snd v"
        unfolding zenv_ok_def by blast+
      have c: "cts u" "\<forall>v\<in>vars u. snd v \<noteq> -1" "\<forall>T\<in>tys u. \<forall>(v, S)\<in>tvars T. snd v \<noteq> -1"
        using z integer_nonneg_ne_m1 by fastforce+
      from zterm_of_zdec_cts[OF c] l(2) have tv: "tvars (typ_of T) \<subseteq> (\<Union>U\<in>tys u. tvars U)" using l(3) by auto
      have "\<forall>U\<in>tys u. tyw ar (tyenv env') A U" using pinvD(3)[OF pi'] etysI[OF l(1)] by blast
      then have "(\<Union>U\<in>tys u. tvars U) \<subseteq> Ar" by (auto simp: tyw_def Ar_def)
      with tv show "PU (typ_of T)" by (intro PUi) blast
    qed
    have pvv: "\<forall>(a, T)\<in>set (visible_vars vis). PU T"
    proof (intro ballI, clarify)
      fix a T assume "(a, T) \<in> set (visible_vars vis)"
      with visT have "T = W a" by blast
      with spec[OF A(3), of a] show "PU T" by (intro PUi) (auto simp: tyA_def Ar_def)
    qed
    have znp: "\<exists>q'. znorm_proof ztargs env' vis q = returnZ q' \<and>
        prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr q) (zprf_tr q') \<and>
        zprf_all (\<lambda>t. (\<exists>Ts U. has_type V' Ts (zdec t) U) \<and> (\<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)))
          (\<lambda>T. zcan T \<and> PU (typ_of T)) q'"
      if "\<not> env_is_empty env'" "zprf_all (zann_vis V tvl X env') (ztyp_vis tvl (tyenv env')) q"
        "zconst_free q" "zno_class q" "zrf q"
        "zprf_all (\<lambda>t. \<forall>T\<in>ztys t. zcan T \<and> PU (typ_of T)) (\<lambda>T. zcan T \<and> PU (typ_of T)) q" for q
      using znorm_proof_rel[of env' vis V V' q PU, folded tvl_def X_def] that acE tcE etE zo zt tv vv
        vn[unfolded \<rho>v_def] vh[unfolded \<rho>v_def] pu pe pvv
      by (simp add: vis_def)
    have Dr: "\<exists>rp''. (if env_is_empty env' then returnZ rp' else znorm_proof ztargs env' [vS, vR] rp') = returnZ rp'' \<and>
        (rp'' = rp' \<and> env_is_empty env' \<or>
         \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr rp') (zprf_tr rp''))"
      sorry
    then obtain rp'' where rp''1: "(if env_is_empty env' then returnZ rp' else znorm_proof ztargs env' [vS, vR] rp') = returnZ rp''"
      and rp''2: "rp'' = rp' \<and> env_is_empty env' \<or>
         \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr rp') (zprf_tr rp'')" by blast
    have Ds: "\<exists>sp''. (if above env' smax then returnZ sprf else znorm_proof ztargs env' [vS, vR] sprf) = returnZ sp'' \<and>
        (sp'' = sprf \<and> (env_is_empty env' \<or> above env' smax) \<or>
         \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sp''))"
      if "\<not> env_is_empty env'"
      sorry
    have oldok: "cts X \<and> (\<forall>v\<in>vars X. 0 \<le> snd v) \<and> (\<forall>U\<in>tys X. tyA ar A U)" if "X \<in> set (na_oldAs na)" for X
    proof -
      have vX: "\<forall>v\<in>vars X. 0 \<le> snd v" using oldvars[OF that] nn RRn rnidx by (fastforce simp: RS_def)
      have rA: "cts Y \<and> (\<forall>U\<in>tys Y. tyA ar A U)" if "Y \<in> set (rev rAs)" for Y
        using wR(1) that by (auto simp: wt_term_def intro: has_type_cts)
      have cBi: "cts Bi" "\<forall>U\<in>tys Bi. tyA ar A U" using wS(2) by (auto simp: wt_term_def intro: has_type_cts)
      from renc consider "na_oldAs na = As0"
        | (ren) "na_oldAs na = map (strip_apply (ren_term (rename_bvs dps (rtpairs @ tps1) Bi As0)) Bi) As0"
        by (elim disjE conjE) auto
      then show ?thesis
      proof cases
        case 1
        with that rAs' rA vX show ?thesis by auto
      next
        case ren
        let ?r = "rename_bvs dps (rtpairs @ tps1) Bi As0"
        from that ren obtain Ao where Ao: "Ao \<in> set As0" "X = strip_apply (ren_term ?r) Bi Ao" by auto
        have Ao': "cts Ao \<and> (\<forall>U\<in>tys Ao. tyA ar A U)" using Ao(1) rAs' rA by auto
        have "cts X" unfolding Ao(2) by (rule cts_strip_apply) (use cBi Ao' in auto)
        moreover have "\<forall>U\<in>tys X. tyA ar A U" unfolding Ao(2) by (rule tys_strip_apply) (use cBi Ao' in auto)
        ultimately show ?thesis using vX by blast
      qed
    qed
    have DO: "\<exists>Os. mapZ (zterm_of ztargs) (na_oldAs na) = returnZ Os \<and> map zdec Os = na_oldAs na \<and> (\<forall>Oz\<in>set Os. zcanon Oz)"
    proof -
      have "\<forall>X\<in>set (na_oldAs na). \<exists>Oz. zterm_of ztargs X = returnZ Oz \<and> (zdec Oz = X \<and> zcanon Oz)"
      proof
        fix X assume X: "X \<in> set (na_oldAs na)"
        from oldok[OF X] have c: "cts X" "\<forall>v\<in>vars X. snd v \<noteq> -1" "\<forall>U\<in>tys X. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1"
          using A0 by (fastforce simp: tyA_def)+
        from zterm_of_zdec_cts[OF c] obtain Oz where "zterm_of ztargs X = returnZ Oz" "zdec Oz = X" by blast
        then show "\<exists>Oz. zterm_of ztargs X = returnZ Oz \<and> (zdec Oz = X \<and> zcanon Oz)"
          by (blast intro: zterm_of_zcanon)
      qed
      from mapZ_rel[OF this] obtain Os where "mapZ (zterm_of ztargs) (na_oldAs na) = returnZ Os"
        "list_all2 (\<lambda>X Oz. zdec Oz = X \<and> zcanon Oz) (na_oldAs na) Os" by blast
      moreover from this(2) have "map zdec Os = na_oldAs na" "\<forall>Oz\<in>set Os. zcanon Oz"
        by (induction rule: list_all2_induct) auto
      ultimately show ?thesis by blast
    qed
    have DN: "\<exists>Nz. mapZ normt (Bs @ na_As na) = returnZ Nz \<and> list_all2 (\<lambda>X N. ok (norm_term env' X) (zdec N)) (Bs @ na_As na) Nz"
    proof -
      have "\<forall>X\<in>set (Bs @ na_As na). \<exists>N. normt X = returnZ N \<and> ok (norm_term env' X) (zdec N)"
      proof
        fix X assume X: "X \<in> set (Bs @ na_As na)"
        have wt: "\<exists>Wx. wtprop A Wx env' X \<and> pinv alg ar A Wx env' []"
          using X BC As pi' pi'' by auto
        then obtain Wx where wx: "wtprop A Wx env' X" "pinv alg ar A Wx env' []" by blast
        from wtprop_norm_ok[OF wx(2) wx(1)] obtain X' where n: "ok (norm_term env' X) X'" by blast
        have tw: "\<forall>U\<in>tys X. tyw ar (tyenv env') A U" using wx(1) by (simp add: wtprop_def)
        have cX: "cts X"
        proof (cases "X \<in> set Bs")
          case True
          with wS(1) show ?thesis by (auto simp: wt_term_def intro: has_type_cts)
        next
          case False
          with X have "X \<in> set (na_As na)" by simp
          then obtain k where k: "k < length (na_As na)" "X = na_As na ! k" by (auto simp: in_set_conv_nth)
          have k': "k < length (na_oldAs na)" using k lold by simp
          have "cts (na_oldAs na ! k)" using oldok[OF nth_mem[OF k']] by blast
          with list_all2_nthD[OF flat k'] k(2) show ?thesis by (auto split: if_splits intro: cts_flatten_params)
        qed
        have vX0: "\<forall>v\<in>vars X. 0 \<le> snd v"
        proof
          fix v assume v: "v \<in> vars X"
          show "0 \<le> snd v"
          proof (cases "X \<in> set Bs")
            case True
            with v have "v \<in> RS" by (auto simp: RS_def vars_thm_def vars_list_implies)
            then show ?thesis using nn by (auto simp: RS_def)
          next
            case False
            with X have "X \<in> set (na_As na)" by simp
            from nAvars[OF this] v have "v \<in> RS \<union> rn ` RR" by blast
            then show ?thesis using nn RRn rnidx by (auto simp: RS_def)
          qed
        qed
        have vX: "\<forall>v\<in>vars X. snd v \<noteq> -1" using vX0 integer_nonneg_ne_m1 by blast
        have tX: "\<forall>U\<in>tys X. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" using tw tyAn by blast
        have tcX: "\<forall>U\<in>tys X. tcons (tyenv env') U" using tw tyw_tcons[OF tiE] by blast
        from normt_ok[OF n cX vX tX tcX acE tcE etE zo zt] show "\<exists>N. normt X = returnZ N \<and> ok (norm_term env' X) (zdec N)"
          using n by (auto simp: normt_def)
      qed
      from mapZ_rel[OF this] show ?thesis .
    qed
    then obtain Nz where Nz1: "mapZ normt (Bs @ na_As na) = returnZ Nz"
      and Nz2: "list_all2 (\<lambda>X N. ok (norm_term env' X) (zdec N)) (Bs @ na_As na) Nz" by blast
    have Da: "\<exists>asm. (if 0 < na_n na then (case A1o of None \<Rightarrow> raiseZ ZOption
          | Some C \<Rightarrow> normt C \<bind> (\<lambda>C'. returnZ [zmk_asm_prf C' (na_n na) (nlift + 1)])) else returnZ []) = returnZ asm \<and>
        ((A1o = None \<or> \<not> 0 < na_n na) \<and> asm = [] \<or>
         (\<exists>A1 C'. A1o = Some A1 \<and> 0 < na_n na \<and> ok (norm_term env' A1) (zdec C') \<and> zcanon C' \<and>
           asm = [zmk_asm_prf C' (na_n na) (nlift + 1)]))"
    proof (cases "0 < na_n na")
      case False
      then show ?thesis by simp
    next
      case True
      with A1oN obtain A1 where A1: "A1o = Some A1" by (cases A1o) auto
      have A1r: "A1 \<in> set (rev rAs)" using A1 A1o rAs' by (cases Pre) auto
      have rsA: "typed env' W' [] A1 propT \<and> below (maxidx env') A1 \<and> (\<forall>U\<in>tys A1. tyw ar (tyenv env') A U)"
      proof -
        have mem: "(A1, propT) \<in> set (xsS @ xsR)" using A1r by (simp add: xsR_def)
        from bspec[OF rsx[unfolded rs_typed_def] mem] show ?thesis by simp
      qed
      have cA1: "cok A1" using rule(1) A1r by (auto simp: wt_thm_def P)
      have wtA: "wt_term ar A W rmax A1 propT" using wR(1) A1r by blast
      have wf: "wfp ar A1" using wtA cA1 by (auto simp: wfp_def wt_term_def swf_tm_def)
      have wtp: "wtprop A W' env' A1" using rsA wf by (simp add: wtprop_def)
      from wtprop_norm_ok[OF pi' wtp] obtain A1' where n: "ok (norm_term env' A1) A1'" by blast
      have cX: "cts A1" using wtA by (auto simp: wt_term_def intro: has_type_cts)
      have vX: "\<forall>v\<in>vars A1. snd v \<noteq> -1"
      proof
        fix v assume "v \<in> vars A1"
        with A1r have "v \<in> RR" by (auto simp: RR_def vars_thm_def vars_list_implies P)
        with RRn show "snd v \<noteq> -1" using integer_nonneg_ne_m1 by blast
      qed
      have tX: "\<forall>U\<in>tys A1. \<forall>(v, S)\<in>tvars U. snd v \<noteq> -1" using rsA tyAn by blast
      have tcX: "\<forall>U\<in>tys A1. tcons (tyenv env') U" using rsA tyw_tcons[OF tiE] by blast
      from normt_ok[OF n cX vX tX tcX acE tcE etE zo zt] obtain C' where
        C': "(zterm_of ztargs A1 \<bind> znorm_term ztargs env') = returnZ C'" "zdec C' = A1'" by blast
      from C'(1) obtain z where z: "zterm_of ztargs A1 = returnZ z" "znorm_term ztargs env' z = returnZ C'"
        by (auto simp: bindZ_eq_returnZ)
      have "zcanon C'" by (rule zcanon_znorm_term[OF z(2) zterm_of_zcanon[OF z(1) HOL.refl]])
      with True A1 n C' show ?thesis by (auto simp: normt_def)
    qed
    then obtain asm where asm1: "(if 0 < na_n na then (case A1o of None \<Rightarrow> raiseZ ZOption
          | Some C \<Rightarrow> normt C \<bind> (\<lambda>C'. returnZ [zmk_asm_prf C' (na_n na) (nlift + 1)])) else returnZ []) = returnZ asm"
      and asm2: "(A1o = None \<or> \<not> 0 < na_n na) \<and> asm = [] \<or>
         (\<exists>A1 C'. A1o = Some A1 \<and> 0 < na_n na \<and> ok (norm_term env' A1) (zdec C') \<and> zcanon C' \<and>
           asm = [zmk_asm_prf C' (na_n na) (nlift + 1)])" by blast
    from DO obtain Os where Os1: "mapZ (zterm_of ztargs) (na_oldAs na) = returnZ Os"
      and Os2: "map zdec Os = na_oldAs na" and Os3: "\<forall>Oz\<in>set Os. zcanon Oz" by blast
    have Df: "\<exists>fs. (if flatten then mapZ (\<lambda>x. znorm_proof ztargs env' [vS, vR] (zflatten_params_proof 0 0 (na_n na) x))
          (zip Os (downto (la' - 1) 0)) else returnZ (map (\<lambda>x. ZBoundp (snd x)) (zip Os (downto (la' - 1) 0)))) = returnZ fs \<and>
        length fs = la \<and> (\<forall>k<la. zprf_tr (fs ! k) = fpk k \<or>
          \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (fpk k) (zprf_tr (fs ! k)))"
      sorry
    then obtain fs where fs1: "(if flatten then mapZ (\<lambda>x. znorm_proof ztargs env' [vS, vR] (zflatten_params_proof 0 0 (na_n na) x))
          (zip Os (downto (la' - 1) 0)) else returnZ (map (\<lambda>x. ZBoundp (snd x)) (zip Os (downto (la' - 1) 0)))) = returnZ fs"
      and fs2: "length fs = la" "\<forall>k<la. zprf_tr (fs ! k) = fpk k \<or>
          \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (fpk k) (zprf_tr (fs ! k))" by blast
    have core: "zbicompose_core ztargs env' flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) [vS, vR] q s =
        returnZ (ZAbsps Nz (ZAppp (ZAppps s (map ZBoundp (downto (integer_of_nat (length Bs) + la' - 1) la')))
          (ZAppps q (asm @ fs))))" for q s
      using zbicompose_core_eq[OF Nz1[unfolded normt_def] asm1[unfolded normt_def] Os1 lold fs1[unfolded la'_def la_def],
          of q s]
      by (simp add: la'_def la_def)
    show thesis
    proof (cases "env_is_empty env'")
      case True
      with rp''1 rp''2 have "rp'' = rp'" by simp
      show thesis
      proof (rule that[OF _ _ Nz2 _ rp''2 asm2 fs2])
        show "zbicompose_proof ztargs env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) [vS, vR]
            rp' sprf = returnZ (ZAbsps Nz (ZAppp (ZAppps sprf (map ZBoundp (downto (integer_of_nat (length Bs) +
              integer_of_nat la - 1) (integer_of_nat la)))) (ZAppps rp'' (asm @ fs))))"
          using True core \<open>rp'' = rp'\<close> by (simp add: zbicompose_proof_def la'_def)
        show "sprf = sprf \<and> (env_is_empty env' \<or> above env' smax) \<or>
            \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sprf)"
          using True by simp
      qed simp
    next
      case False
      from Ds[OF False] obtain sp'' where sp''1: "(if above env' smax then returnZ sprf else znorm_proof ztargs env' [vS, vR] sprf) =
          returnZ sp''"
        and sp''2: "sp'' = sprf \<and> (env_is_empty env' \<or> above env' smax) \<or>
         \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sp'')" by blast
      show thesis
      proof (rule that[OF _ _ Nz2 sp''2 rp''2 asm2 fs2])
        show "zbicompose_proof ztargs env' smax flatten Bs (na_As na) A1o (na_oldAs na) (na_n na) (nlift + 1) [vS, vR]
            rp' sprf = returnZ (ZAbsps Nz (ZAppp (ZAppps sp'' (map ZBoundp (downto (integer_of_nat (length Bs) +
              integer_of_nat la - 1) (integer_of_nat la)))) (ZAppps rp'' (asm @ fs))))"
          using False rp''1 sp''1 core by (simp add: zbicompose_proof_def la'_def)
      qed simp
    qed
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
    have agS: "0 \<le> snd (id x) \<and> tctx env' W3 (id x) = tnorm (tyenv env') (W x)" if "x \<in> RS" "0 \<le> snd x" for x
    proof -
      have "x \<notin> OH" using that(1) by (simp add: OH_def RS_def)
      then have "W3 x = W' x" using W''d RSs[OF that(1)] W3x by fastforce
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
    text \<open>The instance of the rule, through the renaming of its new premises.\<close>
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
      have "tctx env' W'' (rn x) = tctx env' W' x"
      proof (cases "\<exists>X\<in>set As0. x \<in> vars X")
        case True
        with rnt show ?thesis by (auto simp: rn_def)
      next
        case False
        with that(1) have "x \<in> vars B \<or> (\<exists>X\<in>set Pre. x \<in> vars X) \<or> (\<exists>(t, u)\<in>set rtpairs. x \<in> vars t \<or> x \<in> vars u)"
          using rAs' by (auto simp: RR_def vars_thm_def vars_list_implies P)
        from keep[OF this] show ?thesis by (simp add: vtyp_def split: option.splits)
      qed
      moreover have "vtyp env' W3 (rn x) = vtyp env' W'' (rn x)"
        using W3x[OF rnOH[OF that(1)]] by (simp add: vtyp_def split: option.split)
      ultimately show ?thesis using agW'[OF that(1)] rnidx that(2) by simp
    qed
    define PR where "PR = prf_vars (zprf_tr rprf)"
    have agR': "0 \<le> snd (rn x) \<and> tctx env' W3 (rn x) = tnorm (tyenv env') (W x)" if "x \<in> RR \<union> PR" "0 \<le> snd x" for x
    proof (cases "x \<in> RR")
      case True
      then show ?thesis using agR that(2) by blast
    next
      case False
      with that(1) have xP: "x \<in> PR" by blast
      show ?thesis
      proof (cases "x \<in> RS")
        case True
        have "snd x \<le> smax" using RSs[OF True] .
        then have "rn x = x" by (simp add: rn_def ren_of_def split: option.splits)
        with agS[OF True that(2)] show ?thesis by simp
      next
        case nS: False
        have xO: "x \<in> OH" using xP False nS by (simp add: OH_def PR_def RS_def RR_def)
        have "rn x = x" using hid xO False xP rbr by (auto simp: rn_def PR_def RR_def)
        with agH[OF xO] show ?thesis by simp
      qed
    qed
    define \<theta>R where "\<theta>R = (\<lambda>x. if x \<in> RR \<union> PR then \<theta>' (rn x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyR: "inst_typed W V' [] \<rho>' \<theta>R"
      unfolding \<theta>R_def by (rule inst_typed_transfer[OF ty' pi3 gs' agR']) (simp_all add: tcW)
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
    have Rok0: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>R 0 (zprf_tr rprf)) (psubst \<rho>' \<theta>R 0 rprop)"
      by (rule prf_validD[OF rv g' tyR solR])
    have Rok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 (zprf_tr rp')) (psubst \<rho>' \<theta>R 0 rprop)"
    proof -
      have "prf_inst \<rho>' \<theta>' 0 (zprf_tr rp') = prf_inst \<rho>' (\<theta>' \<circ> ren_of na smax) 0 (zprf_tr rprf)" by (rule rp'i)
      also have "\<dots> = prf_inst \<rho>' \<theta>R 0 (zprf_tr rprf)"
        by (rule prf_inst_cong) (simp add: \<theta>R_def PR_def rn_def)
      finally show ?thesis using Rok0 by simp
    qed
    text \<open>The instance of the proof state, at its variables and the variables of its proof.\<close>
    define PS where "PS = prf_vars (zprf_tr sprf)"
    have agS': "0 \<le> snd (id x) \<and> tctx env' W3 (id x) = tnorm (tyenv env') (W x)" if "x \<in> RS \<union> PS" "0 \<le> snd x" for x
    proof (cases "x \<in> RS")
      case True
      then show ?thesis using agS that(2) by blast
    next
      case nS: False
      with that(1) have xP: "x \<in> PS" by blast
      have sx: "snd x \<le> smax" using zinv_prf_vars[OF sz] xP by (simp add: PS_def)
      show ?thesis
      proof (cases "x \<in> RR")
        case True
        have "rn x = x" using sx by (simp add: rn_def ren_of_def split: option.splits)
        with agR[OF True that(2)] show ?thesis by simp
      next
        case False
        have "x \<in> OH" using xP nS False by (simp add: OH_def PS_def RS_def RR_def)
        from agH[OF this] show ?thesis by simp
      qed
    qed
    define \<theta>S where "\<theta>S = (\<lambda>x. if x \<in> RS \<union> PS then \<theta>' (id x) else Free STR ''u'' (tsubst \<rho>' (W x)))"
    have tyS: "inst_typed W V' [] \<rho>' \<theta>S"
      unfolding \<theta>S_def by (rule inst_typed_transfer[OF ty' pi3 gs' agS']) (simp_all add: tcW)
    have psS: "psubst \<rho>' \<theta>S l X = psubst \<rho>' \<theta>' l X" if "vars X \<subseteq> RS" for l X
      by (rule psubst_cong) (use that in \<open>auto simp: \<theta>S_def\<close>)
    have solS: "tr (psubst \<rho>' \<theta>S 0 t) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>S 0 u)" if "(t, u) \<in> set stpairs" for t u
    proof -
      have "vars t \<subseteq> RS" "vars u \<subseteq> RS" using that by (auto simp: RS_def vars_thm_def)
      moreover have "(t, u) \<in> set tus" using that tus by auto
      ultimately show ?thesis using dsol' by (simp add: psS)
    qed
    have Sok: "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>' 0 (zprf_tr sprf))
        (list_implies (map (psubst \<rho>' \<theta>' 0) Bs @ [psubst \<rho>' \<theta>' 0 Bi]) (psubst \<rho>' \<theta>' 0 C))"
    proof -
      have "prf_ok V' H [] [] (prf_inst \<rho>' \<theta>S 0 (zprf_tr sprf)) (psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C))"
        by (rule prf_validD[OF sv g' tyS solS])
      moreover have "prf_inst \<rho>' \<theta>S 0 (zprf_tr sprf) = prf_inst \<rho>' \<theta>' 0 (zprf_tr sprf)"
        by (rule prf_inst_cong) (simp add: \<theta>S_def PS_def)
      moreover have "psubst \<rho>' \<theta>S 0 (list_implies (Bs @ [Bi]) C) = psubst \<rho>' \<theta>' 0 (list_implies (Bs @ [Bi]) C)"
        by (rule psS) (auto simp: RS_def vars_thm_def)
      ultimately show ?thesis by (simp add: psubst_list_implies')
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
    have wtP: "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' W'') (maxidx env') (br_prop r) propT"
      using wtr by (simp add: wt_thm_def)
    have "wty (tctx env' W'') [] (br_prop r) propT" by (rule wtyr[OF wtP]) (simp add: vars_thm_def)
    then have "wty (tctx env' W3) [] (br_prop r) propT"
      using rOH tctx3 by (auto simp: wty_def vars_thm_def intro: has_type_vars_cong)
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
          then have tp0: "typed env' W'' [] ?A' propT" and tw: "\<forall>U\<in>tys ?A'. tyw ar (tyenv env') A U"
            by (auto simp: wtprop_def)
          have nO: "x \<notin> OH" if "x \<in> vars ?A'" for x
          proof -
            from nAvars[OF nth_mem[OF kA(1)]] that have "x \<in> RS \<union> rn ` RR" by blast
            then show ?thesis using rnOH by (auto simp: OH_def RS_def)
          qed
          have tp': "typed env' W3 [] ?A' propT"
            using tp0 unfolding typed_def by (rule has_type_vars_cong) (simp add: tctx3 nO)
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
    text \<open>The composed tight proof, at the instance \<open>(\<rho>, \<theta>0)\<close>.\<close>
    have zp: "zprf_tr p = mk_AbsPs (map zdec Nz) (PAppp (proof_combP (zprf_tr sp'')
        (map PBound (downto (integer_of_nat (length Bs) + integer_of_nat la - 1) (integer_of_nat la))))
        (proof_combP (zprf_tr rp'') (map zprf_tr (asm @ fs))))"
      by (simp add: pe ZAbsps_tr ZAppps_tr comp_def)
    have zb: "zbridge env' \<rho> \<theta>0 \<rho>' \<sigma>' \<theta>'"
      unfolding zbridge_def
    proof (intro conjI allI impI)
      show "\<forall>y\<in>vars (\<theta>0 x). 0 \<le> snd y" for x using ty0x[of x] by (simp add: wty_def)
    qed (use ie swf smeq cl0x cl'x tyc in auto)
    have tcz: "prf_all (\<lambda>t. True) (tcons (tyenv env')) (zprf_tr q)" if "zinv A W m q" for q m
      by (rule zprf_all_tr[of "zann A W m" "zty A m"]) (use that tcA in \<open>auto simp: zinv_def zty_def tyA_def\<close>)
    have instq: "prf_aeq (prf_inst \<rho>' \<theta>' 0 (zprf_tr q)) (prf_inst \<rho> \<theta>0 0 (zprf_tr q'))"
      if "q' = q \<and> env_is_empty env' \<or>
        \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr q) (zprf_tr q')"
        "prf_all (\<lambda>t. True) (tcons (tyenv env')) (zprf_tr q)" for q q'
      using that(1)
    proof
      assume e: "q' = q \<and> env_is_empty env'"
      have "\<rho>' = \<rho>" using agT e by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
      moreover have "\<theta>' = \<theta>0" using unb\<theta> e by (intro ext) (auto simp: env_is_empty_def vt_is_empty_lookup)
      ultimately show ?thesis using e by (simp add: prf_aeq.refl)
    next
      assume "\<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr q) (zprf_tr q')"
      then show ?thesis by (intro prf_rel_zrel_inst[OF _ that(2) zb]) auto
    qed
    have Sz: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 (zprf_tr sp''))
        (list_implies (map (psubst \<rho>' \<theta>' 0) Bs @ [psubst \<rho>' \<theta>' 0 Bi]) (psubst \<rho>' \<theta>' 0 C))"
    proof -
      have "prf_aeq (prf_inst \<rho>' \<theta>' 0 (zprf_tr sprf)) (prf_inst \<rho> \<theta>0 0 (zprf_tr sp''))"
      proof (cases "sp'' = sprf \<and> above env' smax \<and> \<not> env_is_empty env'")
        case True
        have unbT: "vt_lookup (tyenv env') v = None" if "snd v \<le> smax" for v
          using True that unfolding above_def by (blast intro: vt_above_lookup)
        have unbV: "vt_lookup (tenv env') v = None" if "snd v \<le> smax" for v
          using True that unfolding above_def by (blast intro: vt_above_lookup)
        have tcong: "tsubst \<rho>' U = tsubst \<rho> U" if "\<forall>(v, S)\<in>tvars U. snd v \<le> smax" for U
          by (rule tsubst_cong) (use that unbT agT in fastforce)
        have "prf_inst \<rho>' \<theta>' 0 (zprf_tr sprf) = prf_inst \<rho> \<theta>0 0 (zprf_tr sprf)"
        proof (rule prf_inst_tcong_vars)
          show "\<forall>x\<in>prf_vars (zprf_tr sprf). \<theta>' x = \<theta>0 x" using zinv_prf_vars[OF sz] unbV unb\<theta> by auto
          show "prf_all (\<lambda>t. \<forall>U\<in>tys t. tsubst \<rho>' U = tsubst \<rho> U) (\<lambda>U. tsubst \<rho>' U = tsubst \<rho> U) (zprf_tr sprf)"
          proof (rule zprf_all_tr[of "zann A W smax" "zty A smax"])
            show "zprf_all (zann A W smax) (zty A smax) sprf" using sz by (simp add: zinv_def)
            show "\<forall>U\<in>tys (zdec t). tsubst \<rho>' U = tsubst \<rho> U" if "zann A W smax t" for t
            proof
              fix U assume "U \<in> tys (zdec t)"
              from tvars_tys_zdec[OF this] that have "\<forall>(v, S)\<in>tvars U. snd v \<le> smax"
                by (fastforce simp: zann_def zty_def)
              then show "tsubst \<rho>' U = tsubst \<rho> U" by (rule tcong)
            qed
            show "tsubst \<rho>' (typ_of T) = tsubst \<rho> (typ_of T)" if "zty A smax T" for T
              using that by (intro tcong) (auto simp: zty_def)
          qed
        qed
        with True show ?thesis by (simp add: prf_aeq.refl)
      next
        case False
        with sp'' have "sp'' = sprf \<and> env_is_empty env' \<or>
            \<not> env_is_empty env' \<and> prf_rel (ann_zrel env') (tnorm (tyenv env')) (zprf_tr sprf) (zprf_tr sp'')"
          by blast
        from instq[OF this tcz[OF sz]] show ?thesis .
      qed
      from prf_ok_aeq[OF Sok this] show ?thesis .
    qed
    have Rz: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 (zprf_tr rp''))
        (list_implies (map (psubst \<rho>' \<theta>R 0) Pre @ map (psubst \<rho>' \<theta>R 0) As0) (psubst \<rho>' \<theta>R 0 B))"
    proof -
      have rz': "prf_all (\<lambda>t. True) (tcons (tyenv env')) (zprf_tr rp')"
      proof (cases "na_ren na")
        case None
        with rp' have "rp' = rprf" by simp
        with tcz[OF rz] show ?thesis by simp
      next
        case (Some rr)
        with rp' have e: "map_zproof id (\<lambda>t. returnZ (zren_term rr smax t)) rprf = returnZ rp'"
          by (simp add: zren_proof_def)
        have "zprf_all (\<lambda>t. \<forall>T\<in>ztys t. zty A rmax T) (zty A rmax) rp'"
          by (rule zprf_all_zren[OF e rzc, of "zann A W rmax"]) (use rz in \<open>auto simp: zinv_def zann_def\<close>)
        then show ?thesis by (rule zprf_all_tr) (use tcA in \<open>auto simp: zty_def tyA_def\<close>)
      qed
      have "prf_aeq (prf_inst \<rho>' \<theta>' 0 (zprf_tr rp')) (prf_inst \<rho> \<theta>0 0 (zprf_tr rp''))"
        by (rule instq[OF rp'' rz'])
      from prf_ok_aeq[OF Rok this] show ?thesis by (simp add: P rAs' psubst_list_implies')
    qed
    define Nz' where "Nz' = map (psubst \<rho> \<theta>0 0 \<circ> zdec) Nz"
    have lNz: "length Nz' = length Bs + length (na_As na)" using list_all2_lengthD[OF Nz] by (simp add: Nz'_def)
    have wNz: "\<forall>N\<in>set Nz'. wty V' [] N propT"
    proof
      fix N assume "N \<in> set Nz'"
      then obtain j where j: "j < length Nz" "N = psubst \<rho> \<theta>0 0 (zdec (Nz ! j))"
        by (auto simp: Nz'_def in_set_conv_nth)
      have j': "j < length (Bs @ na_As na)" using j(1) list_all2_lengthD[OF Nz] by simp
      let ?X = "(Bs @ na_As na) ! j"
      have n: "ok (norm_term env' ?X) (zdec (Nz ! j))" using list_all2_nthD[OF Nz j'] .
      have nO: "y \<notin> OH" if "y \<in> vars ?X" for y
      proof (cases "j < length Bs")
        case True
        with that have "y \<in> RS" by (auto simp: RS_def vars_thm_def vars_list_implies nth_append)
        then show ?thesis by (simp add: OH_def RS_def)
      next
        case False
        with that j' have y: "y \<in> vars (na_As na ! (j - length Bs))" by (simp add: nth_append)
        have jj: "j - length Bs < length (na_As na)" using j' False by simp
        from y nAvars[OF nth_mem[OF jj]] have "y \<in> RS \<union> rn ` RR" by blast
        then show ?thesis using rnOH by (auto simp: OH_def RS_def)
      qed
      obtain Wx where wx: "wtprop A Wx env' ?X" "pinv alg ar A Wx env' []"
        "\<And>y. y \<in> vars ?X \<union> fst ` bvps env' \<Longrightarrow> tctx env' Wx y = tctx env' W3 y"
      proof (cases "j < length Bs")
        case True
        have "wtprop A W' env' ?X" using BC True by (simp add: nth_append)
        moreover have "tctx env' W' y = tctx env' W3 y" if "y \<in> vars ?X \<union> fst ` bvps env'" for y
        proof -
          have "y \<notin> OH" using that nO OHf by blast
          moreover have "W'' y = W' y"
          proof (rule ccontr)
            assume "W'' y \<noteq> W' y"
            with spec[OF W''d, of y] spec[OF ag, of y] have s: "smax < snd y" "y \<notin> fst ` bvps env'"
              by (auto simp: sel)
            with that have "y \<in> vars ?X" by blast
            with True have "y \<in> RS" by (auto simp: RS_def vars_thm_def vars_list_implies nth_append)
            with RSs s show False by fastforce
          qed
          ultimately show ?thesis using tctx3[of y] by (simp add: vtyp_def split: option.split)
        qed
        ultimately show thesis using pi' by (intro that[of W']) auto
      next
        case False
        have "wtprop A W'' env' ?X" using As False j' by (simp add: nth_append)
        moreover have "tctx env' W'' y = tctx env' W3 y" if "y \<in> vars ?X \<union> fst ` bvps env'" for y
        proof -
          have "y \<notin> OH" using that nO OHf by blast
          from tctx3[OF this] show ?thesis by simp
        qed
        ultimately show thesis using pi'' by (intro that[of W'']) auto
      qed
      have sw: "swf_tm ar [] ?X" using wx(1) by (simp add: wtprop_def wfp_def swf_tm_def)
      have "wt_term ar (tvars_env (tyenv env') \<union> A) (tctx env' Wx) (maxidx env') (zdec (Nz ! j))
          (tnorm (tyenv env') propT)"
        by (rule norm_term_wt_term[OF wx(2) _ _ _ sw n]) (use wx(1) in \<open>simp_all add: wtprop_def\<close>)
      then have h: "has_type (tctx env' Wx) [] (zdec (Nz ! j)) propT"
        by (simp add: wt_term_def propT_def)
      have vN: "vars (zdec (Nz ! j)) \<subseteq> vars ?X \<union> fst ` bvps env'" by (rule norm_term_vars[OF n])
      have h3: "has_type (tctx env' W3) [] (zdec (Nz ! j)) propT"
      proof (rule has_type_vars_cong[OF h])
        fix x assume "x \<in> vars (zdec (Nz ! j))"
        with vN have "x \<in> vars ?X \<union> fst ` bvps env'" by blast
        from wx(3)[OF this] show "tctx env' W3 x = tctx env' Wx x" by simp
      qed
      have nnX: "\<forall>y\<in>vars ?X \<union> fst ` bvps env'. 0 \<le> snd y"
      proof
        fix y assume y: "y \<in> vars ?X \<union> fst ` bvps env'"
        show "0 \<le> snd y"
        proof (cases "y \<in> vars ?X")
          case True
          show ?thesis
          proof (cases "j < length Bs")
            case jB: True
            with True have "y \<in> RS" by (auto simp: RS_def vars_thm_def vars_list_implies nth_append)
            then show ?thesis using nn by (auto simp: RS_def)
          next
            case False
            with True j' have y: "y \<in> vars (na_As na ! (j - length Bs))" by (simp add: nth_append)
            have jj: "j - length Bs < length (na_As na)" using j' False by simp
            from y nAvars[OF nth_mem[OF jj]] have "y \<in> RS \<union> rn ` RR" by blast
            then show ?thesis using nn RRn rnidx by (auto simp: RS_def)
          qed
        next
          case False
          with y have "y \<in> fst ` bvps env'" by blast
          then obtain x U u T where l: "vt_lookup (tenv env') x = Some (U, u)" "(y, T) \<in> vps u"
            by (auto simp: bvps_def)
          have yu: "y \<in> vars u" using l(2) by (force simp: vars_vps)
          from ze rbr(1) l(1) have "\<forall>v\<in>vars u. 0 \<le> snd v" unfolding zenv_ok_def by blast
          with yu show ?thesis by blast
        qed
      qed
      have "wty (tctx env' W3) [] (zdec (Nz ! j)) propT" using h3 vN nnX by (auto simp: wty_def)
      from wty_psubst[OF this tyr0] j(2) show "wty V' [] N propT" by simp
    qed
    have relNz: "tr (Nz' ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho>' \<theta>' 0 ((Bs @ na_As na) ! j))" if "j < length Nz'" for j
    proof -
      have j': "j < length (Bs @ na_As na)" using that lNz by simp
      have n: "ok (norm_term env' ((Bs @ na_As na) ! j)) (zdec (Nz ! j))" using list_all2_nthD[OF Nz j'] .
      have w: "wfp ar ((Bs @ na_As na) ! j)" using wS'(1) wN j' by (auto simp: nth_append)
      have "inst_rel \<rho> (isubst \<theta>0) \<rho>' \<sigma>' ((Bs @ na_As na) ! j) (zdec (Nz ! j))"
        by (rule inst_rel_norm[OF ie rg clI swf w n])
      then have "sm \<rho> (isubst \<theta>0) (zdec (Nz ! j)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> sm \<rho>' \<sigma>' ((Bs @ na_As na) ! j)" by simp
      from rel_tr[OF this] that show ?thesis by (simp add: Nz'_def)
    qed
    have args: "list_all2 (\<lambda>a P. prf_ok V' H [] (rev Nz') a P) (map (prf_inst \<rho> \<theta>0 0 \<circ> zprf_tr) (asm @ fs))
        (map (psubst \<rho>' \<theta>R 0) Pre @ map (psubst \<rho>' \<theta>R 0) As0)"
      sorry
    have okp: "prf_ok V' H [] [] (prf_inst \<rho> \<theta>0 0 (zprf_tr p)) (list_implies Nz' (psubst \<rho>' \<theta>' 0 C))"
    proof -
      have "prf_ok V' H [] [] (mk_AbsPs Nz' (PAppp
          (proof_combP (prf_inst \<rho> \<theta>0 0 (zprf_tr sp'')) (map PBound (downto (integer_of_nat (length (map (psubst \<rho>' \<theta>' 0) Bs)) +
            integer_of_nat (length (na_As na)) - 1) (integer_of_nat (length (na_As na))))))
          (proof_combP (prf_inst \<rho> \<theta>0 0 (zprf_tr rp'')) (map (prf_inst \<rho> \<theta>0 0 \<circ> zprf_tr) (asm @ fs)))))
          (list_implies Nz' (psubst \<rho>' \<theta>' 0 C))"
      proof (rule prf_ok_compose_a[OF Sz Rz BBi_eq _ wNz _ args])
        show "length Nz' = length (map (psubst \<rho>' \<theta>' 0) Bs) + length (na_As na)" using lNz by simp
        show "\<forall>j<length (map (psubst \<rho>' \<theta>' 0) Bs). tr (Nz' ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)"
        proof (intro allI impI)
          fix j assume j: "j < length (map (psubst \<rho>' \<theta>' 0) Bs)"
          then have "j < length Nz'" using lNz by simp
          from relNz[OF this] j show "tr (Nz' ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (map (psubst \<rho>' \<theta>' 0) Bs ! j)" by (simp add: nth_append)
        qed
      qed
      moreover have "prf_inst \<rho> \<theta>0 0 (PBound j) = PBound j" for j by simp
      ultimately show ?thesis
        by (simp add: zp prf_inst_mk_AbsPs prf_inst_proof_combP Nz'_def la_def comp_def)
    qed
    have pvn: "\<forall>x\<in>prf_vars (zprf_tr p). 0 \<le> snd x"
      sorry
    have "prf_inst \<rho> \<theta>0 0 (zprf_tr p) = prf_inst \<rho> \<theta> 0 (zprf_tr p)"
      by (rule prf_inst_cong) (use pvn in \<open>simp add: \<theta>0_def\<close>)
    moreover have "psubst \<rho> \<theta> 0 (br_prop r) = psubst \<rho> \<theta>0 0 (br_prop r)"
      using eq0[of "br_prop r" 0] nnr by (simp add: vars_thm_def)
    moreover have "tr (list_implies Nz' (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 (br_prop r))"
    proof -
      have "tr (psubst \<rho>' \<theta>' 0 C) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (psubst \<rho> \<theta>0 0 C')" by (rule equiv_sym[OF rel_tr[OF relC]])
      moreover have "list_all2 (\<lambda>X Y. tr X \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr Y) Nz' Ns"
      proof (rule list_all2_all_nthI)
        show "length Nz' = length Ns" using lNz lHs by (simp add: Ns_def)
        fix j assume j: "j < length Nz'"
        have "j < length Hs" using j lNz lHs by simp
        from relNz[OF j] relN[OF this] show "tr (Nz' ! j) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (Ns ! j)" by (meson equiv_sym equiv_trans)
      qed
      ultimately have "tr (list_implies Nz' (psubst \<rho>' \<theta>' 0 C)) \<equiv>\<^sub>\<beta>\<^sub>\<eta> tr (list_implies Ns (psubst \<rho> \<theta>0 0 C'))"
        by (intro tr_list_implies_cong)
      then show ?thesis by (simp add: bprop psubst_list_implies' Ns_def)
    qed
    ultimately show "prf_ok V' H [] [] (prf_inst \<rho> \<theta> 0 (zprf_tr p)) (psubst \<rho> \<theta> 0 (br_prop r))"
      using prf_ok.conv[OF okp _ wtyP] by simp
  qed
  text \<open>The invariant of the new proof.\<close>
  let ?Ar = "tvars_env (tyenv env') \<union> A"
  have ti'': "tinv ar (maxidx env') (tyenv env') A" by (rule pinvD(2)[OF pi''])
  have wfp: "wft ar propT" using imp by (simp add: tyA_def imp_type_def)
  from wt_thm_restrict[OF wtr wfp] obtain Wr where Wr: "\<forall>x. tyA ar ?Ar (Wr x)"
    "wt_thm ar ?Ar Wr (maxidx env') (br_tpairs r) (br_prop r)"
    "\<forall>x\<in>vars_thm (br_tpairs r) (br_prop r). Wr x = tctx env' W'' x" .
  define Wf where "Wf x = (if x \<in> vars_thm (br_tpairs r) (br_prop r) then Wr x else tctx env' W3 x)" for x
  have thm3: "tctx env' W3 x = tctx env' W'' x" if "x \<in> vars_thm (br_tpairs r) (br_prop r)" for x
    by (rule tctx3[OF rOH[OF that]])
  have Wfty: "\<forall>x. tyA ar ?Ar (Wf x)"
  proof
    fix x
    have tw: "tyw ar (tyenv env') A (vtyp env' W3 x)"
    proof (cases "vt_lookup (tenv env') x")
      case None
      have "\<forall>y. tyw ar (tyenv env') A (W3 y)" using pi3 by (simp add: pinv_def)
      with None show ?thesis by (simp add: vtyp_def del: split_paired_All)
    next
      case (Some Uu)
      then obtain U u where l: "vt_lookup (tenv env') x = Some (U, u)" by (cases Uu) auto
      have "U \<in> etys env'" using etysI[OF l] by blast
      with l pi3 show ?thesis by (auto simp: vtyp_def pinv_def)
    qed
    have "tyA ar ?Ar (tctx env' W3 x)" using tyw_tnorm[OF ti'' tw] by (simp add: tyA_def tyw_def)
    then show "tyA ar ?Ar (Wf x)" using spec[OF Wr(1), of x] by (simp add: Wf_def)
  qed
  have Wfthm: "wt_thm ar ?Ar Wf (maxidx env') (br_tpairs r) (br_prop r)"
  proof -
    have c: "wt_term ar ?Ar Wf (maxidx env') t T"
      if "wt_term ar ?Ar Wr (maxidx env') t T" "vars t \<subseteq> vars_thm (br_tpairs r) (br_prop r)" for t T
    proof -
      have "has_type Wf [] t T"
        by (rule has_type_vars_cong[of Wr]) (use that in \<open>auto simp: wt_term_def Wf_def\<close>)
      with that(1) show ?thesis by (simp add: wt_term_def)
    qed
    show ?thesis using Wr(2) unfolding wt_thm_def by (fastforce intro: c simp: vars_thm_def)
  qed
  have tvlo: "\<forall>q\<in>tvars_env (tyenv (br_env r)). 0 \<le> snd (fst q)"
    by (rule bicompose_aux_thm_typed(4)[OF ok res cfg finA state rule A(1) _ A(3) ns er fl vl _ lo _ _ cA])
      (use A(2) A0 nn in auto)
  have pz: "zinv ?Ar Wf (maxidx env') p"
    sorry
  have "zthm_prf_inv (maxidx env') (br_tpairs r) (br_prop r) H p"
    unfolding zthm_prf_inv_def
  proof (intro exI[of _ ?Ar] exI[of _ Wf] conjI)
    show "finite ?Ar" using finA finite_tvars_env by simp
    show "scons ?Ar" using ti'' by (simp add: tinv_def)
    show "tcert alg ?Ar" using pinvD(7)[OF pi'' cA] cA by simp
    show "\<forall>q\<in>?Ar. 0 \<le> snd (fst q) \<and> snd (fst q) \<le> maxidx env'"
      using tvlo A0 ti'' rbr(1) by (auto simp: tinv_def)
    show "\<forall>x. tyA ar ?Ar (Wf x)" by (rule Wfty)
    show "wt_thm ar ?Ar Wf (maxidx env') (br_tpairs r) (br_prop r)" by (rule Wfthm)
    show "prf_valid alg ar Wf H (br_tpairs r) (zprf_tr p) (br_prop r)"
      by (rule prf_valid_cong_vars[OF pvld]) (auto simp: Wf_def Wr(3) thm3)
    show "zinv ?Ar Wf (maxidx env') p" by (rule pz)
  qed
  then show ?thesis using bp rbr rp' by (simp add: nlift_def)
qed

end

end
