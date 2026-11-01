section \<open>Normalisation of tight terms\<close>

theory ZTerm_Norm
  imports ZTerm_Bicompose
begin

text \<open>
  The normalisation of tight types and terms with respect to an environment computes the
  classic normalisation on the decoded types and terms, if the environment binds no variables
  of index \<open>-1\<close> (free variables of tight terms) and its values have none.
\<close>

definition tyenv_zok :: "tyenv \<Rightarrow> bool" where
  "tyenv_zok \<theta> \<longleftrightarrow> (\<forall>v S U. vt_lookup \<theta> v = Some (S, U) \<longrightarrow> snd v \<noteq> -1 \<and> (\<forall>(w, S')\<in>tvars U. snd w \<noteq> -1))"

lemma typ_of_eq_TFree: "typ_of T = TFree a S \<longleftrightarrow> T = ZTVar (a, -1) S"
  by (cases T) (auto simp: propT_def)

lemma typ_of_eq_TVar: "typ_of T = TVar v S \<longleftrightarrow> T = ZTVar v S \<and> snd v \<noteq> -1"
  by (cases T) (auto simp: propT_def)

lemma mapZ_ex:
  "\<forall>x\<in>set xs. \<exists>y. f x = returnZ y \<and> g y = h x \<Longrightarrow> \<exists>ys. mapZ f xs = returnZ ys \<and> map g ys = map h xs"
  by (induction xs) auto

lemma tyenv_zok_lookup:
  "tyenv_zok \<theta> \<Longrightarrow> vt_lookup \<theta> v = Some (S, U) \<Longrightarrow> snd v \<noteq> -1 \<and> (\<forall>(w, S')\<in>tvars U. snd w \<noteq> -1)"
  unfolding tyenv_zok_def by blast

lemma znorm_type_aux_ok':
  assumes ac: "tacyc \<theta>" and tc: "tcons_env \<theta>" and zo: "tyenv_zok \<theta>"
  shows "tcons \<theta> T0 \<Longrightarrow> typ_of T = T0 \<Longrightarrow> \<exists>T'. znorm_type_aux \<theta> T = returnZ T' \<and> typ_of T' = tnorm \<theta> T0"
proof (induction T0 arbitrary: T rule: tnorm_induct[OF ac tc, consumes 1, case_names tfree ty unb bnd])
  case (tfree a S)
  then have T: "T = ZTVar (a, -1) S" by (simp add: typ_of_eq_TFree)
  have "vt_lookup \<theta> (a, -1) = None"
    using tyenv_zok_lookup[OF zo, of "(a, -1)"] by (cases "vt_lookup \<theta> (a, -1)") auto
  then show ?case unfolding T by (subst znorm_type_aux.simps) (simp add: type_lookup_ok)
next
  case (ty a Ts)
  have IH: "\<exists>T'. znorm_type_aux \<theta> U = returnZ T' \<and> typ_of T' = tnorm \<theta> (typ_of U)"
    if "typ_of U \<in> set Ts" for U
    using ty.IH[OF that refl] .
  show ?case
  proof (cases T)
    case (ZFun U V)
    with ty.prems IH[of U] IH[of V] show ?thesis by (subst znorm_type_aux.simps) auto
  next
    case (ZType1 c U)
    with ty.prems IH[of U] show ?thesis by (subst znorm_type_aux.simps) auto
  next
    case (ZType c Us)
    with ty.prems have "\<forall>U\<in>set Us. \<exists>U'. znorm_type_aux \<theta> U = returnZ U' \<and> typ_of U' = (tnorm \<theta> \<circ> typ_of) U"
      using IH by auto
    from mapZ_ex[OF this] obtain Us' where "mapZ (znorm_type_aux \<theta>) Us = returnZ Us'"
      "map typ_of Us' = map (tnorm \<theta> \<circ> typ_of) Us" by blast
    with ZType ty.prems show ?thesis by (subst znorm_type_aux.simps) auto
  next
    case ZProp
    with ty.prems show ?thesis by (subst znorm_type_aux.simps) (simp add: propT_def)
  next
    case (ZType0 c)
    with ty.prems show ?thesis by (subst znorm_type_aux.simps) simp
  next
    case (ZTVar v S)
    with ty.prems show ?thesis by (simp split: if_splits)
  qed
next
  case (unb v S)
  then have T: "T = ZTVar v S" by (simp add: typ_of_eq_TVar)
  from unb show ?case unfolding T by (subst znorm_type_aux.simps) (simp add: type_lookup_ok tnorm_TVar[OF ac])
next
  case (bnd v S U)
  then have T: "T = ZTVar v S" by (simp add: typ_of_eq_TVar)
  have tU: "typ_of (ztyp_of U) = U"
    using tyenv_zok_lookup[OF zo bnd.hyps(1)] by (intro typ_of_ztyp_of) auto
  from bnd.IH[OF tU] obtain T' where
    "znorm_type_aux \<theta> (ztyp_of U) = returnZ T'" "typ_of T' = tnorm \<theta> U" by blast
  with bnd.hyps(1) show ?case
    unfolding T by (subst znorm_type_aux.simps) (simp add: type_lookup_ok tnorm_TVar[OF ac])
qed
lemma znorm_type_aux_ok:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tyenv_zok \<theta>" "tcons \<theta> (typ_of T)"
  shows "\<exists>T'. znorm_type_aux \<theta> T = returnZ T' \<and> typ_of T' = tnorm \<theta> (typ_of T)"
  using znorm_type_aux_ok'[OF assms refl] .

lemma znorm_type_ok:
  assumes "tacyc \<theta>" "tcons_env \<theta>" "tyenv_zok \<theta>" "tcons \<theta> (typ_of T)"
  shows "\<exists>T'. znorm_type \<theta> T = returnZ T' \<and> typ_of T' = tnorm \<theta> (typ_of T)"
  using znorm_type_aux_ok[OF assms] by (simp add: znorm_type_def tnorm_empty)
context csig
begin

subsection \<open>Bound variables\<close>

lemma zdec_zincr_bv: "zdec (zincr_bv inc lev t) = incr_bv inc lev (zdec t)"
  by (induction inc lev t rule: zincr_bv.induct) (auto simp: of_class_def)

lemma zdec_zincr_boundvars: "zdec (zincr_boundvars inc t) = incr_boundvars inc (zdec t)"
  by (simp add: zincr_boundvars_def incr_boundvars_def zdec_zincr_bv)

lemma zdec_zsubst_bound: "zdec (zsubst_bound arg lev t) = subst_bound_aux (zdec arg) lev (zdec t)"
  by (induction arg lev t rule: zsubst_bound.induct) (auto simp: of_class_def zdec_zincr_boundvars)

lemma zdec_subst_term_bound: "zdec (subst_term_bound arg t) = subst_bound (zdec arg) (zdec t)"
  by (simp add: subst_term_bound_def subst_bound_def zdec_zsubst_bound)

lemma zdec_eq_Abs: "zdec z = Abs a T b \<longleftrightarrow> (\<exists>T' b'. z = ZAbs a T' b' \<and> typ_of T' = T \<and> zdec b' = b)"
  by (cases z) (auto simp: of_class_def)

subsection \<open>Types of constants\<close>

lemma map_of_zip_map2: "map_of (zip ps (map f Us)) x = map_option f (map_of (zip ps Us) x)"
  by (induction ps arbitrary: Us) (auto simp: zip_Cons1 split: list.splits)

lemma tnorm_tsubst': "tnorm \<theta> (tsubst \<sigma> U) = tsubst (\<lambda>v S. tnorm \<theta> (\<sigma> v S)) U"
  by (simp add: tnorm_def tsubst_tsubst)

lemma tnorm_zconst_typ: "tnorm \<theta> (zconst_typ c Us) = zconst_typ c (map (tnorm \<theta>) Us)"
proof -
  have d: "tnorm \<theta> dummyT = dummyT" by (simp add: dummyT_def)
  have p: "tnorm \<theta> (case map_of (zip ps Vs) x of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) =
      (case map_of (zip ps (map (tnorm \<theta>) Vs)) x of Some X \<Rightarrow> X | None \<Rightarrow> dummyT)" for ps Vs x
    by (simp add: map_of_zip_map2 d split: option.splits)
  show ?thesis
  proof (cases "c = STR ''Pure.imp'' \<or> c = STR ''Pure.all''")
    case True
    then show ?thesis by (auto simp: zconst_typ_def imp_type_def propT_def d split: list.splits)
  next
    case False
    then show ?thesis by (simp add: zconst_typ_def tnorm_tsubst' p d split: option.splits)
  qed
qed
subsection \<open>Normalisation with respect to an environment\<close>

fun ztys :: "zterm \<Rightarrow> ztyp set" where
  "ztys (ZVar xi T) = {T}"
| "ztys (ZBound i) = {}"
| "ztys (ZConst0 c) = {}"
| "ztys (ZConst1 c T) = {T}"
| "ztys (ZConst c Ts) = set Ts"
| "ztys (ZAbs a T t) = insert T (ztys t)"
| "ztys (ZApp t u) = ztys t \<union> ztys u"
| "ztys (ZOfclass T c) = {T}"

lemma ztys_zincr_bv: "ztys (zincr_bv inc lev t) = ztys t"
  by (induction inc lev t rule: zincr_bv.induct) auto

lemma ztys_zsubst_bound: "ztys (zsubst_bound arg lev t) \<subseteq> ztys arg \<union> ztys t"
  by (induction arg lev t rule: zsubst_bound.induct) (auto simp: zincr_boundvars_def ztys_zincr_bv)

lemma ztys_subst_term_bound: "ztys (subst_term_bound arg t) \<subseteq> ztys arg \<union> ztys t"
  by (simp add: subst_term_bound_def ztys_zsubst_bound)

text \<open>The values of the term environment convert to tight terms with consistent types.\<close>

definition tenv_zok :: "ztypargs \<Rightarrow> env \<Rightarrow> bool" where
  "tenv_zok ta env \<longleftrightarrow> (\<forall>x U u. vt_lookup (tenv env) x = Some (U, u) \<longrightarrow> snd x \<noteq> -1 \<and>
    (\<exists>zu. zterm_of ta u = returnZ zu \<and> zdec zu = u \<and> (\<forall>V\<in>ztys zu. tcons (tyenv env) (typ_of V))))"

lemma liftMZ_Ok[simp]: "liftMZ (Some (Ok x)) = returnZ x"
  by (simp add: liftMZ_def returnZ_def)

lemma zlookup_sim:
  assumes "ok (lookup env xi (typ_of T)) r" "tenv_zok ta env"
  shows "\<exists>r'. zlookup ta env xi T = returnZ r' \<and> map_option zdec r' = r \<and>
    (\<forall>zu. r' = Some zu \<longrightarrow> (\<forall>V\<in>ztys zu. tcons (tyenv env) (typ_of V)))"
proof (cases r)
  case None
  with assms(1) show ?thesis by (auto simp: zlookup_def)
next
  case (Some u)
  from ok_lookup_Some[OF assms(1)[unfolded Some]] obtain U where l: "vt_lookup (tenv env) xi = Some (U, u)"
    by blast
  with assms(2) obtain zu where "zterm_of ta u = returnZ zu" "zdec zu = u" "\<forall>V\<in>ztys zu. tcons (tyenv env) (typ_of V)"
    unfolding tenv_zok_def by blast
  moreover have "\<not> vt_is_empty (tenv env)" using l by (auto simp: vt_is_empty_lookup)
  ultimately show ?thesis using assms(1) Some by (auto simp: zlookup_def)
qed

lemma zlookup_free:
  "tenv_zok ta env \<Longrightarrow> zlookup ta env (x, -1) T = returnZ None"
proof -
  assume z: "tenv_zok ta env"
  have "vt_lookup (tenv env) (x, -1) = None"
    using z by (cases "vt_lookup (tenv env) (x, -1)") (auto simp: tenv_zok_def)
  then show ?thesis by (auto simp: zlookup_def lookup_def)
qed

lemma tvars_zconst_typ: "tvars (zconst_typ c Us) \<subseteq> (\<Union>U\<in>set Us. tvars U)"
proof (cases "c = STR ''Pure.imp'' \<or> c = STR ''Pure.all''")
  case True
  then show ?thesis by (auto simp: zconst_typ_def imp_type_def propT_def dummyT_def split: list.splits)
next
  case False
  have h: "(case map_of (zip ps Us) y of Some X \<Rightarrow> X | None \<Rightarrow> dummyT) \<in> insert dummyT (set Us)" for ps y
    by (auto split: option.splits dest: map_of_SomeD set_zip_rightD)
  have d: "tvars dummyT = {}" by (simp add: dummyT_def)
  show ?thesis
  proof
    fix x assume "x \<in> tvars (zconst_typ c Us)"
    with False obtain U0 v S where "ctab c = Some U0" "(v, S) \<in> tvars U0"
      "x \<in> tvars (case map_of (zip (tparams U0) Us) (v, S) of Some X \<Rightarrow> X | None \<Rightarrow> dummyT)"
      by (auto simp: zconst_typ_def tvars_tsubst d split: option.splits)
    with h[of "tparams U0" "(v, S)"] d show "x \<in> (\<Union>U\<in>set Us. tvars U)" by auto
  qed
qed

lemma tcons_zconst_typ: "\<forall>U\<in>set Us. tcons \<theta> U \<Longrightarrow> tcons \<theta> (zconst_typ c Us)"
  using tvars_zconst_typ[of c Us] unfolding tcons_def by blast

lemma tcons_tys_zdec: "\<forall>V\<in>ztys z. tcons \<theta> (typ_of V) \<Longrightarrow> \<forall>U\<in>tys (zdec z). tcons \<theta> U"
  by (induction z) (auto simp: of_class_def propT_def intro!: tcons_zconst_typ split: if_splits)

lemma znorm_term_aux_sim:
  assumes "norm_term2 env t0 = Some r"
  shows "r = Ok t0' \<Longrightarrow> \<forall>U\<in>tys t0. tcons (tyenv env) U \<Longrightarrow> tacyc (tyenv env) \<Longrightarrow> tcons_env (tyenv env) \<Longrightarrow>
    \<forall>U\<in>etys env. tcons (tyenv env) U \<Longrightarrow> tyenv_zok (tyenv env) \<Longrightarrow> tenv_zok ta env \<Longrightarrow>
    (\<forall>a T. t0 = Const a T \<longrightarrow> t0' = Const a (tnorm (tyenv env) T)) \<and>
    (\<forall>z. zdec z = t0 \<longrightarrow> (\<forall>V\<in>ztys z. tcons (tyenv env) (typ_of V)) \<longrightarrow>
      (\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and>
        (\<forall>V\<in>ztys z'. tcons (tyenv env) (typ_of V))))"
  using assms
proof (induction env t0 r arbitrary: t0' rule: norm_term2.raw_induct[rotated, consumes 1])
  case (1 nt env t0 r)
  note t0' = "1.hyps"[unfolded "1.prems"(1)]
  let ?\<theta> = "tyenv env"
  have ac: "tacyc ?\<theta>" and tc: "tcons_env ?\<theta>" and et: "\<forall>U\<in>etys env. tcons ?\<theta> U" and zo: "tyenv_zok ?\<theta>"
    and zt: "tenv_zok ta env"
    using "1.prems"(3-7) by auto
  have IH: "(\<forall>a T. s0 = Const a T \<longrightarrow> s0' = Const a (tnorm ?\<theta> T)) \<and>
      (\<forall>z. zdec z = s0 \<longrightarrow> (\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)) \<longrightarrow>
        (\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = s0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))))"
    if "nt env s0 = Some (Ok s0')" "\<forall>U\<in>tys s0. tcons ?\<theta> U" for s0 s0'
    using "1.IH"[OF that(1) HOL.refl that(2) ac tc et zo zt] .
  have nta: "norm_type_aux ?\<theta> T = return (tnorm ?\<theta> T)" if "tcons ?\<theta> T" for T
    by (rule norm_type_aux_ok[OF ac tc that])
  have znt: "\<exists>T'. znorm_type ?\<theta> T = returnZ T' \<and> typ_of T' = tnorm ?\<theta> (typ_of T) \<and> tcons ?\<theta> (typ_of T')"
    if "tcons ?\<theta> (typ_of T)" for T
    using znorm_type_ok[OF ac tc zo that] tcons_tnorm[OF ac] by metis
  note tt = "1.prems"(2)
  show ?case
  proof (cases t0)
    case (Const a T)
    from tt Const have tT: "tcons ?\<theta> T" by simp
    from t0' Const have r0: "t0' = Const a (tnorm ?\<theta> T)" by (simp add: nta[OF tT])
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" "\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)" for z
    proof (cases z)
      case (ZConst0 c)
      with z(1) Const have T: "T = zconst_typ a []" "c = a" by auto
      with ZConst0 r0 show ?thesis by (subst znorm_term_aux.simps) (simp add: tnorm_zconst_typ)
    next
      case (ZConst1 c U)
      with z(1) Const have T: "T = zconst_typ a [typ_of U]" "c = a" by auto
      from z(2) ZConst1 znt[of U] obtain U' where "znorm_type ?\<theta> U = returnZ U'"
        "typ_of U' = tnorm ?\<theta> (typ_of U)" "tcons ?\<theta> (typ_of U')" by auto
      with T r0 ZConst1 show ?thesis by (subst znorm_term_aux.simps) (simp add: tnorm_zconst_typ)
    next
      case (ZConst c Us)
      with z(1) Const have T: "T = zconst_typ a (map typ_of Us)" "c = a" by auto
      have "\<forall>U\<in>set Us. \<exists>U'. znorm_type ?\<theta> U = returnZ U' \<and> typ_of U' = (tnorm ?\<theta> \<circ> typ_of) U"
        using znt z(2) ZConst by fastforce
      from mapZ_ex[OF this] obtain Us' where Us': "mapZ (znorm_type ?\<theta>) Us = returnZ Us'"
        "map typ_of Us' = map (tnorm ?\<theta> \<circ> typ_of) Us" by blast
      have "\<forall>V\<in>set Us'. tcons ?\<theta> (typ_of V)"
      proof
        fix V assume "V \<in> set Us'"
        then have "typ_of V \<in> set (map (tnorm ?\<theta> \<circ> typ_of) Us)" using Us'(2) by (metis image_eqI list.set_map)
        then show "tcons ?\<theta> (typ_of V)" using tcons_tnorm[OF ac] by auto
      qed
      with Us' T r0 ZConst show ?thesis
        by (subst znorm_term_aux.simps) (simp add: tnorm_zconst_typ)
    qed (use z Const in \<open>auto simp: of_class_def split: if_splits\<close>)
    with r0 Const show ?thesis by auto
  next
    case (Free a T)
    from tt Free have tT: "tcons ?\<theta> T" by simp
    from t0' Free have r0: "t0' = Free a (tnorm ?\<theta> T)" by (simp add: nta[OF tT])
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" "\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)" for z
    proof -
      from z(1) Free obtain T' where zz: "z = ZVar (a, -1) T'" "typ_of T' = T"
        by (cases z) (auto simp: of_class_def split: if_splits)
      from znt[of T'] zz z(2) obtain T'' where "znorm_type ?\<theta> T' = returnZ T''"
        "typ_of T'' = tnorm ?\<theta> (typ_of T')" "tcons ?\<theta> (typ_of T'')" by auto
      with zz r0 zlookup_free[OF zt] show ?thesis by (subst znorm_term_aux.simps) simp
    qed
    with Free r0 show ?thesis by auto
  next
    case (Var xi T)
    from tt Var have tT: "tcons ?\<theta> T" by simp
    from t0' Var obtain r' where lk: "ok (lookup env xi T) r'"
      and rest: "ok (case r' of Some u \<Rightarrow> nt env u
        | None \<Rightarrow> norm_type_aux ?\<theta> T \<bind> (\<lambda>T'. return (Var xi T'))) t0'"
      by auto
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" "\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)" for z
    proof -
      from z(1) Var obtain T' where zz: "z = ZVar xi T'" "typ_of T' = T" "snd xi \<noteq> -1"
        by (cases z) (auto simp: of_class_def split: if_splits)
      from zlookup_sim[OF lk[folded zz(2)] zt] obtain r'' where zl: "zlookup ta env xi T' = returnZ r''"
        "map_option zdec r'' = r'" "\<forall>zu. r'' = Some zu \<longrightarrow> (\<forall>V\<in>ztys zu. tcons ?\<theta> (typ_of V))"
        by blast
      show ?thesis
      proof (cases r')
        case None
        with rest have r0: "t0' = Var xi (tnorm ?\<theta> T)" by (simp add: nta[OF tT])
        from znt[of T'] zz z(2) obtain T'' where "znorm_type ?\<theta> T' = returnZ T''"
          "typ_of T'' = tnorm ?\<theta> (typ_of T')" "tcons ?\<theta> (typ_of T'')" by auto
        with zz zl None r0 show ?thesis by (subst znorm_term_aux.simps) simp
      next
        case (Some u)
        from zl(2) Some obtain zu where r'': "r'' = Some zu" "zdec zu = u" by auto
        from ok_lookup_Some[OF lk[unfolded Some]] obtain U where "vt_lookup (tenv env) xi = Some (U, u)"
          by blast
        then have tu: "\<forall>V\<in>tys u. tcons ?\<theta> V" using et etysI[of env xi U u] by blast
        from rest Some have "nt env u = Some (Ok t0')" by simp
        from IH[OF this tu] r'' zl(3) obtain z' where "znorm_term_aux ((ta, env), zu) = returnZ z'"
          "zdec z' = t0'" "\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V)"
          by blast
        with zz zl r'' show ?thesis by (subst znorm_term_aux.simps) simp
      qed
    qed
    with Var show ?thesis by auto
  next
    case (Bound i)
    with t0' have r0: "t0' = Bound i" by simp
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" for z
    proof -
      from z Bound have "z = ZBound i" by (cases z) (auto simp: of_class_def split: if_splits)
      with r0 show ?thesis by (subst znorm_term_aux.simps) simp
    qed
    with Bound show ?thesis by auto
  next
    case (Abs a T b)
    from tt Abs have tT: "tcons ?\<theta> T" and tb: "\<forall>U\<in>tys b. tcons ?\<theta> U" by auto
    from t0' Abs obtain b0' where nb: "nt env b = Some (Ok b0')" and r0: "t0' = Abs a (tnorm ?\<theta> T) b0'"
      by (auto simp: nta[OF tT])
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" "\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)" for z
    proof -
      from z(1) Abs obtain T' b' where zz: "z = ZAbs a T' b'" "typ_of T' = T" "zdec b' = b"
        using zdec_eq_Abs by blast
      from znt[of T'] zz z(2) obtain T'' where T'': "znorm_type ?\<theta> T' = returnZ T''"
        "typ_of T'' = tnorm ?\<theta> (typ_of T')" "tcons ?\<theta> (typ_of T'')" by auto
      from IH[OF nb tb] zz z(2) obtain b'' where "znorm_term_aux ((ta, env), b') = returnZ b''"
        "zdec b'' = b0'" "\<forall>V\<in>ztys b''. tcons ?\<theta> (typ_of V)" by auto
      with zz T'' r0 show ?thesis by (subst znorm_term_aux.simps) simp
    qed
    with Abs show ?thesis by auto
  next
    case (App f0 u0)
    from tt App have tf: "\<forall>U\<in>tys f0. tcons ?\<theta> U" and tu: "\<forall>U\<in>tys u0. tcons ?\<theta> U" by auto
    have "\<exists>z'. znorm_term_aux ((ta, env), z) = returnZ z' \<and> zdec z' = t0' \<and> (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
      if z: "zdec z = t0" "\<forall>V\<in>ztys z. tcons ?\<theta> (typ_of V)" for z
    proof (cases z)
      case (ZOfclass T c)
      with z App have f0: "f0 = Const (c + STR ''_class'') (Type STR ''itself'' [typ_of T] \<rightarrow>\<^sub>T propT)"
        and u0: "u0 = Const STR ''Pure.type'' (Type STR ''itself'' [typ_of T])"
        by (auto simp: of_class_def)
      have tT: "tcons ?\<theta> (typ_of T)" using z(2) ZOfclass by simp
      from t0' App f0 obtain nf0 where nf0: "nt env f0 = Some (Ok nf0)"
        and rest: "ok (case nf0 of Abs _ _ body \<Rightarrow> nt env (subst_bound u0 body)
          | _ \<Rightarrow> nt env u0 \<bind> (\<lambda>nu. return (nf0 $ nu))) t0'"
        by auto
      from IH[OF nf0 tf] f0
      have nf0': "nf0 = Const (c + STR ''_class'') (tnorm ?\<theta> (Type STR ''itself'' [typ_of T] \<rightarrow>\<^sub>T propT))"
        by blast
      with rest obtain nu0 where nu0: "nt env u0 = Some (Ok nu0)" and r0: "t0' = nf0 $ nu0" by auto
      from IH[OF nu0 tu] u0 have nu0': "nu0 = Const STR ''Pure.type'' (tnorm ?\<theta> (Type STR ''itself'' [typ_of T]))"
        by blast
      from znt[OF tT] obtain T' where "znorm_type ?\<theta> T = returnZ T'" "typ_of T' = tnorm ?\<theta> (typ_of T)"
        "tcons ?\<theta> (typ_of T')" by blast
      with ZOfclass r0 nf0' nu0' show ?thesis
        by (subst znorm_term_aux.simps) (simp add: of_class_def propT_def)
    next
      case (ZApp g v)
      with z App have g: "zdec g = f0" and v: "zdec v = u0" and tg: "\<forall>V\<in>ztys g. tcons ?\<theta> (typ_of V)"
        and tv: "\<forall>V\<in>ztys v. tcons ?\<theta> (typ_of V)" by auto
      have sb: "\<exists>z'. znorm_term_aux ((ta, env), subst_term_bound v body') = returnZ z' \<and> zdec z' = t0' \<and>
          (\<forall>V\<in>ztys z'. tcons ?\<theta> (typ_of V))"
        if "nt env (subst_bound u0 body) = Some (Ok t0')" "zdec body' = body" "\<forall>U\<in>tys body. tcons ?\<theta> U"
          "\<forall>V\<in>ztys body'. tcons ?\<theta> (typ_of V)" for body body'
      proof -
        have "\<forall>U\<in>tys (subst_bound u0 body). tcons ?\<theta> U" using tys_subst_bound[of u0 body] that(3) tu by auto
        note IH' = IH[OF that(1) this]
        have "zdec (subst_term_bound v body') = subst_bound u0 body"
          by (simp add: zdec_subst_term_bound v that(2))
        moreover have "\<forall>V\<in>ztys (subst_term_bound v body'). tcons ?\<theta> (typ_of V)"
          using ztys_subst_term_bound[of v body'] tv that(4) by auto
        ultimately show ?thesis using IH' by blast
      qed
      show ?thesis
      proof (cases "\<exists>a T body. f0 = Abs a T body")
        case True
        then obtain x T0 body0 where f0: "f0 = Abs x T0 body0" by blast
        from g f0 obtain T' body' where ga: "g = ZAbs x T' body'" "zdec body' = body0"
          using zdec_eq_Abs by blast
        from t0' App f0 have n: "nt env (subst_bound u0 body0) = Some (Ok t0')" by simp
        have tbd: "\<forall>U\<in>tys body0. tcons ?\<theta> U" using tf f0 by auto
        have tbd': "\<forall>V\<in>ztys body'. tcons ?\<theta> (typ_of V)" using tg ga by auto
        from sb[OF n ga(2) tbd tbd'] ga ZApp show ?thesis by (subst znorm_term_aux.simps) simp
      next
        case False
        have gA: "\<forall>x T' b'. g \<noteq> ZAbs x T' b'" using False g by auto
        from t0' App False obtain nf0 where nf0: "nt env f0 = Some (Ok nf0)"
          and rest: "ok (case nf0 of Abs _ _ body \<Rightarrow> nt env (subst_bound u0 body)
            | _ \<Rightarrow> nt env u0 \<bind> (\<lambda>nu. return (nf0 $ nu))) t0'"
          by (cases f0) auto
        from IH[OF nf0 tf] g tg obtain nf where nf: "znorm_term_aux ((ta, env), g) = returnZ nf"
          "zdec nf = nf0" "\<forall>V\<in>ztys nf. tcons ?\<theta> (typ_of V)" by blast
        have unf: "znorm_term_aux ((ta, env), z) = (case nf of
            ZAbs _ _ body \<Rightarrow> znorm_term_aux ((ta, env), subst_term_bound v body)
          | _ \<Rightarrow> znorm_term_aux ((ta, env), v) \<bind> (\<lambda>nu. returnZ (ZApp nf nu)))"
          unfolding ZApp using gA nf(1) by (subst znorm_term_aux.simps) (cases g; simp cong: zterm.case_cong)
        show ?thesis
        proof (cases "\<exists>a T body. nf0 = Abs a T body")
          case True
          then obtain x T0 body0 where nf0A: "nf0 = Abs x T0 body0" by blast
          from nf(2) nf0A obtain T' body' where nfA: "nf = ZAbs x T' body'" "zdec body' = body0"
            using zdec_eq_Abs by blast
          from rest nf0A have n: "nt env (subst_bound u0 body0) = Some (Ok t0')" by simp
          have tbd: "\<forall>U\<in>tys body0. tcons ?\<theta> U"
            using tcons_tys_zdec[OF nf(3)] nf(2) nf0A by auto
          have tbd': "\<forall>V\<in>ztys body'. tcons ?\<theta> (typ_of V)" using nf(3) nfA by auto
          from sb[OF n nfA(2) tbd tbd'] unf nfA show ?thesis by simp
        next
          case False
          from rest False obtain nu0 where nu0: "nt env u0 = Some (Ok nu0)" and r0: "t0' = nf0 $ nu0"
            by (cases nf0) auto
          from IH[OF nu0 tu] v tv obtain nu where "znorm_term_aux ((ta, env), v) = returnZ nu"
            "zdec nu = nu0" "\<forall>V\<in>ztys nu. tcons ?\<theta> (typ_of V)" by blast
          moreover have "\<forall>x T' b'. nf \<noteq> ZAbs x T' b'" using False nf(2) by auto
          ultimately show ?thesis using unf r0 nf by (cases nf) auto
        qed
      qed
    qed (use z App in \<open>auto simp: of_class_def split: if_splits\<close>)
    with App show ?thesis by auto
  qed
qed

end

end
